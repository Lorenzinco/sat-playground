use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;

use std::collections::{BTreeMap, HashMap};
use std::io::Write;

/// A deterministic value that can be assigned to an extension variable when a
/// model is reconstructed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum ExtensionOrigin {
    Dip,
    Bva,
    #[default]
    Other,
}

#[derive(Clone, Copy)]
struct ExactSubstitution {
    inputs: (i32, i32),
    origin: ExtensionOrigin,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExtensionDefinition {
    And(Vec<Literal>),
    Ite {
        condition: Literal,
        when_true: Literal,
        when_false: Literal,
    },
}

#[derive(Clone, Default)]
pub struct ExtensionMap {
    substitutions: HashMap<(i32, i32), i32>,
    substitution_inputs: HashMap<i32, ExactSubstitution>,
    substitution_partners: HashMap<i32, BTreeMap<i32, i32>>,
    definitions: BTreeMap<u32, ExtensionDefinition>,
    literal_utility: Vec<f64>,
    utility_increment: f64,
    utility_conflict_epoch: u64,
    utility_seen_epoch: Vec<u64>,
}

impl ExtensionMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns an exact, reusable binary-AND extension for the two literals.
    ///
    /// Not every registered definition is indexed as a substitution. Binary BVA
    /// AND grids add the reverse implication and are exact; larger BVA ANDs and
    /// ITE definitions remain model-only and are not reusable through this map.
    pub fn substitute(&self, lit1: &Literal, lit2: &Literal) -> Option<Literal> {
        self.substitutions
            .get(&ordered_pair(lit1.get_index(), lit2.get_index()))
            .copied()
            .map(Literal::new)
    }

    /// Returns the inputs of an active exact binary-AND substitution.
    ///
    /// This deliberately excludes model-only non-binary BVA and ITE definitions.
    /// A negated substitute can be expanded in a clause using De Morgan's law.
    pub fn substitution_inputs(&self, substitute: &Literal) -> Option<(Literal, Literal)> {
        self.substitution_inputs_with_origin(substitute)
            .map(|(first, second, _)| (first, second))
    }

    pub(crate) fn substitution_inputs_with_origin(
        &self,
        substitute: &Literal,
    ) -> Option<(Literal, Literal, ExtensionOrigin)> {
        self.substitution_inputs
            .get(&substitute.get_index())
            .map(|substitution| {
                let (first, second) = substitution.inputs;
                (
                    Literal::new(first),
                    Literal::new(second),
                    substitution.origin,
                )
            })
    }

    /// Returns `(partner, replacement)` for active exact binary-AND pairs
    /// containing this signed input, sorted by the partner's signed index.
    /// Model-only definitions are excluded; a self-pair is returned once.
    pub(crate) fn substitution_partners(
        &self,
        input: &Literal,
    ) -> impl Iterator<Item = (Literal, Literal)> + '_ {
        self.substitution_partners
            .get(&input.get_index())
            .into_iter()
            .flat_map(|partners| partners.iter())
            .map(|(&partner, &replacement)| (Literal::new(partner), Literal::new(replacement)))
    }

    pub fn definition(&self, extension: &Literal) -> Option<&ExtensionDefinition> {
        self.definitions.get(&extension.get_index().unsigned_abs())
    }

    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (Literal, &ExtensionDefinition)> + '_ {
        self.definitions
            .iter()
            .map(|(&variable, definition)| (Literal::new(variable as i32), definition))
    }

    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    /// Records a successful implication without affecting the branching heuristic.
    pub(crate) fn bump_propagation_utility(&mut self, literal: &Literal) {
        self.bump_literal_utility(literal);
    }

    /// Starts one conflict epoch. A signed literal is counted at most once even
    /// when it occurs in several clauses traversed by the analysis.
    pub(crate) fn begin_conflict_utility(&mut self) {
        self.utility_conflict_epoch = self.utility_conflict_epoch.wrapping_add(1);
        if self.utility_conflict_epoch == 0 {
            self.utility_seen_epoch.fill(0);
            self.utility_conflict_epoch = 1;
        }
    }

    pub(crate) fn bump_conflict_utility(&mut self, literal: &Literal) {
        let index = literal.get_unsigned_index() as usize;
        self.ensure_utility_index(index);
        if self.utility_seen_epoch[index] == self.utility_conflict_epoch {
            return;
        }
        self.utility_seen_epoch[index] = self.utility_conflict_epoch;
        self.bump_literal_utility(literal);
    }

    /// EVSIDS-style lazy decay: newer propagation and conflict events receive a
    /// larger increment, avoiding a full scan of all literal scores per conflict.
    pub(crate) fn decay_literal_utility(&mut self) {
        const UTILITY_DECAY: f64 = 0.95;
        self.ensure_utility_increment();
        if self.utility_increment / UTILITY_DECAY > 1e150 {
            self.rescale_literal_utility();
        }
        self.utility_increment /= UTILITY_DECAY;
    }

    pub(crate) fn literal_utility(&self, literal: &Literal) -> f64 {
        self.literal_utility
            .get(literal.get_unsigned_index() as usize)
            .copied()
            .unwrap_or(0.0)
    }

    fn bump_literal_utility(&mut self, literal: &Literal) {
        let index = literal.get_unsigned_index() as usize;
        self.ensure_utility_index(index);
        self.ensure_utility_increment();
        if self.literal_utility[index] + self.utility_increment > 1e150 {
            self.rescale_literal_utility();
        }
        self.literal_utility[index] += self.utility_increment;
    }

    fn ensure_utility_index(&mut self, index: usize) {
        if index >= self.literal_utility.len() {
            self.literal_utility.resize(index + 1, 0.0);
            self.utility_seen_epoch.resize(index + 1, 0);
        }
    }

    fn ensure_utility_increment(&mut self) {
        if self.utility_increment == 0.0 {
            self.utility_increment = 1.0;
        }
    }

    fn rescale_literal_utility(&mut self) {
        let divider = self
            .literal_utility
            .iter()
            .copied()
            .fold(self.utility_increment, f64::max);
        let factor = 1.0 / divider;
        for score in &mut self.literal_utility {
            *score *= factor;
        }
        self.utility_increment *= factor;
    }

    pub fn add_substitution(&mut self, lit1: &Literal, lit2: &Literal, substitute: &Literal) {
        self.add_substitution_with_origin(lit1, lit2, substitute, ExtensionOrigin::Other);
    }

    pub(crate) fn add_dip_substitution(
        &mut self,
        lit1: &Literal,
        lit2: &Literal,
        substitute: &Literal,
    ) {
        self.add_substitution_with_origin(lit1, lit2, substitute, ExtensionOrigin::Dip);
    }

    pub(crate) fn add_bva_substitution(
        &mut self,
        lit1: &Literal,
        lit2: &Literal,
        substitute: &Literal,
    ) {
        self.add_substitution_with_origin(lit1, lit2, substitute, ExtensionOrigin::Bva);
    }

    fn add_substitution_with_origin(
        &mut self,
        lit1: &Literal,
        lit2: &Literal,
        substitute: &Literal,
        origin: ExtensionOrigin,
    ) {
        let inputs = ordered_pair(lit1.get_index(), lit2.get_index());
        let replacement = substitute.get_index();
        if let Some(previous) = self.substitutions.get(&inputs).copied() {
            self.remove_substitution(previous);
        }
        // The reverse index represents one active pair per signed replacement.
        self.remove_substitution(replacement);
        self.substitutions.insert(inputs, replacement);
        for (input, partner) in [inputs, (inputs.1, inputs.0)] {
            self.substitution_partners
                .entry(input)
                .or_default()
                .insert(partner, replacement);
        }
        self.substitution_inputs
            .insert(substitute.get_index(), ExactSubstitution { inputs, origin });
        self.add_and_definition(vec![*lit1, *lit2], substitute);
    }

    pub(crate) fn substitution_origin(&self, substitute: &Literal) -> Option<ExtensionOrigin> {
        let index = substitute.get_index();
        self.substitution_inputs
            .get(&index)
            .or_else(|| self.substitution_inputs.get(&-index))
            .map(|substitution| substitution.origin)
    }

    /// Prevents conflict learning from reusing a substitution variable that BVE
    /// removed from the live formula. Its definition is intentionally retained
    /// for model reconstruction.
    pub fn remove_substitution_variable(&mut self, variable: usize) {
        let Ok(variable) = i64::try_from(variable) else {
            return;
        };
        for signed in [variable, -variable] {
            if let Ok(replacement) = i32::try_from(signed) {
                self.remove_substitution(replacement);
            }
        }
    }

    fn remove_substitution(&mut self, replacement: i32) {
        let Some(substitution) = self.substitution_inputs.remove(&replacement) else {
            return;
        };
        let inputs = substitution.inputs;
        self.substitutions.remove(&inputs);
        for (input, partner) in [inputs, (inputs.1, inputs.0)] {
            if let Some(partners) = self.substitution_partners.get_mut(&input) {
                partners.remove(&partner);
                if partners.is_empty() {
                    self.substitution_partners.remove(&input);
                }
            }
        }
    }

    pub fn add_and_definition(&mut self, inputs: Vec<Literal>, extension: &Literal) {
        assert!(
            !inputs.is_empty(),
            "an AND extension needs at least one input"
        );
        self.definitions.insert(
            extension.get_index().unsigned_abs(),
            ExtensionDefinition::And(inputs),
        );
    }

    pub fn add_ite_definition(
        &mut self,
        condition: Literal,
        when_true: Literal,
        when_false: Literal,
        extension: &Literal,
    ) {
        self.definitions.insert(
            extension.get_index().unsigned_abs(),
            ExtensionDefinition::Ite {
                condition,
                when_true,
                when_false,
            },
        );
    }
}

fn ordered_pair(first: i32, second: i32) -> (i32, i32) {
    if first > second {
        (first, second)
    } else {
        (second, first)
    }
}

pub fn extension_literal<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    x: &Literal,
    y: &Literal,
) -> Literal {
    if let Some(ext_lit) = formula.extensions.substitute(x, y) {
        return ext_lit;
    }

    let z = formula.add_literal();
    formula.stats.add_extension_literal();
    formula.extensions.add_dip_substitution(x, y, &z);

    formula.add_clause(
        Clause::from_literals(vec![z, x.negated(), y.negated()], 0),
        logger,
        None,
    );
    formula.add_clause(
        Clause::from_literals(vec![z.negated(), *x], 0),
        logger,
        None,
    );
    formula.add_clause(
        Clause::from_literals(vec![z.negated(), *y], 0),
        logger,
        None,
    );

    z
}

#[cfg(test)]
mod tests {
    use super::*;

    fn partners(extensions: &ExtensionMap, input: i32) -> Vec<(i32, i32)> {
        extensions
            .substitution_partners(&Literal::new(input))
            .map(|(partner, replacement)| (partner.get_index(), replacement.get_index()))
            .collect()
    }

    fn add(extensions: &mut ExtensionMap, first: i32, second: i32, replacement: i32) {
        extensions.add_substitution(
            &Literal::new(first),
            &Literal::new(second),
            &Literal::new(replacement),
        );
    }

    #[test]
    fn literal_utility_is_signed_recent_and_deduplicated_per_conflict() {
        let mut extensions = ExtensionMap::new();
        let positive = Literal::new(2);
        let negative = positive.negated();

        extensions.bump_propagation_utility(&positive);
        assert_eq!(extensions.literal_utility(&positive), 1.0);
        assert_eq!(extensions.literal_utility(&negative), 0.0);

        extensions.begin_conflict_utility();
        extensions.bump_conflict_utility(&negative);
        extensions.bump_conflict_utility(&negative);
        assert_eq!(extensions.literal_utility(&negative), 1.0);
        extensions.decay_literal_utility();

        extensions.bump_propagation_utility(&positive);
        assert!(extensions.literal_utility(&positive) > 2.0);
        assert_eq!(extensions.literal_utility(&negative), 1.0);
    }

    #[test]
    fn adjacency_is_signed_symmetric_sorted_and_excludes_model_only_definitions() {
        let mut extensions = ExtensionMap::new();
        add(&mut extensions, 1, 3, 10);
        add(&mut extensions, -2, 1, 11);
        add(&mut extensions, -1, 4, 12);
        add(&mut extensions, 1, 1, 13);
        add(&mut extensions, 1, 3, 10);
        extensions.add_and_definition(vec![Literal::new(1), Literal::new(5)], &Literal::new(14));
        extensions.add_ite_definition(
            Literal::new(1),
            Literal::new(6),
            Literal::new(7),
            &Literal::new(15),
        );

        assert_eq!(partners(&extensions, 1), vec![(-2, 11), (1, 13), (3, 10)]);
        assert_eq!(partners(&extensions, -2), vec![(1, 11)]);
        assert_eq!(partners(&extensions, 3), vec![(1, 10)]);
        assert_eq!(partners(&extensions, -1), vec![(4, 12)]);
        assert!(partners(&extensions, 5).is_empty());
        assert!(partners(&extensions, 6).is_empty());
        assert!(partners(&extensions, 99).is_empty());

        extensions.remove_substitution_variable(13);
        assert_eq!(partners(&extensions, 1), vec![(-2, 11), (3, 10)]);
    }

    #[test]
    fn overwritten_pair_removes_old_reverse_entry_and_survives_old_invalidation() {
        let mut extensions = ExtensionMap::new();
        add(&mut extensions, 1, -2, 10);
        add(&mut extensions, -2, 1, 11);
        assert_eq!(extensions.substitution_inputs(&Literal::new(10)), None);
        assert!(extensions.definition(&Literal::new(10)).is_some());
        extensions.remove_substitution_variable(10);
        assert_eq!(partners(&extensions, 1), vec![(-2, 11)]);
        assert_eq!(partners(&extensions, -2), vec![(1, 11)]);
        assert_eq!(
            extensions.substitute(&Literal::new(1), &Literal::new(-2)),
            Some(Literal::new(11))
        );
        assert_eq!(
            extensions.substitution_inputs(&Literal::new(11)),
            Some((Literal::new(1), Literal::new(-2)))
        );
    }

    #[test]
    fn reused_replacement_removes_old_pair_from_all_indexes() {
        let mut extensions = ExtensionMap::new();
        add(&mut extensions, 1, 2, 10);
        add(&mut extensions, 2, 3, 10);
        assert_eq!(
            extensions.substitute(&Literal::new(1), &Literal::new(2)),
            None
        );
        assert!(partners(&extensions, 1).is_empty());
        assert_eq!(partners(&extensions, 2), vec![(3, 10)]);
        assert_eq!(partners(&extensions, 3), vec![(2, 10)]);
        assert_eq!(
            extensions.substitution_inputs(&Literal::new(10)),
            Some((Literal::new(3), Literal::new(2)))
        );
    }

    #[test]
    fn invalidation_removes_both_replacement_signs_and_keeps_unrelated_pairs() {
        let mut extensions = ExtensionMap::new();
        add(&mut extensions, 1, 2, 10);
        add(&mut extensions, 1, 3, -10);
        add(&mut extensions, 1, 4, 11);
        extensions.remove_substitution_variable(10);
        extensions.remove_substitution_variable(10);
        extensions.remove_substitution_variable(99);
        assert_eq!(partners(&extensions, 1), vec![(4, 11)]);
        assert!(partners(&extensions, 2).is_empty());
        assert!(partners(&extensions, 3).is_empty());
        for replacement in [10, -10] {
            assert_eq!(
                extensions.substitution_inputs(&Literal::new(replacement)),
                None
            );
            assert!(extensions.definition(&Literal::new(replacement)).is_some());
        }
        assert_eq!(
            extensions.substitute(&Literal::new(1), &Literal::new(2)),
            None
        );
        assert_eq!(
            extensions.substitute(&Literal::new(1), &Literal::new(3)),
            None
        );
        extensions.remove_substitution_variable(11);
        assert!(extensions.substitution_partners.is_empty());
        assert!(extensions.substitutions.is_empty());
        assert!(extensions.substitution_inputs.is_empty());
    }

    #[test]
    fn binary_and_substitutions_are_commutative_and_have_a_definition() {
        let mut extensions = ExtensionMap::new();
        let x = Literal::new(1);
        let y = Literal::new(-2);
        let z = Literal::new(3);

        extensions.add_substitution(&x, &y, &z);

        assert_eq!(extensions.substitute(&x, &y), Some(z));
        assert_eq!(extensions.substitute(&y, &x), Some(z));
        assert_eq!(extensions.substitution_inputs(&z), Some((x, y)));
        assert_eq!(
            extensions.definition(&z),
            Some(&ExtensionDefinition::And(vec![x, y]))
        );
    }

    #[test]
    fn exact_substitutions_retain_their_creation_origin() {
        let mut extensions = ExtensionMap::new();
        extensions.add_dip_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(10));
        extensions.add_bva_substitution(&Literal::new(3), &Literal::new(4), &Literal::new(11));
        extensions.add_substitution(&Literal::new(5), &Literal::new(6), &Literal::new(12));

        assert_eq!(
            extensions.substitution_origin(&Literal::new(10)),
            Some(ExtensionOrigin::Dip)
        );
        assert_eq!(
            extensions.substitution_origin(&Literal::new(-10)),
            Some(ExtensionOrigin::Dip)
        );
        assert_eq!(
            extensions.substitution_origin(&Literal::new(11)),
            Some(ExtensionOrigin::Bva)
        );
        assert_eq!(
            extensions.substitution_origin(&Literal::new(12)),
            Some(ExtensionOrigin::Other)
        );
    }

    #[test]
    fn eliminated_substitution_is_removed_but_its_definition_is_retained() {
        let mut extensions = ExtensionMap::new();
        let x = Literal::new(1);
        let y = Literal::new(2);
        let z = Literal::new(3);
        extensions.add_substitution(&x, &y, &z);

        extensions.remove_substitution_variable(3);

        assert_eq!(extensions.substitute(&x, &y), None);
        assert_eq!(extensions.substitution_inputs(&z), None);
        assert_eq!(
            extensions.definition(&z),
            Some(&ExtensionDefinition::And(vec![x, y]))
        );
    }

    #[test]
    fn ite_definitions_are_registered_without_claiming_binary_substitution() {
        let mut extensions = ExtensionMap::new();
        let condition = Literal::new(1);
        let when_true = Literal::new(-2);
        let when_false = Literal::new(3);
        let z = Literal::new(4);

        extensions.add_ite_definition(condition, when_true, when_false, &z);

        assert_eq!(
            extensions.definition(&z),
            Some(&ExtensionDefinition::Ite {
                condition,
                when_true,
                when_false,
            })
        );
        assert_eq!(extensions.substitute(&when_true, &when_false), None);
        assert_eq!(
            extensions.iter().next(),
            Some((z, extensions.definition(&z).unwrap()))
        );
    }
}
