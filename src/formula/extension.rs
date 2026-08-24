use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;

use std::collections::{BTreeMap, HashMap};
use std::io::Write;

/// A deterministic value that can be assigned to an extension variable when a
/// model is reconstructed.
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
    substitution_inputs: HashMap<i32, (i32, i32)>,
    substitution_partners: HashMap<i32, BTreeMap<i32, i32>>,
    definitions: BTreeMap<u32, ExtensionDefinition>,
}

impl ExtensionMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns an exact, reusable binary-AND extension for the two literals.
    ///
    /// Not every registered definition is indexed as a substitution. In
    /// particular, BVA's AND-grid encoding permits the auxiliary variable to be
    /// underconstrained, so it is recorded for model reconstruction but must not
    /// be reused as an equivalence by conflict learning.
    pub fn substitute(&self, lit1: &Literal, lit2: &Literal) -> Option<Literal> {
        self.substitutions
            .get(&ordered_pair(lit1.get_index(), lit2.get_index()))
            .copied()
            .map(Literal::new)
    }

    /// Returns the inputs of an active exact binary-AND substitution.
    ///
    /// This deliberately excludes model-only BVA and ITE definitions. A negated
    /// substitute can be expanded in a clause using De Morgan's law.
    pub fn substitution_inputs(&self, substitute: &Literal) -> Option<(Literal, Literal)> {
        self.substitution_inputs
            .get(&substitute.get_index())
            .copied()
            .map(|(first, second)| (Literal::new(first), Literal::new(second)))
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

    pub fn add_substitution(&mut self, lit1: &Literal, lit2: &Literal, substitute: &Literal) {
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
            .insert(substitute.get_index(), inputs);
        self.add_and_definition(vec![*lit1, *lit2], substitute);
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
        let Some(inputs) = self.substitution_inputs.remove(&replacement) else {
            return;
        };
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
    formula.extensions.add_substitution(x, y, &z);

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
