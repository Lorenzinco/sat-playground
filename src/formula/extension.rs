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
        self.substitutions.insert(
            ordered_pair(lit1.get_index(), lit2.get_index()),
            substitute.get_index(),
        );
        self.add_and_definition(vec![*lit1, *lit2], substitute);
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

    #[test]
    fn binary_and_substitutions_are_commutative_and_have_a_definition() {
        let mut extensions = ExtensionMap::new();
        let x = Literal::new(1);
        let y = Literal::new(-2);
        let z = Literal::new(3);

        extensions.add_substitution(&x, &y, &z);

        assert_eq!(extensions.substitute(&x, &y), Some(z));
        assert_eq!(extensions.substitute(&y, &x), Some(z));
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
