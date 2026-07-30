use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;

use std::collections::HashMap;
use std::io::Write;

#[derive(Clone)]
pub struct ExtensionMap {
    map: HashMap<(i32, i32), i32>,
}

impl ExtensionMap {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    pub fn substitute(&self, lit1: &Literal, lit2: &Literal) -> Option<Literal> {
        let idx1 = lit1.get_index();
        let idx2 = lit2.get_index();
        let index = if idx1 > idx2 {
            self.map.get(&(idx1, idx2))
        } else {
            self.map.get(&(idx2, idx1))
        };
        match index {
            Some(&idx) => Some(Literal::new(idx)),
            _ => None,
        }
    }

    pub fn add_substitution(&mut self, lit1: &Literal, lit2: &Literal, substitute: &Literal) {
        let idx1 = lit1.get_index();
        let idx2 = lit2.get_index();
        if idx1 > idx2 {
            self.map.insert((idx1, idx2), substitute.get_index());
        } else {
            self.map.insert((idx2, idx1), substitute.get_index());
        }
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
        Clause::from_literals(vec![z.clone(), x.negated(), y.negated()], 0),
        logger,
        None,
    );
    formula.add_clause(
        Clause::from_literals(vec![z.negated(), x.clone()], 0),
        logger,
        None,
    );
    formula.add_clause(
        Clause::from_literals(vec![z.negated(), y.clone()], 0),
        logger,
        None,
    );

    z
}
