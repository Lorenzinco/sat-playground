use crate::formula::literal::Literal;
use std::collections::HashMap;

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
