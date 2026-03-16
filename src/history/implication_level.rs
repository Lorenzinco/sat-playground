use std::collections::HashMap;
use crate::formula::literal::Literal;

pub struct ImplicationLevels {
    map: HashMap<Literal, usize>
}

impl ImplicationLevels {
    pub fn new() -> Self {
        Self {
            map: HashMap::new()
        }
    }
    
    pub fn set_level(&mut self, lit: &Literal, level: usize) {
        self.map.insert(lit.clone(), level);
    }
    
    pub fn get_level(&self, lit: &Literal) -> Option<usize> {
        self.map.get(lit).cloned()
    }
    
    pub fn unset_level(&mut self, lit: &Literal) {
        self.map.remove(lit);
    }
}