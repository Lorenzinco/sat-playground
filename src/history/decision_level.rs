use crate::formula::literal::Literal;
use indexmap::IndexMap;


pub struct DecisionLevel{
    decision_literal: Option<Literal>,
    implied_literals: IndexMap<Literal,Option<usize>>    
}

impl DecisionLevel{
    
    pub fn new(decision_literal: &Literal) -> Self {
        Self {
            decision_literal: Some(decision_literal.clone()),
            implied_literals: IndexMap::new()
        }
    }
    
    pub fn empty() -> Self {
        Self {
            decision_literal: None,
            implied_literals: IndexMap::new()
        }
    }
    
    pub fn add_implied_literal(&mut self, lit: &Literal, clause_index: Option<usize>) {
        self.implied_literals.insert(lit.clone(), clause_index);
    }

    pub fn get_decision_literal(&self) -> Option<&Literal> {
        self.decision_literal.as_ref()
    }
    
    pub fn get_implied_literals_with_clauses(&self) -> Vec<(&Literal, usize)> {
        self.implied_literals.iter().filter(|c| c.1.is_some()).map(|c| (c.0,c.1.unwrap())).collect()
    }
    
    pub fn get_implied_literals(&self) -> Vec<&Literal> {
        self.implied_literals.keys().collect()
    }
}

