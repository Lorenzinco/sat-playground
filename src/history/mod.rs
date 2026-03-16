pub mod decision_level;
pub mod implication_level;

use crate::history::decision_level::DecisionLevel;
use crate::history::implication_level::ImplicationLevels;
use crate::formula::assignment::Assignment;
use crate::formula::literal::Literal;


pub struct History {
    decision_levels: Vec<DecisionLevel>,
    implication_levels_indexes: implication_level::ImplicationLevels
}

impl History {
    /// History contains the pile of decisions made, as well as a hashmap that goes from literal to eventually which level it was implied.
    pub fn new()->Self{
        let mut decision_levels: Vec<DecisionLevel> = Vec::new();
        decision_levels.push(DecisionLevel::empty());
        Self {
            decision_levels: decision_levels,
            implication_levels_indexes: ImplicationLevels::new()
        }
    }
    
    /// Adds a decision and a new decision level, a decision is an arbitrary value choice for a variable.
    pub fn add_decision(&mut self, literal: &Literal) {
        self.decision_levels.push(DecisionLevel::new(literal))
    }
    
    /// Adds an implication inside the last level of decision, also keeps track of which clause this implication appears in
    /// Returns a literal if this decision created a conflict with that literal
    pub fn add_implication(&mut self, literal: &Literal, clause_index: Option<usize>)->Option<Literal>{
        let level = self.decision_levels.last_mut().expect("No decisions yet!");
        let negated = literal.negated();
        
        if let Some(_) = self.implication_levels_indexes.get_level(&negated){
            return Some(negated)
        }
        
        level.add_implied_literal(literal, clause_index);
        self.implication_levels_indexes.set_level(literal, self.decision_levels.len().checked_sub(1).expect("No decisions yet!"));
        
        None
    }
    
    /// Unsets inside the assignments all of the implications starting from level <level> onwards, also modifies the decision levels and implication levels undoing what's beyond <level>.
    pub fn revert_decision(&mut self, level: usize, assignment: &mut Assignment) {
        if level == 0 { return }
        
        let to_revert = self.decision_levels.split_off(level);
        
        for decision in to_revert {
            assignment.unset(decision.get_decision_literal().expect("Reverting unit implications").get_index());
            for implication in decision.get_implied_literals() {
                assignment.unset(implication.get_index())
            }
        }
    }
    
    pub fn revert_last_decision(&mut self, assignment: &mut Assignment) {
        self.revert_decision(self.get_decision_level(), assignment);
    }
    
    pub fn get_decision_level(&self)->usize {
        self.decision_levels.len()-1
    }
    
    pub fn last_decision_literal(&self)->Option<&Literal>{
        self.decision_levels.last().expect("at least one").get_decision_literal()
    }
    
    
}