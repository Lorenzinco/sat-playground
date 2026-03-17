pub mod decision_level;
pub mod implication_level;

use crate::history::decision_level::DecisionLevel;
use crate::history::implication_level::ImplicationLevels;
use crate::formula::assignment::Assignment;
use crate::formula::literal::Literal;


pub struct History {
    decision_levels: Vec<DecisionLevel>,
    pub implication_levels_indexes: implication_level::ImplicationLevels
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
        
        let negated = literal.negated();
        if let Some(_) = self.decision_levels.iter().filter(|il| il.get_decision_literal().is_some_and(|lit| lit == &negated)).next(){
            return Some(negated)
        }
        if let Some(_) = self.implication_levels_indexes.get_level(&negated){
            return Some(negated)
        }
        
        let level = self.decision_levels.last_mut().expect("No decisions yet!");
        
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

#[cfg(test)]
mod history{
    use crate::formula::Formula;
    use super::*;
    
    #[test]
    fn no_decisions(){
        let mut history = History::new();
        
        let lit = Literal::new(0,true);
        
        history.add_implication(&lit, None);
        assert_eq!(history.get_decision_level(),0);
    }
    
    #[test]
    fn conflict(){
        let mut history = History::new();
        
        let lit = Literal::new(0,true);
        let neg = lit.negated();
        
        history.add_decision(&lit);
        let conflict = history.add_implication(&neg, Some(2));
        assert!(conflict.is_some());
        assert_eq!(conflict.unwrap(),lit);   
    }
    
    #[test]
    fn revert_decision(){
        let clauses:Vec<Vec<i64>> = vec![vec![-1,2],vec![-2,-3],vec![3,-4]];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();
        
        let lit1 = Literal::new(0,false);
        
        formula.assignment.assign_history(&lit1, &mut history);
        assert!(formula.pure_literals_propagate_history(&mut history));
        println!("{:?}",formula);
        
        assert!(formula.assignment.get_value(0).is_some());
        assert!(formula.assignment.get_value(1).is_some());
        assert!(formula.assignment.get_value(2).is_some());
        assert!(formula.assignment.get_value(3).is_some());
        
        history.revert_last_decision(&mut formula.assignment);
        
        assert!(formula.assignment.get_value(0).is_none());
        assert!(formula.assignment.get_value(1).is_none());
        assert!(formula.assignment.get_value(2).is_none());
        assert!(formula.assignment.get_value(3).is_none());
    }
    
    #[test]
    fn implication_level(){
        let clauses:Vec<Vec<i64>> = vec![vec![-1,2],vec![-2,-3],vec![3,-4]];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();
        let lit1 = Literal::new(0,false);
        
        formula.assignment.assign_history(&lit1, &mut history);
        assert!(formula.pure_literals_propagate_history(&mut history));
        println!("{:?}",formula);
        
        assert!(formula.assignment.get_value(0).is_some());
        assert!(formula.assignment.get_value(1).is_some());
        assert!(formula.assignment.get_value(2).is_some());
        assert!(formula.assignment.get_value(3).is_some());
        
        let lit2 = Literal::new(1,false);
        assert!(history.implication_levels_indexes.get_level(&lit2).is_some_and(|level| level == 1));
        assert!(history.add_implication(&lit2.negated(),Some(2)).is_some_and(|conflict| conflict == lit2));
    }
}