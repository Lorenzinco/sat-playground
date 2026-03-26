pub mod decision_level;
pub mod implication_level;

use fastbit::BitVec;
use fastbit::BitRead;
use fastbit::BitWrite;

use crate::history::decision_level::DecisionLevel;
use crate::history::implication_level::ImplicationLevels;
use crate::formula::assignment::Assignment;
use crate::formula::literal::Literal;
use crate::formula::clause::Clause;
use crate::formula::Formula;


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
        self.decision_levels.push(DecisionLevel::new(literal));
        self.implication_levels_indexes.set_level(literal, self.get_decision_level());
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
            if let Some(lit) = decision.get_decision_literal() {
                assignment.unset(lit.get_index());
                self.implication_levels_indexes.unset_level(lit); 
            }
            
            for implication in decision.get_implied_literals() {
                assignment.unset(implication.get_index());
                self.implication_levels_indexes.unset_level(implication);
            }
        }
    }
    
    pub fn revert_last_decision(&mut self, assignment: &mut Assignment) {
        self.revert_decision(self.get_decision_level(), assignment);
    }
    
    pub fn get_decision_level(&self)->usize {
        self.decision_levels.len()-1
    }
    
    fn get_literal_level(&self, lit: &Literal) -> Option<usize> {
        self.implication_levels_indexes.get_level(lit)
            .or_else(|| self.implication_levels_indexes.get_level(&lit.negated()))
}
    
    pub fn last_decision_literal(&self)->Option<&Literal>{
        self.decision_levels.last().expect("at least one").get_decision_literal()
    }
    
    
    /// Returns the learned minimized clause at 1UIP and the conflict level the clause was found at.
    pub fn analyze_conflict(&self, formula: &Formula, conflict_clause_index: usize) -> (Clause, usize) {
        let current_level = self.get_decision_level();
        if current_level == 0 { return (Clause::new(), 0); } // Unsat

        let mut seen = BitVec::<u64>::new(formula.assignment.len());
        let mut learned_lits: Vec<Literal> = Vec::new();
        let mut path_count = 0;
        
        let mut current_clause_idx = Some(conflict_clause_index);
        let mut resolved_lit: Option<Literal> = None;

        let level_data = &self.decision_levels[current_level];
        let mut trail_iter = level_data.get_implied_literals_rev()
            .chain(level_data.get_decision_literal().into_iter());

        loop {
            if let Some(clause_idx) = current_clause_idx {
                let clause = &formula.get_clauses()[clause_idx];
                for lit in clause.iter() {
                    if Some(lit) == resolved_lit.as_ref() { continue; }
                    
                    let var = lit.get_index() as usize;
                    if !seen.test(var) {
                        seen.set(var);
                        if self.get_literal_level(lit) == Some(current_level) {
                            path_count += 1;
                        } else {
                            learned_lits.push(lit.clone());
                        }
                    }
                }
            }

            loop {
                if let Some(lit) = trail_iter.next() {
                    let var = lit.get_index() as usize;
                    if seen.test(var) {
                        resolved_lit = Some(lit.clone());
                        path_count -= 1;
                        current_clause_idx = level_data.get_reason(lit);
                        break;
                    }
                } else {
                    unreachable!("Trail is empty but path_count is > 0");
                }
            }

            if path_count == 0 {
                learned_lits.push(resolved_lit.unwrap().negated());
                break;
            }
        }
        
        let last_idx = learned_lits.len() - 1;
        learned_lits.swap(0, last_idx);

        let mut min_seen = BitVec::<u64>::new(formula.assignment.len());
        for lit in &learned_lits {
            min_seen.set(lit.get_index() as usize);
        }
        
        let mut poisoned = BitVec::<u64>::new(formula.assignment.len());
        
        let mut minimized_lits = Vec::new();
        minimized_lits.push(learned_lits[0].clone());
        
        for lit in learned_lits.iter().skip(1) {
            let var = lit.get_index() as usize;
            let level = self.get_literal_level(lit).unwrap_or(0);
            
            if level == 0 { continue; }
            
            let mut stack = vec![lit.clone()];
            let mut local_seen = Vec::new();
            let mut failed = false;
            
            while let Some(current) = stack.pop() {
                let c_var = current.get_index() as usize;
                
                if c_var != var && min_seen.test(c_var) { continue; }
                
                if poisoned.test(c_var) { 
                    failed = true; 
                    break; 
                }
                
                let c_level = self.get_literal_level(&current).unwrap_or(0);
                if c_level == 0 { continue; }
                
                let reason_idx = self.decision_levels[c_level].get_reason(&current);
                
                match reason_idx {
                    None => {
                        failed = true;
                        break;
                    }
                    Some(idx) => {
                        let clause = &formula.get_clauses()[idx];
                        
                        if c_var != var {
                            min_seen.set(c_var);
                            local_seen.push(c_var);
                        }
                        
                        for child in clause.get_literals() {
                            let child_var = child.get_index() as usize;
                            if child_var != c_var {
                                stack.push(child.clone());
                            }
                        }
                    }
                }
            }
            
            if failed {
                for &c_var in &local_seen {
                    min_seen.reset(c_var);
                    poisoned.set(c_var);
                }
                poisoned.set(var);
                minimized_lits.push(lit.clone());
            } else {
            }
        }
        
        let mut backtrack_level = 0;
        for lit in minimized_lits.iter().skip(1) {
            let level = self.get_literal_level(lit).unwrap_or(0);
            if level > backtrack_level {
                backtrack_level = level;
            }
        }
        
        (Clause::from_literals(&minimized_lits), backtrack_level)
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
    
    #[test]
    fn analyze_conflict_basic() {
        
        let clauses: Vec<Vec<i64>> = vec![
            vec![-1, 2],   // 0: -x1 v x2
            vec![-2, 3],   // 1: -x2 v x3
            vec![-3, 4],   // 2: -x3 v x4
            vec![-1, -4]   // 3: -x1 v -x4  (conflict)
        ];
        
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();
        
        let x1 = Literal::new(0, false); // x1
        
        formula.assignment.assign_history(&x1, &mut history);
        
        let x2 = Literal::new(1, false);
        formula.assignment.assign(x2.get_index(), true);
        history.add_implication(&x2, Some(0)); // Reason: C0 (-1, 2)
        
        let x3 = Literal::new(2, false);
        formula.assignment.assign(x3.get_index(), true);
        history.add_implication(&x3, Some(1)); // Reason: C1 (-2, 3)
        
        let x4 = Literal::new(3, false);
        formula.assignment.assign(x4.get_index(), true);
        history.add_implication(&x4, Some(2)); // Reason: C2 (-3, 4)
        
        let (learned, backtrack_level) = history.analyze_conflict(&formula, 3);
        
        println!("Learned clause: {}", learned);
        
        assert_eq!(learned.len(), 1);
        let lit = learned.iter().next().unwrap();
        assert_eq!(lit.get_index(), 0);
        assert!(lit.is_negated()); // -x1
        
        assert_eq!(backtrack_level, 0);
    }
    
    #[test]
    fn analyze_conflict_with_backtrack() {
        
        let clauses: Vec<Vec<i64>> = vec![
            vec![-1, 2],      // 0: -x1 v x2
            vec![-3, -2, 4],  // 1: -x3 v -x2 v x4
            vec![-3, -4]      // 2: -x3 v -x4 (Conflict)
        ];
        
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();
        
        let x1 = Literal::new(0, false);
        formula.assignment.assign_history(&x1, &mut history);
        
        let x2 = Literal::new(1, false);
        formula.assignment.assign(x2.get_index(), true);
        history.add_implication(&x2, Some(0));
        
        let x3 = Literal::new(2, false);
        formula.assignment.assign_history(&x3, &mut history);
        
        let x4 = Literal::new(3, false);
        formula.assignment.assign(x4.get_index(), true);
        history.add_implication(&x4, Some(1));
        
        
        let (learned, backtrack_level) = history.analyze_conflict(&formula, 2);
        
        println!("Learned: {}", learned);
        
        assert_eq!(learned.len(), 2);
        assert_eq!(backtrack_level, 1);
    }
    
    #[test]
    fn conflict_analysis_unsat() {
        let history = History::new();
        let clauses: Vec<Vec<i64>> = vec![vec![1], vec![-1]]; // Unsat immediately
        let formula = Formula::from_vec(clauses);
        
        let (clause, level) = history.analyze_conflict(&formula, 0);
        assert!(clause.len() == 0); 
        assert_eq!(level, 0);
    }
    
    #[test]
    fn conflict_analysis_simple() {
        
        let clauses: Vec<Vec<i64>> = vec![
            vec![-1, 2],
            vec![-2, 3],
            vec![-3, 4],
            vec![-4, -5],
            vec![-4, 5]
        ];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let lit1 = Literal::new(0, false); // 1
        history.add_decision(&lit1);
        formula.assignment.assign(0, true);

        
        // 1 implies 2
        let lit2 = Literal::new(1, false);
        formula.assignment.assign(1, true); 
        history.add_implication(&lit2, Some(0));

        // 2 implies 3
        let lit3 = Literal::new(2, false);
        formula.assignment.assign(2, true);
        history.add_implication(&lit3, Some(1));

        // 3 implies 4
        let lit4 = Literal::new(3, false);
        formula.assignment.assign(3, true);
        history.add_implication(&lit4, Some(2));

        // 4 implies -5
        let lit5_neg = Literal::new(4, true); // -5
        formula.assignment.assign(4, false);
        history.add_implication(&lit5_neg, Some(3));


        let (learned_clause, backtrack_level) = history.analyze_conflict(&formula, 4);
        
        // 1-UIP Analysis:
        // Resolution on 5 (from C4 and C3): -4 v -4 = -4
        // Resolution on 4 (from -4 and C2): -3
        // Resolution on 3 (from -3 and C1): -2
        // Resolution on 2 (from -2 and C0): -1
        // 1 is decision literal, stop.
        // Learned: {-1}
        
        assert_eq!(learned_clause.len(), 1);
        let lits = learned_clause.get_literals();
        println!("{:?}",learned_clause);
        assert_eq!(lits[0].get_index(), 3);
        assert!(lits[0].is_negated());
        assert_eq!(backtrack_level, 0);
    }
}