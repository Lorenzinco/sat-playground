use crate::formula::Formula;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::formula::literal::Literal;
use pyo3::prelude::PyResult;
use std::collections::VecDeque;

pub fn solve_cdcl<'py>(formula: &mut Formula, implication_point: ImplicationPoint) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut queue: VecDeque<Literal> = VecDeque::new();
    
    let mut initial_units = Vec::new();
       for (i, clause) in formula.get_clauses().iter().enumerate() {
           if clause.len() == 1 {
               initial_units.push((i, clause.get_literals()[0].clone()));
           }
       }
   
    for (i, lit) in initial_units {
        if lit.eval(&formula.assignment) == Some(false) {
            return Ok(None); // Conflict at level 0
        } else if lit.eval(&formula.assignment) == None {
            formula.assignment.assign(lit.get_index(), !lit.is_negated());
            history.add_implication(&lit, Some(i));
            queue.push_back(lit);
        }
    }

    // Do initial propagation
    if let Some(_conflict_idx) = formula.propagate_twl(&mut history, &mut queue) {
        return Ok(None); // Conflict at decision level 0 means UNSAT
    }

    loop {

        let lit = match formula.get_unassigned_literal(){
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        // Branching (Decision)
        history.add_decision(&lit);
        formula.assignment.assign(lit.get_index(), !lit.is_negated());
        queue.push_back(lit); // Push our decision into the queue to propagate it

        // Inner conflict loop
        while let Some(conflict_idx) = formula.propagate_twl(&mut history, &mut queue) {
            if history.get_decision_level() == 0 {
                return Ok(None); // UNSAT
            }
            
            // Analyze the conflict and learn a new clause
            let (learned, backtrack_level) = history.analyze_conflict(formula, conflict_idx,implication_point);
            formula.stats.add_conflict();
            // Backtrack
            history.revert_decision(backtrack_level + 1, &mut formula.assignment);
            queue.clear(); // Important: flush the queue after a backtrack!
            
            // The learned clause should be unit at the backtrack level.
            // In 1-UIP, the first literal in the learned clause is the asserting literal.
            let asserting_lit = learned.get_literals()[0].clone();
            
            formula.stats.add_learnt_clause(&learned);
            formula.add_clause(learned);
            let new_clause_idx = formula.get_clauses().len() - 1;
            
            // Force the implication of the learned clause
            formula.assignment.assign(asserting_lit.get_index(), !asserting_lit.is_negated());
            history.add_implication(&asserting_lit, Some(new_clause_idx));
            
            // Enqueue the asserting literal so it can propagate!
            queue.push_back(asserting_lit);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Formula;

    #[test]
    fn test_cdcl_simple_sat_uip() {
        // (x1 v x2) ^ (-x1 v x3)
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);

        let res = solve_cdcl(&mut formula,ImplicationPoint::UIP).unwrap();
        assert!(res.is_some());
    }

    #[test]
    fn test_cdcl_simple_unsat_uip() {
        // (x1) ^ (-x1)
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);

        let res = solve_cdcl(&mut formula,ImplicationPoint::UIP).unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_cdcl_inner_conflict_loop_uip() {
        // (x1 v x2) ^ (x1 v -x2) ^ (-x1 v x3) ^ (-x1 v -x3)
        let mut formula =
            Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);

        let res = solve_cdcl(&mut formula,ImplicationPoint::UIP).unwrap();
        assert!(res.is_none());
    }
}
