use crate::formula::Formula;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use pyo3::prelude::PyResult;
use std::collections::VecDeque;

pub fn solve_cdcl<'py>(
    formula: &mut Formula,
    implication_point: ImplicationPoint,
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut queue: VecDeque<Literal> = VecDeque::new();

    // Initial unit clauses
    let mut initial_units = Vec::new();
    for (i, clause) in formula.get_clauses().iter().enumerate() {
        if clause.len() == 1 {
            initial_units.push((i, clause.get_literals()[0].clone()));
        }
    }

    for (i, lit) in initial_units {
        match lit.eval(&formula.assignment) {
            Some(false) => return Ok(None), // level-0 conflict
            Some(true) => {}
            None => {
                formula.assignment.assign(lit.get_index(), !lit.is_negated());
                history.add_implication(&lit, Some(i));
                queue.push_back(lit);
            }
        }
    }

    // Initial propagation
    if formula.propagate_twl(&mut history, &mut queue).is_some() {
        return Ok(None);
    }

    loop {
        let decision_lit = match formula.get_unassigned_literal() {
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        // Decision
        history.add_decision(&decision_lit);
        formula
            .assignment
            .assign(decision_lit.get_index(), !decision_lit.is_negated());
        queue.push_back(decision_lit);

        // Conflict loop
        while let Some(conflict_idx) = formula.propagate_twl(&mut history, &mut queue) {
            if history.get_decision_level() == 0 {
                return Ok(None);
            }

            let (mut learned, backtrack_level, dip_pair) =
                history.analyze_conflict(formula, conflict_idx, implication_point);

            // DIP compression: replace the two DIP literals by an extension variable z
            if let Some((l1, l2)) = dip_pair.clone() {
                let z = match formula.extensions.substitute(&l1, &l2) {
                    Some(ext_lit) => {
                        ext_lit
                    },
                    None => {
                        let new_z = formula.add_literal();
                        formula.stats.add_literal();
                        formula.extensions.add_substitution(&l1, &l2, &new_z);

                        // z <-> (l1 v l2)
                        formula.add_clause(Clause::from_literals(&vec![
                            new_z.negated(),
                            l1.clone(),
                            l2.clone(),
                        ]));
                        formula.add_clause(Clause::from_literals(&vec![
                            new_z.clone(),
                            l1.negated(),
                        ]));
                        formula.add_clause(Clause::from_literals(&vec![
                            new_z.clone(),
                            l2.negated(),
                        ]));

                        new_z
                    }
                };

                // Replace the first two literals (the DIP pair) with z.
                // This assumes analyze_conflict returns the DIP pair in the first two positions.
                let mut new_lits = vec![z];
                for lit in learned.get_literals().iter().skip(2) {
                    new_lits.push(lit.clone());
                }
                learned = Clause::from_literals(&new_lits);
            }

            // Greedy extension substitution over the remaining clause
            let mut final_lits = Vec::new();
            let mut lits_iter = learned.get_literals().iter().peekable();

            while let Some(current_lit) = lits_iter.next() {
                if let Some(next_lit) = lits_iter.peek() {
                    if let Some(substitute) = formula.extensions.substitute(current_lit, next_lit) {
                        final_lits.push(substitute);
                        lits_iter.next();
                        continue;
                    }
                }
                final_lits.push(current_lit.clone());
            }

            learned = Clause::from_literals(&final_lits);

            // Backtrack before adding/using the learned clause
            formula.stats.add_conflict();
            history.revert_decision(backtrack_level + 1, &mut formula.assignment);
            queue.clear();

            formula.stats.add_learnt_clause(&learned);
            formula.add_clause(learned.clone());
            let new_clause_idx = formula.get_clauses().len() - 1;

            // Both UIP and DIP clauses are now asserting at the backtrack level.
            // For DIP, the extension variable `z` acts as the asserting unit literal.
            let asserting_lit = learned.get_literals()[0].clone();
            match asserting_lit.eval(&formula.assignment) {
                Some(false) => {
                    // Defensive: if this happens, the learned clause/backtrack level is inconsistent
                    return Ok(None);
                }
                Some(true) => {
                    // Already assigned consistently; nothing to enqueue
                }
                None => {
                    formula
                        .assignment
                        .assign(asserting_lit.get_index(), !asserting_lit.is_negated());
                    history.add_implication(&asserting_lit, Some(new_clause_idx));
                    queue.push_back(asserting_lit);
                    
                    // IF IT WAS A DIP, WE MUST FORCE BCP ON THE UNDERLYING VARIABLES
                    // TO PREVENT A DETERMINISTIC INFINITE LOOP
                    if let Some((l1, _l2)) = dip_pair {
                        // We heuristically force one of the DIP literals to false 
                        // to force the other to true via the z definition clause.
                        let force_false_lit = l1.negated();
                        if force_false_lit.eval(&formula.assignment).is_none() {
                            formula.assignment.assign(force_false_lit.get_index(), !force_false_lit.is_negated());
                            history.add_implication(&force_false_lit, None); // Driven by heuristics, no specific clause reason
                            queue.push_back(force_false_lit);
                        }
                    }
                }
            }
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
    
    #[test]
    fn test_cdcl_simple_sat_dip() {
        // (x1 v x2) ^ (-x1 v x3)
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);

        let res = solve_cdcl(&mut formula, ImplicationPoint::DIP).unwrap();
        assert!(res.is_some());
    }

    #[test]
    fn test_cdcl_simple_unsat_dip() {
        // (x1) ^ (-x1)
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);

        let res = solve_cdcl(&mut formula, ImplicationPoint::DIP).unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_cdcl_inner_conflict_loop_dip() {
        // (x1 v x2) ^ (x1 v -x2) ^ (-x1 v x3) ^ (-x1 v -x3)
        let mut formula =
            Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);

        let res = solve_cdcl(&mut formula, ImplicationPoint::DIP).unwrap();
        assert!(res.is_none());
    }
}
