use crate::drat::DratLogger;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::formula::vsids::Vsids;
use crate::formula::Formula;
use crate::history::ConflictLearnResult;
use crate::history::History;
use crate::history::ImplicationPoint;

use pyo3::prelude::PyResult;

use std::collections::VecDeque;
use std::fs::File;

pub fn solve_cdcl<'py>(
    formula: &mut Formula,
    implication_point: ImplicationPoint,
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut queue: VecDeque<Literal> = VecDeque::new();
    let mut vsids = Vsids::new(formula.assignment.len());
    let mut logger = DratLogger::new(File::create("proof.drat").unwrap());

    // Initial unit clauses
    let mut initial_units = Vec::new();
    for (i, clause) in formula.get_clauses().iter().enumerate() {
        if clause.len() == 1 {
            initial_units.push((i, clause.get_literals()[0].clone()));
        }
    }

    for (i, lit) in initial_units {
        match lit.eval(&formula.assignment) {
            Some(false) => {
                let _ = logger.log_empty_clause();
                return Ok(None);
            }
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
        let _ = logger.log_empty_clause();
        return Ok(None);
    }

    loop {
        let decision_lit = match vsids.get_best_unassigned(formula) {
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        history.add_decision(&decision_lit);
        formula
            .assignment
            .assign(decision_lit.get_index(), !decision_lit.is_negated());
        queue.push_back(decision_lit);

        while let Some(conflict_idx) = formula.propagate_twl(&mut history, &mut queue) {
            if history.get_decision_level() == 0 {
                let _ = logger.log_empty_clause();
                return Ok(None);
            }

            formula.stats.add_conflict();

            match history.analyze_conflict(formula, conflict_idx, implication_point) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                } => {
                    let learned = clause.clone();

                    // Proof logging: standard UIP clause only.
                    let _ = logger.log_add(learned.get_literals());

                    let mut actual_backtrack = backtrack_level;
                    history.revert_decision(actual_backtrack + 1, &mut formula.assignment);

                    while learned.is_empty(&formula.assignment) {
                        if actual_backtrack == 0 {
                            let _ = logger.log_empty_clause();
                            return Ok(None);
                        }
                        actual_backtrack -= 1;
                        history.revert_decision(actual_backtrack + 1, &mut formula.assignment);
                    }

                    queue.clear();

                    formula.stats.add_learnt_clause(&learned);
                    formula.add_clause(learned.clone());
                    let clause_idx = formula.get_clauses().len() - 1;

                    for lit in learned.get_literals() {
                        vsids.bump(lit);
                    }
                    vsids.decay_all();

                    if let Some(asserting_lit) =
                        find_asserting_literal(&learned, &formula.assignment)
                    {
                        enqueue_asserting_literal(
                            formula,
                            &mut history,
                            &mut queue,
                            asserting_lit,
                            clause_idx,
                        )?;
                    }
                }

                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    uip_clause,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                } => {
                    // PROOF SIDE: Log the standard 1UIP clause first!
                    // This acts as the logical anchor for drat-trim to verify the pre_clause!
                    let _ = logger.log_add(uip_clause.get_literals());

                    // Get or create z for z <-> (dip_a ∧ dip_b)
                    let z = match formula.extensions.substitute(&dip_a, &dip_b) {
                        Some(ext_lit) => ext_lit,
                        None => {
                            let new_z = formula.add_literal();
                            formula.stats.add_literal();

                            formula
                                .extensions
                                .add_substitution(&dip_a, &dip_b, &new_z);
                            
                            let extension_axiom = Clause::from_literals(&vec![
                                new_z.clone(),
                                dip_a.negated(),
                                dip_b.negated(),
                            ]);
                            let ext_a = Clause::from_literals(&vec![
                                new_z.negated(),
                                dip_a.clone(),
                            ]);
                            let ext_b = Clause::from_literals(&vec![
                                new_z.negated(),
                                dip_b.clone(),
                            ]);
                           
                            let _ = logger.log_add(&extension_axiom.get_literals());
                            formula.add_clause(extension_axiom);
                            let _ = logger.log_add(&ext_a.get_literals());
                            formula.add_clause(ext_a);
                            let _ = logger.log_add(&ext_b.get_literals());
                            formula.add_clause(ext_b);
                           
                            new_z
                        }
                    };

                    // Internal DIP learned clauses:
                    let mut post_lits = Vec::with_capacity(post_clause_without_z.len() + 1);
                    post_lits.push(z.negated());
                    post_lits.extend(post_clause_without_z.into_iter());
                    let post_clause = Clause::from_literals(&post_lits);

                    let mut pre_lits = Vec::with_capacity(pre_clause_without_z.len() + 1);
                    pre_lits.push(z.clone());
                    pre_lits.extend(pre_clause_without_z.into_iter());
                    let pre_clause = Clause::from_literals(&pre_lits);
                    
                    // println!("Preclause: {:?}, post clause: {:?}",pre_clause,post_clause);

                    let mut actual_backtrack = backtrack_level;
                    history.revert_decision(actual_backtrack + 1, &mut formula.assignment);

                    while post_clause.is_empty(&formula.assignment) {
                        if actual_backtrack == 0 {
                            let _ = logger.log_empty_clause();
                            return Ok(None);
                        }
                        actual_backtrack -= 1;
                        history.revert_decision(actual_backtrack + 1, &mut formula.assignment);
                    }

                    queue.clear();

                    for lit in post_clause.get_literals() {
                        vsids.bump(lit);
                    }
                    for lit in pre_clause.get_literals() {
                        vsids.bump(lit);
                    }
                    vsids.decay_all();

                    // PROOF & SOLVER SIDE: Add post_clause FIRST
                    formula.stats.add_learnt_clause(&post_clause);
                    let _ = logger.log_add(&post_clause.get_literals());
                    formula.add_clause(post_clause);
                    
                    let post_idx = formula.get_clauses().len() - 1;

                    // PROOF & SOLVER SIDE: Add pre_clause SECOND
                    formula.stats.add_learnt_clause(&pre_clause);
                    let _ = logger.log_add(&pre_clause.get_literals());
                    formula.add_clause(pre_clause);

                    // After backtracking, post should assert ¬z.
                    let asserting_lit = z.negated();

                    match asserting_lit.eval(&formula.assignment) {
                        Some(false) => {
                            if actual_backtrack == 0 {
                                let _ = logger.log_empty_clause();
                                return Ok(None);
                            }
                            return Err(pyo3::exceptions::PyRuntimeError::new_err(
                                "DIP post clause asserts a falsified literal after backtrack",
                            ));
                        }
                        Some(true) => {
                            // Already satisfied
                        }
                        None => {
                            enqueue_asserting_literal(
                                formula,
                                &mut history,
                                &mut queue,
                                asserting_lit,
                                post_idx,
                            )?;
                        }
                    }
                }
            }
        }
    }
}

fn find_asserting_literal(
    clause: &Clause,
    assignment: &crate::formula::assignment::Assignment,
) -> Option<Literal> {
    let mut unassigned = None;

    for lit in clause.get_literals() {
        match lit.eval(assignment) {
            Some(true) => return Some(lit.clone()),
            Some(false) => {}
            None => {
                if unassigned.is_some() {
                    return None;
                }
                unassigned = Some(lit.clone());
            }
        }
    }

    unassigned
}

fn enqueue_asserting_literal(
    formula: &mut Formula,
    history: &mut History,
    queue: &mut VecDeque<Literal>,
    lit: Literal,
    reason_clause_idx: usize,
) -> PyResult<()> {
    match lit.eval(&formula.assignment) {
        Some(false) => Err(pyo3::exceptions::PyRuntimeError::new_err(
            "asserting literal is false after backtrack",
        )),
        Some(true) => Ok(()),
        None => {
            formula
                .assignment
                .assign(lit.get_index(), !lit.is_negated());
            history.add_implication(&lit, Some(reason_clause_idx));
            queue.push_back(lit);
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Formula;

    #[test]
    fn test_cdcl_simple_sat_uip() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
        let res = solve_cdcl(&mut formula, ImplicationPoint::UIP).unwrap();
        assert!(res.is_some());
    }

    #[test]
    fn test_cdcl_simple_unsat_uip() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);
        let res = solve_cdcl(&mut formula, ImplicationPoint::UIP).unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_cdcl_inner_conflict_loop_uip() {
        let mut formula =
            Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);
        let res = solve_cdcl(&mut formula, ImplicationPoint::UIP).unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_cdcl_simple_sat_dip() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
        let res = solve_cdcl(&mut formula, ImplicationPoint::DIP).unwrap();
        assert!(res.is_some());
    }

    #[test]
    fn test_cdcl_simple_unsat_dip() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);
        let res = solve_cdcl(&mut formula, ImplicationPoint::DIP).unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_cdcl_inner_conflict_loop_dip() {
        let mut formula =
            Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);
        let res = solve_cdcl(&mut formula, ImplicationPoint::DIP).unwrap();
        assert!(res.is_none());
    }
}