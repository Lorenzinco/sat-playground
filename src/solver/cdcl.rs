use crate::drat::DratLogger;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::heuristics::Heuristics;
use crate::formula::Formula;
use crate::history::ConflictLearnResult;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::python::signal_checker;

use pyo3::prelude::PyResult;
use pyo3::Python;

use std::collections::VecDeque;
use std::io::Write;

pub fn solve_cdcl<'py, W:Write>(
    py: Python<'_>,
    formula: &mut Formula,
    implication_point: ImplicationPoint,
    heuristics: &mut Heuristics,
    logger: &mut Option<DratLogger<W>>
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut queue: VecDeque<Literal> = VecDeque::new();
    let mut steps = 0;
    
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
                if let Some(log) = logger {
                    let _ = log.log_empty_clause();
                }
                return Ok(None);
            }
            Some(true) => {}
            None => {
                formula.assignment.assign(lit.get_index().abs() as usize, !lit.is_negated());
                history.add_implication(&lit, Some(i));
                queue.push_back(lit);
            }
        }
    }

    // Initial propagation
    if formula.propagate_twl(&mut history, &mut queue).is_some() {
        if let Some(log) = logger {
            let _ = log.log_empty_clause();
        }
        return Ok(None);
    }

    loop {

        signal_checker(py, &mut steps)?;

        let decision_lit = match heuristics.get_decision_literal(formula){
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model()))
        };
        

        history.add_decision(&decision_lit);
        formula
            .assignment
            .assign(decision_lit.get_index().abs() as usize, !decision_lit.is_negated());
        queue.push_back(decision_lit);

        while let Some(conflict_idx) = formula.propagate_twl(&mut history, &mut queue) {
            if history.get_decision_level() == 0 {
                if let Some(log) = logger {
                    let _ = log.log_empty_clause();
                }
                return Ok(None);
            }

            formula.stats.add_conflict();

            let mut learned = Clause::new();

            match history.analyze_conflict(formula, conflict_idx, implication_point) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                } => {
                    learned = clause;

                    let mut actual_backtrack = backtrack_level;
                    history.revert_decision(actual_backtrack + 1, &mut formula.assignment);

                    while learned.is_empty(&formula.assignment) {
                        if actual_backtrack == 0 {
                            if let Some(log) = logger {
                                let _ = log.log_empty_clause();
                            }
                            return Ok(None);
                        }
                        actual_backtrack -= 1;
                        history.revert_decision(actual_backtrack + 1, &mut formula.assignment);
                    }

                    queue.clear();

                    formula.stats.add_learnt_clause(&learned);
                    formula.add_clause(learned.clone(),logger);
                    let clause_idx = formula.get_clauses().len() - 1;


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
                    post_clause_without_z,
                    backtrack_level,
                } => {

                    // z <-> (dip_a ∧ dip_b)
                    let z = match formula.extensions.substitute(&dip_a, &dip_b) {
                        Some(ext_lit) => {
                            ext_lit
                        }, // substitution already exists
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
                           
                            formula.add_clause(extension_axiom,logger);
                            formula.add_clause(ext_a,logger);
                            formula.add_clause(ext_b,logger);
                           
                            new_z
                        }
                    };

                    // post_dip 
                    let mut post_lits = Vec::with_capacity(post_clause_without_z.len() + 1);
                    post_lits.push(z.negated());
                    post_lits.extend(post_clause_without_z.into_iter());
                    let post_clause = Clause::from_literals(&post_lits);
                    
                    // println!("Preclause: {:?}, post clause: {:?}",pre_clause,post_clause);

                    let mut actual_backtrack = backtrack_level;
                    history.revert_decision(actual_backtrack + 1, &mut formula.assignment);

                    while post_clause.is_empty(&formula.assignment) {
                        if actual_backtrack == 0 {
                            if let Some(log) = logger {
                                let _ = log.log_empty_clause();
                            }
                            return Ok(None);
                        }
                        actual_backtrack -= 1;
                        history.revert_decision(actual_backtrack + 1, &mut formula.assignment);
                    }

                    queue.clear();

                    
                    for lit in post_clause.get_literals() {
                        let _ = learned.add_literal(lit); 
                    }

                    // Log post learned clause
                    formula.stats.add_learnt_clause(&post_clause);
                    formula.add_clause(post_clause, logger);
                    
                    let post_idx = formula.get_clauses().len() - 1;

                    // ¬z is asserting.
                    let asserting_lit = z.negated();

                    match asserting_lit.eval(&formula.assignment) {
                        Some(false) => {
                            if actual_backtrack == 0 {
                                if let Some(log) = logger {
                                    let _ = log.log_empty_clause();
                                }
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

            heuristics.bump(learned.get_literals());
            heuristics.decay();
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
                .assign(lit.get_index().abs() as usize, !lit.is_negated());
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
    use pyo3::Python;
    use std::io::Empty;
    use std::sync::{Mutex, OnceLock};

    fn proof_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn with_proof_lock<F: FnOnce()>(f: F) {
        let _guard = proof_lock().lock().unwrap();
        f();
    }

    #[test]
    fn test_cdcl_simple_sat_uip() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
                let res = solve_cdcl::<Empty>(py, &mut formula, ImplicationPoint::UIP, &mut Heuristics::Random, &mut None).unwrap();
                assert!(res.is_some());
            });
        });
    }

    #[test]
    fn test_cdcl_simple_unsat_uip() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);
                let res = solve_cdcl::<Empty>(py, &mut formula, ImplicationPoint::UIP, &mut Heuristics::Random, &mut None).unwrap();
                assert!(res.is_none());
            });
        });
    }

    #[test]
    fn test_cdcl_inner_conflict_loop_uip() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula =
                    Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);
                let res = solve_cdcl::<Empty>(py, &mut formula, ImplicationPoint::UIP,&mut Heuristics::Random,&mut None).unwrap();
                assert!(res.is_none());
            });
        });
    }

    #[test]
    fn test_cdcl_simple_sat_dip() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
                let res = solve_cdcl::<Empty>(py, &mut formula, ImplicationPoint::DIP,&mut Heuristics::Random,&mut None).unwrap();
                assert!(res.is_some());
            });
        });
    }

    #[test]
    fn test_cdcl_simple_unsat_dip() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);
                let res = solve_cdcl::<Empty>(py, &mut formula, ImplicationPoint::DIP,&mut Heuristics::Random,&mut None).unwrap();
                assert!(res.is_none());
            });
        });
    }

    #[test]
    fn test_cdcl_inner_conflict_loop_dip() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula =
                    Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);
                let res = solve_cdcl::<Empty>(py, &mut formula, ImplicationPoint::DIP,&mut Heuristics::Random,&mut None).unwrap();
                assert!(res.is_none());
            });
        });
    }
}
