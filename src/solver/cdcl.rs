use crate::formula::Formula;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::formula::vsids::Vsids;
use crate::history::ConflictLearnResult;

use pyo3::prelude::PyResult;

use std::collections::VecDeque;

pub fn solve_cdcl<'py>(
    formula: &mut Formula,
    implication_point: ImplicationPoint,
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut queue: VecDeque<Literal> = VecDeque::new();
    let mut vsids = Vsids::new(formula.assignment.len());

    // Initial unit clauses
    let mut initial_units = Vec::new();
    for (i, clause) in formula.get_clauses().iter().enumerate() {
        if clause.len() == 1 {
            initial_units.push((i, clause.get_literals()[0].clone()));
        }
    }

    for (i, lit) in initial_units {
        match lit.eval(&formula.assignment) {
            Some(false) => return Ok(None),
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
        let decision_lit = match vsids.get_best_unassigned(formula) {
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

            formula.stats.add_conflict();

            match history.analyze_conflict(formula, conflict_idx, implication_point) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                } => {
                    let learned =
                        Clause::from_literals(&apply_recursive_extension_substitution(formula, clause.get_literals().clone()));

                    history.revert_decision(backtrack_level + 1, &mut formula.assignment);
                    queue.clear();

                    formula.stats.add_learnt_clause(&learned);
                    formula.add_clause(learned.clone());
                    let clause_idx = formula.get_clauses().len() - 1;

                    for lit in learned.get_literals() {
                        vsids.bump(lit);
                    }
                    vsids.decay_all();

                    let asserting_lit = match find_asserting_literal(&learned, &formula.assignment) {
                        Some(lit) => lit,
                        None => return Ok(None),
                    };

                    enqueue_asserting_literal(
                        formula,
                        &mut history,
                        &mut queue,
                        asserting_lit,
                        clause_idx,
                    )?;
                }

                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    first_uip: _first_uip,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                } => {
                    let z = match formula.extensions.substitute(&dip_a, &dip_b) {
                        Some(ext_lit) => ext_lit,
                        None => {
                            let new_z = formula.add_literal();
                            formula.stats.add_literal();
                            formula.extensions.add_substitution(&dip_a, &dip_b, &new_z);

                            // Follow the encoding convention already used in your code:
                            // z <-> (dip_a v dip_b)
                            println!("{new_z} <-> ({dip_a}v{dip_b})");
                            formula.add_clause(Clause::from_literals(&vec![
                                new_z.negated(),
                                dip_a.clone(),
                                dip_b.clone(),
                            ]));
                            formula.add_clause(Clause::from_literals(&vec![
                                new_z.clone(),
                                dip_a.negated(),
                            ]));
                            formula.add_clause(Clause::from_literals(&vec![
                                new_z.clone(),
                                dip_b.negated(),
                            ]));

                            new_z
                        }
                    };

                    // pre = pre_clause_without_z ∨ z
                    let mut pre_lits = pre_clause_without_z;
                    pre_lits.push(z.clone());
                    let pre_clause =
                        Clause::from_literals(&apply_recursive_extension_substitution(formula, pre_lits));

                    // post = post_clause_without_z ∨ ¬z
                    let mut post_lits = post_clause_without_z;
                    post_lits.push(z.negated());
                    let post_clause =
                        Clause::from_literals(&apply_recursive_extension_substitution(formula, post_lits));

                    let mut actual_backtrack = backtrack_level;
                    // Dynamically fix the backtrack level if VSIDS guessed an extension variable wrongly
                    while post_clause.is_empty(&formula.assignment) {
                        println!("Guessed wrongly");
                        if actual_backtrack == 0 {
                            return Ok(None); // Truly UNSAT at level 0
                        }
                        actual_backtrack -= 1;
                        history.revert_decision(actual_backtrack + 1, &mut formula.assignment);
                    }
                    println!("Learning clauses: {pre_clause}{post_clause}");
                    
                    history.revert_decision(backtrack_level + 1, &mut formula.assignment);
                    queue.clear();

                    for lit in pre_clause.get_literals() {
                        vsids.bump(lit);
                    }
                    for lit in post_clause.get_literals() {
                        vsids.bump(lit);
                    }
                    formula.stats.add_learnt_clause(&pre_clause);
                    formula.add_clause(pre_clause);
                    let _pre_idx = formula.get_clauses().len() - 1;

                    formula.stats.add_learnt_clause(&post_clause);
                    formula.add_clause(post_clause);
                    let post_idx = formula.get_clauses().len() - 1;

                    vsids.decay_all();

                    // After backtracking to l_D, the post-DIP clause should assert ¬z.
                    let asserting_lit = z.negated();

                    match asserting_lit.eval(&formula.assignment) {
                        Some(false) => {
                            return Ok(None);
                        }
                        Some(true) => {
                            // Already assigned consistently.
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

fn apply_recursive_extension_substitution(
    formula: &Formula,
    mut lits: Vec<Literal>,
) -> Vec<Literal> {
    let mut changed = true;

    while changed {
        changed = false;

        'outer: for i in 0..lits.len() {
            for j in (i + 1)..lits.len() {
                if let Some(substitute) = formula.extensions.substitute(&lits[i], &lits[j]) {
                    lits.remove(j);
                    lits.remove(i);
                    lits.push(substitute);
                    changed = true;
                    break 'outer;
                }
            }
        }
    }

    lits
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
