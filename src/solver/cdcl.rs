use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::assignment::AssignResult;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::heuristics::Heuristics;
use crate::history::ConflictLearnResult;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::python::signal_checker;

use pyo3::Python;
use pyo3::prelude::PyResult;

use std::collections::VecDeque;
use std::io::Write;

pub fn solve_cdcl<'py, W: Write>(
    py: Python<'_>,
    formula: &mut Formula,
    implication_point: ImplicationPoint,
    heuristics: &mut Heuristics,
    logger: &mut Option<DratLogger<W>>,
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut steps = 0;

    let initial_units: Vec<_> = formula
        .get_clauses()
        .iter()
        .enumerate()
        .filter(|(_, clause)| clause.len() == 1)
        .map(|(idx, clause)| (idx, clause.get_literals()[0].clone()))
        .collect();

    let mut initial_propagation = Vec::new();
    for (idx, lit) in initial_units {
        match formula
            .assignment
            .assign_implication(lit, &mut history, Some(idx))
        {
            AssignResult::Conflict => return unsat(logger),
            AssignResult::AlreadyAssigned => {}
            AssignResult::Assigned(lit) => initial_propagation.push(lit),
        }
    }

    if propagate_from(formula, &mut history, initial_propagation).is_some() {
        return unsat(logger);
    }

    loop {
        signal_checker(py, &mut steps)?;

        let decision_lit = match heuristics.get_decision_literal(formula) {
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        history.add_decision(&decision_lit);
        formula.assignment.assign(
            decision_lit.get_index().abs() as usize,
            !decision_lit.is_negated(),
        );

        let mut propagation = vec![decision_lit.clone()];
        while let Some(conflict_idx) = propagate_from(formula, &mut history, propagation.drain(..))
        {
            if history.get_decision_level() == 0 {
                return unsat(logger);
            }

            formula.stats.add_conflict();

            let learned = match history.analyze_conflict(formula, conflict_idx, implication_point) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                } => learn_uip_clause(
                    formula,
                    &mut history,
                    logger,
                    &mut propagation,
                    clause,
                    backtrack_level,
                )?,
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                } => learn_dip_clauses(
                    formula,
                    &mut history,
                    logger,
                    &mut propagation,
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                )?,
            };

            let Some(learned) = learned else {
                return unsat(logger);
            };

            heuristics.bump(learned.get_literals());
            heuristics.decay();
        }
    }
}

fn learn_uip_clause<W: Write>(
    formula: &mut Formula,
    history: &mut History,
    logger: &mut Option<DratLogger<W>>,
    propagation: &mut Vec<Literal>,
    learned: Clause,
    backtrack_level: usize,
) -> PyResult<Option<Clause>> {
    if backtrack_until_not_conflicting(&learned, backtrack_level, history, formula).is_none() {
        return Ok(None);
    }

    let asserting_lit = learned
        .get_unit_literal(&formula.assignment)
        .cloned()
        .expect("UIP learned clause must assert after backtrack");

    formula.stats.add_learnt_clause(&learned);
    let clause_idx = formula.add_clause(learned.clone(), logger);

    if let AssignResult::Assigned(lit) =
        formula
            .assignment
            .assign_implication(asserting_lit, history, Some(clause_idx))
    {
        propagation.push(lit);
    }

    Ok(Some(learned))
}

fn learn_dip_clauses<W: Write>(
    formula: &mut Formula,
    history: &mut History,
    logger: &mut Option<DratLogger<W>>,
    propagation: &mut Vec<Literal>,
    dip_a: Literal,
    dip_b: Literal,
    pre_clause_without_z: Vec<Literal>,
    post_clause_without_z: Vec<Literal>,
    backtrack_level: usize,
) -> PyResult<Option<Clause>> {
    let z = extension_literal(formula, logger, &dip_a, &dip_b);
    let post_clause = prefixed_clause(z.negated(), post_clause_without_z);
    let pre_clause = prefixed_clause(z.clone(), pre_clause_without_z);

    let Some(actual_backtrack) =
        backtrack_until_not_conflicting(&post_clause, backtrack_level, history, formula)
    else {
        return Ok(None);
    };

    let mut learned = Clause::new();
    for lit in post_clause
        .get_literals()
        .iter()
        .chain(pre_clause.get_literals())
    {
        let _ = learned.add_literal(lit);
    }

    let post_label = format!(
        "DIP post clause dip_a={:?} dip_b={:?} z={:?} backtrack_level={}",
        dip_a, dip_b, z, actual_backtrack
    );
    if post_clause.is_empty(&formula.assignment) {
        return Err(pyo3::exceptions::PyRuntimeError::new_err(format!(
            "{} is conflicting immediately after backtrack: {:?}",
            post_label, post_clause
        )));
    }
    if !post_clause.is_satisfied(&formula.assignment) && !post_clause.is_unit(&formula.assignment) {
        return Err(pyo3::exceptions::PyRuntimeError::new_err(format!(
            "{} is neither satisfied nor asserting after backtrack: {:?}",
            post_label, post_clause
        )));
    }

    formula.stats.add_learnt_clause(&post_clause);
    let post_idx = formula.add_clause(post_clause, logger);

    formula.stats.add_learnt_clause(&pre_clause);
    let pre_idx = formula.add_clause(pre_clause.clone(), logger);

    match formula
        .assignment
        .assign_implication(z.negated(), history, Some(post_idx))
    {
        AssignResult::Conflict if actual_backtrack == 0 => return Ok(None),
        AssignResult::Conflict => {
            return Err(pyo3::exceptions::PyRuntimeError::new_err(
                "DIP post clause asserts a falsified literal after backtrack",
            ));
        }
        AssignResult::AlreadyAssigned => {}
        AssignResult::Assigned(lit) => propagation.push(lit),
    }

    if pre_clause.is_empty(&formula.assignment) {
        return Err(pyo3::exceptions::PyRuntimeError::new_err(format!(
            "DIP pre clause became conflicting immediately after post propagation: {:?}",
            pre_clause
        )));
    }

    if let Some(asserting_lit) = pre_clause.get_unit_literal(&formula.assignment).cloned() {
        if let AssignResult::Assigned(lit) =
            formula
                .assignment
                .assign_implication(asserting_lit, history, Some(pre_idx))
        {
            propagation.push(lit);
        }
    }

    Ok(Some(learned))
}

fn prefixed_clause(first: Literal, rest: Vec<Literal>) -> Clause {
    let mut lits = Vec::with_capacity(rest.len() + 1);
    lits.push(first);
    lits.extend(rest);
    Clause::from_lits(lits)
}

fn unsat<W: Write>(logger: &mut Option<DratLogger<W>>) -> PyResult<Option<Vec<bool>>> {
    if let Some(log) = logger {
        let _ = log.log_empty_clause();
    }
    Ok(None)
}

fn propagate_from<I>(formula: &mut Formula, history: &mut History, lits: I) -> Option<usize>
where
    I: IntoIterator<Item = Literal>,
{
    let mut queue: VecDeque<_> = lits.into_iter().collect();
    formula.propagate_twl(history, &mut queue)
}

fn backtrack_until_not_conflicting(
    clause: &Clause,
    preferred_level: usize,
    history: &mut History,
    formula: &mut Formula,
) -> Option<usize> {
    let mut level = preferred_level;
    loop {
        history.revert_decision(level + 1, &mut formula.assignment);
        if !clause.is_empty(&formula.assignment) {
            return Some(level);
        }
        if level == 0 {
            return None;
        }
        level -= 1;
    }
}

fn extension_literal<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    dip_a: &Literal,
    dip_b: &Literal,
) -> Literal {
    if let Some(ext_lit) = formula.extensions.substitute(dip_a, dip_b) {
        return ext_lit;
    }

    let z = formula.add_literal();
    formula.stats.add_literal();
    formula.extensions.add_substitution(dip_a, dip_b, &z);

    formula.add_clause(
        Clause::from_lits(vec![z.clone(), dip_a.negated(), dip_b.negated()]),
        logger,
    );
    formula.add_clause(Clause::from_lits(vec![z.negated(), dip_a.clone()]), logger);
    formula.add_clause(Clause::from_lits(vec![z.negated(), dip_b.clone()]), logger);

    z
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
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::UIP,
                    &mut Heuristics::Random,
                    &mut None,
                )
                .unwrap();
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
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::UIP,
                    &mut Heuristics::Random,
                    &mut None,
                )
                .unwrap();
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
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::UIP,
                    &mut Heuristics::Random,
                    &mut None,
                )
                .unwrap();
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
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::DIP,
                    &mut Heuristics::Random,
                    &mut None,
                )
                .unwrap();
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
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::DIP,
                    &mut Heuristics::Random,
                    &mut None,
                )
                .unwrap();
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
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::DIP,
                    &mut Heuristics::Random,
                    &mut None,
                )
                .unwrap();
                assert!(res.is_none());
            });
        });
    }
}
