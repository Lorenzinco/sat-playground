use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::assignment::AssignResult;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::heuristics::Heuristics;
use crate::history::ConflictLearnResult;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::process::Process;
use crate::python::signal_checker;

use pyo3::Python;
use pyo3::prelude::PyResult;

use std::collections::VecDeque;
use std::io::Write;
use std::time::Instant;

const RESTART_CONFLICT_SCALE: u64 = 100;
const INPROCESSING_RESTART_INTERVAL: u64 = 8;
const DB_REDUCTION_CONFLICT_INTERVAL: u64 = 2_000;

pub fn solve_cdcl<'py, W: Write>(
    py: Python<'_>,
    formula: &mut Formula,
    implication_point: ImplicationPoint,
    heuristics: &mut Heuristics,
    logger: &mut Option<DratLogger<W>>,
    inprocessing: Vec<Process>,
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    let mut steps = 0;
    let mut restart_count = 0;
    let mut conflicts_at_last_restart = 0;
    let mut next_restart_conflicts = RESTART_CONFLICT_SCALE * luby(restart_count + 1);
    let mut next_db_reduction_conflicts = DB_REDUCTION_CONFLICT_INTERVAL;

    if formula.get_clauses().iter().any(|clause| clause.len() == 0) {
        return unsat(logger);
    }

    let initial_units: Vec<_> = formula
        .get_clauses()
        .iter()
        .enumerate()
        .filter(|(_, clause)| clause.len() == 1)
        .map(|(idx, clause)| (idx, clause.get_literals()[0].clone()))
        .collect();

    let mut initial_propagation = Vec::new();
    for (idx, lit) in initial_units {
        match formula.assign_implication(lit, &mut history, Some(idx)) {
            AssignResult::Conflict => return unsat(logger),
            AssignResult::AlreadyAssigned => {}
            AssignResult::Assigned(lit) => initial_propagation.push(lit),
        }
    }

    let propagation_start = Instant::now();
    let initial_conflict = propagate_from(formula, &mut history, initial_propagation);
    formula
        .stats
        .record_propagation_time(propagation_start.elapsed());
    if initial_conflict.is_some() {
        return unsat(logger);
    }

    loop {
        signal_checker(py, &mut steps)?;

        let decision_lit = match heuristics.get_decision_literal(formula) {
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        formula.add_decision(&decision_lit, &mut history);

        let mut propagation = vec![decision_lit.clone()];
        loop {
            let propagation_start = Instant::now();
            let conflict = propagate_from(formula, &mut history, propagation.drain(..));
            formula
                .stats
                .record_propagation_time(propagation_start.elapsed());

            let Some(conflict_idx) = conflict else {
                break;
            };

            if history.get_decision_level() == 0 {
                return unsat(logger);
            }

            formula.stats.add_conflict();

            let analysis_start = Instant::now();
            let conflict_result =
                history.analyze_conflict(formula, conflict_idx, implication_point);
            formula
                .stats
                .record_conflict_analysis_time(analysis_start.elapsed());

            let learning_start = Instant::now();
            let learned = match conflict_result {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                    minimized_literals,
                    minimization_time,
                } => {
                    formula
                        .stats
                        .add_minimized_literals(minimized_literals as u64);
                    formula.stats.record_minimization_time(minimization_time);
                    learn_uip_clause(
                        formula,
                        &mut history,
                        logger,
                        &mut propagation,
                        clause,
                        backtrack_level,
                    )?
                }
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    pre_lbd,
                    post_lbd,
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
                    pre_lbd,
                    post_lbd,
                    backtrack_level,
                )?,
            };
            formula.stats.record_learning_time(learning_start.elapsed());

            let Some(learned) = learned else {
                return unsat(logger);
            };

            heuristics.bump(learned.get_literals());
            heuristics.decay();

            if formula.stats.conflicts >= next_db_reduction_conflicts {
                let reduce_start = Instant::now();
                formula.reduce_db(&mut history, logger, Some((py, &mut steps)))?;
                formula
                    .stats
                    .record_db_reduction_time(reduce_start.elapsed());
                next_db_reduction_conflicts += DB_REDUCTION_CONFLICT_INTERVAL;
            }

            if formula.stats.conflicts - conflicts_at_last_restart >= next_restart_conflicts {
                restart_count += 1;
                conflicts_at_last_restart = formula.stats.conflicts;
                next_restart_conflicts = RESTART_CONFLICT_SCALE * luby(restart_count + 1);
                let run_inprocessing = restart_count.is_multiple_of(INPROCESSING_RESTART_INTERVAL);
                restart(
                    py,
                    &mut steps,
                    formula,
                    &mut history,
                    &inprocessing,
                    run_inprocessing,
                    logger,
                )?;
                propagation.clear();
                break;
            }
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

    formula.stats.add_learnt_clause(&learned);
    let clause_idx = formula.add_clause(learned.clone(), logger, Some(history));

    if let Some(unit) = formula
        .get_clause_at_idx(clause_idx)
        .get_unit_literal(&formula.assignment)
        .cloned()
    {
        if let AssignResult::Assigned(lit) =
            formula.assign_implication(unit, history, Some(clause_idx))
        {
            propagation.push(lit);
        }
    } else if formula
        .get_clause_at_idx(clause_idx)
        .is_empty(&formula.assignment)
    {
        return Ok(None);
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
    pre_lbd: i64,
    post_lbd: i64,
    backtrack_level: usize,
) -> PyResult<Option<Clause>> {
    let z = extension_literal(formula, logger, &dip_a, &dip_b);
    let post_clause = prefixed_clause(z.negated(), post_clause_without_z, post_lbd);
    let pre_clause = prefixed_clause(z.clone(), pre_clause_without_z, pre_lbd);

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
    let post_idx = formula.add_clause_unchecked(post_clause, logger);

    formula.stats.add_learnt_clause(&pre_clause);
    let pre_idx = formula.add_clause_unchecked(pre_clause.clone(), logger);

    if let Some(post_unit) = formula
        .get_clause_at_idx(post_idx)
        .get_unit_literal(&formula.assignment)
        .cloned()
    {
        match formula.assign_implication(post_unit, history, Some(post_idx)) {
            AssignResult::Conflict if actual_backtrack == 0 => return Ok(None),
            AssignResult::Conflict => {
                return Err(pyo3::exceptions::PyRuntimeError::new_err(
                    "DIP post clause asserts a falsified literal after backtrack",
                ));
            }
            AssignResult::AlreadyAssigned => {}
            AssignResult::Assigned(lit) => propagation.push(lit),
        }
    } else if formula
        .get_clause_at_idx(post_idx)
        .is_empty(&formula.assignment)
    {
        return Ok(None);
    }

    if pre_clause.is_empty(&formula.assignment) {
        return Err(pyo3::exceptions::PyRuntimeError::new_err(format!(
            "DIP pre clause became conflicting immediately after post propagation: {:?}",
            pre_clause
        )));
    }

    if let Some(asserting_lit) = pre_clause.get_unit_literal(&formula.assignment).cloned() {
        if let AssignResult::Assigned(lit) =
            formula.assign_implication(asserting_lit, history, Some(pre_idx))
        {
            propagation.push(lit);
        }
    }

    Ok(Some(learned))
}

fn prefixed_clause(first: Literal, rest: Vec<Literal>, lbd: i64) -> Clause {
    let mut lits = Vec::with_capacity(rest.len() + 1);
    lits.push(first);
    lits.extend(rest);
    Clause::from_literals(lits, lbd)
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

fn luby(index: u64) -> u64 {
    debug_assert!(index > 0);

    let mut k = 1;
    while (1_u64 << k) - 1 < index {
        k += 1;
    }

    if index == (1_u64 << k) - 1 {
        1_u64 << (k - 1)
    } else {
        luby(index - (1_u64 << (k - 1)) + 1)
    }
}

fn restart<W: Write>(
    py: Python<'_>,
    steps: &mut u64,
    formula: &mut Formula,
    history: &mut History,
    inprocessing: &[Process],
    run_inprocessing: bool,
    logger: &mut Option<DratLogger<W>>,
) -> PyResult<()> {
    let restart_start = Instant::now();
    formula.stats.add_restart();
    formula.revert_decision(1, history);

    if run_inprocessing {
        let inprocessing_start = Instant::now();
        formula.process(
            inprocessing.to_vec(),
            logger,
            Some((py, steps)),
            false,
            Some(history),
        )?;
        formula
            .stats
            .record_inprocessing_time(inprocessing_start.elapsed());
    }

    formula.stats.record_restart_time(restart_start.elapsed());
    Ok(())
}

fn backtrack_until_not_conflicting(
    clause: &Clause,
    preferred_level: usize,
    history: &mut History,
    formula: &mut Formula,
) -> Option<usize> {
    let mut level = preferred_level;
    loop {
        formula.revert_decision(level + 1, history);
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
    formula.stats.add_extension_literal();
    formula.extensions.add_substitution(dip_a, dip_b, &z);

    formula.add_clause(
        Clause::from_literals(vec![z.clone(), dip_a.negated(), dip_b.negated()], 0),
        logger,
        None,
    );
    formula.add_clause(
        Clause::from_literals(vec![z.negated(), dip_a.clone()], 0),
        logger,
        None,
    );
    formula.add_clause(
        Clause::from_literals(vec![z.negated(), dip_b.clone()], 0),
        logger,
        None,
    );

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
    fn luby_sequence_matches_expected_prefix() {
        let got: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(got, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    #[test]
    fn restart_backtracks_to_root_and_unlocks_reason_clauses() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1, 2]]);
        let mut history = History::new();

        let decision = Literal::new(1);
        formula.add_decision(&decision, &mut history);
        let implied = Literal::new(2);
        assert!(matches!(
            formula.assign_implication(implied, &mut history, Some(1)),
            AssignResult::Assigned(_)
        ));
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 1);

        Python::attach(|py| {
            let mut steps = 0;
            let mut logger: Option<DratLogger<Empty>> = None;
            restart(
                py,
                &mut steps,
                &mut formula,
                &mut history,
                &[],
                true,
                &mut logger,
            )
            .unwrap();
        });

        assert_eq!(formula.stats.restarts, 1);
        assert!(formula.stats.restart_nanos >= formula.stats.inprocessing_nanos);
        assert_eq!(history.get_decision_level(), 0);
        assert_eq!(formula.assignment.get_value(1), None);
        assert_eq!(formula.assignment.get_value(2), None);
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 0);
    }

    #[test]
    fn extension_axioms_have_zero_lbd() {
        let mut formula = Formula::from_vec(vec![vec![1, 2]]);
        let a = Literal::new(1);
        let b = Literal::new(2);
        let mut logger: Option<DratLogger<Empty>> = None;

        extension_literal(&mut formula, &mut logger, &a, &b);

        assert_eq!(formula.stats.extension_literals, 1);
        assert_eq!(formula.stats.bva_literals, 0);
        assert_eq!(formula.stats.literals_learnt, 1);

        let clauses = formula.get_clauses();
        assert_eq!(clauses[clauses.len() - 3].lbd, 0);
        assert_eq!(clauses[clauses.len() - 2].lbd, 0);
        assert_eq!(clauses[clauses.len() - 1].lbd, 0);
    }

    #[test]
    fn cdcl_reports_unsat_for_structural_empty_clause() {
        with_proof_lock(|| {
            Python::initialize();
            Python::attach(|py| {
                let mut formula = Formula::from_vec(vec![vec![1]]);
                formula.add_clause_unchecked::<Empty>(
                    Clause::from_literals(Vec::new(), -1),
                    &mut None,
                );
                let res = solve_cdcl::<Empty>(
                    py,
                    &mut formula,
                    ImplicationPoint::UIP,
                    &mut Heuristics::Random,
                    &mut None,
                    Vec::new(),
                )
                .unwrap();
                assert!(res.is_none());
            });
        });
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
                )
                .unwrap();
                assert!(res.is_none());
            });
        });
    }
}
