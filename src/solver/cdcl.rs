use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::assignment::AssignResult;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::guidance::GuidanceTracker;
use crate::heuristics::Heuristics;
use crate::history::ConflictLearnResult;
use crate::history::History;
use crate::history::ImplicationPoint;
use crate::process::{ClauseScope, Process};

use crate::formula::extension::extension_literal;

use crate::python::signal_checker;

use pyo3::Python;
use pyo3::prelude::PyResult;

use std::collections::VecDeque;
use std::io::Write;
use std::time::Instant;

const RESTART_CONFLICT_SCALE: u64 = 100;
const GES_RESTART_INTERVAL: u64 = 2;
const INPROCESSING_RESTART_INTERVAL: u64 = 8;
const DB_REDUCTION_CONFLICT_INTERVAL: u64 = 2_000;

pub fn solve_cdcl<'py, W: Write>(
    py: Python<'_>,
    formula: &mut Formula,
    implication_point: ImplicationPoint,
    heuristics: &mut Heuristics,
    logger: &mut Option<DratLogger<W>>,
    inprocessing: Vec<Process>,
    guidance: &mut Option<GuidanceTracker>,
) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    formula.configure_ges_trail_tracking(
        inprocessing.contains(&Process::GESTrail) && inprocessing.iter().any(is_ges),
    );
    let mut steps = 0;
    let mut restart_count = 0;
    let mut conflicts_at_last_restart = 0;
    let mut next_restart_conflicts = RESTART_CONFLICT_SCALE * luby(restart_count + 1);
    let mut next_db_reduction_conflicts = DB_REDUCTION_CONFLICT_INTERVAL;

    if formula.get_clauses().any(|(_, clause)| clause.len() == 0) {
        return unsat(logger);
    }

    let initial_units: Vec<_> = formula
        .get_clauses()
        .filter(|(_, clause)| clause.len() == 1)
        .map(|(idx, clause)| (idx, clause.get_literals()[0]))
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

        let mut propagation = vec![decision_lit];
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
                    post_clause_without_z,
                } => learn_dip_clauses(
                    formula,
                    &mut history,
                    logger,
                    &mut propagation,
                    dip_a,
                    dip_b,
                    post_clause_without_z,
                    guidance,
                )?,
            };
            formula.stats.record_learning_time(learning_start.elapsed());

            let Some(learned) = learned else {
                return unsat(logger);
            };

            heuristics.bump(formula, learned.get_literals());
            heuristics.decay(formula);

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
                let run_ges = restart_count.is_multiple_of(GES_RESTART_INTERVAL);
                let run_inprocessing = restart_count.is_multiple_of(INPROCESSING_RESTART_INTERVAL);
                if restart(
                    py,
                    &mut steps,
                    formula,
                    &mut history,
                    &inprocessing,
                    run_ges,
                    run_inprocessing,
                    logger,
                )? {
                    return unsat(logger);
                }
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
    if history
        .backtrack_until_not_conflicting(&learned, backtrack_level, formula)
        .is_none()
    {
        return Ok(None);
    }

    formula.stats.add_learnt_clause(&learned);
    let clause_idx = formula.add_clause(learned.clone(), logger, Some(history));

    if let Some(unit) = formula
        .get_clause_at_idx(clause_idx)
        .get_unit_literal(&formula.assignment)
        .copied()
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
    post_clause_without_z: Vec<Literal>,
    guidance: &mut Option<GuidanceTracker>,
) -> PyResult<Option<Clause>> {
    let z = extension_literal(formula, logger, &dip_a, &dip_b);
    observe_dip_extension(guidance, &dip_a, &dip_b, &z)?;

    let first = z.negated();
    let mut post_literals = Vec::with_capacity(post_clause_without_z.len() + 1);
    post_literals.push(first);
    post_literals.extend(
        post_clause_without_z
            .into_iter()
            .filter(|literal| literal != &first),
    );
    let (mut post_literals, minimized_literals, minimization_time) =
        history.minimize_clause_literals(formula, post_literals);
    formula
        .stats
        .add_minimized_literals(minimized_literals as u64);
    formula.stats.record_minimization_time(minimization_time);
    order_asserting_clause(&mut post_literals, history);
    let (post_backtrack_level, post_lbd) = dip_post_clause_metrics(&post_literals, history);
    if post_lbd == 1 {
        formula.stats.dip_unit_post_clauses += 1;
    } else {
        debug_assert_eq!(post_lbd, 2);
        formula.stats.dip_glue_post_clauses += 1;
    }
    let post_clause = Clause::from_literals(post_literals, post_lbd);

    let Some(actual_backtrack) =
        history.backtrack_until_not_conflicting(&post_clause, post_backtrack_level, formula)
    else {
        return Ok(None);
    };

    let learned = Clause::new(
        post_clause.get_literals().into(),
        post_clause.lbd,
        crate::formula::clause::CreationType::Learned,
    );

    if post_clause.is_empty(&formula.assignment) {
        return Err(pyo3::exceptions::PyRuntimeError::new_err(format!(
            "DIP post clause dip_a={:?} dip_b={:?} z={:?} backtrack_level={} is conflicting immediately after backtrack: {:?}",
            dip_a, dip_b, z, actual_backtrack, post_clause
        )));
    }
    if !post_clause.is_unit(&formula.assignment) {
        return Err(pyo3::exceptions::PyRuntimeError::new_err(format!(
            "DIP post clause dip_a={:?} dip_b={:?} z={:?} backtrack_level={} is not asserting after backtrack: {:?}",
            dip_a, dip_b, z, actual_backtrack, post_clause
        )));
    }

    formula.stats.add_learnt_clause(&post_clause);
    let post_idx = formula.add_clause_unchecked(post_clause, logger);

    if let Some(post_unit) = formula
        .get_clause_at_idx(post_idx)
        .get_unit_literal(&formula.assignment)
        .copied()
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

    Ok(Some(learned))
}

fn observe_dip_extension(
    guidance: &mut Option<GuidanceTracker>,
    dip_a: &Literal,
    dip_b: &Literal,
    result: &Literal,
) -> PyResult<()> {
    if let Some(tracker) = guidance {
        tracker.observe(dip_a.get_index(), dip_b.get_index(), result.get_index())?;
    }
    Ok(())
}

fn dip_post_clause_metrics(literals: &[Literal], history: &History) -> (usize, i16) {
    let mut levels = Vec::new();
    let mut backtrack_level = 0;
    for literal in literals.iter().skip(1) {
        let Some(level) = history.get_literal_level(literal) else {
            continue;
        };
        backtrack_level = backtrack_level.max(level);
        if !levels.contains(&level) {
            levels.push(level);
        }
    }

    // The unassigned extension literal forms its own LBD block.
    let lbd = i16::try_from(levels.len())
        .unwrap_or(i16::MAX)
        .saturating_add(1);
    (backtrack_level, lbd)
}

fn order_asserting_clause(literals: &mut [Literal], history: &History) {
    if literals.len() <= 2 {
        return;
    }

    let mut highest = 1;
    let mut highest_level = history.get_literal_level(&literals[1]).unwrap_or(0);
    for index in 2..literals.len() {
        let level = history.get_literal_level(&literals[index]).unwrap_or(0);
        if level > highest_level {
            highest = index;
            highest_level = level;
        }
    }
    literals.swap(1, highest);
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

fn global_inprocessing_scope(formula: &Formula) -> ClauseScope {
    ClauseScope::range(0..formula.clause_slots_len())
}

fn is_ges(process: &Process) -> bool {
    matches!(
        process,
        Process::GES
            | Process::GESAlways
            | Process::GESLBD
            | Process::GESRandom
            | Process::GESPar
            | Process::GESUtility
            | Process::GESVSIDS
    )
}

fn is_ges_modifier(process: &Process) -> bool {
    matches!(process, Process::GESCompress | Process::GESTrail)
}

fn scheduled_inprocessing(
    inprocessing: &[Process],
    run_ges: bool,
    run_inprocessing: bool,
) -> Vec<Process> {
    let ges_enabled = inprocessing.iter().any(is_ges);
    let mut methods = inprocessing
        .iter()
        .copied()
        .filter(|process| {
            if is_ges(process) {
                run_ges
            } else if is_ges_modifier(process) {
                run_ges && ges_enabled
            } else {
                run_inprocessing
            }
        })
        .collect::<Vec<_>>();

    if run_ges
        && run_inprocessing
        && ges_enabled
        && let Some(bva_index) = methods.iter().position(|process| *process == Process::BVA)
    {
        let trailing = methods.drain(bva_index + 1..).collect::<Vec<_>>();
        let (ges, others): (Vec<_>, Vec<_>) = trailing
            .into_iter()
            .partition(|process| is_ges(process) || is_ges_modifier(process));
        methods.splice(bva_index..bva_index, ges);
        methods.extend(others);
    }

    if let Some(preference_index) = methods
        .iter()
        .position(|process| *process == Process::Preference)
    {
        let trailing = methods.drain(preference_index + 1..).collect::<Vec<_>>();
        let (ges, others): (Vec<_>, Vec<_>) = trailing
            .into_iter()
            .partition(|process| is_ges(process) || is_ges_modifier(process));
        methods.splice(preference_index..preference_index, ges);
        methods.extend(others);
    }

    if run_inprocessing
        && methods.contains(&Process::BVA)
        && let Some(vivification_index) = methods
            .iter()
            .position(|process| *process == Process::Vivification)
    {
        let vivification = methods.remove(vivification_index);
        let bva_index = methods
            .iter()
            .position(|process| *process == Process::BVA)
            .unwrap();
        methods.insert(bva_index, vivification);
    }

    if run_inprocessing
        && let Some(bva_index) = methods.iter().position(|process| *process == Process::BVA)
        && let Some(preference_index) = methods
            .iter()
            .position(|process| *process == Process::Preference)
    {
        let preference = methods.remove(preference_index);
        let insertion = if preference_index < bva_index {
            bva_index - 1
        } else {
            bva_index
        };
        methods.insert(insertion, preference);
    }

    methods
}

fn restart<W: Write>(
    py: Python<'_>,
    steps: &mut u64,
    formula: &mut Formula,
    history: &mut History,
    inprocessing: &[Process],
    run_ges: bool,
    run_inprocessing: bool,
    logger: &mut Option<DratLogger<W>>,
) -> PyResult<bool> {
    let restart_start = Instant::now();
    formula.stats.add_restart();
    let methods = scheduled_inprocessing(inprocessing, run_ges, run_inprocessing);
    let ran_ges = methods.iter().any(is_ges);
    let reasoning_levels =
        ran_ges.then(|| history.snapshot_literal_levels(formula.assignment.len()));
    formula.revert_decision(1, history);

    let first_new_clause = formula.clause_slots_len();
    if !methods.is_empty() {
        let inprocessing_start = Instant::now();
        let scope = global_inprocessing_scope(formula);
        if let Some(preference_index) = methods
            .iter()
            .position(|method| *method == Process::Preference)
        {
            let before = &methods[..preference_index];
            let after = &methods[preference_index + 1..];
            if !before.is_empty() {
                formula.process_in_phase(
                    before,
                    &scope,
                    logger,
                    Some((py, steps)),
                    false,
                    Some(history),
                    reasoning_levels.as_deref(),
                    crate::process::ProcessPhase::Inprocessing,
                )?;
            }
            if crate::process::preference::process_at_restart(formula, history, logger) {
                formula
                    .stats
                    .record_inprocessing_time(inprocessing_start.elapsed());
                formula.stats.record_restart_time(restart_start.elapsed());
                return Ok(true);
            }
            if !after.is_empty() {
                formula.process_in_phase(
                    after,
                    &scope,
                    logger,
                    Some((py, steps)),
                    false,
                    Some(history),
                    reasoning_levels.as_deref(),
                    crate::process::ProcessPhase::Inprocessing,
                )?;
            }
        } else {
            formula.process_in_phase(
                &methods,
                &scope,
                logger,
                Some((py, steps)),
                false,
                Some(history),
                reasoning_levels.as_deref(),
                crate::process::ProcessPhase::Inprocessing,
            )?;
        }
        formula
            .stats
            .record_inprocessing_time(inprocessing_start.elapsed());
    }
    if ran_ges {
        formula.clear_ges_trail_touched();
    }

    let mut propagation = Vec::new();
    let mut root_conflict = false;
    for idx in first_new_clause..formula.clause_slots_len() {
        if formula.is_clause_garbage(idx) {
            continue;
        }
        let assertion = {
            let clause = formula.get_clause_at_idx(idx);
            if clause.is_empty(&formula.assignment) {
                None
            } else {
                clause.get_unit_literal(&formula.assignment).copied()
            }
        };
        let Some(literal) = assertion else {
            if formula.get_clause_at_idx(idx).is_empty(&formula.assignment) {
                root_conflict = true;
                break;
            }
            continue;
        };
        match formula.assign_implication(literal, history, Some(idx)) {
            AssignResult::Conflict => {
                root_conflict = true;
                break;
            }
            AssignResult::AlreadyAssigned => {}
            AssignResult::Assigned(literal) => propagation.push(literal),
        }
    }
    if !root_conflict && !propagation.is_empty() {
        let propagation_start = Instant::now();
        root_conflict = propagate_from(formula, history, propagation).is_some();
        formula
            .stats
            .record_propagation_time(propagation_start.elapsed());
    }

    formula.stats.record_restart_time(restart_start.elapsed());
    Ok(root_conflict)
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
    fn inprocessing_scope_includes_the_global_clause_database() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4]]);
        formula.get_clause_at_idx_mut(1).lbd = 2;
        formula.get_clause_at_idx_mut(2).lbd = 4;
        formula.get_clause_at_idx_mut(3).lbd = 7;

        let scope = global_inprocessing_scope(&formula);

        assert!(
            formula
                .get_clauses()
                .all(|(index, clause)| scope.includes(index, clause))
        );
    }

    #[test]
    fn scheduled_inprocessing_runs_ges_before_bva_without_duplication() {
        let selected = [
            Process::BVE,
            Process::GESRandom,
            Process::GESCompress,
            Process::GESTrail,
            Process::Subsumption,
            Process::GES,
            Process::GESAlways,
            Process::BVA,
            Process::GESPar,
            Process::Others,
            Process::GESUtility,
            Process::GESVSIDS,
            Process::GESLBD,
        ];
        assert_eq!(
            scheduled_inprocessing(&selected, true, false),
            vec![
                Process::GESRandom,
                Process::GESCompress,
                Process::GESTrail,
                Process::GES,
                Process::GESAlways,
                Process::GESPar,
                Process::GESUtility,
                Process::GESVSIDS,
                Process::GESLBD
            ]
        );
        assert_eq!(
            scheduled_inprocessing(&selected, false, true),
            vec![
                Process::BVE,
                Process::Subsumption,
                Process::BVA,
                Process::Others,
            ]
        );
        assert_eq!(
            scheduled_inprocessing(&selected, true, true),
            vec![
                Process::BVE,
                Process::GESRandom,
                Process::GESCompress,
                Process::GESTrail,
                Process::Subsumption,
                Process::GES,
                Process::GESAlways,
                Process::GESPar,
                Process::GESUtility,
                Process::GESVSIDS,
                Process::GESLBD,
                Process::BVA,
                Process::Others,
            ]
        );
        assert_eq!(
            scheduled_inprocessing(
                &[Process::BVA, Process::GESUtility, Process::GESVSIDS],
                true,
                true,
            ),
            vec![Process::GESUtility, Process::GESVSIDS, Process::BVA]
        );
        let with_preference = [Process::BVA, Process::Preference, Process::GESUtility];
        assert_eq!(
            scheduled_inprocessing(&with_preference, true, false),
            vec![Process::GESUtility]
        );
        assert_eq!(
            scheduled_inprocessing(&with_preference, false, true),
            vec![Process::Preference, Process::BVA]
        );
        assert_eq!(
            scheduled_inprocessing(&with_preference, true, true),
            vec![Process::GESUtility, Process::Preference, Process::BVA]
        );
        assert_eq!(
            scheduled_inprocessing(&[Process::Preference], false, true),
            vec![Process::Preference]
        );
        assert_eq!(
            scheduled_inprocessing(&[Process::Preference, Process::GESVSIDS], true, true),
            vec![Process::GESVSIDS, Process::Preference]
        );
        let others = [
            Process::BVA,
            Process::BVE,
            Process::GESCompress,
            Process::GESTrail,
            Process::Subsumption,
            Process::Others,
        ];
        assert!(scheduled_inprocessing(&others, false, false).is_empty());
        assert!(scheduled_inprocessing(&others, true, false).is_empty());
        assert_eq!(
            scheduled_inprocessing(&others, false, true),
            vec![
                Process::BVA,
                Process::BVE,
                Process::Subsumption,
                Process::Others
            ]
        );
        for run_ges in [false, true] {
            for run_inprocessing in [false, true] {
                assert!(scheduled_inprocessing(&[], run_ges, run_inprocessing).is_empty());
            }
        }
    }

    #[test]
    fn vivification_is_opt_in_and_runs_before_preference_and_bva() {
        for selected in [
            vec![Process::BVA, Process::Preference, Process::Vivification],
            vec![Process::Vivification, Process::Preference, Process::BVA],
        ] {
            assert!(scheduled_inprocessing(&selected, true, false).is_empty());
            assert!(scheduled_inprocessing(&selected, false, false).is_empty());
            for run_ges in [false, true] {
                assert_eq!(
                    scheduled_inprocessing(&selected, run_ges, true),
                    vec![Process::Vivification, Process::Preference, Process::BVA]
                );
            }
        }
        assert_eq!(
            scheduled_inprocessing(&[Process::Vivification], false, true),
            vec![Process::Vivification]
        );
        assert_eq!(
            scheduled_inprocessing(
                &[Process::BVA, Process::Vivification, Process::GES],
                true,
                true
            ),
            vec![Process::GES, Process::Vivification, Process::BVA]
        );
        assert_eq!(
            scheduled_inprocessing(&[Process::BVA], false, true),
            vec![Process::BVA]
        );
    }

    #[test]
    fn restart_consumes_and_clears_trail_touches_before_the_next_segment() {
        Python::initialize();
        Python::attach(|py| {
            let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4]]);
            for (_, clause) in formula.get_clauses_mut() {
                clause.lbd = 3;
            }
            formula.configure_ges_trail_tracking(true);
            formula.record_ges_analysis_use(2);
            let mut history = History::new();
            formula.add_decision(&Literal::new(1), &mut history);
            let mut logger: Option<DratLogger<Empty>> = None;
            let mut steps = 0;

            restart(
                py,
                &mut steps,
                &mut formula,
                &mut history,
                &[Process::GESVSIDS, Process::GESTrail],
                true,
                false,
                &mut logger,
            )
            .unwrap();

            assert!(formula.ges_trail_touched.is_empty());
            assert_eq!(formula.stats.ges_trail_unique_touches, 1);
            assert_eq!(formula.stats.ges_trail_clauses_selected, 1);
            assert_eq!(formula.stats.ges_trail_cursor_selected, 3);
            assert_eq!(formula.stats.ges_trail_duplicate_skips, 1);
        });
    }

    #[test]
    fn restart_preserves_trail_touches_when_ges_is_not_due() {
        Python::initialize();
        Python::attach(|py| {
            let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3]]);
            formula.configure_ges_trail_tracking(true);
            formula.record_ges_analysis_use(2);
            let mut history = History::new();
            formula.add_decision(&Literal::new(1), &mut history);
            let mut logger: Option<DratLogger<Empty>> = None;
            let mut steps = 0;

            restart(
                py,
                &mut steps,
                &mut formula,
                &mut history,
                &[Process::GESVSIDS, Process::GESTrail],
                false,
                false,
                &mut logger,
            )
            .unwrap();

            assert_eq!(formula.ges_trail_touched, vec![2]);
            assert_eq!(formula.stats.ges_trail_clauses_selected, 0);
        });
    }

    #[test]
    fn restart_runs_each_ges_once_with_pre_backtrack_reasoning() {
        Python::attach(|py| {
            for process in [
                Process::GES,
                Process::GESAlways,
                Process::GESLBD,
                Process::GESRandom,
                Process::GESPar,
                Process::GESUtility,
            ] {
                for run_inprocessing in [false, true] {
                    let mut formula = Formula::from_vec(vec![vec![-1, -2, 3]]);
                    formula.get_clause_at_idx_mut(0).lbd = 3;
                    let mut logger: Option<DratLogger<Empty>> = None;
                    let extension = extension_literal(
                        &mut formula,
                        &mut logger,
                        &Literal::new(1),
                        &Literal::new(2),
                    );
                    let mut history = History::new();
                    formula.add_decision(&Literal::new(1), &mut history);
                    for literal in [Literal::new(2), Literal::new(3), extension] {
                        assert!(matches!(
                            formula.assign_implication(literal, &mut history, None),
                            AssignResult::Assigned(_)
                        ));
                    }

                    let mut steps = 0;
                    restart(
                        py,
                        &mut steps,
                        &mut formula,
                        &mut history,
                        &[Process::Subsumption, process],
                        true,
                        run_inprocessing,
                        &mut logger,
                    )
                    .unwrap();

                    assert_eq!(history.get_decision_level(), 0);
                    assert_eq!(formula.assignment.get_value(1), None);
                    assert_eq!(formula.stats.restarts, 1);
                    assert_eq!(formula.stats.ges_clauses_inspected, 1);
                    // All literals shared one level in the pre-backtrack snapshot,
                    // so shortening ties rather than improves LBD. Only the
                    // isolated unconditional variant installs that rewrite.
                    let always = process == Process::GESAlways;
                    assert_eq!(formula.stats.ges_rewrites_rejected, u64::from(!always));
                    assert_eq!(formula.stats.ges_lbd_improvements, 0);
                    assert_eq!(formula.stats.ges_literals_removed, u64::from(always));
                    assert_eq!(formula.is_clause_garbage(0), always);
                    if always {
                        assert_eq!(formula.get_clause_at_idx(4).len(), 2);
                        assert_eq!(formula.get_clause_at_idx(4).lbd, 2);
                    } else {
                        assert_eq!(formula.get_clause_at_idx(0).len(), 3);
                    }
                }
            }
        });
    }

    #[test]
    fn restart_immediately_propagates_a_ges_clause_that_is_unit_at_root() {
        Python::initialize();
        Python::attach(|py| {
            let mut formula = Formula::from_vec(vec![vec![-1, -2, 3]]);
            formula.get_clause_at_idx_mut(0).lbd = 0;
            let mut logger: Option<DratLogger<Empty>> = None;
            let extension = extension_literal(
                &mut formula,
                &mut logger,
                &Literal::new(1),
                &Literal::new(2),
            );
            let mut history = History::new();
            assert!(matches!(
                formula.assign_implication(Literal::new(-3), &mut history, None),
                AssignResult::Assigned(_)
            ));
            let mut steps = 0;

            let conflict = restart(
                py,
                &mut steps,
                &mut formula,
                &mut history,
                &[Process::GES, Process::GESCompress],
                true,
                false,
                &mut logger,
            )
            .unwrap();

            assert!(!conflict);
            assert_eq!(history.get_decision_level(), 0);
            assert_eq!(
                formula.assignment.get_value(extension.get_index() as usize),
                Some(false)
            );
            let replacement = formula.get_clause_at_idx(4);
            assert_eq!(
                replacement.get_literals(),
                &[extension.negated(), Literal::new(3)]
            );
        });
    }

    #[test]
    fn ges_replacement_watches_ignore_literals_already_false_at_root() {
        Python::initialize();
        Python::attach(|py| {
            let mut formula = Formula::from_vec(vec![vec![-1, -2, 3, 4, 5]]);
            formula.get_clause_at_idx_mut(0).lbd = 0;
            let mut logger: Option<DratLogger<Empty>> = None;
            let extension = extension_literal(
                &mut formula,
                &mut logger,
                &Literal::new(1),
                &Literal::new(2),
            );
            let mut history = History::new();
            for literal in [Literal::new(-3), Literal::new(-4)] {
                assert!(matches!(
                    formula.assign_implication(literal, &mut history, None),
                    AssignResult::Assigned(_)
                ));
            }
            let mut steps = 0;

            assert!(
                !restart(
                    py,
                    &mut steps,
                    &mut formula,
                    &mut history,
                    &[Process::GES, Process::GESCompress],
                    true,
                    false,
                    &mut logger,
                )
                .unwrap()
            );

            let replacement = formula.get_clause_at_idx(4);
            assert_eq!(
                replacement.watched_literals(),
                Some((&Literal::new(5), Some(&extension.negated())))
            );
            formula.add_decision(&Literal::new(-5), &mut history);
            assert_eq!(
                propagate_from(&mut formula, &mut history, [Literal::new(-5)]),
                None
            );
            assert_eq!(
                formula.assignment.get_value(extension.get_index() as usize),
                Some(false)
            );
        });
    }

    #[test]
    fn restart_vivification_backtracks_and_propagates_new_root_unit() {
        Python::initialize();
        Python::attach(|py| {
            let mut formula =
                Formula::from_vec(vec![vec![1, 2, 3], vec![1, 4], vec![1, -4], vec![-1, 5]]);
            let mut history = History::new();
            assert!(!formula.rebuild_root_implications(&mut history));
            for variable in 1..=5 {
                assert_eq!(formula.assignment.get_value(variable), None);
            }
            formula.add_decision(&Literal::new(1), &mut history);
            assert_eq!(
                propagate_from(&mut formula, &mut history, [Literal::new(1)]),
                None
            );
            assert_eq!(formula.get_clause_at_idx(3).lock_count, 1);
            formula.add_decision(&Literal::new(2), &mut history);
            assert_eq!(history.get_decision_level(), 2);
            let mut steps = 0;
            let mut logger: Option<DratLogger<Empty>> = None;

            assert!(
                !restart(
                    py,
                    &mut steps,
                    &mut formula,
                    &mut history,
                    &[Process::Vivification],
                    false,
                    true,
                    &mut logger,
                )
                .unwrap()
            );

            assert_eq!(formula.stats.vivification_passes, 1);
            assert_eq!(formula.stats.vivification_clauses_strengthened, 1);
            assert_eq!(formula.stats.vivification_units, 1);
            assert_eq!(history.get_decision_level(), 0);
            assert_eq!(history.trail(), history.level_trail(0));
            for variable in [1, 5] {
                assert_eq!(formula.assignment.get_value(variable), Some(true));
                assert_eq!(
                    history.get_literal_level(&Literal::new(variable as i32)),
                    Some(0)
                );
            }
            for variable in [2, 3, 4] {
                assert_eq!(formula.assignment.get_value(variable), None);
                assert_eq!(
                    history.get_literal_level(&Literal::new(variable as i32)),
                    None
                );
            }
            assert!(formula.is_clause_garbage(0));
            assert_eq!(
                formula.get_clause_at_idx(4).get_literals(),
                &[Literal::new(1)]
            );
            assert_eq!(
                history.active_reason_indices(),
                [3, 4].into_iter().collect()
            );
            for (index, clause) in formula.get_clauses() {
                assert_eq!(
                    clause.lock_count,
                    if index == 3 || index == 4 { 1 } else { 0 }
                );
            }
        });
    }

    #[test]
    fn restart_vivification_preserves_bva_definitions() {
        Python::initialize();
        Python::attach(|py| {
            let mut clauses = vec![vec![1, 2, 3], vec![1, 4], vec![1, -4], vec![-1, 5]];
            clauses.extend((6..=7).flat_map(|a| (8..=11).map(move |b| vec![a, b])));
            let mut formula = Formula::from_vec(clauses);
            let mut history = History::new();
            let mut steps = 0;
            let mut logger: Option<DratLogger<Empty>> = None;
            assert!(
                !restart(
                    py,
                    &mut steps,
                    &mut formula,
                    &mut history,
                    &[Process::BVA],
                    false,
                    true,
                    &mut logger,
                )
                .unwrap()
            );
            assert!(formula.stats.bva_literals > 0);
            let definitions: Vec<_> = formula
                .get_clauses()
                .filter(|(_, clause)| clause.lbd == 0)
                .map(|(index, clause)| (index, clause.get_literals().to_vec()))
                .collect();
            assert!(!definitions.is_empty());
            assert_eq!(formula.assignment.get_value(1), None);
            formula.add_decision(&Literal::new(2), &mut history);

            assert!(
                !restart(
                    py,
                    &mut steps,
                    &mut formula,
                    &mut history,
                    &[Process::Vivification],
                    false,
                    true,
                    &mut logger,
                )
                .unwrap()
            );

            assert_eq!(formula.stats.vivification_passes, 1);
            assert!(formula.stats.vivification_clauses_strengthened > 0);
            assert_eq!(history.get_decision_level(), 0);
            assert_eq!(formula.assignment.get_value(1), Some(true));
            assert_eq!(formula.assignment.get_value(5), Some(true));
            for (index, literals) in definitions {
                assert!(!formula.is_clause_garbage(index));
                let clause = formula.get_clause_at_idx(index);
                assert_eq!(clause.lbd, 0);
                assert_eq!(clause.get_literals(), literals);
                assert_eq!(clause.lock_count, 0);
            }
        });
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
                false,
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
    fn dip_post_metrics_include_all_lower_literals_after_fresh_extension() {
        let mut history = History::new();
        let lower = Literal::new(1);
        let higher = Literal::new(2);
        let extension = Literal::new(3);
        history.add_decision(&lower);
        history.add_decision(&higher);

        let (backtrack_level, lbd) = dip_post_clause_metrics(
            &[extension.negated(), lower.negated(), higher.negated()],
            &history,
        );

        assert_eq!(backtrack_level, 2);
        assert_eq!(lbd, 3);
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

        let extension_lbds = formula
            .get_clauses()
            .rev()
            .take(3)
            .map(|(_, clause)| clause.lbd)
            .collect::<Vec<_>>();
        assert_eq!(extension_lbds, vec![0, 0, 0]);
    }

    #[test]
    fn dip_guidance_observes_the_actual_reused_extension_variable() {
        use crate::guidance::{GuidanceSpec, GuidanceTracker};

        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![5]]);
        let dip_a = Literal::new(1);
        let dip_b = Literal::new(2);
        let mut logger: Option<DratLogger<Empty>> = None;
        let mut guidance = Some(
            GuidanceTracker::new(
                GuidanceSpec::StaticAndDag {
                    original_variables: 2,
                    operands: vec![[1, 2]],
                },
                None,
            )
            .unwrap(),
        );

        let first = extension_literal(&mut formula, &mut logger, &dip_a, &dip_b);
        assert_eq!(first.get_index(), 6);
        observe_dip_extension(&mut guidance, &dip_a, &dip_b, &first).unwrap();

        let reused = extension_literal(&mut formula, &mut logger, &dip_b, &dip_a);
        assert_eq!(reused.get_index(), 6);
        observe_dip_extension(&mut guidance, &dip_b, &dip_a, &reused).unwrap();

        let summary = guidance.as_ref().unwrap().summary();
        assert_eq!(summary.checks, 2);
        assert_eq!(summary.matches, 2);
        assert_eq!(summary.unique_matches, 1);
        assert_eq!(summary.stages_completed, 1);
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
                    &mut None,
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
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
                    Vec::new(),
                    &mut None,
                )
                .unwrap();
                assert!(res.is_none());
            });
        });
    }
}
