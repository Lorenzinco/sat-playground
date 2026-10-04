//! Bounded, root-only clause vivification. Probes never use search propagation.
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::assignment::AssignResult;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;

use crate::process::ClauseScope;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use std::collections::{HashSet, VecDeque};
use std::io::Write;

const ROUND_LIMIT: u64 = 50_000;
const CLAUSE_LIMIT: u64 = 4_096;
const WINDOW: usize = 4_096;
const CANDIDATES: usize = 256;

#[derive(Default)]
struct Scratch {
    literals: Vec<Literal>,
    resolvent: Vec<Literal>,
    result: Vec<Literal>,
    queue: VecDeque<Literal>,
    seen: HashSet<Literal>,
    assumptions: Vec<Literal>,
}

// Traverse only the reason dependencies of the conflict, not the entire trail.
// Leaves must be explicitly recorded probe assumptions: root assignments are not
// proof premises. A positive implication retains the candidate literal while
// tracing the dependencies of its virtual negation.
fn resolve(
    formula: &Formula,
    history: &History,
    scratch: &mut Scratch,
    positive: Option<Literal>,
    ticks: &mut u64,
    limit: u64,
) -> Result<(), ()> {
    scratch.result.clear();
    if let Some(literal) = positive {
        scratch.result.push(literal);
    }
    scratch.seen.clear();
    while let Some(false_literal) = scratch.resolvent.pop() {
        if *ticks >= limit {
            return Err(());
        }
        *ticks += 1;
        if !scratch.seen.insert(false_literal) {
            continue;
        }
        let literal = false_literal.negated();
        let level_index = history.get_literal_level(&literal).ok_or(())?;
        if let Some(reason) = history.get_reason(&literal) {
            for antecedent in formula.get_clause_at_idx(reason) {
                if *ticks >= limit {
                    return Err(());
                }
                *ticks += 1;
                if *antecedent != literal {
                    scratch.resolvent.push(*antecedent);
                }
            }
        } else if level_index == 1 && scratch.assumptions.contains(&literal) {
            scratch.result.push(false_literal);
        } else {
            // In particular, do not silently discard unproved root facts.
            return Err(());
        }
    }
    Ok(())
}

fn probe(
    formula: &mut Formula,
    history: &mut History,
    index: usize,
    scratch: &mut Scratch,
    ticks: &mut u64,
    limit: u64,
) -> Result<(), ()> {
    scratch.queue.clear();
    scratch.result.clear();
    scratch.assumptions.clear();
    debug_assert_eq!(history.get_decision_level(), 0);
    for position in 0..scratch.literals.len() {
        if *ticks >= limit {
            return Err(());
        }
        let literal = scratch.literals[position];
        match literal.eval(&formula.assignment) {
            Some(false) => continue,
            Some(true) => {
                scratch.resolvent.clear();
                scratch.resolvent.push(literal.negated());
                resolve(formula, history, scratch, Some(literal), ticks, limit)?;
                return Ok(());
            }
            None => {
                let assumption = literal.negated();
                if scratch.assumptions.is_empty() {
                    formula.assignment.assign_literal(assumption);
                    history.add_decision(&assumption);
                } else {
                    // Later assumptions share the same level and bypass search
                    // utility updates, just like the probing propagator.
                    formula.assignment.assign_literal(assumption);
                    let conflict = history.add_implication(&assumption, None);
                    debug_assert!(conflict.is_none());
                }
                scratch.assumptions.push(assumption);
                scratch.queue.push_back(assumption);
                if let Some(conflict) = formula.propagate_twl_with_mode::<true>(
                    history,
                    &mut scratch.queue,
                    index,
                    ticks,
                    limit,
                )? {
                    scratch.resolvent.clear();
                    scratch
                        .resolvent
                        .extend_from_slice(formula.get_clause_at_idx(conflict).get_literals());
                    resolve(formula, history, scratch, None, ticks, limit)?;
                    return Ok(());
                }
            }
        }
    }
    // The excluded candidate supplies the final conflict when all its literals
    // are false. Resolving their reasons can remove negatively implied literals.
    scratch.resolvent.clear();
    scratch.resolvent.extend_from_slice(&scratch.literals);
    resolve(formula, history, scratch, None, ticks, limit)
}

// Flat rollback retains the trail buffers for the next candidate while leaving
// root assignments and their reason locks untouched.
fn rollback_probe(formula: &mut Formula, history: &mut History, scratch: &mut Scratch) {
    if !scratch.assumptions.is_empty() {
        assert_eq!(history.get_decision_level(), 1);
        formula.revert_decision(1, history);
        scratch.assumptions.clear();
    }
    scratch.queue.clear();
}

pub fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
) -> PyResult<()> {
    let mut owned = None;
    let owns_history = history.is_none();
    let history = history.unwrap_or_else(|| owned.get_or_insert_with(History::new));
    if history.get_decision_level() != 0 {
        return Err(PyValueError::new_err(
            "vivification requires a root-level history",
        ));
    }
    let result = run(formula, scope, logger, &mut signal, history);
    // A temporary history must not leave assignments or reason locks behind.
    // Search rebuilds its own root trail afterwards.
    if owns_history {
        formula.rewind_root_implications(history);
    }
    result
}

fn run<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: &mut Option<(Python<'_>, &mut u64)>,
    history: &mut History,
) -> PyResult<()> {
    formula.stats.vivification_passes += 1;
    let mut scratch = Scratch::default();
    let mut root_conflict = formula.rebuild_root_implications(history);
    // Newly attached clauses may already be unit under old root assignments,
    // whose watch events have been consumed. Scan once before any probes.
    if !root_conflict {
        for index in 0..formula.clause_slots_len() {
            if formula.is_clause_garbage(index) {
                continue;
            }
            let clause = formula.get_clause_at_idx(index);
            if clause.is_empty(&formula.assignment) {
                root_conflict = true;
                break;
            }
            if let Some(literal) = clause.get_unit_literal(&formula.assignment).copied() {
                match formula.assign_implication(literal, history, Some(index)) {
                    AssignResult::Conflict => {
                        root_conflict = true;
                        break;
                    }
                    AssignResult::Assigned(literal) => scratch.queue.push_back(literal),
                    AssignResult::AlreadyAssigned => {}
                }
            }
        }
        if !root_conflict {
            root_conflict = formula.propagate_twl(history, &mut scratch.queue).is_some();
        }
    }
    if root_conflict {
        if !formula.get_clauses().any(|(_, clause)| clause.len() == 0) {
            formula.add_clause_unchecked(Clause::from_literals(Vec::new(), -1), logger);
        }
        return Ok(());
    }
    let slots = formula.clause_slots_len();
    if slots == 0 {
        return Ok(());
    }
    let mut candidates = Vec::with_capacity(CANDIDATES);
    let start = formula.vivification_cursor % slots;
    for offset in 0..slots.min(WINDOW) {
        let index = (start + offset) % slots;
        formula.vivification_cursor = (index + 1) % slots;
        if formula.is_clause_garbage(index) {
            continue;
        }
        let clause = formula.get_clause_at_idx(index);
        if clause.lbd != 0
            && clause.lock_count == 0
            && (3..=32).contains(&clause.len())
            && scope.includes(index, clause)
        {
            candidates.push(index);
            if candidates.len() == CANDIDATES {
                break;
            }
        }
    }
    candidates.sort_unstable_by_key(|&index| {
        let clause = formula.get_clause_at_idx(index);
        (
            if clause.lbd > 0 {
                clause.lbd as usize
            } else {
                usize::MAX
            },
            clause.len(),
            index,
        )
    });
    let mut ticks = 0;
    for index in candidates {
        if ticks >= ROUND_LIMIT {
            formula.stats.vivification_budget_exhaustions += 1;
            break;
        }
        let clause = formula.get_clause_at_idx(index);
        if clause.lock_count != 0 || formula.is_clause_garbage(index) {
            continue;
        }
        scratch.literals.clear();
        scratch.literals.extend_from_slice(clause.get_literals());
        scratch.literals.sort_unstable_by_key(|lit| {
            (
                std::cmp::Reverse(formula.occurrences_and_garbage(lit).len()),
                lit.get_index(),
            )
        });
        formula.stats.vivification_clauses_tried += 1;
        let before = ticks;
        let limit = ROUND_LIMIT.min(ticks + CLAUSE_LIMIT);
        let outcome = probe(formula, history, index, &mut scratch, &mut ticks, limit);
        rollback_probe(formula, history, &mut scratch);
        formula.stats.vivification_propagation_ticks += ticks - before;
        if outcome.is_err() {
            if ticks >= limit {
                formula.stats.vivification_budget_exhaustions += 1;
            }
        } else if scratch.result.len() < scratch.literals.len()
            && scratch
                .result
                .iter()
                .all(|lit| scratch.literals.contains(lit))
            && formula.get_clause_at_idx(index).lock_count == 0
        {
            let old = formula.get_clause_at_idx(index);
            let mut replacement = Clause::from_literals(
                scratch.result.clone(),
                if old.lbd > 0 {
                    old.lbd.min(scratch.result.len().max(1) as i16)
                } else {
                    old.lbd
                },
            );
            replacement.activity = old.activity;
            replacement.ges_protection = old.ges_protection;
            replacement.bva_generated = old.bva_generated;
            replacement.ges_generated = old.ges_generated;
            replacement.ges_used = old.ges_used;
            if replacement.lbd > 0 {
                formula.stats.add_learnt_clause(&replacement);
            }
            let new_index = formula.add_clause_unchecked(replacement, logger);
            formula.record_clause_removal(index);
            // Provenance belongs to the surviving replacement, not both slots.
            // Do not mark the retired source as used to suppress accounting.
            formula.get_clause_at_idx_mut(index).ges_generated = false;
            formula.delete_clause(index, logger);
            formula.stats.vivification_clauses_strengthened += 1;
            formula.stats.vivification_literals_removed +=
                (scratch.literals.len() - scratch.result.len()) as u64;
            formula.stats.vivification_units += u64::from(scratch.result.len() == 1);
            if scratch.result.is_empty() {
                return Ok(());
            }
            // Only the added clause can disturb root closure. Inspect its at
            // most 32 literals instead of rescanning the whole clause database.
            let mut unit = None;
            let mut unassigned = 0;
            let mut satisfied = false;
            for literal in &scratch.result {
                match literal.eval(&formula.assignment) {
                    Some(true) => {
                        satisfied = true;
                        break;
                    }
                    Some(false) => {}
                    None => {
                        unit = Some(*literal);
                        unassigned += 1;
                    }
                }
            }
            let mut conflict = !satisfied && unassigned == 0;
            if !satisfied && unassigned == 1 {
                match formula.assign_implication(unit.unwrap(), history, Some(new_index)) {
                    AssignResult::Conflict => conflict = true,
                    AssignResult::Assigned(literal) => {
                        scratch.queue.push_back(literal);
                        conflict = formula.propagate_twl(history, &mut scratch.queue).is_some();
                    }
                    AssignResult::AlreadyAssigned => {}
                }
            }
            if conflict {
                formula.add_clause_unchecked(Clause::from_literals(Vec::new(), -1), logger);
                return Ok(());
            }
        }
        if let Some((py, counter)) = signal.as_mut() {
            **counter += 1;
            py.check_signals()?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Empty;

    fn execute(formula: &mut Formula) {
        let scope = ClauseScope::range(0..formula.clause_slots_len());
        process::<Empty>(formula, &scope, &mut None, None, None).unwrap();
    }

    #[test]
    fn flat_trail_allocation_and_root_state_survive_budget_rollback() {
        let mut formula =
            Formula::from_vec(vec![vec![1, 10_000, 10_001], vec![1, -10_002], vec![2]]);
        let mut history = History::new();
        assert!(!formula.rebuild_root_implications(&mut history));
        let mut scratch = Scratch::default();
        scratch
            .literals
            .extend_from_slice(formula.get_clause_at_idx(0).get_literals());
        let mut ticks = 0;
        probe(
            &mut formula,
            &mut history,
            0,
            &mut scratch,
            &mut ticks,
            CLAUSE_LIMIT,
        )
        .unwrap();
        assert_eq!(history.get_decision_level(), 1);
        assert_eq!(history.level_trail(1).len(), 4);
        let trail_allocation = history.trail().as_ptr();
        assert_eq!(scratch.assumptions.len(), 3);
        assert_eq!(scratch.result.len(), 3);
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 1);
        rollback_probe(&mut formula, &mut history, &mut scratch);
        assert_eq!(history.trail().as_ptr(), trail_allocation);
        assert_eq!(history.trail(), &[Literal::new(2)]);
        assert!(scratch.assumptions.is_empty());
        assert_eq!(history.get_decision_level(), 0);
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 0);
        assert_eq!(formula.get_clause_at_idx(2).lock_count, 1);
        assert_eq!(formula.assignment.get_value(2), Some(true));
        for variable in [1, 10_000, 10_001, 10_002] {
            assert_eq!(formula.assignment.get_value(variable), None);
            assert_eq!(
                history.get_literal_level(&Literal::new(variable as i32)),
                None
            );
        }
        ticks = 0;
        assert!(probe(&mut formula, &mut history, 0, &mut scratch, &mut ticks, 1).is_err());
        assert_eq!(history.get_decision_level(), 1);
        assert_eq!(history.trail().as_ptr(), trail_allocation);
        rollback_probe(&mut formula, &mut history, &mut scratch);
        assert_eq!(history.trail().as_ptr(), trail_allocation);
        assert_eq!(history.get_decision_level(), 0);
        assert_eq!(formula.assignment.get_value(1), None);
        assert_eq!(formula.assignment.get_value(2), Some(true));
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 0);
        assert_eq!(formula.get_clause_at_idx(2).lock_count, 1);
        ticks = 0;
        probe(
            &mut formula,
            &mut history,
            0,
            &mut scratch,
            &mut ticks,
            CLAUSE_LIMIT,
        )
        .unwrap();
        assert_eq!(scratch.assumptions.len(), 3);
        assert_eq!(history.trail().as_ptr(), trail_allocation);
        rollback_probe(&mut formula, &mut history, &mut scratch);
        assert_eq!(history.trail().as_ptr(), trail_allocation);
    }

    #[test]
    fn learned_replacement_updates_live_clause_and_literal_counts() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3], vec![1, -2]]);
        formula.get_clause_at_idx_mut(0).lbd = 3;
        let tracked = formula.get_clause_at_idx(0).clone();
        formula.stats.add_learnt_clause(&tracked);
        execute(&mut formula);
        assert!(formula.is_clause_garbage(0));
        assert_eq!(formula.get_clause_at_idx(2).lbd, 2);
        assert_eq!(formula.stats.clauses_learnt, 2);
        assert_eq!(formula.stats.clauses_deleted, 1);
        assert_eq!(formula.stats.clauses_kept, 1);
        assert_eq!(formula.stats.learnt_clause_literals_kept, 2);
        assert_eq!(formula.stats.avg_clause_length, 2.0);
    }

    #[test]
    fn strengthened_ges_provenance_is_retired_exactly_once() {
        for use_replacement in [false, true] {
            let mut formula = Formula::from_vec(vec![vec![1, 2, 3], vec![1, -2]]);
            formula.get_clause_at_idx_mut(0).ges_generated = true;
            execute(&mut formula);
            assert!(formula.is_clause_garbage(0));

            assert!(formula.get_clause_at_idx(2).ges_generated);
            assert!(!formula.get_clause_at_idx(2).ges_used);
            assert_eq!(formula.stats.ges_replacements_deleted_unused, 0);
            if use_replacement {
                let mut history = History::new();
                formula.add_decision(&Literal::new(-1), &mut history);
                let mut queue = VecDeque::from([Literal::new(-1)]);
                formula.propagate_twl(&mut history, &mut queue);
                assert!(formula.get_clause_at_idx(2).ges_used);
                assert_eq!(formula.stats.ges_replacement_reason_uses, 1);
                formula.revert_decision(1, &mut history);
            }
            formula.record_clause_removal(2);
            formula.delete_clause::<Empty>(2, &mut None);
            formula.delete_clause::<Empty>(0, &mut None);
            formula.delete_clause::<Empty>(2, &mut None);
            assert_eq!(
                formula.stats.ges_replacements_deleted_unused,
                u64::from(!use_replacement)
            );
        }
    }

    #[test]
    fn newly_attached_root_unit_closes_before_candidate_selection() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![3], vec![-2, 4]]);
        let mut history = History::new();
        assert!(!formula.rebuild_root_implications(&mut history));
        let mut attached = Clause::from_literals(
            vec![Literal::new(-1), Literal::new(-3), Literal::new(2)],
            -1,
        );
        attached.ges_generated = true;
        let index = formula.add_clause_unchecked::<Empty>(attached, &mut None);
        assert_eq!(formula.assignment.get_value(2), None);
        process::<Empty>(
            &mut formula,
            &ClauseScope::range(0..4),
            &mut None,
            None,
            Some(&mut history),
        )
        .unwrap();
        assert_eq!(formula.assignment.get_value(2), Some(true));
        assert_eq!(formula.assignment.get_value(4), Some(true));
        assert_eq!(formula.get_clause_at_idx(index).lock_count, 1);
        assert_eq!(formula.get_clause_at_idx(2).lock_count, 1);
        assert!(!formula.is_clause_garbage(index));
        assert_eq!(formula.stats.vivification_clauses_tried, 0);
        assert_eq!(formula.stats.ges_replacement_reason_uses, 1);
    }

    #[test]
    fn unsupported_root_fact_is_not_counted_as_budget_exhaustion() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        let mut history = History::new();
        formula.assign_implication(Literal::new(1), &mut history, None);
        process::<Empty>(
            &mut formula,
            &ClauseScope::range(0..1),
            &mut None,
            None,
            Some(&mut history),
        )
        .unwrap();
        assert_eq!(formula.stats.vivification_clauses_tried, 1);
        assert_eq!(formula.stats.vivification_clauses_strengthened, 0);
        assert_eq!(formula.stats.vivification_budget_exhaustions, 0);
        assert_eq!(history.get_decision_level(), 0);
    }

    #[test]
    fn candidate_cannot_imply_itself() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        execute(&mut formula);
        assert_eq!(formula.stats.vivification_clauses_strengthened, 0);
        assert_eq!(formula.get_clause_at_idx(0).len(), 3);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 0);
    }

    #[test]
    fn negative_and_positive_implications_strengthen() {
        for binary in [vec![1, -2], vec![1, 2]] {
            let mut formula = Formula::from_vec(vec![vec![1, 2, 3], binary]);
            execute(&mut formula);
            assert!(formula.is_clause_garbage(0));
            assert_eq!(formula.stats.vivification_literals_removed, 1);
            assert!(formula.get_clauses().all(|(_, c)| c.lock_count == 0));
            for variable in 1..=3 {
                assert_eq!(formula.assignment.get_value(variable), None);
            }
        }
    }

    #[test]
    fn conflict_produces_root_unit_and_releases_temporary_locks() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3], vec![1, 4], vec![1, -4]]);
        execute(&mut formula);
        assert_eq!(formula.stats.vivification_units, 1);
        assert!(
            formula
                .get_clauses()
                .any(|(_, c)| c.get_literals() == [Literal::new(1)])
        );
        assert!(formula.get_clauses().all(|(_, c)| c.lock_count == 0));
    }

    #[test]
    fn budget_abort_rolls_back_and_definitions_are_not_candidates() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3], vec![1, 4]]);
        formula.get_clause_at_idx_mut(0).lbd = 0;
        execute(&mut formula);
        assert_eq!(formula.stats.vivification_clauses_tried, 0);
        let mut history = History::new();
        let mut scratch = Scratch::default();
        scratch.literals = vec![Literal::new(1), Literal::new(2), Literal::new(3)];
        let mut ticks = 0;
        assert!(probe(&mut formula, &mut history, 0, &mut scratch, &mut ticks, 1).is_err());
        formula.revert_decision(1, &mut history);
        assert_eq!(history.get_decision_level(), 0);
        assert!(formula.get_clauses().all(|(_, c)| c.lock_count == 0));
        for variable in 1..=4 {
            assert_eq!(formula.assignment.get_value(variable), None);
        }
    }

    #[test]
    fn existing_root_reasons_stay_locked_and_probe_locks_are_released() {
        let mut formula = Formula::from_vec(vec![vec![-4], vec![4, -5], vec![1, 2, 5]]);
        let mut history = History::new();
        assert!(!formula.rebuild_root_implications(&mut history));
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 1);
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 1);
        let scope = ClauseScope::range(0..3);
        process::<Empty>(&mut formula, &scope, &mut None, None, Some(&mut history)).unwrap();
        assert!(formula.is_clause_garbage(2));
        assert_eq!(history.get_decision_level(), 0);
        assert_eq!(formula.assignment.get_value(4), Some(false));
        assert_eq!(formula.assignment.get_value(5), Some(false));
        assert_eq!(formula.assignment.get_value(1), None);
        assert_eq!(formula.assignment.get_value(2), None);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 1);
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 1);
        assert_eq!(formula.get_clause_at_idx(3).lock_count, 0);
    }

    #[test]
    fn new_root_unit_propagates_and_keeps_its_reason_locked() {
        let mut formula =
            Formula::from_vec(vec![vec![1, 2, 3], vec![1, 4], vec![1, -4], vec![-1, 5]]);
        let mut history = History::new();
        process::<Empty>(
            &mut formula,
            &ClauseScope::range(0..4),
            &mut None,
            None,
            Some(&mut history),
        )
        .unwrap();
        assert_eq!(formula.assignment.get_value(1), Some(true));
        assert_eq!(formula.assignment.get_value(5), Some(true));
        assert_eq!(formula.get_clause_at_idx(4).lock_count, 1);
        assert_eq!(formula.get_clause_at_idx(3).lock_count, 1);
        assert_eq!(formula.get_clause_at_idx(1).lock_count, 0);
        assert_eq!(formula.get_clause_at_idx(2).lock_count, 0);
        assert_eq!(history.get_decision_level(), 0);
    }

    #[test]
    fn probes_and_analysis_do_not_pollute_ges_or_literal_utility() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3], vec![1, -2]]);
        formula.get_clause_at_idx_mut(1).ges_generated = true;
        formula.configure_ges_trail_tracking(true);
        execute(&mut formula);
        assert_eq!(formula.stats.vivification_clauses_strengthened, 1);
        assert_eq!(formula.stats.ges_replacement_reason_uses, 0);
        assert_eq!(formula.stats.ges_replacement_analysis_uses, 0);
        assert_eq!(formula.stats.ges_trail_unique_touches, 0);
        assert!(formula.ges_trail_touched.is_empty());
        assert!(!formula.get_clause_at_idx(1).ges_used);
        for variable in 1..=3 {
            for sign in [-1, 1] {
                assert_eq!(
                    formula
                        .extensions
                        .literal_utility(&Literal::new(variable * sign)),
                    0.0
                );
            }
        }
    }

    #[test]
    fn analysis_is_targeted_and_rejects_reasonless_root_facts() {
        let mut clauses = vec![vec![1], vec![2, 3, 4]];
        clauses.extend((5..=100).map(|variable| vec![variable]));
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();
        assert!(!formula.rebuild_root_implications(&mut history));
        let mut scratch = Scratch::default();
        scratch.resolvent.push(Literal::new(-1));
        let mut ticks = 0;
        resolve(
            &formula,
            &history,
            &mut scratch,
            Some(Literal::new(1)),
            &mut ticks,
            3,
        )
        .unwrap();
        assert_eq!(ticks, 2);
        assert_eq!(scratch.result, vec![Literal::new(1)]);

        formula.assign_implication(Literal::new(2), &mut history, None);
        scratch.resolvent.push(Literal::new(-2));
        assert!(resolve(&formula, &history, &mut scratch, None, &mut ticks, 10).is_err());
    }

    // Independent scan-based propagation deliberately does not use watchlists.
    fn rup(database: &[Vec<i32>], addition: &[i32]) -> bool {
        let mut values = [None; 5];
        for &lit in addition {
            let slot = &mut values[lit.unsigned_abs() as usize];
            let value = lit < 0;
            if slot.is_some_and(|old| old != value) {
                return true;
            }
            *slot = Some(value);
        }
        loop {
            let mut changed = false;
            for clause in database {
                if clause
                    .iter()
                    .any(|&lit| values[lit.unsigned_abs() as usize] == Some(lit > 0))
                {
                    continue;
                }
                let mut unassigned = clause
                    .iter()
                    .copied()
                    .filter(|lit| values[lit.unsigned_abs() as usize].is_none());
                let Some(unit) = unassigned.next() else {
                    return true;
                };
                if unassigned.next().is_none() {
                    values[unit.unsigned_abs() as usize] = Some(unit > 0);
                    changed = true;
                }
            }
            if !changed {
                return false;
            }
        }
    }

    #[test]
    fn exhaustive_small_models_and_logged_additions_are_preserved() {
        let binaries: Vec<Vec<i32>> = (1..=4)
            .flat_map(|a| {
                ((a + 1)..=4)
                    .flat_map(move |b| [vec![a, b], vec![a, -b], vec![-a, b], vec![-a, -b]])
            })
            .collect();
        for first in &binaries {
            for second in &binaries {
                let original = vec![vec![1, 2, 3], first.clone(), second.clone()];
                let mut formula = Formula::from_vec(original.clone());
                let mut proof = Vec::new();
                {
                    let mut logger = Some(DratLogger::new(&mut proof));
                    let scope = ClauseScope::range(0..formula.clause_slots_len());
                    process(&mut formula, &scope, &mut logger, None, None).unwrap();
                }
                for model in 0..16 {
                    let satisfies = |clause: &[i32]| {
                        clause.iter().any(|lit| {
                            let value = model & (1 << (lit.unsigned_abs() - 1)) != 0;
                            value == (*lit > 0)
                        })
                    };
                    let before = original.iter().all(|c| satisfies(c));
                    let after = formula.get_clauses().all(|(_, c)| {
                        satisfies(&c.iter().map(|lit| lit.get_index()).collect::<Vec<_>>())
                    });
                    assert_eq!(before, after, "model {model}, formula {original:?}");
                }
                let mut database = original;
                for line in std::str::from_utf8(&proof).unwrap().lines() {
                    let deletion = line.starts_with("d ");
                    let text = line.strip_prefix("d ").unwrap_or(line);
                    let clause: Vec<i32> = text
                        .split_whitespace()
                        .map(|word| word.parse().unwrap())
                        .take_while(|lit| *lit != 0)
                        .collect();
                    if deletion {
                        let position = database
                            .iter()
                            .position(|old| {
                                old.len() == clause.len()
                                    && old.iter().all(|lit| clause.contains(lit))
                            })
                            .expect("deleted clause exists");
                        database.remove(position);
                    } else {
                        assert!(rup(&database, &clause), "non-RUP addition {clause:?}");
                        database.push(clause);
                    }
                }
            }
        }
    }

    #[test]
    fn nonroot_history_is_rejected_without_mutation() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        let mut history = History::new();
        formula.add_decision(&Literal::new(1), &mut history);
        assert!(
            process::<Empty>(
                &mut formula,
                &ClauseScope::range(0..1),
                &mut None,
                None,
                Some(&mut history)
            )
            .is_err()
        );
        assert_eq!(history.get_decision_level(), 1);
    }
}
