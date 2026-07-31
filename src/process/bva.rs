use crate::circuits::and_gate::AndGate;
use crate::circuits::factorization::{
    BudgetResult, Factorization, continue_search, factor_eligible_clause, literal_tie_key,
};
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::literal::Literal;
use crate::formula::Formula;
use crate::history::History;
use crate::process::ProcessBudget;
use pyo3::prelude::PyResult;
use pyo3::Python;
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Global rotating cursor over physical clause slots.
///
/// The solver is single-threaded, so relaxed ordering is sufficient. An atomic
/// is used only to provide safe global interior mutability without `static mut`.
static BVA_CURSOR: AtomicUsize = AtomicUsize::new(0);

/// Fraction of the formula's physical clause slots inspected by each BVA pass.
///
/// A value of `1.0` reproduces a full-formula pass. A value of `0.10` inspects
/// approximately ten percent of the physical clause slots per invocation.
const BVA_SCAN_FRACTION: f32 = 0.1;

/// Eligible clauses contained in one cyclic raw clause-slot window.
///
/// `indices` is used to enumerate the selected clauses while `included` gives
/// O(1) membership checks when scanning occurrence lists.
#[derive(Debug)]
pub(crate) struct ClauseWindow {
    indices: Vec<usize>,
    included: Vec<bool>,
}

impl ClauseWindow {
    fn select(
        formula: &Formula,
        initial_clause_limit: usize,
        scan_fraction: f32,
    ) -> Self {
        if initial_clause_limit == 0 {
            return Self {
                indices: Vec::new(),
                included: Vec::new(),
            };
        }

        let scan_fraction = scan_fraction.clamp(0.0, 1.0);
        if scan_fraction == 0.0 {
            return Self {
                indices: Vec::new(),
                included: vec![false; initial_clause_limit],
            };
        }

        let scan_len = ((initial_clause_limit as f32 * scan_fraction).ceil() as usize)
            .clamp(1, initial_clause_limit);

        let raw_cursor = BVA_CURSOR.fetch_add(scan_len, Ordering::Relaxed);
        let start = raw_cursor % initial_clause_limit;

        let mut indices = Vec::with_capacity(scan_len);
        let mut included = vec![false; initial_clause_limit];

        // First choose the cyclic raw physical window. Only clauses inside that
        // selected window are then filtered for garbage and BVA eligibility.
        for offset in 0..scan_len {
            let idx = (start + offset) % initial_clause_limit;

            if formula.is_clause_garbage(idx)
                || !factor_eligible_clause(formula.get_clause_at_idx(idx))
            {
                continue;
            }

            indices.push(idx);
            included[idx] = true;
        }

        Self { indices, included }
    }

    #[inline]
    pub(crate) fn contains(&self, idx: usize) -> bool {
        self.included.get(idx).copied().unwrap_or(false)
    }

    #[inline]
    fn indices(&self) -> &[usize] {
        &self.indices
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.indices.is_empty()
    }

    #[cfg(test)]
    pub(crate) fn all_eligible(
        formula: &Formula,
        initial_clause_limit: usize,
    ) -> Self {
        let mut indices = Vec::new();
        let mut included = vec![false; initial_clause_limit];
    
        for idx in 0..initial_clause_limit {
            if formula.is_clause_garbage(idx)
                || !factor_eligible_clause(formula.get_clause_at_idx(idx))
            {
                continue;
            }
    
            indices.push(idx);
            included[idx] = true;
        }
    
        Self { indices, included }
    }
}

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    budget: &ProcessBudget,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {

    let initial_clause_limit = formula.clause_slots_len();
    let initial_variable_limit = formula.assignment.len();

    let window = ClauseWindow::select(
        formula,
        initial_clause_limit,
        BVA_SCAN_FRACTION,
    );

    if window.is_empty() {
        return Ok(());
    }

    let mut pending_deleted = (0..initial_clause_limit)
        .map(|idx| formula.is_clause_garbage(idx))
        .collect::<Vec<_>>();

    let schedule = match initial_literal_schedule(
        formula,
        &window,
    )? {
        BudgetResult::Complete(schedule) => schedule,
        BudgetResult::Exhausted => return Ok(()),
    };

    let mut deletion_indices = Vec::new();
    let mut gate_variables_seen = vec![false; initial_variable_limit];

    let run_result = (|| -> PyResult<()> {
        for start in schedule {
            if !continue_search(budget, &mut signal)? {
                break;
            }

            let and_gate = match AndGate::find(
                formula,
                &window,
                start,
                &pending_deleted
            )? {
                BudgetResult::Complete(candidate) => candidate,
                BudgetResult::Exhausted => break,
            };

            let variable = start.unsigned_abs() as usize;
            let gate = if !gate_variables_seen[variable] {
                gate_variables_seen[variable] = true;

                let has_opposite = match has_live_eligible_occurrence(
                    formula,
                    -start,
                    &window,
                    &pending_deleted,
                )? {
                    BudgetResult::Complete(has_opposite) => has_opposite,
                    BudgetResult::Exhausted => break,
                };

                if formula.assignment.get_value(variable).is_none() && has_opposite {
                    match Gate::find(
                        formula,
                        &window,
                        &pending_deleted,
                        start
                    )? {
                        BudgetResult::Complete(candidate) => candidate,
                        BudgetResult::Exhausted => break,
                    }
                } else {
                    None
                }
            } else {
                None
            };

            let candidate = Factorization::select(and_gate, gate);

            // Applying a selected factorization is atomic: definitions,
            // quotients, and source claims must not be interrupted midway.

            if let Some(candidate) = candidate {
                candidate.apply(
                    formula,
                    logger,
                    &mut pending_deleted,
                    &mut deletion_indices,
                );
            }
        }

        Ok(())
    })();

    // Keep source indices stable throughout the pass. Finalization only marks
    // source clauses; Formula::reduce_db owns deferred compaction and remapping.
    finalize_pending_deletions(
        formula,
        logger,
        &pending_deleted,
        &mut deletion_indices,
    );

    run_result
}

/// Creates a literal schedule only from clauses in the selected eligible window.
///
/// The function does not scan every variable in the formula. It first gathers
/// literals from the selected candidate clauses, then counts only occurrences
/// that also belong to the same candidate window.
fn initial_literal_schedule(
    formula: &mut Formula,
    window: &ClauseWindow,
) -> PyResult<BudgetResult<Vec<i32>>> {
    let mut literals = Vec::new();

    for &idx in window.indices() {

        literals.extend(
            formula
                .get_clause_at_idx(idx)
                .iter()
                .map(Literal::get_index),
        );
    }

    literals.sort_unstable();
    literals.dedup();

    let mut schedule = Vec::with_capacity(literals.len());

    for literal_idx in literals {

        let literal = Literal::new(literal_idx);

        // Clean only occurrence lists touched by this selected window.
        formula.clean_occurrence(&literal);

        let count = formula
            .live_occurrences(&literal)
            .filter(|&idx| window.contains(idx))
            .count();

        if count > 1 {
            schedule.push((literal_idx, count));
        }
    }

    schedule.sort_unstable_by(
        |&(literal_a, count_a), &(literal_b, count_b)| {
            count_a
                .cmp(&count_b)
                .then_with(|| {
                    literal_tie_key(literal_a)
                        .cmp(&literal_tie_key(literal_b))
                })
        },
    );

    Ok(BudgetResult::Complete(
        schedule
            .into_iter()
            .map(|(literal, _)| literal)
            .collect(),
    ))
}

#[inline]
pub(crate) fn live_window_factor_clause(
    formula: &Formula,
    idx: usize,
    window: &ClauseWindow,
    pending_deleted: &[bool],
) -> bool {
    window.contains(idx)
        && !pending_deleted[idx]
        && !formula.is_clause_garbage(idx)
}

fn has_live_eligible_occurrence(
    formula: &Formula,
    literal: i32,
    window: &ClauseWindow,
    pending_deleted: &[bool],
) -> PyResult<BudgetResult<bool>> {
    for idx in formula.live_occurrences(&Literal::new(literal)) {

        if live_window_factor_clause(
            formula,
            idx,
            window,
            pending_deleted,
        ) {
            return Ok(BudgetResult::Complete(true));
        }
    }

    Ok(BudgetResult::Complete(false))
}

fn finalize_pending_deletions<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    pending_deleted: &[bool],
    deletion_indices: &mut Vec<usize>,
) {
    if deletion_indices.is_empty() {
        return;
    }

    deletion_indices.sort_unstable();
    deletion_indices.dedup();

    debug_assert_eq!(
        pending_deleted
            .iter()
            .enumerate()
            .filter(|(idx, pending)| **pending && !formula.is_clause_garbage(*idx))
            .count(),
        deletion_indices.len()
    );

    for &idx in deletion_indices.iter() {
        debug_assert!(pending_deleted[idx]);
        debug_assert!(!formula.is_clause_garbage(idx));
        formula.record_clause_removal(idx);
    }

    let newly_deleted = formula.delete_clauses(deletion_indices, logger);
    debug_assert_eq!(newly_deleted, deletion_indices.len());
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_BUDGET: f32 = 60.0;

    fn reset_bva_cursor() {
        BVA_CURSOR.store(0, Ordering::Relaxed);
    }

    fn process_with_budget<W: Write>(
        formula: &mut Formula,
        budget_seconds: f32,
        logger: &mut Option<DratLogger<W>>,
        signal: Option<(Python<'_>, &mut u64)>,
        history: Option<&mut History>,
    ) -> PyResult<()> {
        let budget = ProcessBudget::new(budget_seconds);
        process(formula, &budget, logger, signal, history)
    }

    /// Repeatedly invokes BVA until one complete physical rotation has been
    /// requested. This keeps behavioral tests independent of scan fraction.
    fn process_full_rotation<W: Write>(
        formula: &mut Formula,
        logger: &mut Option<DratLogger<W>>,
        history: Option<&mut History>,
    ) -> PyResult<()> {
        reset_bva_cursor();

        if formula.clause_slots_len() == 0 {
            return Ok(());
        }

        let passes = (1.0 / BVA_SCAN_FRACTION).ceil() as usize;

        match history {
            Some(history) => {
                for pass in 0..passes {
                    let history = if pass == 0 {
                        Some(&mut *history)
                    } else {
                        None
                    };

                    process_with_budget(
                        formula,
                        TEST_BUDGET,
                        logger,
                        None,
                        history,
                    )?;
                }
            }
            None => {
                for _ in 0..passes {
                    process_with_budget(
                        formula,
                        TEST_BUDGET,
                        logger,
                        None,
                        None,
                    )?;
                }
            }
        }

        Ok(())
    }

    fn sorted_clauses(formula: &Formula) -> Vec<Vec<i32>> {
        let mut clauses = formula
            .get_clauses()
            .map(|(_, clause)| clause.sorted_literal_indices())
            .collect::<Vec<_>>();
        clauses.sort();
        clauses
    }

    fn ite_formula() -> Formula {
        Formula::from_vec(vec![
            vec![1, 2, 10],
            vec![-1, 3, 10],
            vec![1, 2, 11],
            vec![-1, 3, 11],
            vec![1, 2, 12],
            vec![-1, 3, 12],
            vec![1, -2, 13],
            vec![-1, -3, 13],
            vec![1, -2, 14],
            vec![-1, -3, 14],
        ])
    }

    #[test]
    fn clause_window_selects_then_filters_raw_slots() {
        reset_bva_cursor();

        let mut formula = Formula::from_vec(vec![
            vec![99],
            vec![1, 10],
            vec![1, 11],
            vec![1, 12],
        ]);
        let mut logger = None;

        assert_eq!(
            formula.delete_clauses::<std::io::Empty>(&[0], &mut logger),
            1
        );

        let window = ClauseWindow::select(&formula, 4, 0.50);

        assert!(!window.contains(0));
        assert!(window.contains(1));
        assert_eq!(window.indices(), &[1]);
    }

    #[test]
    fn clause_window_rotates_cyclically() {
        reset_bva_cursor();

        let formula = Formula::from_vec(vec![
            vec![1, 10],
            vec![1, 11],
            vec![1, 12],
            vec![1, 13],
        ]);

        let first = ClauseWindow::select(&formula, 4, 0.50);
        let second = ClauseWindow::select(&formula, 4, 0.50);

        assert_eq!(first.indices(), &[0, 1]);
        assert_eq!(second.indices(), &[2, 3]);
    }

    #[test]
    fn bva_selects_and_applies_a_gate_factorization() {
        let mut clauses = ite_formula()
            .get_clauses()
            .map(|(_, clause)| {
                clause
                    .iter()
                    .map(Literal::get_index)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        for remainder in 10..=14 {
            for _ in 0..4 {
                clauses.push(vec![remainder, 4, -4]);
            }
        }

        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;

        process_full_rotation::<std::io::Empty>(
            &mut formula,
            &mut logger,
            None,
        )
        .unwrap();

        assert!(formula.stats.bva_literals >= 1);
        assert!(formula.stats.clauses_deleted >= 10);
        assert!(
            formula
                .get_clauses()
                .any(|(_, clause)| {
                    clause.lbd() == 0 && clause.is_bva_generated()
                })
        );
    }

    #[test]
    fn existing_garbage_does_not_shrink_physical_window_limit() {
        reset_bva_cursor();

        let mut clauses = vec![vec![99]];
        clauses.extend(
            [1, 2]
                .into_iter()
                .flat_map(|literal| {
                    (10..=13).map(move |partial| vec![literal, partial])
                }),
        );

        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;

        assert_eq!(
            formula.delete_clauses::<std::io::Empty>(&[0], &mut logger),
            1
        );

        let window = ClauseWindow::select(
            &formula,
            formula.clause_slots_len(),
            1.0,
        );

        assert!(!window.contains(0));
        assert_eq!(window.indices().len(), 8);
    }

    #[test]
    fn buffered_finalization_preserves_a_surviving_physical_history_reason() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
            vec![8],
        ]);

        let reason_literal = Literal::new(8);
        let mut history = History::new();
        formula.assign_implication(
            reason_literal.clone(),
            &mut history,
            Some(8),
        );

        let mut logger = None;

        process_full_rotation::<std::io::Empty>(
            &mut formula,
            &mut logger,
            Some(&mut history),
        )
        .unwrap();

        assert_eq!(
            history.decision_levels[0].get_reason(&reason_literal),
            Some(8)
        );
        assert_eq!(formula.get_clause_at_idx(8).lock_count(), 1);
        assert_eq!(
            formula.get_clause_at_idx(8).get_literals(),
            &vec![reason_literal]
        );
    }

    #[test]
    fn finalization_exposes_consistent_live_occurrence_lists() {
        let mut formula = ite_formula();
        let mut logger = None;

        process_full_rotation::<std::io::Empty>(
            &mut formula,
            &mut logger,
            None,
        )
        .unwrap();

        for variable in 1..formula.assignment.len() {
            for literal in [variable as i32, -(variable as i32)] {
                let expected = formula
                    .get_clauses()
                    .filter_map(|(idx, clause)| {
                        clause
                            .iter()
                            .any(|candidate| {
                                candidate.get_index() == literal
                            })
                            .then_some(idx)
                    })
                    .collect::<Vec<_>>();

                assert_eq!(
                    formula
                        .live_occurrences(&Literal::new(literal))
                        .collect::<Vec<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn zero_budget_skips_profitable_factorizations() {
        reset_bva_cursor();

        let clauses = [1, 2]
            .into_iter()
            .flat_map(|literal| {
                (10..=13).map(move |partial| vec![literal, partial])
            })
            .collect::<Vec<_>>();

        let mut formula = Formula::from_vec(clauses);
        let original = sorted_clauses(&formula);
        let original_variables = formula.assignment.len();
        let mut logger = None;

        process_with_budget::<std::io::Empty>(
            &mut formula,
            0.0,
            &mut logger,
            None,
            None,
        )
        .unwrap();

        assert_eq!(formula.assignment.len(), original_variables);
        assert_eq!(sorted_clauses(&formula), original);
        assert_eq!(formula.stats.bva_literals, 0);
    }
}
