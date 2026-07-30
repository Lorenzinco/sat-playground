use crate::circuits::and_gate::AndGate;
use crate::circuits::factorization::{
    BudgetResult, Factorization, continue_search, factor_eligible_clause, literal_tie_key,
    live_factor_clause,
};
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::process::ProcessBudget;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::io::Write;

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    budget: &ProcessBudget,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {
    if budget.exhausted() {
        return Ok(());
    }

    let initial_clause_limit = formula.clause_slots_len();
    let initial_variable_limit = formula.assignment.len();
    let schedule = match initial_literal_schedule(
        formula,
        initial_clause_limit,
        initial_variable_limit,
        budget,
        &mut signal,
    )? {
        BudgetResult::Complete(schedule) => schedule,
        BudgetResult::Exhausted => return Ok(()),
    };
    if budget.exhausted() {
        return Ok(());
    }

    let mut pending_deleted = (0..initial_clause_limit)
        .map(|idx| formula.is_clause_garbage(idx))
        .collect::<Vec<_>>();
    let mut deletion_indices = Vec::new();
    let mut gate_variables_seen = vec![false; initial_variable_limit];

    let run_result = (|| -> PyResult<()> {
        for start in schedule {
            if !continue_search(budget, &mut signal)? {
                break;
            }

            let and_gate = match AndGate::find(
                formula,
                initial_clause_limit,
                start,
                &pending_deleted,
                budget,
                &mut signal,
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
                    initial_clause_limit,
                    &pending_deleted,
                    budget,
                    &mut signal,
                )? {
                    BudgetResult::Complete(has_opposite) => has_opposite,
                    BudgetResult::Exhausted => break,
                };
                if formula.assignment.get_value(variable).is_none() && has_opposite {
                    match Gate::find(
                        formula,
                        initial_clause_limit,
                        &pending_deleted,
                        start,
                        budget,
                        &mut signal,
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

            // A selected factorization is applied atomically. Definitions,
            // quotients, and source claims must not be interrupted midway.
            if !continue_search(budget, &mut signal)? {
                break;
            }
            if let Some(candidate) = candidate {
                candidate.apply(formula, logger, &mut pending_deleted, &mut deletion_indices);
            }
        }
        Ok(())
    })();

    // Keep source indices stable throughout the pass. Finalization only marks
    // source clauses; Formula::reduce_db owns deferred compaction and remapping.
    finalize_pending_deletions(formula, logger, &pending_deleted, &mut deletion_indices);
    run_result
}

fn initial_literal_schedule(
    formula: &mut Formula,
    initial_clause_limit: usize,
    initial_variable_limit: usize,
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<Vec<i32>>> {
    if !continue_search(budget, signal)? {
        return Ok(BudgetResult::Exhausted);
    }

    let mut schedule = Vec::new();
    for variable in 1..initial_variable_limit {
        for literal in [variable as i32, -(variable as i32)] {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            let literal = Literal::new(literal);
            formula.clean_occurrence(&literal);
            let mut count = 0;
            for idx in formula.live_occurrences(&literal) {
                if !continue_search(budget, signal)? {
                    return Ok(BudgetResult::Exhausted);
                }
                if idx < initial_clause_limit
                    && factor_eligible_clause(formula.get_clause_at_idx(idx))
                {
                    count += 1;
                }
            }
            if count > 1 {
                schedule.push((literal.get_index(), count));
            }
        }
    }

    if !continue_search(budget, signal)? {
        return Ok(BudgetResult::Exhausted);
    }
    schedule.sort_by(|(lit_a, count_a), (lit_b, count_b)| {
        count_a
            .cmp(count_b)
            .then_with(|| literal_tie_key(*lit_a).cmp(&literal_tie_key(*lit_b)))
    });
    Ok(BudgetResult::Complete(
        schedule.into_iter().map(|(literal, _)| literal).collect(),
    ))
}

fn has_live_eligible_occurrence(
    formula: &Formula,
    literal: i32,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<bool>> {
    for idx in formula.live_occurrences(&Literal::new(literal)) {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        if live_factor_clause(formula, idx, initial_clause_limit, pending_deleted) {
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
    fn bva_selects_and_applies_a_gate_factorization() {
        let mut clauses = ite_formula()
            .get_clauses()
            .map(|(_, clause)| clause.iter().map(Literal::get_index).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for remainder in 10..=14 {
            for _ in 0..4 {
                clauses.push(vec![remainder, 4, -4]);
            }
        }
        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 10);
        assert!(
            formula
                .get_clauses()
                .any(|(_, clause)| clause.lbd() == 0 && clause.is_bva_generated())
        );
    }

    #[test]
    fn two_independent_factorizations_are_marked_without_compaction() {
        let mut clauses = Vec::new();
        for literal in [1, 2] {
            for partial in 10..=13 {
                clauses.push(vec![literal, partial]);
            }
        }
        for literal in [3, 4] {
            for partial in 20..=23 {
                clauses.push(vec![literal, partial]);
            }
        }
        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

        assert_eq!(formula.stats.bva_literals, 2);
        assert_eq!(formula.stats.clauses_deleted, 16);
        assert_eq!(formula.live_clause_count(), 12);
        assert_eq!(formula.clause_slots_len(), 28);
        assert_eq!(formula.get_clauses_and_garbage().count(), 28);
    }

    #[test]
    fn existing_garbage_does_not_shrink_the_physical_initial_limit() {
        let mut clauses = vec![vec![99]];
        clauses.extend(
            [1, 2]
                .into_iter()
                .flat_map(|literal| (10..=13).map(move |partial| vec![literal, partial])),
        );
        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;
        assert_eq!(
            formula.delete_clauses::<std::io::Empty>(&[0], &mut logger),
            1
        );
        assert_eq!(formula.live_clause_count(), 8);
        assert_eq!(formula.clause_slots_len(), 9);
        assert_eq!(formula.get_clauses_and_garbage().count(), 9);

        process_with_budget(&mut formula, TEST_BUDGET, &mut logger, None, None).unwrap();

        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(formula.live_clause_count(), 6);
        assert_eq!(formula.clause_slots_len(), 15);
        assert_eq!(formula.get_clauses_and_garbage().count(), 15);
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
        formula.assign_implication(reason_literal.clone(), &mut history, Some(8));
        let mut logger = None;

        process_with_budget::<std::io::Empty>(
            &mut formula,
            TEST_BUDGET,
            &mut logger,
            None,
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
        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

        for variable in 1..formula.assignment.len() {
            for literal in [variable as i32, -(variable as i32)] {
                let expected = formula
                    .get_clauses()
                    .filter_map(|(idx, clause)| {
                        clause
                            .iter()
                            .any(|candidate| candidate.get_index() == literal)
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
        let clauses = [1, 2]
            .into_iter()
            .flat_map(|literal| (10..=13).map(move |partial| vec![literal, partial]))
            .collect::<Vec<_>>();
        let mut formula = Formula::from_vec(clauses);
        let original = sorted_clauses(&formula);
        let original_variables = formula.assignment.len();
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, 0.0, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), original_variables);
        assert_eq!(sorted_clauses(&formula), original);
        assert_eq!(formula.stats.bva_literals, 0);
    }
}
