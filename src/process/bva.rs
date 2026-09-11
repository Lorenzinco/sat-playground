use crate::circuits::and_gate::AndGate;
use crate::circuits::factorization::{
    BvaBudget, FactorSearch, Factorization, factor_eligible_clause, literal_tie_key,
    live_factor_clause,
};
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::process::ClauseScope;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::BTreeMap;
use std::io::Write;

const MAX_BVA_CLAUSE_VISITS_PER_PASS: usize = 50_000;

/// Runs a deterministic BVA pass over signed literals, ranked by descending
/// eligible occurrence count and then by stable literal order.
pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {
    process_with_budget(
        formula,
        scope,
        logger,
        signal,
        MAX_BVA_CLAUSE_VISITS_PER_PASS,
    )
}

fn process_with_budget<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    clause_visit_limit: usize,
) -> PyResult<()> {
    if let Some((py, steps)) = signal {
        signal_checker(py, steps)?;
    }

    let initial_clause_limit = formula.clause_slots_len();
    let mut pending_deleted = (0..initial_clause_limit)
        .map(|clause_idx| {
            formula.is_clause_garbage(clause_idx)
                || !scope.includes(
                    clause_idx,
                    formula.get_clause_and_garbage_at_idx(clause_idx),
                )
        })
        .collect::<Vec<_>>();
    let mut deletion_indices = Vec::new();
    let mut budget = BvaBudget::new(clause_visit_limit);
    let candidates = match deterministic_candidates(formula, &pending_deleted, &mut budget) {
        FactorSearch::Found(candidates) => candidates,
        FactorSearch::NotFound => {
            formula.stats.bva_clause_visits += budget.visits() as u64;
            return Ok(());
        }
        FactorSearch::BudgetExhausted => {
            formula.stats.bva_clause_visits += budget.visits() as u64;
            formula.stats.bva_budget_exhaustions += 1;
            return Ok(());
        }
    };
    let mut exhausted = false;

    for start in candidates {
        match candidate_is_live(formula, start, &pending_deleted, &mut budget) {
            FactorSearch::Found(()) => {}
            FactorSearch::NotFound => continue,
            FactorSearch::BudgetExhausted => {
                exhausted = true;
                break;
            }
        }

        formula.stats.bva_candidates_attempted += 1;
        match factorize_literal(
            formula,
            logger,
            start,
            &mut pending_deleted,
            &mut deletion_indices,
            &mut budget,
        ) {
            FactorSearch::Found((clause_saving, source_clause_count)) => {
                formula.stats.bva_clauses_saved += clause_saving as u64;
                formula.stats.bva_source_clauses_replaced += source_clause_count as u64;
            }
            FactorSearch::NotFound => {}
            FactorSearch::BudgetExhausted => {
                exhausted = true;
                break;
            }
        }
    }

    formula.stats.bva_clause_visits += budget.visits() as u64;
    if exhausted {
        formula.stats.bva_budget_exhaustions += 1;
    }
    finalize_deletions(formula, logger, &mut deletion_indices);
    Ok(())
}

fn deterministic_candidates(
    formula: &Formula,
    pending_deleted: &[bool],
    budget: &mut BvaBudget,
) -> FactorSearch<Vec<i32>> {
    let mut occurrence_counts = BTreeMap::<i32, usize>::new();
    for (clause_idx, clause) in formula.get_clauses() {
        if !budget.visit_clause() {
            return FactorSearch::BudgetExhausted;
        }
        if pending_deleted[clause_idx] || !factor_eligible_clause(clause) {
            continue;
        }
        for literal in clause.iter() {
            *occurrence_counts.entry(literal.get_index()).or_default() += 1;
        }
    }

    let mut candidates = occurrence_counts.into_iter().collect::<Vec<_>>();
    candidates.sort_unstable_by(|(left_literal, left_count), (right_literal, right_count)| {
        right_count
            .cmp(left_count)
            .then_with(|| literal_tie_key(*left_literal).cmp(&literal_tie_key(*right_literal)))
    });
    let candidates = candidates
        .into_iter()
        .map(|(literal, _)| literal)
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        FactorSearch::NotFound
    } else {
        FactorSearch::Found(candidates)
    }
}

fn candidate_is_live(
    formula: &Formula,
    start: i32,
    pending_deleted: &[bool],
    budget: &mut BvaBudget,
) -> FactorSearch<()> {
    for clause_idx in formula.occurrence_of(&Literal::new(start)) {
        if !budget.visit_clause() {
            return FactorSearch::BudgetExhausted;
        }
        if live_factor_clause(formula, clause_idx, pending_deleted) {
            return FactorSearch::Found(());
        }
    }
    FactorSearch::NotFound
}

fn factorize_literal<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    start: i32,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
    budget: &mut BvaBudget,
) -> FactorSearch<(isize, usize)> {
    let and_gate = match AndGate::find(formula, start, pending_deleted, budget) {
        FactorSearch::Found(gate) => Some(gate),
        FactorSearch::NotFound => None,
        FactorSearch::BudgetExhausted => return FactorSearch::BudgetExhausted,
    };
    let variable = start.unsigned_abs() as usize;
    let gate = if formula.assignment.get_value(variable).is_none() {
        match Gate::find(formula, pending_deleted, start, budget) {
            FactorSearch::Found(gate) => Some(gate),
            FactorSearch::NotFound => None,
            FactorSearch::BudgetExhausted => return FactorSearch::BudgetExhausted,
        }
    } else {
        None
    };

    let Some(candidate) = Factorization::select(and_gate, gate) else {
        return FactorSearch::NotFound;
    };
    let clause_saving = candidate.clause_saving();
    let source_clause_count = candidate.source_clause_count();
    candidate.apply(formula, logger, pending_deleted, deletion_indices);
    FactorSearch::Found((clause_saving, source_clause_count))
}

fn finalize_deletions<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    deletion_indices: &mut Vec<usize>,
) {
    deletion_indices.sort_unstable();
    deletion_indices.dedup();

    for &clause_idx in deletion_indices.iter() {
        formula.record_clause_removal(clause_idx);
    }

    let deleted = formula.delete_clauses(deletion_indices, logger);
    debug_assert_eq!(deleted, deletion_indices.len());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::extension::ExtensionDefinition;

    fn factorize_once<W: Write>(
        formula: &mut Formula,
        scope: &ClauseScope,
        logger: &mut Option<DratLogger<W>>,
        start: i32,
    ) -> bool {
        let initial_clause_limit = formula.clause_slots_len();
        let mut pending_deleted = (0..initial_clause_limit)
            .map(|clause_idx| {
                formula.is_clause_garbage(clause_idx)
                    || !scope.includes(
                        clause_idx,
                        formula.get_clause_and_garbage_at_idx(clause_idx),
                    )
            })
            .collect::<Vec<_>>();
        let mut deletion_indices = Vec::new();
        let mut budget = BvaBudget::new(usize::MAX);
        let found = matches!(
            factorize_literal(
                formula,
                logger,
                start,
                &mut pending_deleted,
                &mut deletion_indices,
                &mut budget,
            ),
            FactorSearch::Found(_)
        );
        finalize_deletions(formula, logger, &mut deletion_indices);
        found
    }

    #[test]
    fn empty_formula_is_a_noop() {
        let mut formula = Formula::new(0);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;

        let scope = ClauseScope::range(0..formula.clause_slots_len());
        process(&mut formula, &scope, &mut logger, None, None).unwrap();

        assert_eq!(formula.stats.bva_literals, 0);
        assert!(formula.extensions.is_empty());
    }

    #[test]
    fn selected_and_grid_is_applied_and_finalized() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
        ]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(factorize_once(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.live_clause_count(), 6);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(
            formula.extensions.definition(&Literal::new(7)),
            Some(&ExtensionDefinition::And(vec![
                Literal::new(1),
                Literal::new(2),
            ]))
        );
        for source_index in 0..8 {
            assert!(formula.is_clause_garbage(source_index));
        }
    }

    #[test]
    fn selected_ite_gate_is_applied_and_registered() {
        let mut formula = Formula::from_vec(vec![
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
        ]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(factorize_once(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.live_clause_count(), 9);
        assert_eq!(formula.stats.clauses_deleted, 10);
        assert_eq!(
            formula.extensions.definition(&Literal::new(15)),
            Some(&ExtensionDefinition::Ite {
                condition: Literal::new(1),
                when_true: Literal::new(-3),
                when_false: Literal::new(-2),
            })
        );
    }

    #[test]
    fn unprofitable_seed_does_not_change_the_formula() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 3]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let initial_slots = formula.clause_slots_len();
        let initial_variables = formula.assignment.len();
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(!factorize_once(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.clause_slots_len(), initial_slots);
        assert_eq!(formula.assignment.len(), initial_variables);
        assert!(formula.extensions.is_empty());
    }

    #[test]
    fn candidates_use_occurrence_count_then_stable_literal_order() {
        let formula = Formula::from_vec(vec![
            vec![1, 2],
            vec![1, 3],
            vec![1, -4],
            vec![-1, 2],
            vec![-2, 3],
        ]);
        let pending_deleted = vec![false; formula.clause_slots_len()];
        let mut budget = BvaBudget::new(100);

        let candidates = match deterministic_candidates(&formula, &pending_deleted, &mut budget) {
            FactorSearch::Found(candidates) => candidates,
            FactorSearch::NotFound => panic!("expected candidates"),
            FactorSearch::BudgetExhausted => panic!("unexpected budget exhaustion"),
        };

        assert_eq!(candidates, vec![1, 2, 3, -1, -2, -4]);
        assert_eq!(budget.visits(), 5);
    }

    #[test]
    fn deterministic_pass_applies_multiple_disjoint_factorizations() {
        let clauses = vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
            vec![10, 12],
            vec![10, 13],
            vec![10, 14],
            vec![10, 15],
            vec![11, 12],
            vec![11, 13],
            vec![11, 14],
            vec![11, 15],
        ];
        let mut first = Formula::from_vec(clauses.clone());
        let mut second = Formula::from_vec(clauses);
        let first_scope = ClauseScope::range(0..first.clause_slots_len());
        let second_scope = ClauseScope::range(0..second.clause_slots_len());
        let mut first_proof = Vec::new();
        let mut second_proof = Vec::new();
        let mut first_logger = Some(DratLogger::new(&mut first_proof));
        let mut second_logger = Some(DratLogger::new(&mut second_proof));

        process(&mut first, &first_scope, &mut first_logger, None, None).unwrap();
        process(&mut second, &second_scope, &mut second_logger, None, None).unwrap();
        drop(first_logger);
        drop(second_logger);

        assert_eq!(first.stats.bva_literals, 2);
        assert_eq!(first.stats.bva_clauses_saved, 4);
        assert_eq!(first.stats.bva_source_clauses_replaced, 16);
        assert_eq!(first.live_clause_count(), 12);
        let first_clauses = first
            .get_clauses()
            .map(|(_, clause)| clause.sorted_literal_indices())
            .collect::<Vec<_>>();
        let second_clauses = second
            .get_clauses()
            .map(|(_, clause)| clause.sorted_literal_indices())
            .collect::<Vec<_>>();
        assert_eq!(first_clauses, second_clauses);
        assert_eq!(first_proof, second_proof);
        assert_eq!(
            first.stats.bva_clause_visits,
            second.stats.bva_clause_visits
        );
        assert_eq!(
            first.stats.bva_candidates_attempted,
            second.stats.bva_candidates_attempted
        );
    }

    #[test]
    fn completed_factorization_survives_later_budget_exhaustion() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
            vec![10, 12],
            vec![10, 13],
            vec![10, 14],
            vec![10, 15],
            vec![11, 12],
            vec![11, 13],
            vec![11, 14],
            vec![11, 15],
        ]);
        let scope = ClauseScope::range(0..formula.clause_slots_len());
        let mut logger: Option<DratLogger<std::io::Empty>> = None;

        process_with_budget(&mut formula, &scope, &mut logger, None, 45).unwrap();

        assert_eq!(formula.stats.bva_clause_visits, 45);
        assert_eq!(formula.stats.bva_budget_exhaustions, 1);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(formula.live_clause_count(), 14);
    }

    #[test]
    fn exhausted_candidate_is_not_applied() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
        ]);
        let initial_live_clauses = formula.live_clause_count();
        let scope = ClauseScope::range(0..formula.clause_slots_len());
        let mut logger: Option<DratLogger<std::io::Empty>> = None;

        process_with_budget(&mut formula, &scope, &mut logger, None, 1).unwrap();

        assert_eq!(formula.stats.bva_clause_visits, 1);
        assert_eq!(formula.stats.bva_budget_exhaustions, 1);
        assert_eq!(formula.stats.bva_literals, 0);
        assert_eq!(formula.live_clause_count(), initial_live_clauses);
        assert!(formula.extensions.is_empty());
    }
}
