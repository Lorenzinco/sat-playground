use crate::circuits::and_gate::{AndGate, RemainderIndex};
use crate::circuits::factorization::{
    BvaBudget, FactorSearch, Factorization, factor_eligible_clause, literal_tie_key,
    live_factor_clause,
};
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;
#[cfg(test)]
use crate::history::History;
use crate::process::{ClauseScope, ProcessPhase};
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write;

const MIN_PRODUCTIVITY_CANDIDATES: u64 = 8;
const MIN_FACTOR_PERCENT_FOR_GROWTH: u64 = 1;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct BvaPassReport {
    visits: usize,
    candidates: u64,
    factors: u64,
    exhausted: bool,
}

fn phase_visit_limits(phase: ProcessPhase) -> (usize, usize, usize) {
    match phase {
        ProcessPhase::Preprocessing => (1024, 100_000, 10_000_000),
        ProcessPhase::Inprocessing => (64, 10_000, 500_000),
    }
}

fn pass_visit_limit(clause_slots: usize, phase: ProcessPhase) -> usize {
    let (scale, minimum, maximum) = phase_visit_limits(phase);
    clause_slots.saturating_mul(scale).clamp(minimum, maximum)
}

fn adaptive_pass_visit_limit(formula: &mut Formula, phase: ProcessPhase) -> usize {
    let initial = pass_visit_limit(formula.clause_slots_len(), phase);
    let budget = match phase {
        ProcessPhase::Preprocessing => {
            if formula.bva_preprocessing_budget == 0 {
                formula.bva_preprocessing_budget = initial;
            }
            formula.bva_preprocessing_budget
        }
        ProcessPhase::Inprocessing => {
            if formula.bva_inprocessing_budget == 0 {
                formula.bva_inprocessing_budget = initial;
            }
            formula.bva_inprocessing_budget
        }
    };
    formula.stats.bva_current_budget = budget as u64;
    formula.stats.bva_peak_budget = formula.stats.bva_peak_budget.max(budget as u64);
    budget
}

fn update_adaptive_pass_visit_limit(
    formula: &mut Formula,
    phase: ProcessPhase,
    report: BvaPassReport,
) {
    let (_, minimum, maximum) = phase_visit_limits(phase);
    let poor_pass = report.factors == 0
        || (report.candidates >= MIN_PRODUCTIVITY_CANDIDATES
            && report.factors.saturating_mul(1_000) <= report.candidates);
    let productive_pass = report.candidates >= MIN_PRODUCTIVITY_CANDIDATES
        && report.factors.saturating_mul(100)
            >= report
                .candidates
                .saturating_mul(MIN_FACTOR_PERCENT_FOR_GROWTH)
        && report.factors.saturating_mul(100_000) >= report.visits as u64;

    let current = match phase {
        ProcessPhase::Preprocessing => formula.bva_preprocessing_budget,
        ProcessPhase::Inprocessing => formula.bva_inprocessing_budget,
    };
    let next = if poor_pass {
        current.saturating_sub(current.div_ceil(4)).max(minimum)
    } else if report.exhausted && productive_pass {
        current.saturating_add(current.div_ceil(4)).min(maximum)
    } else {
        current
    };
    formula.stats.bva_budget_decreases += u64::from(next < current);
    formula.stats.bva_budget_increases += u64::from(next > current);
    match phase {
        ProcessPhase::Preprocessing => formula.bva_preprocessing_budget = next,
        ProcessPhase::Inprocessing => formula.bva_inprocessing_budget = next,
    }
}

/// Runs a deterministic BVA pass over signed literals, ranked by descending
/// eligible occurrence count and then by stable literal order. Successful
/// factors reschedule their neighborhood, including newly generated clauses,
/// within a size-scaled, hard-capped clause-visit budget.
#[cfg(test)]
fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {
    process_in_phase(formula, scope, logger, signal, ProcessPhase::Preprocessing)
}

pub(crate) fn process_in_phase<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    phase: ProcessPhase,
) -> PyResult<()> {
    let clause_visit_limit = adaptive_pass_visit_limit(formula, phase);
    let report = process_with_budget(formula, scope, logger, signal, clause_visit_limit)?;
    update_adaptive_pass_visit_limit(formula, phase, report);
    Ok(())
}

fn process_with_budget<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    clause_visit_limit: usize,
) -> PyResult<BvaPassReport> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, steps)?;
    }

    let initial_candidates = formula.stats.bva_candidates_attempted;
    let initial_factors = formula.stats.bva_literals;
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
            return Ok(record_bva_pass(
                formula,
                &budget,
                false,
                initial_candidates,
                initial_factors,
            ));
        }
        FactorSearch::BudgetExhausted => {
            return Ok(record_bva_pass(
                formula,
                &budget,
                true,
                initial_candidates,
                initial_factors,
            ));
        }
    };
    let mut index = RemainderIndex::default();
    let mut exhausted = !index.extend(formula, &pending_deleted, &mut budget);

    // Preserve the initial occurrence ranking, then append changed literals in
    // stable order. Membership deduplication prevents repeated full rescans and
    // lets untouched queued candidates run before a successful seed is retried.
    let mut queued = candidates.iter().copied().collect::<BTreeSet<_>>();
    let mut candidates = VecDeque::from(candidates);
    while let Some(start) = candidates.pop_front() {
        if exhausted {
            break;
        }
        queued.remove(&start);
        if let Some((py, steps)) = signal.as_mut() {
            if let Err(error) = signal_checker(*py, steps) {
                record_bva_pass(formula, &budget, false, initial_candidates, initial_factors);
                finalize_deletions(formula, logger, &mut deletion_indices);
                return Err(error);
            }
        }
        match candidate_is_live(formula, start, &pending_deleted, &mut budget) {
            FactorSearch::Found(()) => {}
            FactorSearch::NotFound => continue,
            FactorSearch::BudgetExhausted => {
                exhausted = true;
                break;
            }
        }

        formula.stats.bva_candidates_attempted += 1;
        let first_added = formula.clause_slots_len();
        let first_deleted = deletion_indices.len();
        match factorize_literal(
            formula,
            logger,
            start,
            &mut pending_deleted,
            &mut deletion_indices,
            &mut budget,
            &index,
        ) {
            FactorSearch::Found((clause_saving, source_clause_count)) => {
                formula.stats.bva_clauses_saved += clause_saving as u64;
                formula.stats.bva_source_clauses_replaced += source_clause_count as u64;

                // Apply is atomic with respect to searching: additions and GES
                // registration finish before generated clauses become eligible.
                // Sources stay physically present until final proof deletions.
                pending_deleted.resize(formula.clause_slots_len(), false);
                if !index.extend(formula, &pending_deleted, &mut budget) {
                    exhausted = true;
                    break;
                }
                let mut touched = BTreeSet::new();
                for clause_idx in deletion_indices[first_deleted..]
                    .iter()
                    .copied()
                    .chain(first_added..formula.clause_slots_len())
                {
                    if !budget.visit_clause() {
                        exhausted = true;
                        break;
                    }
                    for literal in formula.get_clause_at_idx(clause_idx).iter() {
                        let index = literal.get_index();
                        // Gate searches depend on both polarities.
                        touched.insert(index);
                        touched.insert(-index);
                    }
                }
                if exhausted {
                    break;
                }
                let mut touched = touched.into_iter().collect::<Vec<_>>();
                touched.sort_unstable_by_key(|&literal| literal_tie_key(literal));
                for literal in touched {
                    if queued.insert(literal) {
                        candidates.push_back(literal);
                    }
                }
            }
            FactorSearch::NotFound => {}
            FactorSearch::BudgetExhausted => {
                exhausted = true;
                break;
            }
        }
    }

    let report = record_bva_pass(
        formula,
        &budget,
        exhausted,
        initial_candidates,
        initial_factors,
    );
    finalize_deletions(formula, logger, &mut deletion_indices);
    Ok(report)
}

fn record_bva_pass(
    formula: &mut Formula,
    budget: &BvaBudget,
    exhausted: bool,
    initial_candidates: u64,
    initial_factors: u64,
) -> BvaPassReport {
    let visits = budget.visits();
    formula.stats.bva_clause_visits += visits as u64;
    formula.stats.bva_budget_exhaustions += u64::from(exhausted);
    BvaPassReport {
        visits,
        candidates: formula
            .stats
            .bva_candidates_attempted
            .saturating_sub(initial_candidates),
        factors: formula.stats.bva_literals.saturating_sub(initial_factors),
        exhausted,
    }
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
    index: &RemainderIndex,
) -> FactorSearch<(isize, usize)> {
    let and_gate = match AndGate::find(formula, start, pending_deleted, budget, index) {
        FactorSearch::Found(gate) => Some(gate),
        FactorSearch::NotFound => None,
        FactorSearch::BudgetExhausted => return FactorSearch::BudgetExhausted,
    };
    let variable = start.unsigned_abs() as usize;
    let gate = if formula.assignment.get_value(variable).is_none() {
        match Gate::find(formula, pending_deleted, start, budget) {
            FactorSearch::Found(gate) => Some(gate),
            FactorSearch::NotFound => None,
            // The completed AND is safe to commit even if comparison ran out
            // of effort. The next charged operation stops and finalizes the pass.
            FactorSearch::BudgetExhausted if and_gate.is_some() => None,
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
    use crate::formula::extension::{ExtensionDefinition, ExtensionOrigin};
    use crate::process::ges::{GesOptions, Policy, process_with_policy};

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
        let mut index = RemainderIndex::default();
        assert!(index.extend(formula, &pending_deleted, &mut budget));
        let found = matches!(
            factorize_literal(
                formula,
                logger,
                start,
                &mut pending_deleted,
                &mut deletion_indices,
                &mut budget,
                &index,
            ),
            FactorSearch::Found(_)
        );
        finalize_deletions(formula, logger, &mut deletion_indices);
        found
    }

    #[test]
    fn generated_quotients_are_factored_in_the_same_pass() {
        let mut clauses = Vec::new();
        for first in [1, 2] {
            for second in [3, 4] {
                for third in [5, 6, 7, 8] {
                    clauses.push(vec![first, second, third]);
                }
            }
        }
        let mut formula = Formula::from_vec(clauses.clone());
        let initial_slots = formula.clause_slots_len();
        let scope = ClauseScope::range(0..initial_slots);
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));
        process(&mut formula, &scope, &mut logger, None, None).unwrap();
        drop(logger);
        assert!(formula.stats.bva_literals >= 2);
        assert!(
            (initial_slots..formula.clause_slots_len())
                .any(|index| formula.is_clause_garbage(index))
        );
        assert_eq!(formula.stats.bva_budget_exhaustions, 0);

        // Exhaustively check existential projection onto the original variables,
        // not just the satisfiability of this (positive) fixture.
        let live = formula
            .get_clauses()
            .map(|(_, clause)| clause.sorted_literal_indices())
            .collect::<Vec<_>>();
        let satisfies = |clauses: &[Vec<i32>], bits: usize| {
            clauses.iter().all(|clause| {
                clause.iter().any(|&literal| {
                    let value = bits & (1 << (literal.unsigned_abs() as usize - 1)) != 0;
                    value == literal.is_positive()
                })
            })
        };
        for original in 0..256 {
            let projected = (0..(1usize << formula.stats.bva_literals))
                .any(|auxiliary| satisfies(&live, original | (auxiliary << 8)));
            assert_eq!(satisfies(&clauses, original), projected);
        }

        let mut repeated = Formula::from_vec(clauses);
        let mut repeated_proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut repeated_proof));
        process(&mut repeated, &scope, &mut logger, None, None).unwrap();
        drop(logger);
        assert_eq!(proof, repeated_proof);
        assert_eq!(
            formula.stats.bva_clause_visits,
            repeated.stats.bva_clause_visits
        );
    }

    #[test]
    fn pass_budget_is_scaled_and_capped() {
        for (phase, minimum, scaled, maximum) in [
            (ProcessPhase::Preprocessing, 100_000, 1_024_000, 10_000_000),
            (ProcessPhase::Inprocessing, 10_000, 64_000, 500_000),
        ] {
            assert_eq!(pass_visit_limit(0, phase), minimum);
            assert_eq!(pass_visit_limit(1_000, phase), scaled);
            assert_eq!(pass_visit_limit(usize::MAX, phase), maximum);
        }
    }

    #[test]
    fn adaptive_budgets_keep_phase_state_separate_and_use_productivity() {
        let mut formula = Formula::from_vec(vec![vec![1]; 1_000]);

        assert_eq!(
            adaptive_pass_visit_limit(&mut formula, ProcessPhase::Preprocessing),
            1_024_000
        );
        assert_eq!(
            adaptive_pass_visit_limit(&mut formula, ProcessPhase::Inprocessing),
            64_000
        );
        assert_eq!(formula.stats.bva_current_budget, 64_000);
        assert_eq!(formula.stats.bva_peak_budget, 1_024_000);

        update_adaptive_pass_visit_limit(
            &mut formula,
            ProcessPhase::Preprocessing,
            BvaPassReport {
                visits: 1_024_000,
                candidates: 100,
                factors: 0,
                exhausted: true,
            },
        );
        assert_eq!(
            adaptive_pass_visit_limit(&mut formula, ProcessPhase::Preprocessing),
            768_000
        );
        assert_eq!(formula.stats.bva_budget_decreases, 1);

        update_adaptive_pass_visit_limit(
            &mut formula,
            ProcessPhase::Inprocessing,
            BvaPassReport {
                visits: 64_000,
                candidates: 100,
                factors: 2,
                exhausted: true,
            },
        );
        assert_eq!(
            adaptive_pass_visit_limit(&mut formula, ProcessPhase::Inprocessing),
            80_000
        );
        assert_eq!(formula.stats.bva_budget_increases, 1);
    }

    #[test]
    fn adaptive_bva_budget_only_grows_after_exhaustion() {
        let mut formula = Formula::from_vec(vec![vec![1]; 1_000]);
        assert_eq!(
            adaptive_pass_visit_limit(&mut formula, ProcessPhase::Inprocessing),
            64_000
        );

        update_adaptive_pass_visit_limit(
            &mut formula,
            ProcessPhase::Inprocessing,
            BvaPassReport {
                visits: 10_000,
                candidates: 100,
                factors: 2,
                exhausted: false,
            },
        );

        assert_eq!(
            adaptive_pass_visit_limit(&mut formula, ProcessPhase::Inprocessing),
            64_000
        );
        assert_eq!(formula.stats.bva_budget_increases, 0);
        assert_eq!(formula.stats.bva_budget_decreases, 0);
    }

    #[test]
    fn orchestration_passes_distinct_phase_budgets() {
        for phase in [ProcessPhase::Preprocessing, ProcessPhase::Inprocessing] {
            let mut formula = Formula::from_vec(vec![(1..=20).collect(); 8_200]);
            let scope = ClauseScope::range(0..formula.clause_slots_len());
            formula
                .process_in_phase::<std::io::Empty>(
                    vec![crate::process::Process::BVA],
                    &scope,
                    &mut None,
                    None,
                    false,
                    None,
                    None,
                    phase,
                )
                .unwrap();
            assert_eq!(formula.stats.bva_literals, 0);
            match phase {
                ProcessPhase::Preprocessing => {
                    assert_eq!(formula.stats.bva_budget_exhaustions, 0);
                    assert!(formula.stats.bva_clause_visits > 500_000);
                }
                ProcessPhase::Inprocessing => {
                    assert_eq!(formula.stats.bva_budget_exhaustions, 1);
                    assert_eq!(formula.stats.bva_clause_visits, 500_000);
                }
            }
        }
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

        assert_eq!(formula.live_clause_count(), 7);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.bva_binary_and_factors, 1);
        assert_eq!(formula.stats.bva_non_binary_and_factors, 0);
        assert_eq!(formula.stats.bva_ite_factors, 0);
        assert_eq!(formula.stats.bva_xor_factors, 0);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(
            formula.extensions.definition(&Literal::new(7)),
            Some(&ExtensionDefinition::And(vec![
                Literal::new(1),
                Literal::new(2),
            ]))
        );
        assert_eq!(
            formula
                .extensions
                .substitute(&Literal::new(1), &Literal::new(2)),
            Some(Literal::new(7))
        );
        assert_eq!(
            formula.extensions.substitution_inputs(&Literal::new(7)),
            Some((Literal::new(2), Literal::new(1)))
        );
        assert_eq!(
            formula
                .extensions
                .substitution_partners(&Literal::new(1))
                .map(|(partner, replacement)| { (partner.get_index(), replacement.get_index()) })
                .collect::<Vec<_>>(),
            vec![(2, 7)]
        );
        for source_index in 0..8 {
            assert!(formula.is_clause_garbage(source_index));
        }
    }

    #[test]
    fn ges_uses_an_exact_binary_bva_substitution() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
            vec![-1, -2, 20],
        ]);
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));
        let bva_scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(factorize_once(&mut formula, &bva_scope, &mut logger, 1));
        assert_eq!(
            formula.extensions.substitution_origin(&Literal::new(21)),
            Some(ExtensionOrigin::Bva)
        );
        let ges_scope = ClauseScope::range(0..formula.clause_slots_len());
        process_with_policy(
            &mut formula,
            &ges_scope,
            &mut logger,
            None,
            None,
            None,
            Policy::Always,
            GesOptions::default(),
        )
        .unwrap();

        assert_eq!(formula.stats.global_extension_substitution, 1);
        assert!(
            formula
                .get_clauses()
                .any(|(_, clause)| clause.sorted_literal_indices() == vec![-21, 20])
        );
        assert!(formula.is_clause_garbage(8));
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
        assert_eq!(formula.stats.bva_binary_and_factors, 0);
        assert_eq!(formula.stats.bva_non_binary_and_factors, 0);
        assert_eq!(formula.stats.bva_ite_factors, 1);
        assert_eq!(formula.stats.bva_xor_factors, 0);
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
    fn selected_clause_neutral_xor_is_applied_without_growing_the_database() {
        let mut formula = Formula::from_vec(
            (10..=13)
                .flat_map(|remainder| [vec![1, -3, remainder], vec![-1, 3, remainder]])
                .collect(),
        );
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());
        let initial_live_clause_count = formula.live_clause_count();

        assert!(factorize_once(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.live_clause_count(), initial_live_clause_count);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(formula.stats.bva_ite_factors, 0);
        assert_eq!(formula.stats.bva_xor_factors, 1);
        assert_eq!(formula.stats.bva_clauses_saved, 0);
        assert_eq!(
            formula.extensions.definition(&Literal::new(14)),
            Some(&ExtensionDefinition::Ite {
                condition: Literal::new(1),
                when_true: Literal::new(-3),
                when_false: Literal::new(3),
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
        assert_eq!(first.stats.bva_clauses_saved, 2);
        assert_eq!(first.stats.bva_source_clauses_replaced, 16);
        assert_eq!(first.live_clause_count(), 14);
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
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.add_clause_unchecked(
            crate::circuits::factorization::definition_clause(vec![
                Literal::new(-1),
                Literal::new(12),
                Literal::new(13),
            ]),
            &mut logger,
        );
        let scope = ClauseScope::range(0..formula.clause_slots_len());
        let pending = vec![false; formula.clause_slots_len()];
        let mut budget = BvaBudget::new(usize::MAX);
        let FactorSearch::Found(candidates) =
            deterministic_candidates(&formula, &pending, &mut budget)
        else {
            panic!("expected candidates")
        };
        let mut index = RemainderIndex::default();
        assert!(index.extend(&formula, &pending, &mut budget));
        assert!(matches!(
            candidate_is_live(&formula, candidates[0], &pending, &mut budget),
            FactorSearch::Found(())
        ));
        assert!(matches!(
            AndGate::find(&formula, candidates[0], &pending, &mut budget, &index),
            FactorSearch::Found(_)
        ));
        let limit = budget.visits();
        let mut empty_budget = BvaBudget::new(0);
        assert!(matches!(
            Gate::find(&formula, &pending, candidates[0], &mut empty_budget),
            FactorSearch::BudgetExhausted
        ));
        process_with_budget(&mut formula, &scope, &mut logger, None, limit).unwrap();

        assert_eq!(formula.stats.bva_clause_visits, limit as u64);
        assert_eq!(formula.stats.bva_budget_exhaustions, 1);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(formula.live_clause_count(), 16);
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
