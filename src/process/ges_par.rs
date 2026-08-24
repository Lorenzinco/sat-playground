//! Worker-scaled cursor GES: parallel snapshot analysis, then ordered sequential commit.
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::history::History;
use crate::process::ClauseScope;
use crate::process::ges::{
    MAX_CLAUSES_PER_PASS, PassWorkspace, commit_replacements, select_cursor_clause_indices,
};
use pyo3::{PyResult, Python};
use rayon::prelude::*;
use std::io::Write;

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
    reasoning_levels: Option<&[Option<usize>]>,
) -> PyResult<()> {
    check_signal(&mut signal)?;
    let slot = MAX_CLAUSES_PER_PASS;
    let limit = slot.saturating_mul(rayon::current_num_threads());
    let indices = select_cursor_clause_indices(formula, scope, limit);
    // Formula itself is not Sync (its assignment contains a fastbit BitVec).
    // Borrow only the immutable, Sync data needed by substitution analysis.
    let extensions = &formula.extensions;
    let vsids = &formula.vsids;
    let has_history = history.is_some();
    let mut replacements = Vec::new();
    let mut reports = Vec::new();
    let clauses: Vec<_> = indices
        .into_iter()
        .map(|idx| (idx, formula.get_clause_at_idx(idx)))
        .collect();
    check_signal(&mut signal)?;
    // At most one chunk per current worker, scheduled by Rayon (not pinned).
    // Indexed collection preserves window order regardless of worker scheduling.
    // Neither Formula, Python, History nor the proof writer is captured by workers.
    let blocks: Vec<Vec<_>> = clauses
        .par_chunks(slot)
        .map(|block| {
            let mut workspace = PassWorkspace::new(extensions);
            block
                .iter()
                .map(|&(idx, clause)| {
                    (
                        idx,
                        workspace.evaluate(vsids, clause, has_history, reasoning_levels),
                    )
                })
                .collect()
        })
        .collect();
    check_signal(&mut signal)?;
    for block in blocks {
        for (idx, evaluation) in block {
            reports.push(evaluation.report);
            if let Some(replacement) = evaluation.replacement {
                replacements.push((idx, replacement));
            }
        }
    }
    check_signal(&mut signal)?;
    for report in reports {
        report.merge_into(formula);
    }
    commit_replacements(formula, replacements, logger, history);
    Ok(())
}

fn check_signal(signal: &mut Option<(Python<'_>, &mut u64)>) -> PyResult<()> {
    if let Some((py, steps)) = signal.as_mut() {
        **steps += 1;
        // Unlike the amortized solver checker, every analysis boundary polls Python.
        py.check_signals()?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::process::ges::evaluate_clause;

    use crate::formula::extension::extension_literal;
    use crate::formula::literal::Literal;

    fn fixture(count: usize) -> Formula {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 3]; count]);
        let mut logger: Option<DratLogger<Vec<u8>>> = None;
        extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        formula
    }

    fn sequential_window(
        formula: &mut Formula,
        scope: &ClauseScope,
        logger: &mut Option<DratLogger<&mut Vec<u8>>>,
        history: Option<&mut History>,
        levels: Option<&[Option<usize>]>,
    ) {
        let indices = select_cursor_clause_indices(
            formula,
            scope,
            MAX_CLAUSES_PER_PASS.saturating_mul(rayon::current_num_threads()),
        );
        let evaluations: Vec<_> = indices
            .into_iter()
            .map(|idx| {
                (
                    idx,
                    evaluate_clause(
                        &formula.extensions,
                        &formula.vsids,
                        formula.get_clause_at_idx(idx),
                        history.is_some(),
                        levels,
                    ),
                )
            })
            .collect();
        let mut replacements = Vec::new();
        for (idx, evaluation) in evaluations {
            evaluation.report.merge_into(formula);
            if let Some(replacement) = evaluation.replacement {
                replacements.push((idx, replacement));
            }
        }
        commit_replacements(formula, replacements, logger, history);
    }

    fn report(formula: &Formula) -> crate::process::ges::EvaluationReport {
        crate::process::ges::EvaluationReport {
            inspected: formula.stats.ges_clauses_inspected,
            noop: formula.stats.ges_noop_rewrites,
            rejected: formula.stats.ges_rewrites_rejected,
            lbd_improvements: formula.stats.ges_lbd_improvements,
            vsids_improvements: formula.stats.ges_vsids_improvements,
            literals_removed: formula.stats.ges_literals_removed,
        }
    }

    fn state(formula: &Formula) -> Vec<(usize, Vec<Literal>, i16, usize, bool, bool)> {
        formula
            .get_clauses()
            .map(|(idx, clause)| {
                (
                    idx,
                    clause.get_literals().to_vec(),
                    clause.lbd,
                    clause.lock_count as usize,
                    clause.ges_generated,
                    clause.ges_used,
                )
            })
            .collect()
    }

    #[test]
    fn worker_scaled_budget_wraps_and_resumes_with_ordered_proof_and_metadata() {
        for threads in [1, 2, 4] {
            rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    let budget = MAX_CLAUSES_PER_PASS * threads;
                    let count = budget + 7;
                    let scope = ClauseScope::range(0..count);
                    let setup = || {
                        let mut formula = fixture(count);
                        formula.ges_cursor = count - 3;
                        for idx in 0..count {
                            let clause = formula.get_clause_at_idx_mut(idx);
                            clause.lbd = 5;
                            clause.ges_generated = true;
                            clause.ges_used = true;
                        }
                        formula
                    };
                    let mut sequential = setup();
                    let mut parallel = setup();
                    let mut expected = Vec::new();
                    let mut actual = Vec::new();
                    for pass in 0..2 {
                        sequential_window(
                            &mut sequential,
                            &scope,
                            &mut Some(DratLogger::new(&mut expected)),
                            None,
                            None,
                        );
                        process(
                            &mut parallel,
                            &scope,
                            &mut Some(DratLogger::new(&mut actual)),
                            None,
                            None,
                            None,
                        )
                        .unwrap();
                        // The three extension axioms are live scoped entries too.
                        let processed = if pass == 0 { budget - 3 } else { count };
                        assert_eq!(state(&parallel), state(&sequential));
                        assert_eq!(actual, expected);
                        assert_eq!(report(&parallel), report(&sequential));
                        assert_eq!(parallel.stats.ges_clauses_inspected, processed as u64);
                        assert_eq!(
                            parallel.stats.global_extension_substitution,
                            processed as u64
                        );
                        assert_eq!(
                            parallel.stats.clauses_deleted,
                            sequential.stats.clauses_deleted
                        );
                        assert_eq!(
                            parallel.ges_cursor,
                            if pass == 0 { budget - 6 } else { count + 3 }
                        );
                        for idx in 0..count {
                            let selected = pass == 1 || idx >= count - 3 || idx < budget - 6;
                            assert_eq!(parallel.is_clause_garbage(idx), selected);
                            if !selected {
                                let source = parallel.get_clause_at_idx(idx);
                                assert!(source.ges_generated && source.ges_used);
                                assert_eq!(source.lbd, 5);
                                assert_eq!(
                                    source.get_literals(),
                                    &[Literal::new(-1), Literal::new(-2), Literal::new(3)]
                                );
                            }
                        }
                        for offset in 0..processed {
                            let replacement = parallel.get_clause_at_idx(count + 3 + offset);
                            assert_eq!(replacement.lbd, 2);

                            assert!(replacement.ges_generated);
                            assert!(!replacement.ges_used);
                            assert_eq!(replacement.lock_count, 0);
                        }
                    }
                    let proof = String::from_utf8(actual).unwrap();
                    let lines: Vec<_> = proof.lines().collect();
                    assert_eq!(lines.len(), 2 * count);
                    for pair in lines.chunks_exact(2) {
                        assert_eq!(pair, ["3 -4 0", "d -1 -2 3 0"]);
                    }
                });
        }
    }

    #[test]
    fn protected_entries_count_towards_budget_but_garbage_and_out_of_scope_do_not() {
        for threads in [1, 2, 4] {
            rayon::ThreadPoolBuilder::new()
                .num_threads(threads)
                .build()
                .unwrap()
                .install(|| {
                    let budget = MAX_CLAUSES_PER_PASS * threads;
                    let mut formula = fixture(budget + 4);
                    for idx in 0..budget + 4 {
                        formula.get_clause_at_idx_mut(idx).lbd = 5;
                    }
                    let scope = ClauseScope::indices((0..budget + 4).filter(|&idx| idx != 1));
                    let mut logger: Option<DratLogger<Vec<u8>>> = None;
                    formula.delete_clause(0, &mut logger);
                    formula.get_clause_at_idx_mut(2).lbd = 0;
                    formula.get_clause_at_idx_mut(3).lbd = 2;
                    formula.get_clause_at_idx_mut(4).increment_lock_count();
                    process(&mut formula, &scope, &mut logger, None, None, None).unwrap();
                    assert_eq!(formula.ges_cursor, budget + 2);
                    assert_eq!(formula.stats.ges_clauses_inspected, (budget - 3) as u64);
                    for idx in [1, 2, 3, 4, budget + 2, budget + 3] {
                        assert!(!formula.is_clause_garbage(idx));
                    }
                    process(&mut formula, &scope, &mut logger, None, None, None).unwrap();
                    assert_eq!(formula.ges_cursor, 5);
                    assert_eq!(formula.stats.ges_clauses_inspected, (budget - 1) as u64);
                    assert!(formula.is_clause_garbage(budget + 2));
                    assert!(formula.is_clause_garbage(budget + 3));
                });
        }
    }

    #[test]
    fn empty_windows_preserve_cursor() {
        let mut logger: Option<DratLogger<Vec<u8>>> = None;
        for mut formula in [Formula::new(0), Formula::from_vec(vec![vec![1]; 3])] {
            for idx in 0..formula.clause_slots_len() {
                formula.get_clause_at_idx_mut(idx).lbd = 5;
            }
            formula.ges_cursor = usize::MAX;
            process(
                &mut formula,
                &ClauseScope::range(0..0),
                &mut logger,
                None,
                None,
                None,
            )
            .unwrap();
            assert_eq!(formula.ges_cursor, usize::MAX);
            assert_eq!(report(&formula), Default::default());
        }
    }

    #[test]
    fn sync_and_parallel_match_acceptance_and_rejection_reports() {
        for levels in [None, Some([None, Some(1), Some(1), Some(1), Some(1)])] {
            let setup = || {
                let mut formula = Formula::from_vec(vec![vec![-1, -2, 3], vec![-4, 3]]);
                formula.extensions.add_substitution(
                    &Literal::new(1),
                    &Literal::new(2),
                    &Literal::new(4),
                );
                formula
            };
            let mut sequential = setup();
            let mut parallel = setup();
            let scope = ClauseScope::range(0..2);
            let mut expected = Vec::new();
            let mut actual = Vec::new();
            crate::process::ges::process(
                &mut sequential,
                &scope,
                &mut Some(DratLogger::new(&mut expected)),
                None,
                None,
                levels.as_ref().map(|levels| levels.as_slice()),
            )
            .unwrap();
            process(
                &mut parallel,
                &scope,
                &mut Some(DratLogger::new(&mut actual)),
                None,
                None,
                levels.as_ref().map(|levels| levels.as_slice()),
            )
            .unwrap();
            assert_eq!(state(&parallel), state(&sequential));
            assert_eq!(actual, expected);
            assert_eq!(report(&parallel), report(&sequential));
            let report = report(&parallel);
            assert_eq!(report.inspected, 2);
            assert_eq!(report.noop, 1);
            assert_eq!(report.rejected, u64::from(levels.is_some()));
            assert_eq!(report.lbd_improvements, u64::from(levels.is_none()));
            assert_eq!(report.literals_removed, u64::from(levels.is_none()));
        }
    }

    #[test]
    fn scope_garbage_glue_axioms_and_locks_match_sequential() {
        for scope in [ClauseScope::range(2..7), ClauseScope::indices([2, 4, 6])] {
            let setup = || {
                let mut formula = fixture(8);
                for idx in 0..8 {
                    formula.get_clause_at_idx_mut(idx).lbd = 5;
                }
                formula.get_clause_at_idx_mut(0).lbd = -1;
                formula.get_clause_at_idx_mut(2).lbd = 0;
                formula.get_clause_at_idx_mut(4).lbd = 2;
                formula.get_clause_at_idx_mut(6).increment_lock_count();
                let mut logger: Option<DratLogger<Vec<u8>>> = None;
                formula.delete_clause(3, &mut logger);
                formula
            };
            let mut sequential = setup();
            let mut parallel = setup();
            let mut expected = Vec::new();
            let mut actual = Vec::new();
            sequential_window(
                &mut sequential,
                &scope,
                &mut Some(DratLogger::new(&mut expected)),
                None,
                None,
            );
            process(
                &mut parallel,
                &scope,
                &mut Some(DratLogger::new(&mut actual)),
                None,
                None,
                None,
            )
            .unwrap();
            assert_eq!(state(&parallel), state(&sequential));
            assert_eq!(actual, expected);
            for idx in [1, 2, 4, 6, 7] {
                assert!(!parallel.is_clause_garbage(idx));
            }
            assert!(parallel.is_clause_garbage(0));
        }
    }

    #[test]
    fn locked_reason_transfer_matches_sequential() {
        let setup = || {
            let mut formula = fixture(1);
            let mut history = History::new();
            formula.assign_implication(Literal::new(1), &mut history, None);
            formula.assign_implication(Literal::new(2), &mut history, None);
            formula.assign_implication(Literal::new(4), &mut history, Some(1));
            formula.assign_implication(Literal::new(3), &mut history, Some(0));
            (formula, history)
        };
        let (mut sequential, mut sh) = setup();
        let (mut parallel, mut ph) = setup();
        let levels = [None, Some(1), Some(2), Some(3), Some(1)];
        let scope = ClauseScope::range(0..4);
        let mut expected = Vec::new();
        let mut actual = Vec::new();
        sequential_window(
            &mut sequential,
            &scope,
            &mut Some(DratLogger::new(&mut expected)),
            Some(&mut sh),
            Some(&levels),
        );
        process(
            &mut parallel,
            &scope,
            &mut Some(DratLogger::new(&mut actual)),
            None,
            Some(&mut ph),
            Some(&levels),
        )
        .unwrap();
        assert_eq!(state(&parallel), state(&sequential));
        assert_eq!(actual, expected);
        assert_eq!(report(&parallel), report(&sequential));
        assert_eq!(ph.decision_levels[0].get_reason(&Literal::new(3)), Some(4));
        assert_eq!(parallel.get_clause_at_idx(4).lock_count, 1);
        assert!(parallel.is_clause_garbage(0));
    }
}
