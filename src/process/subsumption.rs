use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::process::ClauseScope;
use std::io::Write;
use std::time::Instant;

pub struct IncrementalSubsumption {
    pub subsumed_by_existing: Option<usize>,
    pub subsumed_existing: Vec<usize>,
    pub subset_checks: usize,
}

pub fn preprocess<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
) {
    let start = Instant::now();
    let result = find_subsumed_clauses(formula, scope);
    formula
        .stats
        .add_subsumption_checks(result.subset_checks as u64);
    formula
        .stats
        .add_subsumed_clauses(result.to_delete.len() as u64);

    if !result.to_delete.is_empty() {
        formula.delete_clauses(&result.to_delete, logger);
    }

    formula.stats.record_subsumption_time(start.elapsed());
}

pub fn check_new_clause(formula: &mut Formula, new_clause: &Clause) -> IncrementalSubsumption {
    let mut subset_checks = 0;

    let mut existing_subsumers = formula.candidate_indices_for_clause(new_clause);
    existing_subsumers.sort_unstable();
    existing_subsumers.dedup();

    for idx in existing_subsumers {
        let existing = formula.get_clause_at_idx(idx);
        if existing.lock_count > 0 || existing.len() > new_clause.len() {
            continue;
        }

        subset_checks += 1;
        if existing.is_subset_of(new_clause) {
            return IncrementalSubsumption {
                subsumed_by_existing: Some(idx),
                subsumed_existing: Vec::new(),
                subset_checks,
            };
        }
    }

    let mut subsumed_existing = Vec::new();
    let Some((watch_a, watch_b)) = new_clause.watched_literals() else {
        return IncrementalSubsumption {
            subsumed_by_existing: None,
            subsumed_existing,
            subset_checks,
        };
    };

    for idx in formula.occurrence_intersection(watch_a, watch_b) {
        let existing = formula.get_clause_at_idx(idx);
        if existing.lock_count > 0 || existing.len() < new_clause.len() {
            continue;
        }

        subset_checks += 1;
        if new_clause.is_subset_of(existing) {
            subsumed_existing.push(idx);
        }
    }

    subsumed_existing.sort_unstable();
    subsumed_existing.dedup();

    IncrementalSubsumption {
        subsumed_by_existing: None,
        subsumed_existing,
        subset_checks,
    }
}

struct SubsumptionResult {
    to_delete: Vec<usize>,
    subset_checks: usize,
}

fn find_subsumed_clauses(formula: &mut Formula, scope: &ClauseScope) -> SubsumptionResult {
    let mut deleted = vec![false; formula.clause_slots_len()];
    let mut to_delete = Vec::new();
    let mut subset_checks = 0;

    for subsumer_idx in 0..formula.clause_slots_len() {
        if deleted[subsumer_idx] || formula.is_clause_garbage(subsumer_idx) {
            continue;
        }
        if !scope.includes(subsumer_idx, formula.get_clause_at_idx(subsumer_idx)) {
            continue;
        }

        let (watch_a, watch_b, subsumer_len, subsumer_locked) = {
            let subsumer = formula.get_clause_at_idx(subsumer_idx);
            let Some((watch_a, watch_b)) = subsumer.watched_literals() else {
                continue;
            };
            (
                watch_a.clone(),
                watch_b.cloned(),
                subsumer.len(),
                subsumer.lock_count > 0,
            )
        };
        if subsumer_locked {
            continue;
        }

        for candidate_idx in formula.occurrence_intersection(&watch_a, watch_b.as_ref()) {
            if candidate_idx == subsumer_idx || deleted[candidate_idx] {
                continue;
            }

            let candidate = formula.get_clause_at_idx(candidate_idx);
            if !scope.includes(candidate_idx, candidate) {
                continue;
            }
            if candidate.lbd == 0 || candidate.lock_count > 0 || candidate.len() < subsumer_len {
                continue;
            }

            if candidate.len() == subsumer_len && candidate_idx < subsumer_idx {
                continue;
            }

            subset_checks += 1;
            if formula
                .get_clause_at_idx(subsumer_idx)
                .is_subset_of(candidate)
            {
                deleted[candidate_idx] = true;
                to_delete.push(candidate_idx);
            }
        }
    }

    to_delete.sort_unstable();
    to_delete.dedup();

    SubsumptionResult {
        to_delete,
        subset_checks,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::literal::Literal;

    fn full_scope(formula: &Formula) -> ClauseScope {
        ClauseScope::range(0..formula.clause_slots_len())
    }

    #[test]
    fn subsumption_deletes_strict_superset_clause() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 2, 3], vec![2, 4]]);
        let scope = full_scope(&formula);

        preprocess::<std::io::Empty>(&mut formula, &scope, &mut None);

        assert_eq!(formula.live_clause_count(), 2);
        assert_eq!(formula.stats.clauses_subsumed, 1);
        assert!(formula.stats.subsumption_checks > 0);
        assert!(formula.stats.subsumption_nanos > 0);
        assert!(
            formula
                .get_clauses()
                .any(|(_, clause)| clause.get_literals() == vec![Literal::new(1), Literal::new(2)])
        );
        assert!(
            formula
                .get_clauses()
                .any(|(_, clause)| clause.get_literals() == vec![Literal::new(2), Literal::new(4)])
        );
    }

    #[test]
    fn subsumption_deletes_duplicate_with_higher_index() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 2], vec![1, 2, 3]]);
        let scope = full_scope(&formula);

        preprocess::<std::io::Empty>(&mut formula, &scope, &mut None);

        assert_eq!(formula.live_clause_count(), 1);
        assert_eq!(formula.stats.clauses_subsumed, 2);
        assert_eq!(
            formula.get_clause_at_idx(0).get_literals(),
            &vec![Literal::new(1), Literal::new(2)]
        );
    }

    #[test]
    fn subsumption_skips_locked_candidate_clause() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![1, 2]]);
        formula.get_clause_at_idx_mut(1).increment_lock_count();
        let scope = full_scope(&formula);

        preprocess::<std::io::Empty>(&mut formula, &scope, &mut None);

        assert_eq!(formula.live_clause_count(), 2);
        assert_eq!(formula.stats.clauses_subsumed, 0);
    }

    #[test]
    fn incremental_check_finds_existing_subsumer() {
        let mut formula = Formula::from_vec(vec![vec![1, 2]]);
        let scope = full_scope(&formula);
        formula
            .process::<std::io::Empty>(
                vec![crate::process::Process::Subsumption],
                &scope,
                &mut None,
                None,
                true,
                None,
            )
            .unwrap();

        let idx = formula.add_clause::<std::io::Empty>(
            Clause::from_literals(vec![Literal::new(1), Literal::new(2), Literal::new(3)], 1),
            &mut None,
            None,
        );

        assert_eq!(idx, 0);
        assert_eq!(formula.live_clause_count(), 1);
        assert_eq!(formula.stats.clauses_subsumed, 1);
    }

    #[test]
    fn incremental_check_deletes_existing_subsumed_clause() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        let scope = full_scope(&formula);
        formula
            .process::<std::io::Empty>(
                vec![crate::process::Process::Subsumption],
                &scope,
                &mut None,
                None,
                true,
                None,
            )
            .unwrap();

        let idx = formula.add_clause::<std::io::Empty>(
            Clause::from_literals(vec![Literal::new(1), Literal::new(2)], 1),
            &mut None,
            None,
        );

        assert_eq!(idx, 1);
        assert_eq!(formula.live_clause_count(), 1);
        assert_eq!(formula.clause_slots_len(), 2);
        assert_eq!(formula.get_clauses_and_garbage().count(), 2);
        assert_eq!(
            formula.get_clause_at_idx(1).get_literals(),
            &vec![Literal::new(1), Literal::new(2)]
        );
        assert_eq!(formula.stats.clauses_subsumed, 1);
    }
}
