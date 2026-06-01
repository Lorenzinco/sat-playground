use crate::formula::Formula;
use crate::formula::clause::Clause;
use std::time::Instant;

pub struct IncrementalSubsumption {
    pub subsumed_by_existing: Option<usize>,
    pub subsumed_existing: Vec<usize>,
    pub subset_checks: usize,
}

pub fn preprocess(formula: &mut Formula) {
    let start = Instant::now();
    let result = find_subsumed_clauses(formula);
    formula
        .stats
        .add_subsumption_checks(result.subset_checks as u64);
    formula
        .stats
        .add_subsumed_clauses(result.to_delete.len() as u64);

    if !result.to_delete.is_empty() {
        formula.delete_clauses::<std::io::Empty>(&result.to_delete, &mut None);
    }

    formula.stats.record_subsumption_time(start.elapsed());
}

pub fn check_new_clause(formula: &Formula, new_clause: &Clause) -> IncrementalSubsumption {
    let mut subset_checks = 0;

    let mut existing_subsumers = formula.candidate_indices_for_clause(new_clause);
    existing_subsumers.sort_unstable();
    existing_subsumers.dedup();

    for idx in existing_subsumers {
        let existing = &formula.get_clauses()[idx];
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
        let existing = &formula.get_clauses()[idx];
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

fn find_subsumed_clauses(formula: &Formula) -> SubsumptionResult {
    let clauses = formula.get_clauses();
    let mut deleted = vec![false; clauses.len()];
    let mut to_delete = Vec::new();
    let mut subset_checks = 0;

    for subsumer_idx in 0..clauses.len() {
        if deleted[subsumer_idx] || clauses[subsumer_idx].lock_count > 0 {
            continue;
        }

        let Some((watch_a, watch_b)) = clauses[subsumer_idx].watched_literals() else {
            continue;
        };

        for candidate_idx in formula.occurrence_intersection(watch_a, watch_b) {
            if candidate_idx == subsumer_idx
                || deleted[candidate_idx]
                || clauses[candidate_idx].lock_count > 0
                || clauses[candidate_idx].len() < clauses[subsumer_idx].len()
            {
                continue;
            }

            if clauses[candidate_idx].len() == clauses[subsumer_idx].len()
                && candidate_idx < subsumer_idx
            {
                continue;
            }

            subset_checks += 1;
            if clauses[subsumer_idx].is_subset_of(&clauses[candidate_idx]) {
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

    #[test]
    fn subsumption_deletes_strict_superset_clause() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 2, 3], vec![2, 4]]);

        preprocess(&mut formula);

        let clauses = formula.get_clauses();
        assert_eq!(clauses.len(), 2);
        assert_eq!(formula.stats.clauses_subsumed, 1);
        assert!(formula.stats.subsumption_checks > 0);
        assert!(formula.stats.subsumption_nanos > 0);
        assert!(
            clauses
                .iter()
                .any(|clause| clause.get_literals() == &vec![Literal::new(1), Literal::new(2)])
        );
        assert!(
            clauses
                .iter()
                .any(|clause| clause.get_literals() == &vec![Literal::new(2), Literal::new(4)])
        );
    }

    #[test]
    fn subsumption_deletes_duplicate_with_higher_index() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 2], vec![1, 2, 3]]);

        preprocess(&mut formula);

        assert_eq!(formula.get_clauses().len(), 1);
        assert_eq!(formula.stats.clauses_subsumed, 2);
        assert_eq!(
            formula.get_clauses()[0].get_literals(),
            &vec![Literal::new(1), Literal::new(2)]
        );
    }

    #[test]
    fn subsumption_skips_locked_candidate_clause() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![1, 2]]);
        formula.get_clause_at_idx_mut(1).lock_count = 1;

        preprocess(&mut formula);

        assert_eq!(formula.get_clauses().len(), 2);
        assert_eq!(formula.stats.clauses_subsumed, 0);
    }

    #[test]
    fn incremental_check_finds_existing_subsumer() {
        let mut formula = Formula::from_vec(vec![vec![1, 2]]);
        formula
            .process::<std::io::Empty>(
                vec![crate::process::Process::Subsumption],
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
        assert_eq!(formula.get_clauses().len(), 1);
        assert_eq!(formula.stats.clauses_subsumed, 1);
    }

    #[test]
    fn incremental_check_deletes_existing_subsumed_clause() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        formula
            .process::<std::io::Empty>(
                vec![crate::process::Process::Subsumption],
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

        assert_eq!(idx, 0);
        assert_eq!(formula.get_clauses().len(), 1);
        assert_eq!(
            formula.get_clauses()[0].get_literals(),
            &vec![Literal::new(1), Literal::new(2)]
        );
        assert_eq!(formula.stats.clauses_subsumed, 1);
    }
}
