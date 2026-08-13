use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::python::signal_checker;

use pyo3::Python;
use pyo3::prelude::PyResult;
use std::io::Write;

/// Applies exact extension substitutions to live clauses.
///
/// For every registered `z <-> (a & b)`, a clause containing `!a | !b`
/// can replace that pair with `!z`. The replacement is added before the source
/// clause is deleted, so it is RUP under the source clause and extension axioms.
const MAX_CLAUSES_PER_PASS: usize = 100;

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
) -> PyResult<()> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let mut replacements = Vec::new();
    let live_clause_count = formula.live_clause_count();
    if live_clause_count == 0 {
        return Ok(());
    }
    let start = rand::random_range(0..live_clause_count);

    for (clause_idx, clause) in sequential_clause_window(formula, start, MAX_CLAUSES_PER_PASS) {
        // Extension axioms and BVA clauses justify substitutions and must remain
        // untouched. Locked clauses are active implication reasons.
        if clause.lock_count != 0 {
            continue;
        }

        if let Some(replacement) = substitute_clause(formula, clause) {
            replacements.push((clause_idx, replacement));
        }
    }

    for (clause_idx, replacement) in replacements {
        // Keep proof order: the source clause is needed to RUP-check the
        // replacement, so add the replacement before logging its deletion.
        if replacement.lbd > 0 {
            formula.stats.add_learnt_clause(&replacement);
        }
        formula.add_clause_unchecked(replacement, logger);
        formula.stats.add_global_substitution();
        formula.record_clause_removal(clause_idx);
        formula.delete_clause(clause_idx, logger);
    }

    Ok(())
}

fn sequential_clause_window(
    formula: &Formula,
    start: usize,
    limit: usize,
) -> impl Iterator<Item = (usize, &Clause)> {
    let live_clause_count = formula.live_clause_count();
    let start = if live_clause_count == 0 {
        0
    } else {
        start % live_clause_count
    };

    formula
        .get_clauses()
        .skip(start)
        .chain(formula.get_clauses().take(start))
        .take(limit.min(live_clause_count))
}

fn substitute_clause(formula: &Formula, clause: &Clause) -> Option<Clause> {
    let mut literals = clause.get_literals().to_vec();
    let mut changed = false;

    while literals.len() >= 2 {
        //let mut candidate_count = 0usize;
        let mut highest = None;
        let mut lowest = None;

        for left_idx in 0..literals.len() - 1 {
            let left = literals[left_idx];
            for right_idx in left_idx + 1..literals.len() {
                let right = literals[right_idx];

                // The map stores z <-> (a & b), while clauses contain the
                // De Morgan dual !a | !b that is replaced by !z.
                let Some(replacement) = formula
                    .extensions
                    .substitute(&left.negated(), &right.negated())
                    .map(|literal| literal.negated())
                else {
                    continue;
                };

                // Replacing the pair would make the clause tautological. Such a
                // clause is redundant, but retaining it avoids special deletion
                // handling and never removes a defining axiom accidentally.
                if literals.contains(&replacement.negated()) {
                    continue;
                }

                //candidate_count += 1;
                let score = formula.vsids.literal_activity(&replacement);
                let candidate = (left_idx, right_idx, left, right, replacement, score);

                if highest
                    .as_ref()
                    .is_none_or(|(_, _, _, _, _, best_score)| score > *best_score)
                {
                    highest = Some(candidate);
                }
                if lowest
                    .as_ref()
                    .is_none_or(|(_, _, _, _, _, best_score)| score < *best_score)
                {
                    lowest = Some(candidate);
                }
            }
        }

        /*if candidate_count > 1 {
            let (_, _, high_left, high_right, high_replacement, high_score) =
                highest.as_ref().unwrap();
            let (_, _, low_left, low_right, low_replacement, low_score) = lowest.as_ref().unwrap();
                /*println!(
                "c GES found {} substitution pairs in {:?}",
                candidate_count, literals
            );
            println!(
                "c   highest replacement: ({:?}, {:?}) -> {:?} VSIDS={:.6}",
                high_left, high_right, high_replacement, high_score
            );
            println!(
                "c   lowest replacement:  ({:?}, {:?}) -> {:?} VSIDS={:.6}",
                low_left, low_right, low_replacement, low_score
            );*/
        }*/

        let Some((left_idx, right_idx, _, _, replacement, _)) = highest else {
            break;
        };

        literals.remove(right_idx);
        literals.remove(left_idx);
        if !literals.contains(&replacement) {
            literals.push(replacement);
        }
        changed = true;
    }

    changed.then(|| Clause::from_literals(literals, clause.lbd))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::extension::extension_literal;
    use crate::formula::literal::Literal;

    #[test]
    fn sequential_clause_window_wraps_and_skips_garbage() {
        let mut formula =
            Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4], vec![5], vec![6]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.delete_clause(1, &mut logger);
        formula.delete_clause(4, &mut logger);

        let indices = sequential_clause_window(&formula, 2, 4)
            .map(|(clause_idx, _)| clause_idx)
            .collect::<Vec<_>>();

        assert_eq!(indices, vec![3, 5, 0, 2]);
    }

    #[test]
    fn substitutes_the_negated_inputs_and_logs_add_before_delete() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 4]]);
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));
        let z = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );

        process(&mut formula, &mut logger, None).unwrap();
        drop(logger);

        assert!(formula.is_clause_garbage(0));
        assert_eq!(
            formula.get_clause_at_idx(4).get_literals(),
            &[Literal::new(4), z.negated()]
        );
        assert_eq!(formula.live_clause_count(), 4);
        assert_eq!(formula.stats.clauses_deleted, 1);
        assert_eq!(formula.stats.global_extension_substitution, 1);

        let proof = String::from_utf8(proof).unwrap();
        assert!(proof.ends_with("4 -5 0\nd -1 -2 4 0\n"));
    }

    #[test]
    fn repeatedly_applies_chained_substitutions() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, -3, 4]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let first = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let second = extension_literal(&mut formula, &mut logger, &first, &Literal::new(3));

        process(&mut formula, &mut logger, None).unwrap();

        assert_eq!(
            formula.get_clause_at_idx(7).get_literals(),
            &[Literal::new(4), second.negated()]
        );
    }

    #[test]
    fn substitutes_all_five_disjoint_pairs() {
        let mut formula =
            Formula::from_vec(vec![vec![-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, 11]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let first = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let second = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(3),
            &Literal::new(4),
        );
        let third = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(5),
            &Literal::new(6),
        );
        let fourth = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(7),
            &Literal::new(8),
        );
        let fifth = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(9),
            &Literal::new(10),
        );

        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0)).unwrap();

        assert_eq!(replacement.len(), 6);
        assert!(replacement.get_literals().contains(&Literal::new(11)));
        for extension in [first, second, third, fourth, fifth] {
            assert!(replacement.get_literals().contains(&extension.negated()));
        }
    }

    #[test]
    fn selects_the_highest_replacement_vsids_without_collecting_pairs() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, -3, 4]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let lower = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let higher = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(3),
        );
        // Operand activity favors the first pair, while replacement activity
        // favors the second. GES must rank what it introduces into the clause.
        formula.vsids.activity[1] = 100.0;
        formula.vsids.activity[2] = 100.0;
        formula.vsids.activity[3] = 1.0;
        formula.vsids.activity[lower.get_index().unsigned_abs() as usize] = 2.0;
        formula.vsids.activity[higher.get_index().unsigned_abs() as usize] = 8.0;

        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0)).unwrap();

        assert_eq!(
            replacement.get_literals(),
            &[Literal::new(-2), Literal::new(4), higher.negated()]
        );
        assert!(!replacement.get_literals().contains(&lower.negated()));
    }

    #[test]
    fn keeps_disjoint_substitutions_when_overlapping_pairs_compete() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, -3, -4, -5, 6]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let lower_overlap = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let higher_overlap = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(3),
        );
        let disjoint = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(4),
            &Literal::new(5),
        );
        formula.vsids.activity[lower_overlap.get_index().unsigned_abs() as usize] = 2.0;
        formula.vsids.activity[higher_overlap.get_index().unsigned_abs() as usize] = 8.0;
        formula.vsids.activity[disjoint.get_index().unsigned_abs() as usize] = 4.0;

        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0)).unwrap();

        assert_eq!(replacement.len(), 4);
        assert!(replacement.get_literals().contains(&Literal::new(-2)));
        assert!(replacement.get_literals().contains(&Literal::new(6)));
        assert!(
            replacement
                .get_literals()
                .contains(&higher_overlap.negated())
        );
        assert!(replacement.get_literals().contains(&disjoint.negated()));
        assert!(
            !replacement
                .get_literals()
                .contains(&lower_overlap.negated())
        );
    }

    #[test]
    fn does_not_substitute_positive_inputs_or_locked_clauses() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 4], vec![-1, -2, 5]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        formula.get_clause_at_idx_mut(1).increment_lock_count();

        process(&mut formula, &mut logger, None).unwrap();

        assert!(!formula.is_clause_garbage(0));
        assert!(!formula.is_clause_garbage(1));
        assert_eq!(formula.clause_slots_len(), 5);
    }
}
