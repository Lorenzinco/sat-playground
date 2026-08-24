use fastbit::{BitRead, BitVec, BitWrite};
use std::time::Duration;
use std::time::Instant;

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;

impl History {
    pub fn clause_levels(&self, literals: &[Literal]) -> (usize, i16) {
        let mut counter = self.lbd_scratch.borrow_mut();
        counter.begin();
        let mut first_available = true;
        let mut backtrack_level = 0;
        for level in literals
            .iter()
            .filter_map(|lit| self.get_literal_level(lit))
        {
            counter.insert(level);
            // Skip the first assigned literal, not necessarily literals[0].
            if first_available {
                first_available = false;
            } else {
                backtrack_level = backtrack_level.max(level);
            }
        }
        (backtrack_level, counter.lbd())
    }

    pub fn minimize_clause_literals(
        &self,
        formula: &Formula,
        learned_lits: Vec<Literal>,
    ) -> (Vec<Literal>, usize, Duration) {
        let original_len = learned_lits.len();
        let start = Instant::now();

        if learned_lits.is_empty() {
            return (learned_lits, 0, start.elapsed());
        }

        let mut min_seen = BitVec::<u64>::new(formula.assignment.len() + 1);
        for lit in &learned_lits {
            min_seen.set(lit.get_index().abs() as usize);
        }

        let mut poisoned = BitVec::<u64>::new(formula.assignment.len() + 1);
        let mut minimized_lits = vec![learned_lits[0].clone()];

        for lit in learned_lits.iter().skip(1) {
            let var = lit.get_index().abs() as usize;
            let level = self.get_literal_level(lit).unwrap_or(0);

            if level == 0 {
                continue;
            }

            let mut stack = vec![lit.get_index()];
            let mut local_seen = Vec::new();
            let mut failed = false;

            while let Some(current_idx) = stack.pop() {
                let c_var = current_idx.unsigned_abs() as usize;

                if c_var != var && min_seen.test(c_var) {
                    continue;
                }

                if poisoned.test(c_var) {
                    failed = true;
                    break;
                }

                let current = Literal::new(current_idx);
                let c_level = self.get_literal_level(&current).unwrap_or(0);
                if c_level == 0 {
                    continue;
                }

                let Some(reason_idx) =
                    self.decision_levels[c_level].get_reason(&Literal::new(current_idx))
                else {
                    failed = true;
                    break;
                };

                if c_var != var {
                    min_seen.set(c_var);
                    local_seen.push(c_var);
                }

                for child in formula.get_clause_at_idx(reason_idx).get_literals() {
                    let child_var = child.get_index().unsigned_abs() as usize;
                    if child_var != c_var {
                        stack.push(child.get_index());
                    }
                }
            }

            if failed {
                for &c_var in &local_seen {
                    min_seen.reset(c_var);
                    poisoned.set(c_var);
                }
                poisoned.set(var);
                minimized_lits.push(lit.clone());
            }
        }

        let removed = original_len.saturating_sub(minimized_lits.len());
        (minimized_lits, removed, start.elapsed())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clause_levels_matches_previous_algorithm_for_filtered_and_repeated_levels() {
        let mut history = History::new();
        history.add_implication(&Literal::new(1), None);
        history.add_decision(&Literal::new(2));
        history.add_decision(&Literal::new(3));
        history.add_implication(&Literal::new(4), None);
        let pool = [5, 1, -2, 3, -4, -5].map(Literal::new);
        assert_eq!(history.clause_levels(&[]), (0, 0));
        assert_eq!(history.clause_levels(&[pool[0], pool[3], pool[2]]), (1, 2));
        for encoded in 0..6usize.pow(4) {
            let mut value = encoded;
            let literals: Vec<_> = (0..4)
                .map(|_| {
                    let literal = pool[value % pool.len()].clone();
                    value /= pool.len();
                    literal
                })
                .collect();
            let levels: Vec<_> = literals
                .iter()
                .filter_map(|literal| history.get_literal_level(literal))
                .collect();
            let expected = (
                levels.iter().skip(1).copied().max().unwrap_or(0),
                crate::formula::clause::Clause::calculate_lbd(levels.iter().copied()),
            );
            assert_eq!(history.clause_levels(&literals), expected);
            for limit in [1, 2, 3, i16::MAX] {
                assert_eq!(
                    history.clause_lbd_bounded(&literals, limit),
                    expected.1.min(limit)
                );
            }
            // A bounded operation must not leave marks for the next full operation.
            assert_eq!(history.clause_levels(&literals), expected);
        }
        history
            .implication_levels_indexes
            .unset_level(&Literal::new(3));
        history
            .implication_levels_indexes
            .set_level(&Literal::new(4), 1);
        assert_eq!(history.clause_levels(&[pool[3], pool[4], pool[2]]), (1, 1));
    }

    #[test]
    fn clause_levels_keeps_scanning_for_backtrack_after_lbd_saturates() {
        let mut history = History::new();
        let literals: Vec<_> = (1..=i16::MAX as i32 + 2).map(Literal::new).collect();
        for (level, literal) in literals.iter().enumerate() {
            history.implication_levels_indexes.set_level(literal, level);
        }
        assert_eq!(
            history.clause_levels(&literals),
            (literals.len() - 1, i16::MAX)
        );
    }

    #[test]
    fn clause_levels_ignores_first_literal_for_backtrack_level() {
        let mut history = History::new();
        let a = Literal::new(1);
        let b = Literal::new(2);
        let c = Literal::new(3);

        history.add_decision(&a);
        history.add_decision(&b);
        history.add_implication(&c, None);

        let (backtrack_level, lbd) = history.clause_levels(&[c, b, a]);

        assert_eq!(backtrack_level, 2);
        assert_eq!(lbd, 2);
    }
}
