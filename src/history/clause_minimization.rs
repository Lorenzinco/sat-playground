use std::time::Duration;
use std::time::Instant;

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;

#[derive(Default)]
pub(super) struct MinimizationScratch {
    seen: Vec<u32>,
    poisoned: Vec<u32>,
    stack: Vec<i32>,
    local_seen: Vec<usize>,
    epoch: u32,
}

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
        mut learned_lits: Vec<Literal>,
    ) -> (Vec<Literal>, usize, Duration) {
        let original_len = learned_lits.len();
        let start = Instant::now();

        if learned_lits.is_empty() {
            return (learned_lits, 0, start.elapsed());
        }

        let mut scratch = self.minimization_scratch.borrow_mut();
        let MinimizationScratch {
            seen,
            poisoned,
            stack,
            local_seen,
            epoch,
        } = &mut *scratch;
        seen.resize(formula.assignment.len(), 0);
        poisoned.resize(formula.assignment.len(), 0);
        *epoch = epoch.wrapping_add(1);
        if *epoch == 0 {
            seen.fill(0);
            poisoned.fill(0);
            *epoch = 1;
        }
        for lit in &learned_lits {
            seen[lit.get_index().unsigned_abs() as usize] = *epoch;
        }

        let mut kept = 1;
        for index in 1..original_len {
            let lit = learned_lits[index];
            let var = lit.get_index().unsigned_abs() as usize;
            if self.get_literal_level(&lit).unwrap_or(0) == 0 {
                continue;
            }
            stack.clear();
            stack.push(lit.get_index());
            local_seen.clear();
            let mut failed = false;
            while let Some(current_idx) = stack.pop() {
                let c_var = current_idx.unsigned_abs() as usize;
                if c_var != var && seen[c_var] == *epoch {
                    continue;
                }
                if poisoned[c_var] == *epoch {
                    failed = true;
                    break;
                }
                let current = Literal::new(current_idx);
                if self.get_literal_level(&current).unwrap_or(0) == 0 {
                    continue;
                }
                let Some(reason_idx) = self.get_reason(&current) else {
                    failed = true;
                    break;
                };
                if c_var != var {
                    seen[c_var] = *epoch;
                    local_seen.push(c_var);
                }
                for child in formula.get_clause_at_idx(reason_idx) {
                    if child.get_index().unsigned_abs() as usize != c_var {
                        stack.push(child.get_index());
                    }
                }
            }
            if failed {
                for &c_var in local_seen.iter() {
                    seen[c_var] = 0;
                    poisoned[c_var] = *epoch;
                }
                poisoned[var] = *epoch;
                learned_lits[kept] = lit;
                kept += 1;
            }
        }
        learned_lits.truncate(kept);
        (learned_lits, original_len - kept, start.elapsed())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minimization_reuses_buffers_after_failure_growth_and_epoch_wrap() {
        use std::collections::VecDeque;
        let mut formula = Formula::from_vec(vec![vec![-1, 2], vec![-2, 3]]);
        let decision = formula.add_literal();
        let mut history = History::new();
        formula.add_decision(&Literal::new(1), &mut history);
        assert!(
            formula
                .propagate_twl(&mut history, &mut VecDeque::from([Literal::new(1)]))
                .is_none()
        );
        formula.add_decision(&decision, &mut history);
        let failed = vec![decision.negated(), Literal::new(-3)];
        assert_eq!(
            history.minimize_clause_literals(&formula, failed.clone()).0,
            failed
        );
        let learned = vec![decision.negated(), Literal::new(-2), Literal::new(-1)];
        assert_eq!(
            history
                .minimize_clause_literals(&formula, learned.clone())
                .0,
            vec![decision.negated(), Literal::new(-1)]
        );
        let pointers = {
            let scratch = history.minimization_scratch.borrow();
            (
                scratch.seen.as_ptr(),
                scratch.poisoned.as_ptr(),
                scratch.stack.as_ptr(),
                scratch.local_seen.as_ptr(),
            )
        };
        history.minimization_scratch.borrow_mut().epoch = u32::MAX;
        assert_eq!(
            history.minimize_clause_literals(&formula, failed.clone()).0,
            failed
        );
        let scratch = history.minimization_scratch.borrow();
        assert_eq!(
            pointers,
            (
                scratch.seen.as_ptr(),
                scratch.poisoned.as_ptr(),
                scratch.stack.as_ptr(),
                scratch.local_seen.as_ptr()
            )
        );
        drop(scratch);
        for _ in 0..32 {
            formula.add_literal();
        }
        assert_eq!(
            history.minimize_clause_literals(&formula, learned).0,
            vec![decision.negated(), Literal::new(-1)]
        );
    }

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
        history.revert_last_decision(&mut crate::formula::assignment::Assignment::new(6));
        history.add_implication(&Literal::new(4), None);
        assert_eq!(history.clause_levels(&[pool[3], pool[4], pool[2]]), (1, 1));
    }

    #[test]
    fn clause_levels_keeps_scanning_for_backtrack_after_lbd_saturates() {
        let mut history = History::new();
        let literals: Vec<_> = (1..=i16::MAX as i32 + 2).map(Literal::new).collect();
        history.add_implication(&literals[0], None);
        for literal in literals.iter().skip(1) {
            history.add_decision(literal);
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
