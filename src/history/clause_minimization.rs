use fastbit::{BitRead, BitVec, BitWrite};
use std::time::Duration;
use std::time::Instant;

use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;

impl History {
    pub fn clause_levels(&self, literals: &[Literal]) -> (usize, i64) {
        let levels = literals
            .iter()
            .filter_map(|lit| self.get_literal_and_level(lit).map(|(_, level)| level))
            .collect::<Vec<_>>();

        (
            levels.iter().skip(1).copied().max().unwrap_or(0),
            Clause::calculate_lbd(levels),
        )
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
            let (_, level) = self.get_literal_and_level(lit).unwrap_or((lit.clone(), 0));

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
                let (_, c_level) = self.get_literal_and_level(&current).unwrap_or((current, 0));
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

                for child in formula.get_clauses()[reason_idx].get_literals() {
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
