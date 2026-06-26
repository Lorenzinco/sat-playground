use fastbit::{BitRead, BitVec, BitWrite};
use std::time::Duration;

use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::ConflictLearnResult;
use crate::history::History;

pub fn find_1uip(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> ConflictLearnResult {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return ConflictLearnResult::Uip {
            clause: Clause::new(),
            backtrack_level: 0,
            minimized_literals: 0,
            minimization_time: Duration::ZERO,
        };
    }

    let mut seen = BitVec::<u64>::new(formula.assignment.len() + 1);
    let mut learned_lits = Vec::new();
    let mut path_count = 0;
    let mut current_clause_idx = Some(conflict_clause_index);
    let mut resolved_lit_idx = None;

    let level_data = &history.decision_levels[current_level];
    let mut trail_iter = level_data
        .get_implied_literals_rev()
        .chain(level_data.get_decision_literal().into_iter());

    loop {
        if let Some(clause_idx) = current_clause_idx {
            for lit in formula.get_clauses()[clause_idx].iter() {
                if resolved_lit_idx == Some(lit.get_index()) {
                    continue;
                }

                let var = lit.get_index().unsigned_abs() as usize;
                if !seen.test(var) {
                    seen.set(var);
                    let level = history
                        .get_literal_level(lit)
                        .unwrap_or(0);
                    if level == current_level {
                        path_count += 1;
                    } else {
                        learned_lits.push(lit.clone());
                    }
                }
            }
        }

        loop {
            if let Some(lit) = trail_iter.next() {
                let var = lit.get_index().unsigned_abs() as usize;
                if seen.test(var) {
                    resolved_lit_idx = Some(lit.get_index());
                    path_count -= 1;
                    current_clause_idx = level_data.get_reason(lit);
                    break;
                }
            } else {
                unreachable!("Trail is empty but path_count is > 0");
            }
        }

        if path_count == 0 {
            learned_lits.push(Literal::new(-resolved_lit_idx.unwrap()));
            break;
        }
    }

    let last_idx = learned_lits.len() - 1;
    learned_lits.swap(0, last_idx);

    let (minimized_lits, minimized_literals, minimization_time) =
        history.minimize_clause_literals(formula, learned_lits);
    let (backtrack_level, lbd) = history.clause_levels(&minimized_lits);

    ConflictLearnResult::Uip {
        clause: Clause::from_literals(minimized_lits, lbd),
        backtrack_level,
        minimized_literals,
        minimization_time,
    }
}
