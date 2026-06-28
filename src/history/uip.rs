use std::time::Duration;

use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::history::conflict_analysis::{ConflictAnalysis, analyze_conflict_graph};
use crate::history::{ConflictLearnResult, History};

pub fn find_1uip(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> ConflictLearnResult {
    let Some(analysis) = analyze_conflict_graph(history, formula, conflict_clause_index) else {
        return empty_result();
    };

    learn_from_analysis(&analysis, history, formula)
}

pub(super) fn learn_from_analysis(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
) -> ConflictLearnResult {
    let (minimized_lits, minimized_literals, minimization_time) =
        history.minimize_clause_literals(formula, analysis.uip_clause_literals.clone());
    let (backtrack_level, lbd) = history.clause_levels(&minimized_lits);

    ConflictLearnResult::Uip {
        clause: Clause::from_literals(minimized_lits, lbd),
        backtrack_level,
        minimized_literals,
        minimization_time,
    }
}

pub(super) fn empty_result() -> ConflictLearnResult {
    ConflictLearnResult::Uip {
        clause: Clause::new(),
        backtrack_level: 0,
        minimized_literals: 0,
        minimization_time: Duration::ZERO,
    }
}
