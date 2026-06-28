use fastbit::{BitRead, BitVec, BitWrite};

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::dip;
use crate::history::uip;
use crate::history::{ConflictLearnResult, History, ImplicationPoint};

pub(super) struct ConflictAnalysis {
    pub current_level: usize,
    pub uip_clause_literals: Vec<Literal>,
    pub trail: Vec<Literal>,
    pub first_uip_pos: usize,
    pub successors: Vec<Vec<usize>>,
    pub present: Vec<bool>,
    pub reason_of: Vec<Option<usize>>,
    pub pos_of: Vec<Option<usize>>,
}

pub(super) fn analyze_conflict(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
    implication_point: ImplicationPoint,
) -> ConflictLearnResult {
    let Some(analysis) = analyze_conflict_graph(history, formula, conflict_clause_index) else {
        return uip::empty_result();
    };

    if matches!(implication_point, ImplicationPoint::DIP) {
        if let Some(result) =
            dip::learn_from_analysis(&analysis, history, formula, conflict_clause_index)
        {
            return result;
        }
    }

    uip::learn_from_analysis(&analysis, history, formula)
}

pub(super) fn analyze_conflict_graph(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> Option<ConflictAnalysis> {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return None;
    }

    let (trail, pos_of, reason_of) = current_level_context(history, formula);
    let conflict_idx = trail.len();
    let mut successors = vec![Vec::new(); conflict_idx + 1];
    let mut present = vec![false; conflict_idx + 1];
    present[conflict_idx] = true;

    let mut seen = BitVec::<u64>::new(formula.assignment.len() + 1);
    let mut learned_lits = Vec::new();
    let mut path_count = 0;
    let mut current_clause_idx = Some(conflict_clause_index);
    let mut resolved_lit_idx = None;
    let mut current_node_idx = conflict_idx;

    let level_data = &history.decision_levels[current_level];
    let mut trail_iter = level_data
        .get_implied_literals_rev()
        .chain(level_data.get_decision_literal().into_iter());

    let first_uip_pos = loop {
        if let Some(clause_idx) = current_clause_idx {
            for lit in formula.get_clauses()[clause_idx].iter() {
                if resolved_lit_idx == Some(lit.get_index()) {
                    continue;
                }

                let pred = lit.negated();
                if let Some(pred_idx) = pos_of
                    .get(pred.get_unsigned_index() as usize)
                    .copied()
                    .flatten()
                {
                    successors[pred_idx].push(current_node_idx);
                    present[pred_idx] = true;
                }

                let var = lit.get_index().unsigned_abs() as usize;
                if !seen.test(var) {
                    seen.set(var);
                    let level = history.get_literal_level(lit).unwrap_or(0);
                    if level == current_level {
                        path_count += 1;
                    } else {
                        learned_lits.push(lit.clone());
                    }
                }
            }
        }

        loop {
            let lit = trail_iter
                .next()
                .expect("Trail is empty but path_count is > 0");
            let var = lit.get_index().unsigned_abs() as usize;
            if seen.test(var) {
                resolved_lit_idx = Some(lit.get_index());
                current_node_idx = pos_of[lit.get_unsigned_index() as usize]?;
                present[current_node_idx] = true;
                path_count -= 1;
                current_clause_idx = level_data.get_reason(lit);
                break;
            }
        }

        if path_count == 0 {
            learned_lits.push(Literal::new(-resolved_lit_idx?));
            break current_node_idx;
        }
    };

    let last_idx = learned_lits.len() - 1;
    learned_lits.swap(0, last_idx);

    Some(ConflictAnalysis {
        current_level,
        uip_clause_literals: learned_lits,
        trail,
        first_uip_pos,
        successors,
        present,
        reason_of,
        pos_of,
    })
}

fn current_level_context(
    history: &History,
    formula: &Formula,
) -> (Vec<Literal>, Vec<Option<usize>>, Vec<Option<usize>>) {
    let level = &history.decision_levels[history.get_decision_level()];

    let mut trail = Vec::new();
    let mut pos_of = vec![None; formula.assignment.len() * 2];
    let mut reason_of = Vec::new();

    if let Some(decision) = level.get_decision_literal() {
        pos_of[decision.get_unsigned_index() as usize] = Some(trail.len());
        trail.push(decision.clone());
        reason_of.push(None);
    }

    for lit in level.implied_literals_iter() {
        pos_of[lit.get_unsigned_index() as usize] = Some(trail.len());
        trail.push(lit.clone());
        reason_of.push(level.get_reason(lit));
    }

    (trail, pos_of, reason_of)
}
