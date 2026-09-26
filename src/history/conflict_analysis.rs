use fastbit::{BitRead, BitVec, BitWrite};

use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::dip;
use crate::history::uip;
use crate::history::{ConflictLearnResult, History, ImplicationPoint};

const NO_VERTEX: u32 = u32::MAX;

pub(super) struct ConflictAnalysis {
    pub current_level: usize,
    pub uip_clause_literals: Vec<Literal>,
    pub analyzed_clause_indices: Vec<usize>,
    /// Assigned literals for graph vertices. Vertex 0 is the synthetic conflict
    /// and therefore uses the otherwise-invalid literal value 0.
    pub graph_literals: Vec<i32>,

    /// Flat predecessor CSR. The sink is vertex 0 and the first UIP is the
    /// final (source) vertex; every predecessor has a larger vertex ID.
    pub predecessors: Vec<u32>,
    pub pred_index: Vec<u32>,
}

pub(super) fn analyze_conflict(
    history: &History,
    formula: &mut Formula,
    conflict_clause_index: usize,
    implication_point: ImplicationPoint,
) -> ConflictLearnResult {
    let Some(analysis) = analyze_conflict_graph(history, formula, conflict_clause_index) else {
        formula.record_conflict_literal_utilities(std::iter::empty());
        if matches!(implication_point, ImplicationPoint::DIP) {
            formula.stats.dip_uip_fallbacks += 1;
        }
        return uip::empty_result();
    };
    let conflict_literals = analysis
        .graph_literals
        .iter()
        .copied()
        .skip(1)
        .map(|literal| Literal::new(literal).negated())
        .chain(analysis.uip_clause_literals.iter().copied());
    formula.record_conflict_literal_utilities(conflict_literals);

    // Preserve occurrences rather than deduplicating: a source can be visited
    // repeatedly. Read-only graph inspection helpers do not record solver uses.
    for &clause_idx in &analysis.analyzed_clause_indices {
        formula.record_ges_analysis_use(clause_idx);
    }

    let result = if matches!(implication_point, ImplicationPoint::DIP) {
        match dip::learn_from_analysis(&analysis, history, formula, conflict_clause_index) {
            Some(result) => result,
            None => {
                formula.stats.dip_uip_fallbacks += 1;
                uip::learn_from_analysis(&analysis, history, formula)
            }
        }
    } else {
        uip::learn_from_analysis(&analysis, history, formula)
    };

    for clause_idx in analysis.analyzed_clause_indices {
        let old_lbd = formula.get_clause_at_idx(clause_idx).lbd;
        if old_lbd <= 0 {
            continue;
        }

        let new_lbd = history.clause_lbd_bounded(
            formula.get_clause_at_idx(clause_idx).get_literals(),
            old_lbd,
        );
        let clause = formula.get_clause_at_idx_mut(clause_idx);
        clause.activity = Clause::MAX_ACTIVITY;
        if new_lbd > 0 && new_lbd < clause.lbd {
            clause.lbd = new_lbd;
        }
    }

    result
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

    let level = &history.decision_levels[current_level];
    let mut seen = BitVec::<u64>::new(formula.assignment.len() + 1);
    let mut learned_literals = Vec::new();
    let mut predecessor_literals = Vec::<i32>::new();
    let mut pred_index = Vec::<u32>::new();
    let mut graph_literals = vec![0];
    let mut analyzed_clause_indices = Vec::new();

    let mut path_count = 0usize;
    let mut current_clause = conflict_clause_index;
    let mut resolved_var = None;
    let mut trail_cursor = level.trail_len();

    loop {
        pred_index.push(u32::try_from(predecessor_literals.len()).ok()?);
        analyzed_clause_indices.push(current_clause);

        for literal in formula.get_clause_at_idx(current_clause).iter() {
            let var = literal.get_index().unsigned_abs() as usize;
            if resolved_var == Some(var) {
                continue;
            }

            let literal_level = history.get_literal_level(literal)?;
            if literal_level == 0 {
                continue;
            }

            if literal_level == current_level {
                predecessor_literals.push(literal.negated().get_index());
            }

            if seen.test(var) {
                continue;
            }
            seen.set(var);
            if literal_level == current_level {
                path_count += 1;
            } else {
                learned_literals.push(literal.clone());
            }
        }

        let (position, propagated) = loop {
            trail_cursor = trail_cursor.checked_sub(1)?;
            let literal = level.trail_literal(trail_cursor)?;
            if seen.test(literal.get_index().unsigned_abs() as usize) {
                break (trail_cursor, literal);
            }
        };

        let propagated_var = propagated.get_index().unsigned_abs() as usize;
        seen.reset(propagated_var);
        path_count = path_count.checked_sub(1)?;
        graph_literals.push(propagated.get_index());

        if path_count == 0 {
            learned_literals.push(propagated.negated());
            pred_index.push(u32::try_from(predecessor_literals.len()).ok()?);
            break;
        }

        resolved_var = Some(propagated_var);
        current_clause = level.trail_reason(position)?;
    }

    let asserting = learned_literals.len().checked_sub(1)?;
    learned_literals.swap(0, asserting);

    let mut vertex_by_var = vec![NO_VERTEX; formula.assignment.len()];
    for (vertex, &literal) in graph_literals.iter().enumerate().skip(1) {
        let var = literal.unsigned_abs() as usize;
        if var >= vertex_by_var.len() || vertex_by_var[var] != NO_VERTEX {
            return None;
        }
        vertex_by_var[var] = u32::try_from(vertex).ok()?;
    }

    let mut predecessors = Vec::with_capacity(predecessor_literals.len());
    for literal in predecessor_literals {
        let vertex = *vertex_by_var.get(literal.unsigned_abs() as usize)?;
        if vertex == NO_VERTEX {
            return None;
        }
        predecessors.push(vertex);
    }

    Some(ConflictAnalysis {
        current_level,
        uip_clause_literals: learned_literals,
        analyzed_clause_indices,
        graph_literals,
        predecessors,
        pred_index,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn analyzed_lbd_only_improves_and_activity_refreshes_even_at_threshold() {
        for point in [ImplicationPoint::UIP, ImplicationPoint::DIP] {
            for old_lbd in [-1, 0, 1, 2, 3, i16::MAX] {
                let mut formula = Formula::from_vec(vec![vec![-1, 2], vec![-1, -2, -3]]);
                let mut history = History::new();
                formula.assign_implication(Literal::new(3), &mut history, None);
                formula.add_decision(&Literal::new(1), &mut history);
                formula.assign_implication(Literal::new(2), &mut history, Some(0));
                for idx in 0..2 {
                    let clause = formula.get_clause_at_idx_mut(idx);
                    clause.lbd = old_lbd;
                    clause.activity = 0;
                }
                history.analyze_conflict(&mut formula, 1, point);
                for (idx, exact_lbd) in [(0, 1), (1, 2)] {
                    let clause = formula.get_clause_at_idx(idx);
                    assert_eq!(
                        clause.lbd,
                        if old_lbd > 0 {
                            old_lbd.min(exact_lbd)
                        } else {
                            old_lbd
                        }
                    );
                    assert_eq!(
                        clause.activity,
                        if old_lbd > 0 { Clause::MAX_ACTIVITY } else { 0 }
                    );
                }
            }
        }
    }

    #[test]
    fn ges_analysis_counts_conflict_and_source_occurrences_for_uip_and_dip() {
        for point in [ImplicationPoint::UIP, ImplicationPoint::DIP] {
            let mut formula = Formula::from_vec(vec![vec![-1, 2], vec![-1, -2]]);
            let mut history = History::new();
            formula.add_decision(&Literal::new(1), &mut history);
            formula.assign_implication(Literal::new(2), &mut history, Some(0));
            // Mark after setup to isolate analysis from implication-use accounting.
            for idx in 0..2 {
                formula.get_clause_at_idx_mut(idx).ges_generated = true;
            }
            history.analyze_conflict(&mut formula, 1, point);
            assert_eq!(formula.stats.ges_replacement_analysis_uses, 2);
            assert_eq!(formula.stats.ges_replacement_reason_uses, 0);
            assert_eq!(formula.extensions.literal_utility(&Literal::new(-1)), 1.0);
            assert_eq!(formula.extensions.literal_utility(&Literal::new(-2)), 1.0);
            assert_eq!(formula.extensions.literal_utility(&Literal::new(2)), 1.0);
            assert_eq!(formula.extensions.literal_utility(&Literal::new(1)), 0.0);
            assert!(formula.get_clause_at_idx(0).ges_used);
            assert!(formula.get_clause_at_idx(1).ges_used);
            history.analyze_conflict(&mut formula, 1, point);
            assert_eq!(formula.stats.ges_replacement_analysis_uses, 4);
            formula.revert_last_decision(&mut history);
            formula.delete_clauses::<std::io::Empty>(&[0, 1], &mut None);
            assert_eq!(formula.stats.ges_replacements_deleted_unused, 0);
        }
    }
}
