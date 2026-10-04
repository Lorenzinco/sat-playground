use std::cell::RefMut;

use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::dip;
use crate::history::uip;
use crate::history::{ConflictLearnResult, History, ImplicationPoint};

const NO_VERTEX: u32 = u32::MAX;

#[derive(Default)]
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
    /// Per-vertex lower-level reason frontiers, before global seen deduplication.
    /// Unlike pred_index, lower_index has n + 1 entries (the UIP is empty).
    pub lower_literals: Vec<Literal>,
    pub lower_index: Vec<u32>,
}

pub(super) fn analyze_conflict(
    history: &History,
    formula: &mut Formula,
    conflict_clause_index: usize,
    implication_point: ImplicationPoint,
) -> ConflictLearnResult {
    let analyze = if matches!(implication_point, ImplicationPoint::DIP) {
        analyze_conflict_graph
    } else {
        analyze_uip
    };
    let Some(analysis) = analyze(history, formula, conflict_clause_index) else {
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

    for &clause_idx in &analysis.analyzed_clause_indices {
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

/// Epoch arrays are grown only when variables are added, not cleared per conflict.
#[derive(Default)]
pub(super) struct AnalysisScratch {
    analysis: ConflictAnalysis,
    seen: Vec<u64>,
    vertex_stamps: Vec<u64>,
    vertex_by_var: Vec<u32>,
    epoch: u64,
}

pub(super) fn analyze_conflict_graph<'a>(
    history: &'a History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> Option<RefMut<'a, ConflictAnalysis>> {
    analyze::<true>(history, formula, conflict_clause_index)
}

/// Retains resolved literals and clause occurrences for identical utility/use
/// accounting, but does not construct graph edges or variable-to-vertex maps.
pub(super) fn analyze_uip<'a>(
    history: &'a History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> Option<RefMut<'a, ConflictAnalysis>> {
    analyze::<false>(history, formula, conflict_clause_index)
}

fn analyze<'a, const GRAPH: bool>(
    history: &'a History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> Option<RefMut<'a, ConflictAnalysis>> {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return None;
    }
    let mut scratch = history.analysis_scratch.borrow_mut();
    let AnalysisScratch {
        analysis,
        seen,
        vertex_stamps,
        vertex_by_var,
        epoch,
    } = &mut *scratch;
    *epoch = epoch.wrapping_add(1);
    if *epoch == 0 {
        seen.fill(0);
        vertex_stamps.fill(0);
        *epoch = 1;
    }
    let stamp = *epoch;
    seen.resize(formula.assignment.len() + 1, 0);
    analysis.current_level = current_level;
    analysis.uip_clause_literals.clear();
    analysis.analyzed_clause_indices.clear();
    analysis.graph_literals.clear();
    analysis.graph_literals.push(0);
    analysis.predecessors.clear();
    analysis.pred_index.clear();
    analysis.lower_literals.clear();
    analysis.lower_index.clear();

    let trail = history.level_trail(current_level);
    let mut trail_cursor = trail.len();
    let mut path_count = 0usize;
    let mut current_clause = conflict_clause_index;
    let mut resolved_var = None;
    loop {
        if GRAPH {
            analysis
                .pred_index
                .push(u32::try_from(analysis.predecessors.len()).ok()?);
            analysis
                .lower_index
                .push(u32::try_from(analysis.lower_literals.len()).ok()?);
        }
        analysis.analyzed_clause_indices.push(current_clause);
        for literal in formula.get_clause_at_idx(current_clause).iter() {
            let var = literal.get_index().unsigned_abs() as usize;
            if resolved_var == Some(var) {
                continue;
            }
            let literal_level = history.get_literal_level(literal)?;
            if literal_level == 0 {
                continue;
            }
            if GRAPH {
                if literal_level == current_level {
                    // Raw unsigned variables are remapped in this same buffer.
                    analysis.predecessors.push(u32::try_from(var).ok()?);
                } else {
                    analysis.lower_literals.push(*literal);
                }
            }
            if *seen.get(var)? == stamp {
                continue;
            }
            seen[var] = stamp;
            if literal_level == current_level {
                path_count += 1;
            } else {
                analysis.uip_clause_literals.push(*literal);
            }
        }
        let propagated = loop {
            trail_cursor = trail_cursor.checked_sub(1)?;
            let literal = trail.get(trail_cursor)?;
            if *seen.get(literal.get_index().unsigned_abs() as usize)? == stamp {
                break literal;
            }
        };
        let propagated_var = propagated.get_index().unsigned_abs() as usize;
        seen[propagated_var] = 0;
        path_count = path_count.checked_sub(1)?;
        analysis.graph_literals.push(propagated.get_index());
        if path_count == 0 {
            analysis.uip_clause_literals.push(propagated.negated());
            if GRAPH {
                analysis
                    .pred_index
                    .push(u32::try_from(analysis.predecessors.len()).ok()?);
                let end = u32::try_from(analysis.lower_literals.len()).ok()?;
                analysis.lower_index.extend([end, end]);
            }
            break;
        }
        resolved_var = Some(propagated_var);
        current_clause = history.get_reason(propagated)?;
    }
    let asserting = analysis.uip_clause_literals.len().checked_sub(1)?;
    analysis.uip_clause_literals.swap(0, asserting);

    if GRAPH {
        vertex_stamps.resize(seen.len(), 0);
        vertex_by_var.resize(seen.len(), NO_VERTEX);
        for (vertex, &literal) in analysis.graph_literals.iter().enumerate().skip(1) {
            let var = literal.unsigned_abs() as usize;
            if *vertex_stamps.get(var)? == stamp {
                return None;
            }
            vertex_stamps[var] = stamp;
            vertex_by_var[var] = u32::try_from(vertex).ok()?;
        }
        // Validate the strict reverse-topological invariant while remapping;
        // DIP may therefore use a trusted CSR bottleneck entry point.
        for vertex in 0..analysis.graph_literals.len() - 1 {
            let start = analysis.pred_index[vertex] as usize;
            let end = analysis.pred_index[vertex + 1] as usize;
            for predecessor in &mut analysis.predecessors[start..end] {
                let var = *predecessor as usize;
                if *vertex_stamps.get(var)? != stamp {
                    return None;
                }
                let mapped = vertex_by_var[var];
                if mapped as usize <= vertex {
                    return None;
                }
                *predecessor = mapped;
            }
        }
    }
    Some(RefMut::map(scratch, |scratch| &mut scratch.analysis))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_free_matches_graph_and_frontiers_preserve_shared_lower_literals() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 3], vec![-1, -2, -3]]);
        let mut history = History::new();
        formula.add_decision(&Literal::new(1), &mut history);
        formula.add_decision(&Literal::new(2), &mut history);
        formula.assign_implication(Literal::new(3), &mut history, Some(0));
        let (learned, resolved, clauses) = {
            let analysis = analyze_conflict_graph(&history, &formula, 1).unwrap();
            assert_eq!(analysis.graph_literals, vec![0, 3, 2]);
            assert_eq!(analysis.predecessors, vec![2, 1, 2]);
            assert_eq!(analysis.pred_index, vec![0, 2, 3]);
            assert_eq!(
                analysis.lower_literals,
                vec![Literal::new(-1), Literal::new(-1)]
            );
            assert_eq!(analysis.lower_index, vec![0, 1, 2, 2]);
            (
                analysis.uip_clause_literals.clone(),
                analysis.graph_literals.clone(),
                analysis.analyzed_clause_indices.clone(),
            )
        };
        for _ in 0..2 {
            let analysis = analyze_uip(&history, &formula, 1).unwrap();
            assert_eq!(analysis.uip_clause_literals, learned);
            assert_eq!(analysis.graph_literals, resolved);
            assert_eq!(analysis.analyzed_clause_indices, clauses);
            assert!(analysis.predecessors.is_empty());
            assert!(analysis.pred_index.is_empty());
            assert!(analysis.lower_literals.is_empty());
            assert!(analysis.lower_index.is_empty());
        }
        let analysis = analyze_conflict_graph(&history, &formula, 1).unwrap();
        assert_eq!(analysis.uip_clause_literals, learned);
        assert_eq!(analysis.lower_index, vec![0, 1, 2, 2]);
    }

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
