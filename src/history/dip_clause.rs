use crate::formula::literal::Literal;
use crate::history::History;
use crate::history::conflict_analysis::ConflictAnalysis;

#[derive(Default)]
pub(super) struct ExtractionScratch {
    vertex_marks: Vec<u64>,
    literal_marks: Vec<u64>,
    epoch: u64,
    stack: Vec<u32>,
    output: Vec<Literal>,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum ExtractionRejection {
    InvalidGraph,
    Lbd,
}

pub(super) fn graph_pair(
    analysis: &ConflictAnalysis,
    vertices: (u32, u32),
) -> Option<(Literal, Literal)> {
    let literal = |vertex: u32| {
        let raw = *analysis.graph_literals.get(vertex as usize)?;
        (raw != 0).then(|| Literal::new(raw))
    };
    let a = literal(vertices.0)?;
    let b = literal(vertices.1)?;
    (a.get_index().unsigned_abs() != b.get_index().unsigned_abs()).then_some((a, b))
}

/// Every post-DIP region includes vertex zero's lower frontier. Rejecting two
/// levels here is independent of pair choice and requires no bottleneck search.
pub(super) fn conflict_frontier_has_two_levels(
    analysis: &ConflictAnalysis,
    history: &History,
) -> Option<bool> {
    let start = *analysis.lower_index.first()? as usize;
    let end = *analysis.lower_index.get(1)? as usize;
    let mut first = None;
    for literal in analysis.lower_literals.get(start..end)? {
        let level = history.get_literal_level(literal)?;
        if level == 0 {
            continue;
        }
        if level >= analysis.current_level {
            return None;
        }
        if first.is_some_and(|previous| previous != level) {
            return Some(true);
        }
        first = Some(level);
    }
    Some(false)
}

pub(super) fn extract_with_scratch(
    analysis: &ConflictAnalysis,
    history: &History,
    pair: (u32, u32),
    scratch: &mut ExtractionScratch,
) -> Result<Vec<Literal>, ExtractionRejection> {
    use ExtractionRejection::{InvalidGraph, Lbd};
    let n = analysis.graph_literals.len();
    if graph_pair(analysis, pair).is_none()
        || analysis.pred_index.len() != n
        || analysis.lower_index.len() != n + 1
        || n < 2
    {
        return Err(InvalidGraph);
    }
    scratch.epoch = scratch.epoch.wrapping_add(1);
    if scratch.epoch == 0 {
        scratch.vertex_marks.fill(0);
        scratch.literal_marks.fill(0);
        scratch.epoch = 1;
    }
    let epoch = scratch.epoch;
    scratch.vertex_marks.resize(n, 0);
    scratch.stack.clear();
    scratch.output.clear();
    scratch.stack.push(0);
    scratch.vertex_marks[0] = epoch;
    let mut reached = [false; 2];
    let mut first_level = None;

    while let Some(vertex) = scratch.stack.pop() {
        if vertex == pair.0 {
            reached[0] = true;
            continue;
        }
        if vertex == pair.1 {
            reached[1] = true;
            continue;
        }
        let vertex = vertex as usize;
        // Reaching the source means the supplied pair does not separate it
        // from the conflict. Never resolve the first UIP's reason.
        if vertex == n - 1 {
            return Err(InvalidGraph);
        }
        let start = analysis.lower_index[vertex] as usize;
        let end = analysis.lower_index[vertex + 1] as usize;
        for literal in analysis
            .lower_literals
            .get(start..end)
            .ok_or(InvalidGraph)?
        {
            let level = history.get_literal_level(literal).ok_or(InvalidGraph)?;
            if level == 0 {
                continue;
            }
            if level >= analysis.current_level {
                return Err(InvalidGraph);
            }
            // Abort at the second distinct nonroot level, without finishing
            // this frontier or visiting another graph vertex.
            if first_level.is_some_and(|previous| previous != level) {
                return Err(Lbd);
            }
            first_level = Some(level);
            let variable = literal.get_index().unsigned_abs() as usize;
            if variable >= scratch.literal_marks.len() {
                scratch.literal_marks.resize(variable + 1, 0);
            }
            if scratch.literal_marks[variable] != epoch {
                scratch.literal_marks[variable] = epoch;
                scratch.output.push(*literal);
            }
        }
        let start = analysis.pred_index[vertex] as usize;
        let end = analysis.pred_index[vertex + 1] as usize;
        for &pred in analysis
            .predecessors
            .get(start..end)
            .ok_or(InvalidGraph)?
            .iter()
            .rev()
        {
            let pred_index = pred as usize;
            if pred_index <= vertex || pred_index >= n {
                return Err(InvalidGraph);
            }
            if scratch.vertex_marks[pred_index] != epoch {
                scratch.vertex_marks[pred_index] = epoch;
                scratch.stack.push(pred);
            }
        }
    }
    if !reached[0] || !reached[1] {
        return Err(InvalidGraph);
    }
    // The returned clause must own its literals; cloning retains the reusable
    // output buffer's capacity for subsequent conflicts.
    Ok(scratch.output.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (History, ConflictAnalysis) {
        let mut history = History::new();
        for variable in 1..=3 {
            history.add_decision(&Literal::new(variable));
        }
        let analysis = ConflictAnalysis {
            current_level: 3,
            graph_literals: vec![0, 4, 5, 6],
            predecessors: vec![1, 2, 3, 3],
            pred_index: vec![0, 2, 3, 4],
            // Both selected vertices have lower reasons that must not be read.
            lower_literals: vec![Literal::new(-1), Literal::new(-1), Literal::new(-2)],
            lower_index: vec![0, 1, 2, 3, 3],
            ..ConflictAnalysis::default()
        };
        (history, analysis)
    }

    #[test]
    fn selected_pair_stops_before_its_lower_frontiers_and_scratch_is_reusable() {
        let (history, mut analysis) = fixture();
        let mut scratch = ExtractionScratch::default();
        let clause = extract_with_scratch(&analysis, &history, (1, 2), &mut scratch).unwrap();
        assert_eq!(clause, vec![Literal::new(-1)]);
        analysis.lower_literals.clear();
        analysis.lower_index.fill(0);
        let clause = extract_with_scratch(&analysis, &history, (1, 2), &mut scratch).unwrap();
        assert!(clause.is_empty());
    }

    #[test]
    fn second_distinct_lower_level_aborts_immediately() {
        let (history, mut analysis) = fixture();
        analysis.lower_literals = vec![Literal::new(-1), Literal::new(-2), Literal::new(-3)];
        analysis.lower_index = vec![0, 3, 3, 3, 3];
        assert_eq!(
            conflict_frontier_has_two_levels(&analysis, &history),
            Some(true)
        );
        let mut scratch = ExtractionScratch::default();
        assert!(matches!(
            extract_with_scratch(&analysis, &history, (1, 2), &mut scratch),
            Err(ExtractionRejection::Lbd)
        ));
        // The third (invalid current-level) literal was never inspected.
        assert_eq!(scratch.output, vec![Literal::new(-1)]);
    }

    #[test]
    fn second_level_in_post_region_is_an_lbd_rejection() {
        let (history, mut analysis) = fixture();
        analysis.graph_literals.push(7);
        analysis.predecessors = vec![1, 2, 3, 4, 4];
        analysis.pred_index = vec![0, 2, 3, 4, 5];
        analysis.lower_literals = vec![Literal::new(-1), Literal::new(-2)];
        analysis.lower_index = vec![0, 1, 2, 2, 2, 2];
        assert_eq!(
            conflict_frontier_has_two_levels(&analysis, &history),
            Some(false)
        );
        let mut scratch = ExtractionScratch::default();
        assert!(matches!(
            extract_with_scratch(&analysis, &history, (2, 3), &mut scratch),
            Err(ExtractionRejection::Lbd)
        ));
    }

    #[test]
    fn lower_frontiers_deduplicate_variables() {
        let (history, mut analysis) = fixture();
        analysis.lower_literals = vec![Literal::new(-1), Literal::new(-1)];
        analysis.lower_index = vec![0, 2, 2, 2, 2];
        let mut scratch = ExtractionScratch::default();
        let clause = extract_with_scratch(&analysis, &history, (1, 2), &mut scratch).unwrap();
        assert_eq!(clause, vec![Literal::new(-1)]);
    }
}
