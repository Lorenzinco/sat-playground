use fastbit::{BitRead, BitVec, BitWrite};

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::dip;
use crate::history::uip;
use crate::history::{ConflictLearnResult, History, ImplicationPoint};

const NO_VERTEX: u32 = u32::MAX;

pub(super) struct ConflictAnalysis {
    pub current_level: usize,
    pub uip_clause_literals: Vec<Literal>,
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

    let level = &history.decision_levels[current_level];
    let mut seen = BitVec::<u64>::new(formula.assignment.len() + 1);
    let mut learned_literals = Vec::new();
    let mut predecessor_literals = Vec::<i32>::new();
    let mut pred_index = Vec::<u32>::new();
    let mut graph_literals = vec![0];

    let mut path_count = 0usize;
    let mut current_clause = conflict_clause_index;
    let mut resolved_var = None;
    let mut trail_cursor = level.trail_len();

    loop {
        pred_index.push(u32::try_from(predecessor_literals.len()).ok()?);

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
        graph_literals,
        predecessors,
        pred_index,
    })
}
