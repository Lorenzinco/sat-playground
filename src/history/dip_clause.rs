use fastbit::{BitRead, BitVec, BitWrite};

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::history::conflict_analysis::ConflictAnalysis;

pub(super) struct DipClause {
    pub post: Vec<Literal>,
    pub post_lbd: i64,
}

pub(super) fn extract(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
    dip_vertices: (u32, u32),
) -> Option<(Literal, Literal, DipClause)> {
    let dip_a = graph_literal(analysis, dip_vertices.0)?;
    let dip_b = graph_literal(analysis, dip_vertices.1)?;
    if dip_a.get_index().unsigned_abs() == dip_b.get_index().unsigned_abs() {
        return None;
    }

    let (post, post_levels) = extract_post(
        analysis,
        history,
        formula,
        conflict_clause_index,
        &dip_a,
        &dip_b,
    )?;

    Some((
        dip_a,
        dip_b,
        DipClause {
            post,
            post_lbd: post_levels.len() as i64,
        },
    ))
}

fn graph_literal(analysis: &ConflictAnalysis, vertex: u32) -> Option<Literal> {
    let raw = *analysis.graph_literals.get(vertex as usize)?;
    (raw != 0).then(|| Literal::new(raw))
}

fn extract_post(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
    dip_a: &Literal,
    dip_b: &Literal,
) -> Option<(Vec<Literal>, Vec<usize>)> {
    let level = &history.decision_levels[analysis.current_level];
    let mut seen = BitVec::<u64>::new(formula.assignment.len() + 1);
    let mut lower_literals = Vec::new();
    let mut lower_levels = Vec::new();
    let mut current_clause = conflict_clause_index;
    let mut resolved_var = None;
    let mut trail_cursor = level.trail_len();
    let dip_vars = [
        dip_a.get_index().unsigned_abs() as usize,
        dip_b.get_index().unsigned_abs() as usize,
    ];
    let mut reached = [false; 2];

    loop {
        collect_clause_frontier(
            formula,
            history,
            analysis.current_level,
            current_clause,
            resolved_var,
            &mut seen,
            &mut lower_literals,
            &mut lower_levels,
        )?;

        loop {
            trail_cursor = trail_cursor.checked_sub(1)?;
            let literal = level.trail_literal(trail_cursor)?;
            let var = literal.get_index().unsigned_abs() as usize;
            if !seen.test(var) {
                continue;
            }
            seen.reset(var);

            if var == dip_vars[0] {
                reached[0] = true;
            } else if var == dip_vars[1] {
                reached[1] = true;
            } else {
                resolved_var = Some(var);
                current_clause = level.trail_reason(trail_cursor)?;
                break;
            }

            if reached[0] && reached[1] {
                return Some((lower_literals, lower_levels));
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_clause_frontier(
    formula: &Formula,
    history: &History,
    current_level: usize,
    clause_index: usize,
    resolved_var: Option<usize>,
    seen: &mut BitVec<u64>,
    lower_literals: &mut Vec<Literal>,
    lower_levels: &mut Vec<usize>,
) -> Option<()> {
    for literal in formula.get_clauses()[clause_index].iter() {
        let var = literal.get_index().unsigned_abs() as usize;
        if resolved_var == Some(var) || seen.test(var) {
            continue;
        }

        let level = history.get_literal_level(literal)?;
        if level == 0 {
            continue;
        }

        seen.set(var);
        if level < current_level {
            lower_literals.push(literal.clone());
            push_level(lower_levels, level);
        }
    }
    Some(())
}

fn push_level(levels: &mut Vec<usize>, level: usize) {
    if !levels.contains(&level) {
        levels.push(level);
    }
}
