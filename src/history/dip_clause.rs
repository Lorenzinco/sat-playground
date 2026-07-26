use fastbit::{BitRead, BitVec, BitWrite};

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::history::conflict_analysis::ConflictAnalysis;

pub(super) struct DipClauses {
    pub pre: Vec<Literal>,
    pub post: Vec<Literal>,
    pub pre_lbd: i64,
    pub post_lbd: i64,
}

pub(super) fn extract(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
    dip_vertices: (u32, u32),
) -> Option<(Literal, Literal, DipClauses)> {
    let dip_a = graph_literal(analysis, dip_vertices.0)?;
    let dip_b = graph_literal(analysis, dip_vertices.1)?;
    if dip_a.get_index().unsigned_abs() == dip_b.get_index().unsigned_abs() {
        return None;
    }

    let dip_a_position = graph_position(analysis, dip_vertices.0)?;
    let dip_b_position = graph_position(analysis, dip_vertices.1)?;
    let (post, post_levels) = extract_post(
        analysis,
        history,
        formula,
        conflict_clause_index,
        &dip_a,
        &dip_b,
    )?;
    let (pre, pre_levels) = extract_pre(
        analysis,
        history,
        formula,
        &dip_a,
        dip_a_position,
        &dip_b,
        dip_b_position,
    )?;

    let pre_lbd = pre_levels.len() + 1;
    Some((
        dip_a,
        dip_b,
        DipClauses {
            pre,
            post,
            pre_lbd: pre_lbd as i64,
            post_lbd: post_levels.len() as i64,
        },
    ))
}

fn graph_literal(analysis: &ConflictAnalysis, vertex: u32) -> Option<Literal> {
    let raw = *analysis.graph_literals.get(vertex as usize)?;
    (raw != 0).then(|| Literal::new(raw))
}

fn graph_position(analysis: &ConflictAnalysis, vertex: u32) -> Option<usize> {
    let position = *analysis.trail_positions.get(vertex as usize)?;
    (position != u32::MAX).then_some(position as usize)
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

fn extract_pre(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    dip_a: &Literal,
    dip_a_position: usize,
    dip_b: &Literal,
    dip_b_position: usize,
) -> Option<(Vec<Literal>, Vec<usize>)> {
    let level = &history.decision_levels[analysis.current_level];
    let mut seen = BitVec::<u64>::new(formula.assignment.len() + 1);
    seen.set(dip_a.get_index().unsigned_abs() as usize);
    seen.set(dip_b.get_index().unsigned_abs() as usize);

    let mut lower_literals = Vec::new();
    let mut lower_levels = Vec::new();
    let mut open = 2usize;
    let mut trail_cursor = dip_a_position.max(dip_b_position) + 1;

    let first_uip = loop {
        trail_cursor = trail_cursor.checked_sub(1)?;
        let literal = level.trail_literal(trail_cursor)?;
        let var = literal.get_index().unsigned_abs() as usize;
        if !seen.test(var) {
            continue;
        }

        seen.reset(var);
        open = open.checked_sub(1)?;
        if open == 0 {
            break literal.clone();
        }

        let reason = level.trail_reason(trail_cursor)?;
        for reason_literal in formula.get_clauses()[reason].iter() {
            let reason_var = reason_literal.get_index().unsigned_abs() as usize;
            if reason_var == var || seen.test(reason_var) {
                continue;
            }

            let reason_level = history.get_literal_level(reason_literal)?;
            if reason_level == 0 {
                continue;
            }

            seen.set(reason_var);
            if reason_level == analysis.current_level {
                open += 1;
            } else {
                lower_literals.push(reason_literal.clone());
                push_level(&mut lower_levels, reason_level);
            }
        }
    };

    if analysis.graph_literals.last().copied()? != first_uip.get_index() {
        return None;
    }

    let mut pre = Vec::with_capacity(lower_literals.len() + 1);
    pre.push(first_uip.negated());
    pre.extend(lower_literals);
    Some((pre, lower_levels))
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
