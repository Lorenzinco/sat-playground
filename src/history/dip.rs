use crate::formula::literal::Literal;
use crate::formula::clause::Clause;
use crate::formula::Formula;

use crate::history::ConflictLearnResult;
use crate::history::conflict_graph::graph_from_conflict;
use crate::history::conflict_graph::find_all_two_vertex_bottlenecks;
use crate::history::conflict_graph::find_clauses_from_dip_pair;
use crate::history::uip::find_1uip;
use crate::history::History;

pub fn find_dip(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> ConflictLearnResult {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return ConflictLearnResult::Uip {
            clause: Clause::new(),
            backtrack_level: 0,
        };
    }

    let Ok(graph) = graph_from_conflict(history, formula, conflict_clause_index) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    let Some(mut dips) = find_all_two_vertex_bottlenecks(&graph) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    if dips.is_empty() {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    }

    let (a, b) = choose_best_dip_pair(&mut dips, history);

    let Some((first_uip, mut pre_lits, mut post_lits)) = find_clauses_from_dip_pair(
        &graph,
        history,
        formula,
        conflict_clause_index,
        &a,
        &b,
    ) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    dedup_literals(&mut pre_lits);
    dedup_literals(&mut post_lits);

    let backtrack_level = post_lits
        .iter()
        .filter_map(|lit| history.get_literal_level(lit))
        .max()
        .unwrap_or(0);

    ConflictLearnResult::Dip {
        dip_a: a,
        dip_b: b,
        first_uip,
        pre_clause_without_z: pre_lits,
        post_clause_without_z: post_lits,
        backtrack_level,
    }
}

fn choose_best_dip_pair(
    dips: &mut Vec<(Literal, Literal)>,
    history: &History,
) -> (Literal, Literal) {
    let current_level = history.get_decision_level();
    let level_data = &history.decision_levels[current_level];
    
    let implied_lits: Vec<&Literal> = level_data.get_implied_literals();

    dips.sort_by_key(|(a, b)| {
        let la = history.get_literal_level(a).unwrap_or(0);
        let lb = history.get_literal_level(b).unwrap_or(0);
        
        let pos_a = if la == current_level {
            implied_lits.iter().position(|&l| l == a).unwrap_or(0)
        } else { 0 };
        
        let pos_b = if lb == current_level {
            implied_lits.iter().position(|&l| l == b).unwrap_or(0)
        } else { 0 };

        (la, lb, std::cmp::max(pos_a, pos_b), std::cmp::min(pos_a, pos_b))
    });
    
    dips.pop().unwrap()
}

fn dedup_literals(lits: &mut Vec<Literal>) {
    let mut seen = std::collections::HashSet::new();
    lits.retain(|lit| seen.insert((lit.get_index(), lit.is_negated())));
}
