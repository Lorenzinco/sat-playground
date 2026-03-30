use ultragraph::UltraGraph;

use crate::formula::literal::Literal;
use crate::formula::clause::Clause;
use crate::formula::Formula;

use crate::history::conflict_graph::graph_from_conflict;
use crate::history::conflict_graph::find_all_two_vertex_bottlenecks;
use crate::history::conflict_graph::NodeType;
use crate::history::uip::find_1uip;
use crate::history::History;

pub fn find_dip(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> (Clause, usize, Option<(Literal, Literal)>) {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return (Clause::new(), 0, None);
    }

    let Ok(graph) = graph_from_conflict(history, formula, conflict_clause_index) else {
        let (clause,conflict_level) = find_1uip(history, formula, conflict_clause_index);
        return (clause,conflict_level,None)
    };

    let Some(mut dips) = find_all_two_vertex_bottlenecks(&graph) else {
        let (clause,conflict_level) = find_1uip(history, formula, conflict_clause_index);
        return (clause,conflict_level,None)
    };

    if dips.is_empty() {
        let (clause,conflict_level) = find_1uip(history, formula, conflict_clause_index);
        return (clause,conflict_level,None)
    }

    // Pick one DIP. Start simple.
    let (a, b) = choose_best_dip_pair(&mut dips, history);

    let learned_clause = learn_clause_from_dip_pair(
        &graph,
        history,
        formula,
        conflict_clause_index,
        a.clone(),
        b.clone(),
    );

    let Some(mut learned_lits) = learned_clause else {
        let (clause,conflict_level) = find_1uip(history, formula, conflict_clause_index);
        return (clause,conflict_level,None)
    };

    normalize_asserting_literals_first(&mut learned_lits, &a, &b);

    let backtrack_level = learned_lits
        .iter()
        .skip(2)
        .filter_map(|lit| history.get_literal_level(lit))
        .max()
        .unwrap_or(0);

    (
        Clause::from_literals(&learned_lits),
        backtrack_level,
        Some((a, b)),
    )
}


///Heuristic based, right now the latest
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

fn learn_clause_from_dip_pair(
    _graph: &UltraGraph<NodeType>,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
    dip_a: Literal,
    dip_b: Literal,
) -> Option<Vec<Literal>> {
    let current_level = history.get_decision_level();
    let level_data = &history.decision_levels[current_level];

    // Tracks variables currently in our "cut"
    let mut seen = vec![false; formula.assignment.len()];
    
    // Tracks how many variables in the cut are from `current_level`
    // and are NEITHER `dip_a` NOR `dip_b`.
    let mut active_non_dip_count = 0;

    let mut current_clause_idx = conflict_clause_idx;
    let mut resolved_lit: Option<Literal> = None;

    let mut trail_iter = level_data
        .get_implied_literals_rev()
        .chain(level_data.get_decision_literal().into_iter());

    let mut learned_lits = Vec::new();

    let dip_a_neg = dip_a.negated();
    let dip_b_neg = dip_b.negated();

    loop {
        let clause = &formula.get_clauses()[current_clause_idx];

        for lit in clause.iter() {
            // Skip the literal that was just resolved
            if Some(lit) == resolved_lit.as_ref() {
                continue;
            }

            let var = lit.get_index() as usize;
            if !seen[var] {
                seen[var] = true;

                if history.get_literal_level(lit) == Some(current_level) {
                    if *lit != dip_a_neg && *lit != dip_b_neg {
                        active_non_dip_count += 1;
                    }
                } else {
                    learned_lits.push(lit.clone());
                }
            }
        }

        if active_non_dip_count == 0 {
            break;
        }

        let p = loop {
            let Some(p) = trail_iter.next() else {
                return None; // Should not happen if DIPs are a valid cut
            };
            
            let var = p.get_index() as usize;
            if seen[var] && *p != dip_a && *p != dip_b {
                break p;
            }
        };

        resolved_lit = Some(p.clone());
        active_non_dip_count -= 1;

        let reason_idx = level_data.get_reason(p)?;
        current_clause_idx = reason_idx;
    }

    let var_a = dip_a.get_index() as usize;
    if seen[var_a] {
        learned_lits.push(dip_a_neg);
    }
    
    let var_b = dip_b.get_index() as usize;
    if seen[var_b] {
        learned_lits.push(dip_b_neg);
    }

    Some(learned_lits)
}

fn normalize_asserting_literals_first(
    learned_lits: &mut Vec<Literal>,
    a: &Literal,
    b: &Literal,
) {
    let a_neg = a.negated();
    let b_neg = b.negated();

    let mut target_idx = 0;
    
    for i in 0..learned_lits.len() {
        if learned_lits[i] == a_neg || learned_lits[i] == b_neg {
            learned_lits.swap(target_idx, i);
            target_idx += 1;
            
            // Once we've moved both DIPs to the front, we're done
            if target_idx == 2 {
                break;
            }
        }
    }
}