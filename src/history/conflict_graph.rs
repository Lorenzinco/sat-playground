use std::collections::HashMap;
use std::collections::VecDeque;

use crate::formula::literal::Literal;
use crate::formula::Formula;
use crate::history::History;

use ultragraph::GraphMut;
use ultragraph::UltraGraph;
use ultragraph::GraphView;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NodeType {
    Literal(Literal),
    Conflict,
}

fn get_or_add(
    graph: &mut UltraGraph<NodeType>,
    node_ids: &mut HashMap<NodeType, usize>,
    node: NodeType
) -> Result<usize, Box<dyn std::error::Error>> {
    if let Some(&idx) = node_ids.get(&node) {
        return Ok(idx);
    }

    let idx = match node {
        NodeType::Conflict => graph.add_root_node(NodeType::Conflict)?,
        _ => graph.add_node(node.clone())?,
    };

    node_ids.insert(node, idx);
    Ok(idx)
}

pub fn graph_from_conflict(
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
) -> Result<UltraGraph<NodeType>, Box<dyn std::error::Error>> {
    let current_level = history.get_decision_level();
    let mut graph = UltraGraph::new();

    if current_level == 0 {
        graph.add_root_node(NodeType::Conflict)?;
        return Ok(graph);
    }

    let level_data = &history.decision_levels[current_level];
    let mut node_ids: HashMap<NodeType, usize> = HashMap::new();

    if let Some(decision_lit) = level_data.get_decision_literal() {
        get_or_add(
            &mut graph,
            &mut node_ids,
            NodeType::Literal(decision_lit.clone()),
        )?;
    }

    for lit in level_data.get_implied_literals_rev() {
        get_or_add(
            &mut graph,
            &mut node_ids,
            NodeType::Literal(lit.clone()),
        )?;
    }

    let conflict_id = get_or_add(&mut graph, &mut node_ids, NodeType::Conflict)?;
    let mut implied_lits: Vec<Literal> = level_data.get_implied_literals_rev().cloned().collect();
    implied_lits.reverse();

    for implied in implied_lits.iter() {
        let Some(reason_idx) = level_data.get_reason(implied) else {
            continue;
        };

        let implied_id = get_or_add(
            &mut graph,
            &mut node_ids,
            NodeType::Literal(implied.clone()),
        )?;

        let reason = &formula.get_clauses()[reason_idx];

        for lit in reason.iter() {
            if lit == implied {
                continue;
            }

            let pred = lit.negated();
            if history.get_literal_level(&pred) != Some(current_level) {
                continue;
            }

            let pred_id = get_or_add(
                &mut graph,
                &mut node_ids,
                NodeType::Literal(pred.clone()),
            )?;

            graph.add_edge(pred_id, implied_id, ())?;
        }
    }

    let conflict_clause = &formula.get_clauses()[conflict_clause_idx];
    for lit in conflict_clause.iter() {
        let pred = lit.negated();

        if history.get_literal_level(&pred) != Some(current_level) {
            continue;
        }

        let pred_id = get_or_add(
            &mut graph,
            &mut node_ids,
            NodeType::Literal(pred.clone()),
        )?;

        graph.add_edge(pred_id, conflict_id, ())?;
    }

    Ok(graph)
}

/// Return all exact two-vertex bottlenecks as pairs of literals.
///
/// Semantics:
/// - `s` = unique literal source in the subgraph that can reach the root
/// - `t` = root node (expected to be Conflict)
/// - a pair (u, v) is returned iff removing u and v disconnects s from t
///
/// Returns:
/// - `None` if the graph is malformed for this use case
///   (no root, no unique source, etc.)
/// - `Some(vec)` otherwise; `vec` may be empty
pub fn find_all_two_vertex_bottlenecks<W>(
    graph: &impl GraphView<NodeType, W>,
) -> Option<Vec<(Literal, Literal)>> {
    let last = graph.get_last_index()?;
    let t = graph.get_root_index()?;

    // Build adjacency and reverse adjacency.
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); last + 1];
    let mut rev: Vec<Vec<usize>> = vec![Vec::new(); last + 1];
    let mut present: Vec<bool> = vec![false; last + 1];

    for u in 0..=last {
        if graph.get_node(u).is_none() {
            continue;
        }
        present[u] = true;

        if let Some(edges) = graph.get_edges(u) {
            for (v, _) in edges {
                if v <= last {
                    adj[u].push(v);
                    rev[v].push(u);
                }
            }
        }
    }

    let can_reach_t = reverse_reachable(&rev, t, &present);

    let mut source_candidates = Vec::new();
    for u in 0..=last {
        if !present[u] || !can_reach_t[u] {
            continue;
        }

        match graph.get_node(u)? {
            NodeType::Literal(_) => {
                let indeg_in_relevant = rev[u]
                    .iter()
                    .copied()
                    .filter(|&p| present[p] && can_reach_t[p])
                    .count();

                if indeg_in_relevant == 0 {
                    source_candidates.push(u);
                }
            }
            NodeType::Conflict => {}
        }
    }

    if source_candidates.len() != 1 {
        return None;
    }
    let s = source_candidates[0];

    let reachable_from_s = forward_reachable(&adj, s, &present);
    let relevant: Vec<bool> = (0..=last)
        .map(|u| present[u] && reachable_from_s[u] && can_reach_t[u])
        .collect();

    let mut candidates: Vec<(usize, Literal)> = Vec::new();
    for u in 0..=last {
        if !relevant[u] || u == s || u == t {
            continue;
        }

        if let Some(NodeType::Literal(lit)) = graph.get_node(u) {
            candidates.push((u, lit.clone()));
        }
    }

    let mut out = Vec::new();

    for i in 0..candidates.len() {
        for j in (i + 1)..candidates.len() {
            let (u_idx, u_lit) = &candidates[i];
            let (v_idx, v_lit) = &candidates[j];

            if !exists_path_avoiding_pair(&adj, &relevant, s, t, *u_idx, *v_idx) {
                out.push((u_lit.clone(), v_lit.clone()));
            }
        }
    }

    Some(out)
}

fn reverse_reachable(rev: &[Vec<usize>], start: usize, present: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; rev.len()];
    let mut q = VecDeque::new();

    if start < rev.len() && present[start] {
        seen[start] = true;
        q.push_back(start);
    }

    while let Some(u) = q.pop_front() {
        for &p in &rev[u] {
            if present[p] && !seen[p] {
                seen[p] = true;
                q.push_back(p);
            }
        }
    }

    seen
}

fn forward_reachable(adj: &[Vec<usize>], start: usize, present: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; adj.len()];
    let mut q = VecDeque::new();

    if start < adj.len() && present[start] {
        seen[start] = true;
        q.push_back(start);
    }

    while let Some(u) = q.pop_front() {
        for &v in &adj[u] {
            if present[v] && !seen[v] {
                seen[v] = true;
                q.push_back(v);
            }
        }
    }

    seen
}

fn exists_path_avoiding_pair(
    adj: &[Vec<usize>],
    relevant: &[bool],
    s: usize,
    t: usize,
    ban_a: usize,
    ban_b: usize,
) -> bool {
    if s == ban_a || s == ban_b || t == ban_a || t == ban_b {
        return false;
    }

    let mut seen = vec![false; adj.len()];
    let mut q = VecDeque::new();

    seen[s] = true;
    q.push_back(s);

    while let Some(u) = q.pop_front() {
        if u == t {
            return true;
        }

        for &v in &adj[u] {
            if !relevant[v] || seen[v] || v == ban_a || v == ban_b {
                continue;
            }
            seen[v] = true;
            q.push_back(v);
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use ultragraph::{GraphMut, UltraGraph};

    fn lit(i: u64) -> Literal {
        Literal::new(i, false)
    }

    fn pairset(mut pairs: Vec<(Literal, Literal)>) -> HashSet<(Literal, Literal)> {
        let mut out = HashSet::new();
        for (a, b) in pairs.drain(..) {
            // normalize order so tests don't depend on output ordering
            if a.get_index() <= b.get_index() {
                out.insert((a, b));
            } else {
                out.insert((b, a));
            }
        }
        out
    }

    fn expected(ids: &[(u64, u64)]) -> HashSet<(Literal, Literal)> {
        ids.iter()
            .map(|(a, b)| {
                let la = lit(*a);
                let lb = lit(*b);
                if a <= b { (la, lb) } else { (lb, la) }
            })
            .collect()
    }

    /// Build:
    ///
    /// s -> a -> t
    /// s -> b -> t
    ///
    /// Only {a,b} is a two-vertex bottleneck.
    #[test]
    fn simple_parallel_paths_single_tvb() {
        let mut g = UltraGraph::<NodeType>::new();

        let s = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let a = g.add_node(NodeType::Literal(lit(2))).unwrap();
        let b = g.add_node(NodeType::Literal(lit(3))).unwrap();
        let t = g.add_root_node(NodeType::Conflict).unwrap();

        g.add_edge(s, a, ()).unwrap();
        g.add_edge(s, b, ()).unwrap();
        g.add_edge(a, t, ()).unwrap();
        g.add_edge(b, t, ()).unwrap();

        let got = find_all_two_vertex_bottlenecks(&g).unwrap();
        assert_eq!(pairset(got), expected(&[(2, 3)]));
    }

    /// Build:
    ///
    /// s -> a1 -> a2 -> t
    /// s -> b1 -> b2 -> t
    ///
    /// Every pair with one node from the first path and one from the second path
    /// is a TVB:
    /// {a1,b1}, {a1,b2}, {a2,b1}, {a2,b2}
    #[test]
    fn two_parallel_chains_all_cross_pairs_are_tvbs() {
        let mut g = UltraGraph::<NodeType>::new();

        let s  = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let a1 = g.add_node(NodeType::Literal(lit(2))).unwrap();
        let a2 = g.add_node(NodeType::Literal(lit(3))).unwrap();
        let b1 = g.add_node(NodeType::Literal(lit(4))).unwrap();
        let b2 = g.add_node(NodeType::Literal(lit(5))).unwrap();
        let t  = g.add_root_node(NodeType::Conflict).unwrap();

        g.add_edge(s, a1, ()).unwrap();
        g.add_edge(a1, a2, ()).unwrap();
        g.add_edge(a2, t, ()).unwrap();

        g.add_edge(s, b1, ()).unwrap();
        g.add_edge(b1, b2, ()).unwrap();
        g.add_edge(b2, t, ()).unwrap();

        let got = find_all_two_vertex_bottlenecks(&g).unwrap();
        assert_eq!(
            pairset(got),
            expected(&[(2, 4), (2, 5), (3, 4), (3, 5)])
        );
    }

    /// Build three internally vertex-disjoint paths:
    ///
    /// s -> a -> t
    /// s -> b -> t
    /// s -> c -> t
    ///
    /// No pair can disconnect s from t, because the third path survives.
    #[test]
    fn three_disjoint_paths_give_no_tvbs() {
        let mut g = UltraGraph::<NodeType>::new();

        let s = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let a = g.add_node(NodeType::Literal(lit(2))).unwrap();
        let b = g.add_node(NodeType::Literal(lit(3))).unwrap();
        let c = g.add_node(NodeType::Literal(lit(4))).unwrap();
        let t = g.add_root_node(NodeType::Conflict).unwrap();

        for mid in [a, b, c] {
            g.add_edge(s, mid, ()).unwrap();
            g.add_edge(mid, t, ()).unwrap();
        }

        let got = find_all_two_vertex_bottlenecks(&g).unwrap();
        assert!(got.is_empty());
    }

    /// Build:
    ///
    /// s -> a -> x -> t
    /// s -> b ------> t
    ///
    /// TVBs are {a,b} and {x,b}
    /// but not {a,x} because the b-path survives.
    #[test]
    fn mixed_graph_some_pairs_yes_some_no() {
        let mut g = UltraGraph::<NodeType>::new();

        let s = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let a = g.add_node(NodeType::Literal(lit(2))).unwrap();
        let x = g.add_node(NodeType::Literal(lit(3))).unwrap();
        let b = g.add_node(NodeType::Literal(lit(4))).unwrap();
        let t = g.add_root_node(NodeType::Conflict).unwrap();

        g.add_edge(s, a, ()).unwrap();
        g.add_edge(a, x, ()).unwrap();
        g.add_edge(x, t, ()).unwrap();

        g.add_edge(s, b, ()).unwrap();
        g.add_edge(b, t, ()).unwrap();

        let got = find_all_two_vertex_bottlenecks(&g).unwrap();
        assert_eq!(pairset(got), expected(&[(2, 4), (3, 4)]));
    }

    /// Malformed for this API: two different literal sources with indegree 0
    /// both reaching Conflict.
    ///
    /// The function is expected to return None because it cannot infer a unique s.
    #[test]
    fn malformed_graph_multiple_sources_returns_none() {
        let mut g = UltraGraph::<NodeType>::new();

        let s1 = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let s2 = g.add_node(NodeType::Literal(lit(2))).unwrap();
        let t = g.add_root_node(NodeType::Conflict).unwrap();

        g.add_edge(s1, t, ()).unwrap();
        g.add_edge(s2, t, ()).unwrap();

        let got = find_all_two_vertex_bottlenecks(&g);
        assert!(got.is_none());
    }

    /// Graph with only source and conflict:
    ///
    /// s -> t
    ///
    /// There are no internal literal vertices, so there are no TVBs.
    #[test]
    fn direct_edge_no_internal_vertices() {
        let mut g = UltraGraph::<NodeType>::new();

        let s = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let t = g.add_root_node(NodeType::Conflict).unwrap();
        g.add_edge(s, t, ()).unwrap();

        let got = find_all_two_vertex_bottlenecks(&g).unwrap();
        assert!(got.is_empty());
    }
}