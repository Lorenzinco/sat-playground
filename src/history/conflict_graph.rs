use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;

use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::history::uip::find_1uip;

use ultragraph::GraphMut;
use ultragraph::GraphView;
use ultragraph::UltraGraph;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NodeType {
    Literal(Literal),
    Conflict,
}

fn get_or_add(
    graph: &mut UltraGraph<NodeType>,
    node_ids: &mut HashMap<NodeType, usize>,
    node: NodeType,
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
) -> Result<(UltraGraph<NodeType>, Literal), Box<dyn std::error::Error>> {
    let current_level = history.get_decision_level();
    let mut graph = UltraGraph::new();

    if current_level == 0 {
        graph.add_root_node(NodeType::Conflict)?;
        return Ok((graph, Literal::new(0, false)));
    }

    // Identify the 1UIP to serve as our hard stop (source of the subgraph)
    let (uip_clause, _) = find_1uip(history, formula, conflict_clause_idx);
    let first_uip = uip_clause
        .iter()
        .find(|l| history.get_literal_level(l) == Some(current_level))
        .map(|l| l.negated())
        .unwrap();

    let mut node_ids: HashMap<NodeType, usize> = HashMap::new();
    let _conflict_id = get_or_add(&mut graph, &mut node_ids, NodeType::Conflict)?;

    let mut q = VecDeque::new();
    let mut seen = HashSet::new();

    q.push_back(NodeType::Conflict);
    seen.insert(NodeType::Conflict);

    // BFS backwards from the conflict, stopping at 1UIP
    while let Some(node) = q.pop_front() {
        let node_id = *node_ids.get(&node).unwrap();

        let get_preds = || -> Vec<Literal> {
            match &node {
                NodeType::Conflict => {
                    let clause = &formula.get_clauses()[conflict_clause_idx];
                    clause.get_literals().iter().map(|l| l.negated()).collect()
                }
                NodeType::Literal(lit) => {
                    if lit == &first_uip {
                        return vec![]; // Stop backward exploration at 1UIP
                    }
                    if let Some(reason_idx) = history.decision_levels[current_level].get_reason(lit) {
                        let reason = &formula.get_clauses()[reason_idx];
                        reason.get_literals().iter().filter(|&l| l != lit).map(|l| l.negated()).collect()
                    } else {
                        vec![]
                    }
                }
            }
        };

        for pred in get_preds() {
            if history.get_literal_level(&pred) == Some(current_level) {
                let pred_node = NodeType::Literal(pred.clone());
                let pred_id = get_or_add(&mut graph, &mut node_ids, pred_node.clone())?;
                graph.add_edge(pred_id, node_id, ())?;

                if seen.insert(pred_node.clone()) {
                    q.push_back(pred_node);
                }
            }
        }
    }

    Ok((graph, first_uip))
}

pub fn dump_conflict_graph_dot(
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
    path: &str,
) -> Result<Literal, Box<dyn std::error::Error>> {
    let (graph, first_uip) = graph_from_conflict(history, formula, conflict_clause_idx)?;

    let mut out = std::fs::File::create(path)?;
    use std::io::Write;

    writeln!(out, "digraph ConflictGraph {{")?;
    writeln!(out, "  rankdir=LR;")?;
    writeln!(out, "  node [shape=box, style=rounded];")?;

    let last = graph.get_last_index().unwrap_or(0);

    for idx in 0..=last {
        if let Some(node) = graph.get_node(idx) {
            match node {
                NodeType::Conflict => {
                    writeln!(
                        out,
                        "  n{} [label=\"Conflict\", shape=doublecircle, color=red];",
                        idx
                    )?;
                }
                NodeType::Literal(lit) => {
                    let label = format!("{}", lit);
                    let level = history.get_literal_level(lit).unwrap_or(0);
                    writeln!(
                        out,
                        "  n{} [label={}\nlevel={}] ;",
                        idx,
                        label,
                        level
                    )?;
                }
            }
        }
    }

    for u in 0..=last {
        if graph.get_node(u).is_none() {
            continue;
        }

        if let Some(edges) = graph.get_edges(u) {
            for (v, _) in edges {
                if graph.get_node(v).is_some() {
                    writeln!(out, "  n{} -> n{};", u, v)?;
                }
            }
        }
    }

    writeln!(out, "}}")?;

    Ok(first_uip)
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

pub fn find_clauses_from_dip_pair<W>(
    graph: &impl GraphView<NodeType, W>,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
    dip_a: &Literal,
    dip_b: &Literal,
    first_uip: &Literal,
) -> Option<(Vec<Literal>, Vec<Literal>)> {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return None;
    }

    let last = graph.get_last_index()?;

    let mut dip_a_node = None;
    let mut dip_b_node = None;
    let mut first_uip_node = None;

    let mut adj = vec![Vec::new(); last + 1];

    for u in 0..=last {
        if let Some(node) = graph.get_node(u) {
            if let NodeType::Literal(lit) = node {
                if lit == dip_a { dip_a_node = Some(u); }
                if lit == dip_b { dip_b_node = Some(u); }
                if lit == first_uip { first_uip_node = Some(u); }
            }
            if let Some(edges) = graph.get_edges(u) {
                for (v, _) in edges {
                    if v <= last { adj[u].push(v); }
                }
            }
        }
    }

    let dip_a_node = dip_a_node?;
    let dip_b_node = dip_b_node?;
    let first_uip_node = first_uip_node?;

    // The graph is guaranteed to have NO dead ends and NO nodes prior to first_uip.
    // Pre-region BFS: simply walk forward from 1UIP, stopping at DIPs.
    let mut pre_region = HashSet::new();
    let mut q = VecDeque::new();
    pre_region.insert(first_uip_node);
    q.push_back(first_uip_node);

    while let Some(u) = q.pop_front() {
        if u == dip_a_node || u == dip_b_node { continue; }
        for &v in &adj[u] {
            if pre_region.insert(v) {
                q.push_back(v);
            }
        }
    }
    pre_region.insert(dip_a_node);
    pre_region.insert(dip_b_node);

    // Post-region BFS: walk forward from DIPs.
    let mut post_region = HashSet::new();
    let mut q = VecDeque::new();
    for &start in &[dip_a_node, dip_b_node] {
        for &v in &adj[start] {
            if post_region.insert(v) { q.push_back(v); }
        }
    }

    while let Some(u) = q.pop_front() {
        for &v in &adj[u] {
            if post_region.insert(v) { q.push_back(v); }
        }
    }

    let get_lower_level_preds = |region: &HashSet<usize>| -> Vec<Literal> {
        let mut res = Vec::new();
        let mut seen = HashSet::new();
        for &node in region {
            if let Some(NodeType::Literal(lit)) = graph.get_node(node) {
                let lit_level = history.get_literal_level(lit).unwrap_or(0);
                if lit_level == current_level {
                    if let Some(reason_idx) = history.decision_levels[current_level].get_reason(lit) {
                        let reason = &formula.get_clauses()[reason_idx];
                        for reason_lit in reason.get_literals() {
                            if reason_lit == lit { continue; }
                            let pred = reason_lit.negated();
                            let pred_level = history.get_literal_level(&pred).unwrap_or(0);
                            if pred_level < current_level {
                                if seen.insert(pred.get_signed_index()) { res.push(pred.clone()); }
                            }
                        }
                    }
                }
            } else if let Some(NodeType::Conflict) = graph.get_node(node) {
                let conflict_clause = &formula.get_clauses()[conflict_clause_idx];
                for conflict_lit in conflict_clause.get_literals() {
                    let pred = conflict_lit.negated();
                    let pred_level = history.get_literal_level(&pred).unwrap_or(0);
                    if pred_level < current_level {
                        if seen.insert(pred.get_signed_index()) { res.push(pred.clone()); }
                    }
                }
            }
        }
        res
    };
    
    let mut pre_lits = vec![first_uip.negated()];
    for lit in get_lower_level_preds(&pre_region) { pre_lits.push(lit.negated()); }

    let mut post_lits = Vec::new();
    for lit in get_lower_level_preds(&post_region) { post_lits.push(lit.negated()); }

    Some((pre_lits, post_lits))
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

        let s = g.add_node(NodeType::Literal(lit(1))).unwrap();
        let a1 = g.add_node(NodeType::Literal(lit(2))).unwrap();
        let a2 = g.add_node(NodeType::Literal(lit(3))).unwrap();
        let b1 = g.add_node(NodeType::Literal(lit(4))).unwrap();
        let b2 = g.add_node(NodeType::Literal(lit(5))).unwrap();
        let t = g.add_root_node(NodeType::Conflict).unwrap();

        g.add_edge(s, a1, ()).unwrap();
        g.add_edge(a1, a2, ()).unwrap();
        g.add_edge(a2, t, ()).unwrap();

        g.add_edge(s, b1, ()).unwrap();
        g.add_edge(b1, b2, ()).unwrap();
        g.add_edge(b2, t, ()).unwrap();

        let got = find_all_two_vertex_bottlenecks(&g).unwrap();
        assert_eq!(pairset(got), expected(&[(2, 4), (2, 5), (3, 4), (3, 5)]));
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
