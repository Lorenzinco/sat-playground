use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::conflict_analysis::{ConflictAnalysis, analyze_conflict_graph};
use crate::history::uip;
use crate::history::{ConflictLearnResult, History};

use std::collections::HashSet;

const DIP_MAX_CLAUSE_LBD: i64 = 2;

struct DipCandidate {
    dip_a: Literal,
    dip_b: Literal,
    pre_clause_without_z: Vec<Literal>,
    post_clause_without_z: Vec<Literal>,
    pre_lbd: i64,
    post_lbd: i64,
    l_c: usize,
    l_d: usize,
}

pub fn find_dip(
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> ConflictLearnResult {
    let Some(analysis) = analyze_conflict_graph(history, formula, conflict_clause_index) else {
        return uip::empty_result();
    };

    learn_from_analysis(&analysis, history, formula, conflict_clause_index)
        .unwrap_or_else(|| uip::learn_from_analysis(&analysis, history, formula))
}

pub(super) fn learn_from_analysis(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_index: usize,
) -> Option<ConflictLearnResult> {
    let candidate = find_first_dip_candidate(analysis, history, formula, conflict_clause_index)?;
    Some(ConflictLearnResult::Dip {
        dip_a: candidate.dip_a,
        dip_b: candidate.dip_b,
        pre_clause_without_z: candidate.pre_clause_without_z,
        post_clause_without_z: candidate.post_clause_without_z,
        pre_lbd: candidate.pre_lbd,
        post_lbd: candidate.post_lbd,
        backtrack_level: std::cmp::max(candidate.l_c, candidate.l_d),
    })
}

fn find_first_dip_candidate(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
) -> Option<DipCandidate> {
    let conflict_idx = analysis.trail.len();
    let rev = reverse_adj(&analysis.successors);
    let can_reach_conflict = reachable(&rev, conflict_idx, &analysis.present);

    let mut sources = Vec::new();
    for pos in 0..analysis.trail.len() {
        if !analysis.present[pos] || !can_reach_conflict[pos] {
            continue;
        }

        let indeg = rev[pos]
            .iter()
            .filter(|&&p| analysis.present[p] && can_reach_conflict[p])
            .count();
        if indeg == 0 {
            sources.push(pos);
        }
    }

    if sources.len() != 1 || sources[0] != analysis.first_uip_pos {
        return None;
    }

    let reachable_from_uip = reachable(
        &analysis.successors,
        analysis.first_uip_pos,
        &analysis.present,
    );
    let relevant: Vec<bool> = (0..=conflict_idx)
        .map(|idx| analysis.present[idx] && reachable_from_uip[idx] && can_reach_conflict[idx])
        .collect();

    let compressed = compressed_two_vertex_bottlenecks(
        &analysis.successors,
        &relevant,
        analysis.first_uip_pos,
        conflict_idx,
    )?;

    for range in &compressed.ranges {
        let dip_a_pos = range.left;
        for &dip_b_pos in &compressed.candidates[range.right_path][range.start..range.end] {
            if let Some(candidate) = find_capped_clauses_from_dip_pair(
                analysis,
                history,
                formula,
                conflict_clause_idx,
                dip_a_pos,
                dip_b_pos,
            ) {
                return Some(candidate);
            }
        }
    }

    None
}

struct CompressedDipRanges {
    candidates: [Vec<usize>; 2],
    ranges: Vec<DipPairRange>,
}

struct DipPairRange {
    left: usize,
    right_path: usize,
    start: usize,
    end: usize,
}

#[derive(Clone, Copy)]
struct PathItem {
    node: usize,
    pos: usize,
    reach_other_pos: usize,
}

enum DisjointPaths {
    LessThanTwo,
    ThreeConnected,
    Two([Vec<usize>; 2]),
}

fn compressed_two_vertex_bottlenecks(
    adj: &[Vec<usize>],
    relevant: &[bool],
    s: usize,
    t: usize,
) -> Option<CompressedDipRanges> {
    let paths = match find_disjoint_paths(adj, relevant, s, t) {
        DisjointPaths::Two(paths) => paths,
        DisjointPaths::LessThanTwo | DisjointPaths::ThreeConnected => return None,
    };

    if paths[0].len() <= 2 || paths[1].len() <= 2 {
        return None;
    }

    let mut path_pos = vec![[None; 2]; adj.len()];
    for path_idx in 0..2 {
        for (pos, &node) in paths[path_idx].iter().enumerate() {
            path_pos[node][path_idx] = Some(pos);
        }
    }

    let direct = directly_reachable_path_positions(adj, relevant, &path_pos, t);
    let path_items = [
        non_bypassed_path_items(0, &paths, &direct),
        non_bypassed_path_items(1, &paths, &direct),
    ];

    if path_items[0].is_empty() || path_items[1].is_empty() {
        return None;
    }

    let mut ranges = Vec::new();
    add_ranges_from_path(&path_items, 0, &mut ranges);

    if ranges.is_empty() {
        return None;
    }

    let candidates = [
        path_items[0].iter().map(|item| item.node).collect(),
        path_items[1].iter().map(|item| item.node).collect(),
    ];

    Some(CompressedDipRanges { candidates, ranges })
}

fn directly_reachable_path_positions(
    adj: &[Vec<usize>],
    relevant: &[bool],
    path_pos: &[[Option<usize>; 2]],
    t: usize,
) -> Vec<[usize; 2]> {
    let mut direct = vec![[0, 0]; adj.len()];

    for u in (0..=t).rev() {
        if !relevant[u] {
            continue;
        }

        for &v in &adj[u] {
            if v >= adj.len() || !relevant[v] {
                continue;
            }

            let mut v_on_path = false;
            for path_idx in 0..2 {
                if let Some(pos) = path_pos[v][path_idx] {
                    direct[u][path_idx] = direct[u][path_idx].max(pos);
                    v_on_path = true;
                }
            }

            if !v_on_path {
                direct[u][0] = direct[u][0].max(direct[v][0]);
                direct[u][1] = direct[u][1].max(direct[v][1]);
            }
        }
    }

    direct
}

fn non_bypassed_path_items(
    path_idx: usize,
    paths: &[Vec<usize>; 2],
    direct: &[[usize; 2]],
) -> Vec<PathItem> {
    let other_path = 1 - path_idx;
    let path = &paths[path_idx];
    let other_internal_start = usize::from(paths[other_path].len() > 2);
    let mut max_same_from_prior = 0;
    let mut max_other_from_prior = other_internal_start;
    let mut items = Vec::new();

    for (pos, &node) in path.iter().enumerate() {
        let is_internal = pos > 0 && pos + 1 < path.len();
        if is_internal && max_same_from_prior <= pos {
            items.push(PathItem {
                node,
                pos,
                reach_other_pos: max_other_from_prior,
            });
        }

        max_same_from_prior = max_same_from_prior.max(direct[node][path_idx]);
        max_other_from_prior = max_other_from_prior.max(direct[node][other_path]);
    }

    items
}

fn add_ranges_from_path(
    path_items: &[Vec<PathItem>; 2],
    left_path: usize,
    ranges: &mut Vec<DipPairRange>,
) {
    let right_path = 1 - left_path;
    let left_items = &path_items[left_path];
    let right_items = &path_items[right_path];
    let mut right_limit = 0;

    for item in left_items {
        while right_limit < right_items.len()
            && right_items[right_limit].reach_other_pos <= item.pos
        {
            right_limit += 1;
        }

        if right_limit == 0 {
            continue;
        }

        let start = lower_bound_path_pos(right_items, item.reach_other_pos);
        if start < right_limit {
            ranges.push(DipPairRange {
                left: item.node,
                right_path,
                start,
                end: right_limit,
            });
        }
    }
}

fn lower_bound_path_pos(items: &[PathItem], pos: usize) -> usize {
    let mut lo = 0;
    let mut hi = items.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if items[mid].pos < pos {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

#[derive(Clone)]
struct FlowEdge {
    to: usize,
    rev: usize,
    cap: i32,
}

fn add_flow_edge(graph: &mut [Vec<FlowEdge>], from: usize, to: usize, cap: i32) -> usize {
    let forward_idx = graph[from].len();
    let reverse_idx = graph[to].len();
    graph[from].push(FlowEdge {
        to,
        rev: reverse_idx,
        cap,
    });
    graph[to].push(FlowEdge {
        to: from,
        rev: forward_idx,
        cap: 0,
    });
    forward_idx
}

fn find_disjoint_paths(adj: &[Vec<usize>], relevant: &[bool], s: usize, t: usize) -> DisjointPaths {
    let split_len = adj.len() * 2;
    let mut graph = vec![Vec::new(); split_len];
    let mut original_edges = Vec::new();

    for node in 0..adj.len() {
        if !relevant[node] {
            continue;
        }
        let cap = if node == s || node == t { 3 } else { 1 };
        add_flow_edge(&mut graph, node * 2, node * 2 + 1, cap);
    }

    for u in 0..adj.len() {
        if !relevant[u] {
            continue;
        }
        for &v in &adj[u] {
            if v < adj.len() && relevant[v] {
                let from = u * 2 + 1;
                let to = v * 2;
                let edge_idx = add_flow_edge(&mut graph, from, to, 1);
                original_edges.push((from, edge_idx, u, v));
            }
        }
    }

    let source = s * 2 + 1;
    let sink = t * 2;
    let mut flow = 0;
    while flow < 3 && augment_one_path(&mut graph, source, sink) {
        flow += 1;
    }

    if flow < 2 {
        return DisjointPaths::LessThanTwo;
    }
    if flow >= 3 {
        return DisjointPaths::ThreeConnected;
    }

    let mut used_adj = vec![Vec::new(); adj.len()];
    for (from, edge_idx, u, v) in original_edges {
        if graph[from][edge_idx].cap == 0 {
            used_adj[u].push(v);
        }
    }

    let Some(first) = pop_used_successor(&mut used_adj, s) else {
        return DisjointPaths::LessThanTwo;
    };
    let Some(second) = pop_used_successor(&mut used_adj, s) else {
        return DisjointPaths::LessThanTwo;
    };

    let Some(path_a) = extract_flow_path(&mut used_adj, s, first, t) else {
        return DisjointPaths::LessThanTwo;
    };
    let Some(path_b) = extract_flow_path(&mut used_adj, s, second, t) else {
        return DisjointPaths::LessThanTwo;
    };

    DisjointPaths::Two([path_a, path_b])
}

fn augment_one_path(graph: &mut [Vec<FlowEdge>], source: usize, sink: usize) -> bool {
    let mut parent: Vec<Option<(usize, usize)>> = vec![None; graph.len()];
    let mut queue = std::collections::VecDeque::new();
    parent[source] = Some((source, usize::MAX));
    queue.push_back(source);

    while let Some(u) = queue.pop_front() {
        for edge_idx in 0..graph[u].len() {
            let edge = &graph[u][edge_idx];
            if edge.cap <= 0 || parent[edge.to].is_some() {
                continue;
            }
            parent[edge.to] = Some((u, edge_idx));
            if edge.to == sink {
                break;
            }
            queue.push_back(edge.to);
        }
        if parent[sink].is_some() {
            break;
        }
    }

    if parent[sink].is_none() {
        return false;
    }

    let mut v = sink;
    while v != source {
        let (u, edge_idx) = parent[v].expect("augmenting path parent missing");
        let rev = graph[u][edge_idx].rev;
        graph[u][edge_idx].cap -= 1;
        graph[v][rev].cap += 1;
        v = u;
    }

    true
}

fn pop_used_successor(used_adj: &mut [Vec<usize>], node: usize) -> Option<usize> {
    used_adj.get_mut(node)?.pop()
}

fn extract_flow_path(
    used_adj: &mut [Vec<usize>],
    s: usize,
    first: usize,
    t: usize,
) -> Option<Vec<usize>> {
    let mut path = vec![s, first];
    let mut current = first;
    while current != t {
        current = pop_used_successor(used_adj, current)?;
        path.push(current);
    }
    Some(path)
}

fn find_capped_clauses_from_dip_pair(
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
    dip_a_pos: usize,
    dip_b_pos: usize,
) -> Option<DipCandidate> {
    if dip_a_pos == dip_b_pos
        || dip_a_pos == analysis.first_uip_pos
        || dip_b_pos == analysis.first_uip_pos
    {
        return None;
    }

    let conflict_idx = analysis.trail.len();
    let mut pre_region =
        forward_region(analysis, [analysis.first_uip_pos], &[dip_a_pos, dip_b_pos]);
    pre_region[dip_a_pos] = true;
    pre_region[dip_b_pos] = true;

    let post_region = forward_region(
        analysis,
        analysis.successors[dip_a_pos]
            .iter()
            .chain(analysis.successors[dip_b_pos].iter())
            .copied(),
        &[],
    );
    if !post_region[conflict_idx] {
        return None;
    }

    let covered_none = vec![false; conflict_idx + 1];
    let (pre_lits, pre_levels) = collect_external_preds_capped(
        &pre_region,
        &covered_none,
        true,
        Some(analysis.trail[analysis.first_uip_pos].negated()),
        Some(analysis.current_level),
        analysis,
        history,
        formula,
        conflict_clause_idx,
    )?;

    let mut post_covered = vec![false; conflict_idx + 1];
    post_covered[dip_a_pos] = true;
    post_covered[dip_b_pos] = true;
    let (post_lits, post_levels) = collect_external_preds_capped(
        &post_region,
        &post_covered,
        false,
        None,
        Some(analysis.current_level),
        analysis,
        history,
        formula,
        conflict_clause_idx,
    )?;

    if post_lits.is_empty() {
        return None;
    }

    let pre_lbd = Clause::calculate_lbd(pre_levels.iter().copied());
    let post_lbd = Clause::calculate_lbd(post_levels.iter().copied());
    if pre_lbd > DIP_MAX_CLAUSE_LBD || post_lbd > DIP_MAX_CLAUSE_LBD {
        return None;
    }

    Some(DipCandidate {
        dip_a: analysis.trail[dip_a_pos].clone(),
        dip_b: analysis.trail[dip_b_pos].clone(),
        pre_clause_without_z: pre_lits,
        post_clause_without_z: post_lits,
        pre_lbd,
        post_lbd,
        l_c: highest_non_current_level(&pre_levels, analysis.current_level),
        l_d: highest_non_current_level(&post_levels, analysis.current_level),
    })
}

fn collect_external_preds_capped(
    region: &[bool],
    covered: &[bool],
    include_current_level_external_preds: bool,
    initial_literal: Option<Literal>,
    initial_level: Option<usize>,
    analysis: &ConflictAnalysis,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
) -> Option<(Vec<Literal>, Vec<usize>)> {
    let conflict_idx = analysis.trail.len();
    let mut lbd_levels = HashSet::new();
    let mut levels = Vec::new();
    let mut literals = Vec::new();

    if let Some(level) = initial_level {
        lbd_levels.insert(level);
        levels.push(level);
    }
    if let Some(lit) = initial_literal {
        literals.push(lit);
    }

    let is_internal_current_level_pred = |pred: &Literal| {
        analysis
            .pos_of
            .get(pred.get_unsigned_index() as usize)
            .copied()
            .flatten()
            .is_some_and(|pos| {
                region.get(pos).copied().unwrap_or(false)
                    || covered.get(pos).copied().unwrap_or(false)
            })
    };

    let emitted_level = |pred: &Literal| {
        history.get_literal_level(pred).filter(|&level| {
            !is_internal_current_level_pred(pred)
                && (include_current_level_external_preds || level < analysis.current_level)
        })
    };

    let mut seen = vec![false; analysis.pos_of.len()];
    for idx in 0..region.len() {
        if !region[idx] {
            continue;
        }

        let mut visit_pred = |pred: Literal| -> Option<()> {
            let key = pred.get_unsigned_index() as usize;
            if key >= seen.len() || seen[key] {
                return Some(());
            }

            if let Some(level) = emitted_level(&pred) {
                seen[key] = true;
                lbd_levels.insert(level);
                if lbd_levels.len() as i64 > DIP_MAX_CLAUSE_LBD {
                    return None;
                }
                literals.push(pred.negated());
                levels.push(level);
            }

            Some(())
        };

        if idx == conflict_idx {
            for conflict_lit in formula.get_clauses()[conflict_clause_idx].get_literals() {
                visit_pred(conflict_lit.negated())?;
            }
            continue;
        }

        let Some(reason_idx) = analysis.reason_of[idx] else {
            continue;
        };

        let lit = &analysis.trail[idx];
        for reason_lit in formula.get_clauses()[reason_idx].get_literals() {
            if reason_lit == lit {
                continue;
            }
            visit_pred(reason_lit.negated())?;
        }
    }

    Some((literals, levels))
}

fn forward_region(
    analysis: &ConflictAnalysis,
    seeds: impl IntoIterator<Item = usize>,
    stop_at: &[usize],
) -> Vec<bool> {
    let mut region = vec![false; analysis.trail.len() + 1];
    let mut queue = std::collections::VecDeque::new();

    for seed in seeds {
        if !region[seed] {
            region[seed] = true;
            queue.push_back(seed);
        }
    }

    while let Some(idx) = queue.pop_front() {
        if stop_at.contains(&idx) {
            continue;
        }

        for &succ in &analysis.successors[idx] {
            if !region[succ] {
                region[succ] = true;
                queue.push_back(succ);
            }
        }
    }

    region
}

fn reverse_adj(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut rev = vec![Vec::new(); adj.len()];
    for (u, succs) in adj.iter().enumerate() {
        for &v in succs {
            rev[v].push(u);
        }
    }
    rev
}

fn reachable(adj: &[Vec<usize>], start: usize, present: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; adj.len()];
    let mut queue = std::collections::VecDeque::new();

    if start < adj.len() && present[start] {
        seen[start] = true;
        queue.push_back(start);
    }

    while let Some(u) = queue.pop_front() {
        for &v in &adj[u] {
            if present[v] && !seen[v] {
                seen[v] = true;
                queue.push_back(v);
            }
        }
    }

    seen
}

fn highest_non_current_level(levels: &[usize], current_level: usize) -> usize {
    levels
        .iter()
        .copied()
        .filter(|&level| level < current_level)
        .max()
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use crate::formula::Formula;
    use crate::formula::literal::Literal;
    use crate::history::{ConflictLearnResult, History, ImplicationPoint};
    use std::collections::HashSet;

    fn lit_key(lit: &Literal) -> (i32, bool) {
        (lit.get_index(), lit.is_negated())
    }

    fn lit_set(lits: &[Literal]) -> HashSet<(i32, bool)> {
        lits.iter().map(lit_key).collect()
    }

    fn assert_unique_literals(lits: &[Literal]) {
        let mut seen = HashSet::new();
        for lit in lits {
            assert!(
                seen.insert(lit_key(lit)),
                "duplicate literal in clause: {:?}",
                lits
            );
        }
    }

    fn unordered_pair(a: &Literal, b: &Literal) -> ((i32, bool), (i32, bool)) {
        let ka = lit_key(a);
        let kb = lit_key(b);
        if ka <= kb { (ka, kb) } else { (kb, ka) }
    }

    #[test]
    fn dip_parallel_paths_ignores_dead_end_and_extracts_clauses() {
        // Variables (1-based in DIMACS):
        // 1 x1 (level1 decision), 2 p, 3 q, 4 x2 (level2 decision),
        // 5 a, 6 b, 7 c, 8 d, 9 r, 10 s (dead-end lower-level), 11 j (dead-end current level)
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],       // 0: ¬x1 v p
            vec![-1, 3],       // 1: ¬x1 v q
            vec![-1, 10],      // 2: ¬x1 v s
            vec![-4, -2, 5],   // 3: ¬x2 v ¬p v a
            vec![-4, -3, 6],   // 4: ¬x2 v ¬q v b
            vec![-5, -2, 7],   // 5: ¬a v ¬p v c
            vec![-6, -3, 8],   // 6: ¬b v ¬q v d
            vec![-7, -8, 9],   // 7: ¬c v ¬d v r   (conflict when r=false)
            vec![-4, -10, 11], // 8: ¬x2 v ¬s v j  (dead-end branch)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        // Level 1 decision
        let x1 = Literal::new(1);
        formula.assignment.assign_history(&x1, &mut history);

        let p = Literal::new(2);
        formula
            .assignment
            .assign(p.get_index().abs() as usize, true);
        history.add_implication(&p, Some(0));

        let q = Literal::new(3);
        formula
            .assignment
            .assign(q.get_index().abs() as usize, true);
        history.add_implication(&q, Some(1));

        let s = Literal::new(10);
        formula
            .assignment
            .assign(s.get_index().abs() as usize, true);
        history.add_implication(&s, Some(2));

        // r = false at level 1
        let r_neg = Literal::new(-9);
        formula
            .assignment
            .assign(r_neg.get_index().abs() as usize, false);
        history.add_implication(&r_neg, None);

        // Level 2 decision
        let x2 = Literal::new(4);
        formula.assignment.assign_history(&x2, &mut history);

        let a = Literal::new(5);
        formula
            .assignment
            .assign(a.get_index().abs() as usize, true);
        history.add_implication(&a, Some(3));

        let b = Literal::new(6);
        formula
            .assignment
            .assign(b.get_index().abs() as usize, true);
        history.add_implication(&b, Some(4));

        let c = Literal::new(7);
        formula
            .assignment
            .assign(c.get_index().abs() as usize, true);
        history.add_implication(&c, Some(5));

        let d = Literal::new(8);
        formula
            .assignment
            .assign(d.get_index().abs() as usize, true);
        history.add_implication(&d, Some(6));

        // Dead-end implication (should NOT influence pre_clause)
        let j = Literal::new(11);
        formula
            .assignment
            .assign(j.get_index().abs() as usize, true);
        history.add_implication(&j, Some(8));

        let conflict_idx = 7;

        let (dip_a, dip_b, pre_clause_without_z, post_clause_without_z, backtrack_level) =
            match history.analyze_conflict(&formula, conflict_idx, ImplicationPoint::DIP) {
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                    ..
                } => (
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                ),
                _ => panic!("Expected DIP result"),
            };

        assert_unique_literals(&pre_clause_without_z);
        assert_unique_literals(&post_clause_without_z);

        // The DIP search stops at the first pair that satisfies the pre/post LBD cap.
        assert_eq!(unordered_pair(&dip_a, &dip_b), unordered_pair(&a, &b));

        // Pre-clause should contain ¬x2, ¬p, ¬q only.
        let not_x2 = x2.negated();
        let not_p = p.negated();
        let not_q = q.negated();

        let pre_set = lit_set(&pre_clause_without_z);
        let expected_pre: HashSet<_> = [lit_key(&not_x2), lit_key(&not_p), lit_key(&not_q)]
            .into_iter()
            .collect();
        assert_eq!(pre_set, expected_pre);

        // Post-clause should contain the lower-level inputs to the post-DIP region.
        let r = Literal::new(9);
        let post_set = lit_set(&post_clause_without_z);
        let expected_post: HashSet<_> = [lit_key(&not_p), lit_key(&not_q), lit_key(&r)]
            .into_iter()
            .collect();
        assert_eq!(post_set, expected_post);

        assert_eq!(backtrack_level, 1);
    }

    #[test]
    fn paper_fig1_dip_x8_not_x9_extracts_expected_pre_and_post_clauses() {
        use crate::formula::Formula;
        use crate::formula::literal::Literal;
        use crate::history::History;
        use crate::history::conflict_graph::{find_clauses_from_dip_pair, graph_from_conflict};
        use std::collections::HashSet;

        fn lit_key(lit: &Literal) -> (i32, bool) {
            (lit.get_index(), lit.is_negated())
        }

        fn lit_set(lits: &[Literal]) -> HashSet<(i32, bool)> {
            lits.iter().map(lit_key).collect()
        }

        // Mapping:
        // x1..x13 => DIMACS vars 1..13
        // y1..y6  => DIMACS vars 14..19
        let x = |n: u64| Literal::new(n as i32);
        let y = |n: u64| Literal::new((13 + n) as i32);

        let clauses: Vec<Vec<i32>> = vec![
            vec![14, -1, 2],          // (1)  y1 v ¬x1 v x2
            vec![-1, -3],             // (2)  ¬x1 v ¬x3
            vec![15, -1, 4],          // (3)  y2 v ¬x1 v x4
            vec![-16, -2, 3, -4, 5],  // (4)  ¬y3 v ¬x2 v x3 v ¬x4 v x5
            vec![14, -5, -6],         // (5)  y1 v ¬x5 v ¬x6
            vec![-5, 7],              // (6)  ¬x5 v x7
            vec![6, -7, 8],           // (7)  x6 v ¬x7 v x8
            vec![-16, -17, -5, -9],   // (8)  ¬y3 v ¬y4 v ¬x5 v ¬x9
            vec![-17, 9, -10],        // (9)  ¬y4 v x9 v ¬x10
            vec![-18, 19, -8, 9, 11], // (10) ¬y5 v y6 v ¬x8 v x9 v x11
            vec![-11, 12],            // (11) ¬x11 v x12
            vec![10, -11, 13],        // (12) x10 v ¬x11 v x13
            vec![-12, -13],           // (13) ¬x12 v ¬x13, conflicting
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        // Previous-level assignments:
        // {¬y1, ¬y2, y3, y4, y5, ¬y6}
        for lit in [
            y(1).negated(),
            y(2).negated(),
            y(3),
            y(4),
            y(5),
            y(6).negated(),
        ] {
            formula
                .assignment
                .assign(lit.get_index().abs() as usize, !lit.is_negated());
            history.add_implication(&lit, None);
        }

        // Current decision level: decide x1.
        let x1 = x(1);
        formula.assignment.assign_history(&x1, &mut history);

        // Propagation sequence from Example 3.1 / Figure 1.
        let propagated = [
            (x(2), 0),
            (x(3).negated(), 1),
            (x(4), 2),
            (x(5), 3),
            (x(6).negated(), 4),
            (x(7), 5),
            (x(8), 6),
            (x(9).negated(), 7),
            (x(10).negated(), 8),
            (x(11), 9),
            (x(12), 10),
            (x(13), 11),
        ];

        for (lit, reason) in propagated {
            formula
                .assignment
                .assign(lit.get_index().abs() as usize, !lit.is_negated());
            history.add_implication(&lit, Some(reason));
        }

        let conflict_idx = 12;

        let (graph, first_uip) = graph_from_conflict(&history, &formula, conflict_idx)
            .expect("graph_from_conflict should build Figure 1 graph");

        assert_eq!(lit_key(&first_uip), lit_key(&x(5)));

        // Last row of Figure 2: DIP is x8 and ¬x9.
        let dip_a = x(8);
        let dip_b = x(9).negated();

        let (pre, post) = find_clauses_from_dip_pair(
            &graph,
            &history,
            &formula,
            conflict_idx,
            &dip_a,
            &dip_b,
            &first_uip,
        )
        .expect("DIP {x8, ¬x9} should produce pre/post clauses");

        assert_unique_literals(&pre);
        assert_unique_literals(&post);

        println!("prededuping: {:?}, {:?}", pre, post);
        println!("post: {:?}, {:?}", pre, post);

        // Figure 2 last row:
        // pre-DIP:  ¬x5 ∨ y1 ∨ ¬y3 ∨ ¬y4 ∨ z
        // post-DIP: ¬z ∨ ¬y4 ∨ ¬y5 ∨ y6
        let expected_pre: HashSet<_> = [
            lit_key(&x(5).negated()),
            lit_key(&y(1)),
            lit_key(&y(3).negated()),
            lit_key(&y(4).negated()),
        ]
        .into_iter()
        .collect();

        let expected_post: HashSet<_> = [
            lit_key(&y(4).negated()),
            lit_key(&y(5).negated()),
            lit_key(&y(6)),
        ]
        .into_iter()
        .collect();

        assert_eq!(lit_set(&pre), expected_pre);
        assert_eq!(lit_set(&post), expected_post);
    }

    #[test]
    fn dip_backtrack_level_uses_highest_lower_level_literal() {
        // Variables:
        // 1 x1 (level1), 2 p, 3 q, 4 y (level2), 5 x2 (level3),
        // 6 a, 7 b, 8 c, 9 d
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],      // 0: ¬x1 v p
            vec![-1, 3],      // 1: ¬x1 v q
            vec![-5, -2, 6],  // 2: ¬x2 v ¬p v a
            vec![-5, -3, 7],  // 3: ¬x2 v ¬q v b
            vec![-6, -2, 8],  // 4: ¬a v ¬p v c
            vec![-7, -3, 9],  // 5: ¬b v ¬q v d
            vec![-8, -9, -4], // 6: ¬c v ¬d v ¬y (conflict)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        // Level 1
        let x1 = Literal::new(1);
        formula.assignment.assign_history(&x1, &mut history);

        let p = Literal::new(2);
        formula
            .assignment
            .assign(p.get_index().abs() as usize, true);
        history.add_implication(&p, Some(0));

        let q = Literal::new(3);
        formula
            .assignment
            .assign(q.get_index().abs() as usize, true);
        history.add_implication(&q, Some(1));

        // Level 2
        let y = Literal::new(4);
        formula.assignment.assign_history(&y, &mut history);

        // Level 3
        let x2 = Literal::new(5);
        formula.assignment.assign_history(&x2, &mut history);

        let a = Literal::new(6);
        formula
            .assignment
            .assign(a.get_index().abs() as usize, true);
        history.add_implication(&a, Some(2));

        let b = Literal::new(7);
        formula
            .assignment
            .assign(b.get_index().abs() as usize, true);
        history.add_implication(&b, Some(3));

        let c = Literal::new(8);
        formula
            .assignment
            .assign(c.get_index().abs() as usize, true);
        history.add_implication(&c, Some(4));

        let d = Literal::new(9);
        formula
            .assignment
            .assign(d.get_index().abs() as usize, true);
        history.add_implication(&d, Some(5));

        let conflict_idx = 6;

        let (dip_a, dip_b, pre_clause_without_z, post_clause_without_z, backtrack_level) =
            match history.analyze_conflict(&formula, conflict_idx, ImplicationPoint::DIP) {
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                    ..
                } => (
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                ),
                _ => panic!("Expected DIP result"),
            };

        assert_unique_literals(&pre_clause_without_z);
        assert_unique_literals(&post_clause_without_z);

        // DIPs should still be {c, d}
        assert_eq!(unordered_pair(&dip_a, &dip_b), unordered_pair(&c, &d));

        // Pre-clause should contain ¬x2, ¬p, ¬q only.
        let not_x2 = x2.negated();
        let not_p = p.negated();
        let not_q = q.negated();

        let pre_set = lit_set(&pre_clause_without_z);
        let expected_pre: HashSet<_> = [lit_key(&not_x2), lit_key(&not_p), lit_key(&not_q)]
            .into_iter()
            .collect();
        assert_eq!(pre_set, expected_pre);

        // Post-clause should contain ¬y (y is level 2, conflict contains ¬y)
        let not_y = y.negated();
        let post_set = lit_set(&post_clause_without_z);
        let expected_post: HashSet<_> = [lit_key(&not_y)].into_iter().collect();
        assert_eq!(post_set, expected_post);

        // Backtrack level should be 2 (level of y)
        assert_eq!(backtrack_level, 2);
    }

    #[test]
    fn predip_is_not_asserting_when_lc_is_greater_than_ld() {
        use crate::formula::Formula;
        use crate::formula::clause::Clause;
        use crate::formula::literal::Literal;
        use crate::history::History;

        // Artificial trail:
        //
        // DL1: c
        // DL2: d      <- D = {d}
        // DL3: p      <- C = {p}
        // DL4: f      <- current conflict level / 1UIP level
        //
        // DIP clauses:
        // pre-DIP:  ¬f ∨ ¬p ∨ z
        // post-DIP: ¬z ∨ ¬d
        //
        // lC = level(p) = 3
        // lD = level(d) = 2
        //
        // Backjump to lD = 2:
        // d survives, so post-DIP is unit on ¬z.
        // p is unassigned, so after z=false, pre-DIP is ¬f ∨ ¬p, not unit.

        let mut formula = Formula::new(7);
        let mut history = History::new();

        let c = Literal::new(1);
        let d = Literal::new(2);
        let p = Literal::new(3);
        let f = Literal::new(4);
        let z = Literal::new(7);

        formula.assignment.assign_history(&c, &mut history); // DL1
        formula.assignment.assign_history(&d, &mut history); // DL2
        formula.assignment.assign_history(&p, &mut history); // DL3
        formula.assignment.assign_history(&f, &mut history); // DL4

        let l_c = history.get_literal_level(&p).unwrap();
        let l_d = history.get_literal_level(&d).unwrap();

        assert_eq!(l_c, 3);
        assert_eq!(l_d, 2);
        assert!(l_c > l_d);

        let pre_dip = Clause::from_literals(vec![f.negated(), p.negated(), z.clone()], -1);

        let post_dip = Clause::from_literals(vec![z.negated(), d.negated()], -1);

        // Paper backjump level: lD.
        // Keep levels <= 2, remove levels > 2.
        history.revert_decision(l_d + 1, &mut formula.assignment);

        assert_eq!(formula.assignment.get_value(1), Some(true)); // c survives
        assert_eq!(formula.assignment.get_value(2), Some(true)); // d survives
        assert_eq!(formula.assignment.get_value(3), None); // p gone
        assert_eq!(formula.assignment.get_value(4), None); // f gone
        assert_eq!(formula.assignment.get_value(7), None); // z fresh/unassigned

        // post-DIP: ¬z ∨ ¬d
        // d=true, so ¬d=false.
        // z is unassigned.
        // Therefore post-DIP is unit/asserting on ¬z.
        assert!(post_dip.is_unit(&formula.assignment));
        assert_eq!(
            post_dip.get_unit_literal(&formula.assignment),
            Some(&z.negated())
        );

        // Simulate post-DIP propagation: ¬z, i.e. z=false.
        formula
            .assignment
            .assign(z.get_index().abs() as usize, false);

        // pre-DIP: ¬f ∨ ¬p ∨ z
        // z=false.
        // f is unassigned.
        // p is unassigned because lC=3 > lD=2.
        //
        // So the clause has two unassigned literals: ¬f and ¬p.
        // Therefore it is NOT unit/asserting.
        assert!(!pre_dip.is_unit(&formula.assignment));

        let unassigned = pre_dip.get_unassigned_literals(&formula.assignment);
        assert_eq!(unassigned.len(), 2);
        assert!(unassigned.contains(&&f.negated()));
        assert!(unassigned.contains(&&p.negated()));
    }

    #[test]
    fn find_dip_backtracks_to_max_lc_ld_so_predip_asserts() {
        use crate::formula::Formula;
        use crate::formula::clause::Clause;
        use crate::formula::literal::Literal;
        use crate::history::{ConflictLearnResult, History, ImplicationPoint};

        // Variables:
        //
        // Lower levels:
        //   d at DL1
        //   p at DL2
        //
        // Current level DL3:
        //   f decision / 1UIP
        //   a implied from f and p
        //   b implied from f
        //   conflict from a, b, d
        //
        // Clauses:
        //
        // 0: ¬f ∨ ¬p ∨ a
        //      f=true and p=true imply a=true.
        //      This makes p a lower-level predecessor before the DIP.
        //
        // 1: ¬f ∨ b
        //      f=true implies b=true.
        //
        // 2: ¬a ∨ ¬b ∨ ¬d
        //      a=true, b=true, d=true conflict.
        //      This makes d a lower-level predecessor after the DIP.
        //
        // Current-level graph:
        //
        //        p
        //        |
        //        v
        // f ---> a ----\
        //  \            conflict
        //   ---> b ----/
        //        ^
        //        |
        //        d enters at the conflict clause
        //
        // DIP pair should be {a,b}.
        //
        // C = {p}
        // D = {d}
        //
        // lC = DL(p) = 2
        // lD = DL(d) = 1
        //
        // Since this implementation backjumps to max(lC, lD), both the
        // post-DIP and pre-DIP clauses should become asserting.

        let clauses = vec![
            vec![-3, -2, 4],  // 0: ¬f ∨ ¬p ∨ a
            vec![-3, 5],      // 1: ¬f ∨ b
            vec![-4, -5, -1], // 2: ¬a ∨ ¬b ∨ ¬d conflict
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let d = Literal::new(1);
        let p = Literal::new(2);
        let f = Literal::new(3);
        let a = Literal::new(4);
        let b = Literal::new(5);

        // DL1: d=true
        formula.assignment.assign_history(&d, &mut history);

        // DL2: p=true
        formula.assignment.assign_history(&p, &mut history);

        // DL3 current level: f decision
        formula.assignment.assign_history(&f, &mut history);

        // f,p imply a through clause 0.
        formula
            .assignment
            .assign(a.get_index().abs() as usize, true);
        history.add_implication(&a, Some(0));

        // f implies b through clause 1.
        formula
            .assignment
            .assign(b.get_index().abs() as usize, true);
        history.add_implication(&b, Some(1));

        let conflict_idx = 2;

        let result = history.analyze_conflict(&formula, conflict_idx, ImplicationPoint::DIP);

        let (dip_a, dip_b, pre_clause_without_z, post_clause_without_z, backtrack_level) =
            match result {
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                    ..
                } => (
                    dip_a,
                    dip_b,
                    pre_clause_without_z,
                    post_clause_without_z,
                    backtrack_level,
                ),
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                    ..
                } => {
                    panic!(
                        "expected DIP result, got UIP clause {:?} with backtrack level {}",
                        clause, backtrack_level
                    );
                }
            };

        let unordered = |x: &Literal, y: &Literal| {
            let mut pair = vec![x.get_index(), y.get_index()];
            pair.sort();
            pair
        };

        assert_eq!(unordered(&dip_a, &dip_b), unordered(&a, &b));

        // pre_clause_without_z represents:
        //   ¬f ∨ ¬C
        //
        // Expected:
        //   ¬f ∨ ¬p
        assert!(pre_clause_without_z.contains(&f.negated()));
        assert!(pre_clause_without_z.contains(&p.negated()));

        // post_clause_without_z represents:
        //   ¬D
        //
        // Expected:
        //   ¬d
        assert_eq!(post_clause_without_z, vec![d.negated()]);

        let l_c = history.get_literal_level(&p).unwrap();
        let l_d = history.get_literal_level(&d).unwrap();

        assert_eq!(l_c, 2);
        assert_eq!(l_d, 1);
        assert!(l_c > l_d);

        // This variant backtracks to max(lC, lD) so both post-DIP and pre-DIP assert.
        assert_eq!(backtrack_level, std::cmp::max(l_c, l_d));

        // Introduce z as if solve_cdcl had created the extension:
        //
        // z <-> a ∧ b
        //
        // pre-DIP:  z ∨ ¬f ∨ ¬p
        // post-DIP: ¬z ∨ ¬d
        let z = formula.add_literal();

        let mut pre_lits = vec![z.clone()];
        pre_lits.extend(pre_clause_without_z.clone());
        let pre_dip = Clause::from_literals(pre_lits, -1);

        let mut post_lits = vec![z.negated()];
        post_lits.extend(post_clause_without_z.clone());
        let post_dip = Clause::from_literals(post_lits, -1);

        // Backjump to max(lC, lD).
        history.revert_decision(backtrack_level + 1, &mut formula.assignment);

        // d survives at DL1.
        assert_eq!(
            formula.assignment.get_value(d.get_index().abs() as usize),
            Some(true)
        );

        // p survives because backtrack_level is max(lC, lD)=2.
        assert_eq!(
            formula.assignment.get_value(p.get_index().abs() as usize),
            Some(true)
        );

        // f, a, b are current-level and are also gone.
        assert_eq!(
            formula.assignment.get_value(f.get_index().abs() as usize),
            None
        );
        assert_eq!(
            formula.assignment.get_value(a.get_index().abs() as usize),
            None
        );
        assert_eq!(
            formula.assignment.get_value(b.get_index().abs() as usize),
            None
        );

        // z is fresh/unassigned.
        assert_eq!(
            formula.assignment.get_value(z.get_index().abs() as usize),
            None
        );

        // post-DIP: ¬z ∨ ¬d
        // d=true, so ¬d=false.
        // z is unassigned.
        // Therefore post-DIP is unit on ¬z.
        assert!(post_dip.is_unit(&formula.assignment));
        assert_eq!(
            post_dip.get_unit_literal(&formula.assignment),
            Some(&z.negated())
        );

        // Simulate propagation of ¬z.
        formula
            .assignment
            .assign(z.get_index().abs() as usize, false);

        // pre-DIP: z ∨ ¬f ∨ ¬p
        // z=false and p=true, so z=false and ¬p=false.
        // f is unassigned, therefore pre-DIP is unit on ¬f.
        assert!(pre_dip.is_unit(&formula.assignment));
        assert_eq!(
            pre_dip.get_unit_literal(&formula.assignment),
            Some(&f.negated())
        );
    }
}
