//! Linear-time two-vertex bottlenecks for topologically ordered DAGs.
//!
//! This is a compact Rust specialization of the algorithm used by
//! xMapleLCM-DIP's `TwoVertexBottlenecks::CalcBottlenecks`. The graph is
//! traversed backwards, from sink `0` to source `N - 1`, through predecessor
//! edges. Consequently every predecessor of `v` must have an ID greater than
//! `v`.

const ON_FIRST: u8 = 1;
const ON_SECOND: u8 = 2;
const REACHED: u8 = 4;
const NONE: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct VertexInfo {
    successor: u32,
    status: u8,
}

impl Default for VertexInfo {
    fn default() -> Self {
        Self {
            successor: NONE,
            status: 0,
        }
    }
}

#[derive(Clone, Copy)]
struct Pivot {
    vertex: u32,
    path_position: u32,
    reach_other: u32,
}

#[derive(Clone, Copy)]
struct Candidate {
    vertex: u32,
    path_position: u32,
    min_pair: u32,
    max_pair: u32,
}

#[derive(Default)]
pub(super) struct BottleneckScratch {
    vertices: Vec<VertexInfo>,
    stack: Vec<u32>,
    direct: Vec<[u32; 2]>,
    pivots: [Vec<Pivot>; 2],
    // Both paths run from the source to the sink. Candidate lists run in the
    // opposite order and hold inclusive index ranges into the other list.
    paths: [Vec<u32>; 2],
    lists: [Vec<Candidate>; 2],
}

/// Returns a valid two-vertex bottleneck near the middle of the two paths.
///
/// `pred_index` has one entry per vertex, matching xMapleLCM's compact CSR
/// convention. The predecessors of `v < N - 1` occupy
/// `predecessors[pred_index[v]..pred_index[v + 1]]`; `pred_index[N - 1]` is
/// `predecessors.len()`, since the source has no predecessors. The sink is
/// vertex `0`, the source is vertex `N - 1`, and every listed predecessor of
/// `v` must be in `(v, N)`.
///
/// `None` is returned for malformed input, fewer than two internally
/// vertex-disjoint source-to-sink paths, three internally vertex-disjoint
/// paths, or no valid two-vertex bottleneck. A graph with a single-vertex
/// bottleneck deliberately returns `None`.
///
/// The running time and storage are `O(N + E)`. No per-edge allocation or
/// max-flow network is constructed.
pub fn find_middle_pair(predecessors: &[u32], pred_index: &[u32]) -> Option<(u32, u32)> {
    let n = validate_csr(predecessors, pred_index)?;
    let mut scratch = BottleneckScratch::default();
    calculate_candidates(predecessors, pred_index, n, &mut scratch)?;
    scratch.middle_pair()
}

/// Internal fast path: callers must supply construction-validated, topologically
/// ordered CSR with the source at the final vertex (no trailing CSR offset).
pub(super) fn find_middle_pair_with_scratch(
    predecessors: &[u32],
    pred_index: &[u32],
    scratch: &mut BottleneckScratch,
) -> Option<(u32, u32)> {
    let n = pred_index.len();
    if n < 2 {
        return None;
    }
    calculate_candidates(predecessors, pred_index, n, scratch)?;
    scratch.middle_pair()
}

fn validate_csr(predecessors: &[u32], pred_index: &[u32]) -> Option<usize> {
    let n = pred_index.len();
    if n < 2 || n > u32::MAX as usize || pred_index[0] != 0 {
        return None;
    }
    if pred_index[n - 1] as usize != predecessors.len() {
        return None;
    }

    for vertex in 0..n - 1 {
        let start = pred_index[vertex] as usize;
        let end = pred_index[vertex + 1] as usize;
        if start > end || end > predecessors.len() || start == end {
            return None;
        }
        if predecessors[start..end]
            .iter()
            .any(|&pred| pred as usize <= vertex || pred as usize >= n)
        {
            return None;
        }
    }
    Some(n)
}

fn calculate_candidates(
    predecessors: &[u32],
    pred_index: &[u32],
    n: usize,
    scratch: &mut BottleneckScratch,
) -> Option<()> {
    let BottleneckScratch {
        vertices,
        stack,
        direct,
        pivots,
        paths,
        lists,
    } = scratch;
    let source = (n - 1) as u32;
    vertices.resize(n, VertexInfo::default());
    vertices.fill(VertexInfo::default());
    stack.clear();
    for path in paths.iter_mut() {
        path.clear();
    }
    for pivot in pivots.iter_mut() {
        pivot.clear();
    }
    for list in lists.iter_mut() {
        list.clear();
    }

    // Phase A: choose the same initial sink-to-source path as xMaple.
    let mut current = 0u32;
    vertices[0].status |= ON_FIRST;
    while current != source {
        let next = predecessors[pred_index[current as usize] as usize];
        vertices[next as usize].successor = current;
        vertices[next as usize].status |= ON_FIRST;
        current = next;
    }

    // Phase B: augment without constructing a flow network.
    let second_path_top =
        find_two_disjoint_paths(predecessors, pred_index, vertices, source, stack)?;
    label_and_collect_paths(vertices, second_path_top, source, paths)?;

    // Phase C: reachability outside the two paths.
    direct_path_reach(predecessors, pred_index, vertices, source, direct);
    if direct[0][0] == source || direct[0][1] == source {
        return None;
    }

    // Phases D/E: retain candidates and encode compatible ranges.
    non_bypassed_pivots(&paths[0], 1, direct, source, &mut pivots[0]);
    non_bypassed_pivots(&paths[1], 0, direct, source, &mut pivots[1]);
    if pivots[0].len() <= 1 || pivots[1].len() <= 1 {
        return None;
    }
    candidate_bounds(&pivots[0], &pivots[1], source, &mut lists[0]);
    candidate_bounds(&pivots[1], &pivots[0], source, &mut lists[1]);
    if lists[0].is_empty() || lists[1].is_empty() {
        return None;
    }
    let (left, right) = lists.split_at_mut(1);
    bounds_to_indices(&mut left[0], &right[0])?;
    bounds_to_indices(&mut right[0], &left[0])?;
    Some(())
}

fn find_two_disjoint_paths(
    predecessors: &[u32],
    pred_index: &[u32],
    vertices: &mut [VertexInfo],
    source: u32,
    stack: &mut Vec<u32>,
) -> Option<u32> {
    let mut dfs_start = 0u32;
    let mut furthest_on_first = 0u32;
    let mut furthest_from = NONE;

    loop {
        stack.push(dfs_start);
        vertices[dfs_start as usize].status |= REACHED;

        while let Some(vertex) = stack.pop() {
            let start = pred_index[vertex as usize] as usize;
            let end = pred_index[vertex as usize + 1] as usize;
            for &pred in &predecessors[start..end] {
                let info = &mut vertices[pred as usize];
                if info.status & ON_FIRST != 0 {
                    if pred > furthest_on_first {
                        furthest_on_first = pred;
                        furthest_from = vertex;
                    }
                } else if info.status & REACHED == 0 {
                    info.status |= REACHED;
                    info.successor = vertex;
                    stack.push(pred);
                }
            }
        }

        if furthest_on_first == source {
            return (furthest_from != NONE).then_some(furthest_from);
        }
        if furthest_from == NONE {
            return None;
        }

        let mut backtrack = furthest_from;
        while vertices[backtrack as usize].status & ON_FIRST == 0 {
            vertices[backtrack as usize].status |= ON_FIRST;
            backtrack = vertices[backtrack as usize].successor;
            if backtrack == NONE {
                return None;
            }
        }

        backtrack = furthest_on_first;
        loop {
            let next = vertices[backtrack as usize].successor;
            if next == NONE {
                return None;
            }
            if vertices[next as usize].status & REACHED != 0 {
                break;
            }
            vertices[next as usize].status &= !ON_FIRST;
            backtrack = next;
        }

        // No augmentation past this vertex means it is itself a bottleneck.
        if backtrack == furthest_on_first {
            return None;
        }

        vertices[furthest_on_first as usize].successor = furthest_from;
        dfs_start = backtrack;
        furthest_on_first = 0;
        furthest_from = NONE;
    }
}

fn label_and_collect_paths(
    vertices: &mut [VertexInfo],
    second_path_top: u32,
    source: u32,
    paths: &mut [Vec<u32>; 2],
) -> Option<()> {
    let [second, first] = paths;
    second.push(source);
    vertices[source as usize].status |= ON_SECOND;

    let mut current = second_path_top;
    while current != 0 {
        second.push(current);
        let info = &mut vertices[current as usize];
        info.status = (info.status | ON_SECOND) & !ON_FIRST;
        current = info.successor;
        if current == NONE {
            return None;
        }
    }
    vertices[0].status |= ON_SECOND;
    second.push(0);

    current = source;
    loop {
        if vertices[current as usize].status & ON_FIRST == 0 {
            return None;
        }
        first.push(current);
        if current == 0 {
            break;
        }
        current = vertices[current as usize].successor;
        if current == NONE {
            return None;
        }
    }

    // Match xMaple's list/path association: list A uses the augmented second
    // path, list B the remaining first path.
    Some(())
}

fn direct_path_reach(
    predecessors: &[u32],
    pred_index: &[u32],
    vertices: &[VertexInfo],
    source: u32,
    direct: &mut Vec<[u32; 2]>,
) {
    direct.resize(vertices.len(), [0; 2]);
    direct[source as usize] = [source, source];

    for vertex in (0..source as usize).rev() {
        let start = pred_index[vertex] as usize;
        let end = pred_index[vertex + 1] as usize;
        let mut reach = [0u32; 2];

        for &pred in &predecessors[start..end] {
            let on_paths = vertices[pred as usize].status & (ON_FIRST | ON_SECOND);
            if on_paths == 0 {
                reach[0] = reach[0].max(direct[pred as usize][0]);
                reach[1] = reach[1].max(direct[pred as usize][1]);
            } else {
                if on_paths & ON_FIRST != 0 {
                    reach[0] = reach[0].max(pred);
                }
                if on_paths & ON_SECOND != 0 {
                    reach[1] = reach[1].max(pred);
                }
            }
        }
        direct[vertex] = reach;
    }
}

fn non_bypassed_pivots(
    path: &[u32],
    path_bit: usize,
    direct: &[[u32; 2]],
    source: u32,
    result: &mut Vec<Pivot>,
) {
    let other_bit = 1 - path_bit;
    let mut reach_same = direct[0][path_bit];
    let mut reach_other = direct[0][other_bit];

    // Paths are source-to-sink, while pivots and candidates are sink-to-source.
    for (position, &vertex) in path.iter().enumerate().take(path.len() - 1).skip(1).rev() {
        if vertex >= reach_same {
            result.push(Pivot {
                vertex,
                path_position: position as u32,
                reach_other,
            });
        }
        reach_same = reach_same.max(direct[vertex as usize][path_bit]);
        reach_other = reach_other.max(direct[vertex as usize][other_bit]);
    }

    result.push(Pivot {
        vertex: source,
        path_position: 0,
        reach_other: source,
    });
}

fn candidate_bounds(this: &[Pivot], other: &[Pivot], source: u32, result: &mut Vec<Candidate>) {
    let last_internal_other = other[other.len() - 2].vertex;
    let mut other_idx = 0usize;

    for pivot in &this[..this.len() - 1] {
        while other[other_idx].reach_other <= pivot.vertex {
            other_idx += 1;
        }
        if other_idx == 0 {
            continue;
        }

        let lower = pivot.reach_other;
        let upper = other[other_idx - 1].vertex;
        if lower <= upper && (upper < source || lower <= last_internal_other) {
            result.push(Candidate {
                vertex: pivot.vertex,
                path_position: pivot.path_position,
                min_pair: lower,
                max_pair: upper,
            });
        }
    }
}

fn bounds_to_indices(this: &mut [Candidate], other: &[Candidate]) -> Option<()> {
    let mut min_idx = 0usize;
    let mut max_idx = 0usize;

    for candidate in this {
        while other.get(min_idx)?.vertex < candidate.min_pair {
            min_idx += 1;
        }
        while max_idx + 1 < other.len() && other[max_idx + 1].vertex <= candidate.max_pair {
            max_idx += 1;
        }
        if min_idx > max_idx {
            return None;
        }
        candidate.min_pair = u32::try_from(min_idx).ok()?;
        candidate.max_pair = u32::try_from(max_idx).ok()?;
    }
    Some(())
}

impl BottleneckScratch {
    fn middle_pair(&self) -> Option<(u32, u32)> {
        // xMaple first chooses the candidate nearest the midpoint of the
        // longer complete path, then the compatible candidate nearest the
        // midpoint of the other path.
        let longest = usize::from(self.paths[0].len() <= self.paths[1].len());
        let shortest = 1 - longest;

        let longest_candidates = &self.lists[longest];
        let shortest_candidates = &self.lists[shortest];
        let longest_idx = closest_to_middle(
            longest_candidates,
            self.paths[longest].len(),
            0,
            longest_candidates.len() - 1,
        );

        let chosen = self.lists[longest][longest_idx];
        let min_short = chosen.min_pair as usize;
        let max_short = chosen.max_pair as usize;
        if min_short > max_short || max_short >= shortest_candidates.len() {
            return None;
        }
        let shortest_idx = closest_to_middle(
            shortest_candidates,
            self.paths[shortest].len(),
            min_short,
            max_short,
        );

        let pair = (
            self.lists[longest][longest_idx].vertex,
            self.lists[shortest][shortest_idx].vertex,
        );
        Some(if longest == 0 { pair } else { (pair.1, pair.0) })
    }
}

fn closest_to_middle(candidates: &[Candidate], path_len: usize, start: usize, end: usize) -> usize {
    let middle = path_len / 2;
    let mut best = start;
    let mut best_distance = middle.abs_diff(candidates[start].path_position as usize);

    for idx in start + 1..=end {
        let distance = middle.abs_diff(candidates[idx].path_position as usize);
        if distance < best_distance {
            best = idx;
            best_distance = distance;
        } else {
            break;
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::find_middle_pair;

    fn csr(vertex_count: usize, edges: &[(u32, u32)]) -> (Vec<u32>, Vec<u32>) {
        let mut incoming = vec![Vec::new(); vertex_count];
        for &(from, to) in edges {
            assert!((from as usize) < vertex_count && from > to);
            incoming[to as usize].push(from);
        }

        let mut predecessors = Vec::new();
        let mut pred_index = Vec::with_capacity(vertex_count);
        for preds in incoming {
            pred_index.push(predecessors.len() as u32);
            predecessors.extend(preds);
        }
        (predecessors, pred_index)
    }

    fn path_exists_avoiding(vertex_count: usize, edges: &[(u32, u32)], banned: (u32, u32)) -> bool {
        let source = vertex_count as u32 - 1;
        let mut reachable = vec![false; vertex_count];
        reachable[source as usize] = source != banned.0 && source != banned.1;

        for vertex in (1..vertex_count).rev() {
            if !reachable[vertex] {
                continue;
            }
            for &(from, to) in edges {
                if from as usize == vertex && to != banned.0 && to != banned.1 {
                    reachable[to as usize] = true;
                }
            }
        }
        reachable[0]
    }

    #[test]
    fn public_entry_point_rejects_malformed_csr() {
        for (predecessors, index) in [
            (vec![], vec![]),
            (vec![1], vec![1, 1]),
            (vec![1], vec![0, 0]),
            (vec![0], vec![0, 1]),
            (vec![2], vec![0, 1]),
            (vec![], vec![0, 0]),
            (vec![2, 2], vec![0, 3, 2]),
        ] {
            assert_eq!(find_middle_pair(&predecessors, &index), None);
        }
    }

    #[test]
    fn reused_scratch_preserves_middle_pair_and_resets_after_rejection() {
        let mut scratch = super::BottleneckScratch::default();
        let graphs = [
            (4, vec![(3, 1), (1, 0), (3, 2), (2, 0)]),
            (5, vec![(4, 1), (1, 0), (4, 2), (2, 0), (4, 3), (3, 0)]),
            (
                8,
                vec![
                    (7, 5),
                    (5, 3),
                    (3, 1),
                    (1, 0),
                    (7, 6),
                    (6, 4),
                    (4, 2),
                    (2, 0),
                ],
            ),
        ];
        for _ in 0..2 {
            for (n, edges) in &graphs {
                let (predecessors, pred_index) = csr(*n, edges);
                assert_eq!(
                    super::find_middle_pair_with_scratch(&predecessors, &pred_index, &mut scratch),
                    find_middle_pair(&predecessors, &pred_index),
                );
            }
        }
    }

    #[test]
    fn two_parallel_paths_yield_a_valid_middle_pair() {
        let edges = [(3, 1), (1, 0), (3, 2), (2, 0)];
        let (predecessors, pred_index) = csr(4, &edges);

        let pair = find_middle_pair(&predecessors, &pred_index).unwrap();
        assert_eq!((pair.0.min(pair.1), pair.0.max(pair.1)), (1, 2));
        assert!(!path_exists_avoiding(4, &edges, pair));
    }

    #[test]
    fn three_internally_disjoint_paths_yield_none() {
        let edges = [(4, 1), (1, 0), (4, 2), (2, 0), (4, 3), (3, 0)];
        let (predecessors, pred_index) = csr(5, &edges);

        assert_eq!(find_middle_pair(&predecessors, &pred_index), None);
    }

    #[test]
    fn single_vertex_bottleneck_yields_none() {
        let edges = [(4, 3), (3, 1), (1, 0), (3, 2), (2, 0)];
        let (predecessors, pred_index) = csr(5, &edges);

        assert_eq!(find_middle_pair(&predecessors, &pred_index), None);
    }

    #[test]
    fn bypass_and_cross_edge_reject_invalid_pairs() {
        // Base paths (shown from source to sink):
        // 7-5-3-1-0 and 7-6-4-2-0. The two cross edges make vertex 3
        // incompatible with every vertex on the other path.
        let edges = [
            (7, 5),
            (5, 3),
            (3, 1),
            (1, 0),
            (7, 6),
            (6, 4),
            (4, 2),
            (2, 0),
            (6, 1),
            (5, 2),
        ];
        let (predecessors, pred_index) = csr(8, &edges);

        let pair = find_middle_pair(&predecessors, &pred_index).unwrap();
        assert_ne!(pair.0, 3);
        assert_ne!(pair.1, 3);
        assert!(!path_exists_avoiding(8, &edges, pair), "returned {pair:?}");
    }

    #[test]
    fn exhaustive_small_dags_match_a_separator_oracle() {
        for vertex_count in 4usize..=6 {
            let mut possible_edges = Vec::new();
            for from in 1..vertex_count as u32 {
                for to in 0..from {
                    possible_edges.push((from, to));
                }
            }

            for mask in 0usize..1usize << possible_edges.len() {
                let edges: Vec<_> = possible_edges
                    .iter()
                    .enumerate()
                    .filter_map(|(bit, &edge)| ((mask >> bit) & 1 == 1).then_some(edge))
                    .collect();

                let mut has_predecessor = vec![false; vertex_count - 1];
                for &(_, to) in &edges {
                    has_predecessor[to as usize] = true;
                }
                if has_predecessor.iter().any(|&present| !present) {
                    continue;
                }

                let has_single_bottleneck = (1..vertex_count as u32 - 1)
                    .any(|vertex| !path_exists_avoiding(vertex_count, &edges, (vertex, vertex)));
                let mut valid_pairs = Vec::new();
                for left in 1..vertex_count as u32 - 1 {
                    for right in left + 1..vertex_count as u32 - 1 {
                        if !path_exists_avoiding(vertex_count, &edges, (left, right)) {
                            valid_pairs.push((left, right));
                        }
                    }
                }

                let (predecessors, pred_index) = csr(vertex_count, &edges);
                let actual = find_middle_pair(&predecessors, &pred_index);
                let expected_some = !has_single_bottleneck && !valid_pairs.is_empty();
                assert_eq!(
                    actual.is_some(),
                    expected_some,
                    "vertex_count={vertex_count} edges={edges:?} pairs={valid_pairs:?}"
                );
                if let Some(pair) = actual {
                    assert!(
                        !path_exists_avoiding(vertex_count, &edges, pair),
                        "returned non-separator {pair:?} for {edges:?}"
                    );
                }
            }
        }
    }
}
