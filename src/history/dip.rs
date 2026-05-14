use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::formula::Formula;
use crate::history::uip::find_1uip;
use crate::history::ConflictLearnResult;
use crate::history::History;

use std::collections::HashSet;
use std::collections::VecDeque;

/// Trail-indexed current-level slice.
///
/// `trail.len()` is the synthetic conflict node.
/// `source_pos` is the 1UIP boundary we stop at.
struct DipSlice {
    trail: Vec<Literal>,
    source_pos: usize,
    succ: Vec<Vec<usize>>,
    present: Vec<bool>,
    reason_of: Vec<Option<usize>>,
    pos_of: Vec<Option<usize>>, // signed-index -> trail position
}

fn current_level_context(
    history: &History,
    formula: &Formula,
) -> (Vec<Literal>, Vec<Option<usize>>, Vec<Option<usize>>) {
    let level = &history.decision_levels[history.get_decision_level()];

    let mut trail = Vec::new();
    let mut pos_of = vec![None; formula.assignment.len() * 2];
    let mut reason_of = Vec::new();

    if let Some(decision) = level.get_decision_literal() {
        pos_of[decision.get_signed_index() as usize] = Some(trail.len());
        trail.push(decision.clone());
        reason_of.push(None);
    }

    for lit in level.implied_literals_iter() {
        pos_of[lit.get_signed_index() as usize] = Some(trail.len());
        trail.push(lit.clone());
        reason_of.push(level.get_reason(lit));
    }

    (trail, pos_of, reason_of)
}

fn current_level_predecessors(
    node_idx: usize,
    trail: &[Literal],
    source_pos: usize,
    reason_of: &[Option<usize>],
    pos_of: &[Option<usize>],
    formula: &Formula,
    conflict_clause_idx: usize,
) -> Vec<usize> {
    let conflict_idx = trail.len();

    if node_idx == conflict_idx {
        return formula.get_clauses()[conflict_clause_idx]
            .get_literals()
            .iter()
            .filter_map(|lit| {
                let pred = lit.negated();
                pos_of.get(pred.get_signed_index() as usize).copied().flatten()
            })
            .collect();
    }

    if node_idx == source_pos {
        return vec![];
    }

    let reason_idx = match reason_of.get(node_idx).copied().flatten() {
        Some(idx) => idx,
        None => return vec![],
    };

    let current_lit = &trail[node_idx];

    formula.get_clauses()[reason_idx]
        .get_literals()
        .iter()
        .filter(|reason_lit| *reason_lit != current_lit)
        .filter_map(|reason_lit| {
            let pred = reason_lit.negated();
            pos_of.get(pred.get_signed_index() as usize).copied().flatten()
        })
        .collect()
}

fn build_dip_slice(
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
) -> Option<DipSlice> {
    let current_level = history.get_decision_level();
    if current_level == 0 {
        return None;
    }

    let (uip_clause, _) = find_1uip(history, formula, conflict_clause_idx);
    let first_uip = uip_clause
        .iter()
        .find(|lit| history.get_literal_level(lit) == Some(current_level))
        .map(|lit| lit.negated())?;

    let (trail, pos_of, reason_of) = current_level_context(history, formula);
    let source_pos = pos_of.get(first_uip.get_signed_index() as usize).copied().flatten()?;

    let conflict_idx = trail.len();
    let mut succ = vec![Vec::new(); conflict_idx + 1];
    let mut present = vec![false; conflict_idx + 1];
    let mut queue = VecDeque::new();

    present[conflict_idx] = true;
    queue.push_back(conflict_idx);

    while let Some(node_idx) = queue.pop_front() {
        for pred_idx in current_level_predecessors(
            node_idx,
            &trail,
            source_pos,
            &reason_of,
            &pos_of,
            formula,
            conflict_clause_idx,
        ) {
            succ[pred_idx].push(node_idx);
            if !present[pred_idx] {
                present[pred_idx] = true;
                queue.push_back(pred_idx);
            }
        }
    }

    if !present[source_pos] {
        return None;
    }

    Some(DipSlice {
        trail,
        source_pos,
        succ,
        present,
        reason_of,
        pos_of,
    })
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

fn reverse_reachable(rev: &[Vec<usize>], start: usize, present: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; rev.len()];
    let mut queue = VecDeque::new();

    if start < rev.len() && present[start] {
        seen[start] = true;
        queue.push_back(start);
    }

    while let Some(u) = queue.pop_front() {
        for &p in &rev[u] {
            if present[p] && !seen[p] {
                seen[p] = true;
                queue.push_back(p);
            }
        }
    }

    seen
}

fn forward_reachable(adj: &[Vec<usize>], start: usize, present: &[bool]) -> Vec<bool> {
    let mut seen = vec![false; adj.len()];
    let mut queue = VecDeque::new();

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

fn find_all_two_vertex_bottlenecks(slice: &DipSlice) -> Option<Vec<(Literal, Literal)>> {
    let conflict_idx = slice.trail.len();
    let rev = reverse_adj(&slice.succ);
    let can_reach_t = reverse_reachable(&rev, conflict_idx, &slice.present);

    let mut source_candidates = Vec::new();
    for pos in 0..slice.trail.len() {
        if !slice.present[pos] || !can_reach_t[pos] {
            continue;
        }

        let indeg = rev[pos]
            .iter()
            .filter(|&&p| slice.present[p] && can_reach_t[p])
            .count();

        if indeg == 0 {
            source_candidates.push(pos);
        }
    }

    if source_candidates.len() != 1 || source_candidates[0] != slice.source_pos {
        return None;
    }

    let reachable_from_s = forward_reachable(&slice.succ, slice.source_pos, &slice.present);
    let relevant: Vec<bool> = (0..=conflict_idx)
        .map(|idx| slice.present[idx] && reachable_from_s[idx] && can_reach_t[idx])
        .collect();

    let candidates: Vec<usize> = (0..slice.trail.len())
        .filter(|&pos| pos != slice.source_pos && relevant[pos])
        .collect();

    let mut out = Vec::new();
    for i in 0..candidates.len() {
        for j in (i + 1)..candidates.len() {
            if !exists_path_avoiding_pair(
                &slice.succ,
                &relevant,
                slice.source_pos,
                conflict_idx,
                candidates[i],
                candidates[j],
            ) {
                out.push((
                    slice.trail[candidates[i]].clone(),
                    slice.trail[candidates[j]].clone(),
                ));
            }
        }
    }

    Some(out)
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
    let mut queue = VecDeque::new();

    seen[s] = true;
    queue.push_back(s);

    while let Some(u) = queue.pop_front() {
        if u == t {
            return true;
        }

        for &v in &adj[u] {
            if !relevant[v] || seen[v] || v == ban_a || v == ban_b {
                continue;
            }
            seen[v] = true;
            queue.push_back(v);
        }
    }

    false
}

fn collect_lower_level_preds(
    region: &[bool],
    slice: &DipSlice,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
) -> Vec<Literal> {
    let current_level = history.get_decision_level();
    let conflict_idx = slice.trail.len();

    let mut seen = HashSet::new();
    let mut out = Vec::new();

    for idx in 0..region.len() {
        if !region[idx] {
            continue;
        }

        if idx == conflict_idx {
            let conflict_clause = &formula.get_clauses()[conflict_clause_idx];
            for conflict_lit in conflict_clause.get_literals() {
                let pred = conflict_lit.negated();
                if history.get_literal_level(&pred).unwrap_or(0) < current_level
                    && seen.insert(pred.get_signed_index())
                {
                    out.push(pred);
                }
            }
            continue;
        }

        let lit = &slice.trail[idx];
        if history.get_literal_level(lit) != Some(current_level) {
            continue;
        }

        let Some(reason_idx) = slice.reason_of[idx] else {
            continue;
        };

        let reason = &formula.get_clauses()[reason_idx];
        for reason_lit in reason.get_literals() {
            if reason_lit == lit {
                continue;
            }

            let pred = reason_lit.negated();
            if history.get_literal_level(&pred).unwrap_or(0) < current_level
                && seen.insert(pred.get_signed_index())
            {
                out.push(pred);
            }
        }
    }

    out
}

fn find_clauses_from_dip_pair(
    slice: &DipSlice,
    history: &History,
    formula: &Formula,
    conflict_clause_idx: usize,
    dip_a: &Literal,
    dip_b: &Literal,
) -> Option<(Vec<Literal>, Vec<Literal>)> {
    if dip_a == dip_b {
        return None;
    }

    let dip_a_pos = slice
        .pos_of
        .get(dip_a.get_signed_index() as usize)
        .copied()
        .flatten()?;
    let dip_b_pos = slice
        .pos_of
        .get(dip_b.get_signed_index() as usize)
        .copied()
        .flatten()?;
    let first_uip_pos = slice.source_pos;
    let conflict_idx = slice.trail.len();

    if dip_a_pos == first_uip_pos || dip_b_pos == first_uip_pos {
        return None;
    }

    let mut pre_region = vec![false; conflict_idx + 1];
    let mut queue = VecDeque::new();
    pre_region[first_uip_pos] = true;
    queue.push_back(first_uip_pos);

    while let Some(node_idx) = queue.pop_front() {
        if node_idx == dip_a_pos || node_idx == dip_b_pos {
            continue;
        }

        for &succ in &slice.succ[node_idx] {
            if !pre_region[succ] {
                pre_region[succ] = true;
                queue.push_back(succ);
            }
        }
    }

    pre_region[dip_a_pos] = true;
    pre_region[dip_b_pos] = true;

    let mut post_region = vec![false; conflict_idx + 1];
    let mut queue = VecDeque::new();

    for &start in &[dip_a_pos, dip_b_pos] {
        for &succ in &slice.succ[start] {
            if !post_region[succ] {
                post_region[succ] = true;
                queue.push_back(succ);
            }
        }
    }

    while let Some(node_idx) = queue.pop_front() {
        for &succ in &slice.succ[node_idx] {
            if !post_region[succ] {
                post_region[succ] = true;
                queue.push_back(succ);
            }
        }
    }

    if !post_region[conflict_idx] {
        return None;
    }

    let mut pre_lits = vec![slice.trail[first_uip_pos].negated()];
    for lit in collect_lower_level_preds(&pre_region, slice, history, formula, conflict_clause_idx) {
        pre_lits.push(lit.negated());
    }

    let mut post_lits = Vec::new();
    for lit in collect_lower_level_preds(&post_region, slice, history, formula, conflict_clause_idx) {
        post_lits.push(lit.negated());
    }

    Some((pre_lits, post_lits))
}

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

    let Some(slice) = build_dip_slice(history, formula, conflict_clause_index) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    let Some(mut dips) = find_all_two_vertex_bottlenecks(&slice) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    if dips.is_empty() {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    }

    let (a, b) = choose_best_dip_pair(&mut dips, &slice, history);

    let Some((pre_lits, post_lits)) = find_clauses_from_dip_pair(
        &slice,
        history,
        formula,
        conflict_clause_index,
        &a,
        &b,
    ) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    if post_lits.is_empty() || a.get_index() == b.get_index() {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    }

    let backtrack_level = post_lits
        .iter()
        .filter_map(|lit| history.get_literal_level(lit))
        .max()
        .unwrap_or(0);

    ConflictLearnResult::Dip {
        dip_a: a,
        dip_b: b,
        pre_clause_without_z: pre_lits,
        post_clause_without_z: post_lits,
        backtrack_level,
    }
}

fn choose_best_dip_pair(
    dips: &mut Vec<(Literal, Literal)>,
    slice: &DipSlice,
    history: &History,
) -> (Literal, Literal) {
    let current_level = history.get_decision_level();

    dips.sort_by_key(|(a, b)| {
        let la = history.get_literal_level(a).unwrap_or(0);
        let lb = history.get_literal_level(b).unwrap_or(0);

        let pos_a = if la == current_level {
            slice
                .pos_of
                .get(a.get_signed_index() as usize)
                .copied()
                .flatten()
                .unwrap_or(0)
        } else {
            0
        };

        let pos_b = if lb == current_level {
            slice
                .pos_of
                .get(b.get_signed_index() as usize)
                .copied()
                .flatten()
                .unwrap_or(0)
        } else {
            0
        };

        (la, lb, std::cmp::max(pos_a, pos_b), std::cmp::min(pos_a, pos_b))
    });

    dips.pop().unwrap()
}



#[cfg(test)]
mod tests {
    use crate::history::{ConflictLearnResult, History, ImplicationPoint};
    use crate::formula::Formula;
    use crate::formula::clause::Clause;
    use crate::formula::literal::Literal;
    use std::collections::HashSet;

    fn lit_key(lit: &Literal) -> (u64, bool) {
        (lit.get_index(), lit.is_negated())
    }

    fn lit_set(lits: &[Literal]) -> HashSet<(u64, bool)> {
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

    fn unordered_pair(a: &Literal, b: &Literal) -> ((u64, bool), (u64, bool)) {
        let ka = lit_key(a);
        let kb = lit_key(b);
        if ka <= kb { (ka, kb) } else { (kb, ka) }
    }

    fn lit_value(lit: &Literal, assignment: &std::collections::HashMap<u64, bool>) -> Option<bool> {
        assignment
            .get(&lit.get_index())
            .map(|&var_value| var_value != lit.is_negated())
    }
    
    fn assign_literal_true(
        lit: &Literal,
        assignment: &mut std::collections::HashMap<u64, bool>,
    ) -> bool {
        let value = !lit.is_negated();
    
        match assignment.get(&lit.get_index()) {
            Some(&old) => old == value,
            None => {
                assignment.insert(lit.get_index(), value);
                true
            }
        }
    }
    
    fn is_rup_candidate(formula: &Formula, clause: &Clause) -> bool {
        let mut assignment = std::collections::HashMap::new();
    
        // RUP check: assume negation of the candidate clause.
        for lit in clause.get_literals() {
            let assumption = lit.negated();
    
            if !assign_literal_true(&assumption, &mut assignment) {
                return true;
            }
        }
    
        loop {
            let mut changed = false;
    
            for existing_clause in formula.get_clauses() {
                let mut unassigned = None;
                let mut unassigned_count = 0;
                let mut satisfied = false;
    
                for lit in existing_clause.get_literals() {
                    match lit_value(lit, &assignment) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            unassigned = Some(lit.clone());
                            unassigned_count += 1;
                        }
                    }
                }
    
                if satisfied {
                    continue;
                }
    
                if unassigned_count == 0 {
                    return true;
                }
    
                if unassigned_count == 1 {
                    let unit = unassigned.unwrap();
    
                    if !assign_literal_true(&unit, &mut assignment) {
                        return true;
                    }
    
                    changed = true;
                }
            }
    
            if !changed {
                return false;
            }
        }
    }

    #[test]
    fn paper_fig1_expected_pre_and_post_are_rup_after_extension_axioms() {
        let x = |n: u64| Literal::new(n - 1, false);
        let y = |n: u64| Literal::new(13 + n - 1, false);
    
        // Original Figure 1 clauses plus extension axioms.
        //
        // Fresh extension variable:
        // z = DIMACS var 20, internal index 19.
        //
        // DIP: z <-> (x8 ∧ ¬x9)
        //
        // Extension clauses:
        // z ∨ ¬x8 ∨ x9
        // ¬z ∨ x8
        // ¬z ∨ ¬x9
        let formula = Formula::from_vec(vec![
            vec![14, -1, 2],
            vec![-1, -3],
            vec![15, -1, 4],
            vec![-16, -2, 3, -4, 5],
            vec![14, -5, -6],
            vec![-5, 7],
            vec![6, -7, 8],
            vec![-16, -17, -5, -9],
            vec![-17, 9, -10],
            vec![-18, 19, -8, 9, 11],
            vec![-11, 12],
            vec![10, -11, 13],
            vec![-12, -13],
    
            // Extension axioms for z <-> (x8 ∧ ¬x9)
            vec![20, -8, 9],
            vec![-20, 8],
            vec![-20, -9],
        ]);
    
        let z = Literal::new(19, false);
    
        // Figure 2 last row:
        // pre-DIP:  ¬x5 ∨ y1 ∨ ¬y3 ∨ ¬y4 ∨ z
        // post-DIP: ¬z ∨ ¬y4 ∨ ¬y5 ∨ y6
        let pre_clause = Clause::from_literals(&vec![
            z.clone(),
            x(5).negated(),
            y(1),
            y(3).negated(),
            y(4).negated(),
        ]);
    
        let post_clause = Clause::from_literals(&vec![
            z.negated(),
            y(4).negated(),
            y(5).negated(),
            y(6),
        ]);
    
        assert!(
            is_rup_candidate(&formula, &pre_clause),
            "expected paper pre-DIP clause is not RUP: {:?}",
            pre_clause
        );
    
        assert!(
            is_rup_candidate(&formula, &post_clause),
            "expected paper post-DIP clause is not RUP: {:?}",
            post_clause
        );
    }
    
    #[test]
    fn dip_parallel_paths_ignores_dead_end_and_extracts_clauses() {
        // Variables (1-based in DIMACS):
        // 1 x1 (level1 decision), 2 p, 3 q, 4 x2 (level2 decision),
        // 5 a, 6 b, 7 c, 8 d, 9 r, 10 s (dead-end lower-level), 11 j (dead-end current level)
        let clauses: Vec<Vec<i64>> = vec![
            vec![-1, 2],         // 0: ¬x1 v p
            vec![-1, 3],         // 1: ¬x1 v q
            vec![-1, 10],        // 2: ¬x1 v s
            vec![-4, -2, 5],     // 3: ¬x2 v ¬p v a
            vec![-4, -3, 6],     // 4: ¬x2 v ¬q v b
            vec![-5, -2, 7],     // 5: ¬a v ¬p v c
            vec![-6, -3, 8],     // 6: ¬b v ¬q v d
            vec![-7, -8, 9],     // 7: ¬c v ¬d v r   (conflict when r=false)
            vec![-4, -10, 11],   // 8: ¬x2 v ¬s v j  (dead-end branch)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        // Level 1 decision
        let x1 = Literal::new(0, false);
        formula.assignment.assign_history(&x1, &mut history);

        let p = Literal::new(1, false);
        formula.assignment.assign(p.get_index(), true);
        history.add_implication(&p, Some(0));

        let q = Literal::new(2, false);
        formula.assignment.assign(q.get_index(), true);
        history.add_implication(&q, Some(1));

        let s = Literal::new(9, false);
        formula.assignment.assign(s.get_index(), true);
        history.add_implication(&s, Some(2));

        // r = false at level 1
        let r_neg = Literal::new(8, true);
        formula.assignment.assign(r_neg.get_index(), false);
        history.add_implication(&r_neg, None);

        // Level 2 decision
        let x2 = Literal::new(3, false);
        formula.assignment.assign_history(&x2, &mut history);

        let a = Literal::new(4, false);
        formula.assignment.assign(a.get_index(), true);
        history.add_implication(&a, Some(3));

        let b = Literal::new(5, false);
        formula.assignment.assign(b.get_index(), true);
        history.add_implication(&b, Some(4));

        let c = Literal::new(6, false);
        formula.assignment.assign(c.get_index(), true);
        history.add_implication(&c, Some(5));

        let d = Literal::new(7, false);
        formula.assignment.assign(d.get_index(), true);
        history.add_implication(&d, Some(6));

        // Dead-end implication (should NOT influence pre_clause)
        let j = Literal::new(10, false);
        formula.assignment.assign(j.get_index(), true);
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
                } => (dip_a, dip_b, pre_clause_without_z, post_clause_without_z, backtrack_level),
                _ => panic!("Expected DIP result"),
            };

        assert_unique_literals(&pre_clause_without_z);
        assert_unique_literals(&post_clause_without_z);

        // DIPs should be {c, d} (deepest pair on the two disjoint paths)
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

        // Post-clause should contain r (since ¬r is in conflict clause and r is level 1).
        let r = Literal::new(8, false);
        let post_set = lit_set(&post_clause_without_z);
        let expected_post: HashSet<_> = [lit_key(&r)].into_iter().collect();
        assert_eq!(post_set, expected_post);

        assert_eq!(backtrack_level, 1);
    }

    #[test]
    fn paper_fig1_dip_x8_not_x9_extracts_expected_pre_and_post_clauses() {
        use crate::formula::Formula;
        use crate::formula::literal::Literal;
        use crate::history::History;
        use crate::history::conflict_graph::{
            graph_from_conflict,
            find_clauses_from_dip_pair,
        };
        use std::collections::HashSet;
    
        fn lit_key(lit: &Literal) -> (u64, bool) {
            (lit.get_index(), lit.is_negated())
        }
    
        fn lit_set(lits: &[Literal]) -> HashSet<(u64, bool)> {
            lits.iter().map(lit_key).collect()
        }
    
        // Mapping:
        // x1..x13 => indices 0..12, DIMACS vars 1..13
        // y1..y6  => indices 13..18, DIMACS vars 14..19
        let x = |n: u64| Literal::new(n - 1, false);
        let y = |n: u64| Literal::new(13 + n - 1, false);
    
        let clauses: Vec<Vec<i64>> = vec![
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
                .assign(lit.get_index(), !lit.is_negated());
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
                .assign(lit.get_index(), !lit.is_negated());
            history.add_implication(&lit, Some(reason));
        }
    
        let conflict_idx = 12;
    
        let (graph, first_uip) =
            graph_from_conflict(&history, &formula, conflict_idx)
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

        println!("prededuping: {:?}, {:?}",pre,post);
        println!("post: {:?}, {:?}",pre,post);
    
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
        let clauses: Vec<Vec<i64>> = vec![
            vec![-1, 2],        // 0: ¬x1 v p
            vec![-1, 3],        // 1: ¬x1 v q
            vec![-5, -2, 6],    // 2: ¬x2 v ¬p v a
            vec![-5, -3, 7],    // 3: ¬x2 v ¬q v b
            vec![-6, -2, 8],    // 4: ¬a v ¬p v c
            vec![-7, -3, 9],    // 5: ¬b v ¬q v d
            vec![-8, -9, -4],   // 6: ¬c v ¬d v ¬y (conflict)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        // Level 1
        let x1 = Literal::new(0, false);
        formula.assignment.assign_history(&x1, &mut history);

        let p = Literal::new(1, false);
        formula.assignment.assign(p.get_index(), true);
        history.add_implication(&p, Some(0));

        let q = Literal::new(2, false);
        formula.assignment.assign(q.get_index(), true);
        history.add_implication(&q, Some(1));

        // Level 2
        let y = Literal::new(3, false);
        formula.assignment.assign_history(&y, &mut history);

        // Level 3
        let x2 = Literal::new(4, false);
        formula.assignment.assign_history(&x2, &mut history);

        let a = Literal::new(5, false);
        formula.assignment.assign(a.get_index(), true);
        history.add_implication(&a, Some(2));

        let b = Literal::new(6, false);
        formula.assignment.assign(b.get_index(), true);
        history.add_implication(&b, Some(3));

        let c = Literal::new(7, false);
        formula.assignment.assign(c.get_index(), true);
        history.add_implication(&c, Some(4));

        let d = Literal::new(8, false);
        formula.assignment.assign(d.get_index(), true);
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
                } => (dip_a, dip_b, pre_clause_without_z, post_clause_without_z, backtrack_level),
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
}

