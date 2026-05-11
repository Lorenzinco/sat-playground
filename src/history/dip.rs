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

    let Ok((graph, first_uip)) = graph_from_conflict(history, formula, conflict_clause_index) else {
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

    let Some((mut pre_lits, mut post_lits)) = find_clauses_from_dip_pair(
        &graph,
        history,
        formula,
        conflict_clause_index,
        &a,
        &b,
        &first_uip
    ) else {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    };

    dedup_literals(&mut pre_lits);
    dedup_literals(&mut post_lits);

    if post_lits.is_empty() {
        let (clause, backtrack_level) = find_1uip(history, formula, conflict_clause_index);
        return ConflictLearnResult::Uip { clause, backtrack_level };
    }

    if a.get_index() == b.get_index() {
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

#[cfg(test)]
mod tests {
    use crate::history::{ConflictLearnResult, History, ImplicationPoint};
    use crate::formula::Formula;
    use crate::formula::literal::Literal;
    use std::collections::HashSet;

    fn lit_key(lit: &Literal) -> (u64, bool) {
        (lit.get_index(), lit.is_negated())
    }

    fn lit_set(lits: &[Literal]) -> HashSet<(u64, bool)> {
        lits.iter().map(lit_key).collect()
    }

    fn unordered_pair(a: &Literal, b: &Literal) -> ((u64, bool), (u64, bool)) {
        let ka = lit_key(a);
        let kb = lit_key(b);
        if ka <= kb { (ka, kb) } else { (kb, ka) }
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

