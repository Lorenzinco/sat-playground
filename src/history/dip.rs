use crate::formula::Formula;
use crate::history::conflict_analysis::{ConflictAnalysis, analyze_conflict_graph};
use crate::history::dip_clause;
use crate::history::two_vertex_bottlenecks;
use crate::history::uip;
use crate::history::{ConflictLearnResult, History};

const MAX_DIP_CLAUSE_LBD: i64 = 2;

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
    let pair =
        two_vertex_bottlenecks::find_middle_pair(&analysis.predecessors, &analysis.pred_index)?;
    let (dip_a, dip_b, clause) =
        dip_clause::extract(analysis, history, formula, conflict_clause_index, pair)?;

    // A reused, assigned extension makes the post clause non-asserting: if z is
    // false it is already satisfied, and if z is true its level also affects
    // the required backtrack. Fall back to 1-UIP so every conflict makes progress.
    if formula
        .extensions
        .substitute(&dip_a, &dip_b)
        .is_some_and(|z| z.eval(&formula.assignment).is_some())
    {
        return None;
    }

    if clause.post_lbd > MAX_DIP_CLAUSE_LBD {
        return None;
    }

    Some(ConflictLearnResult::Dip {
        dip_a,
        dip_b,
        post_clause_without_z: clause.post,
    })
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

        let (dip_a, dip_b, post_clause_without_z) =
            match history.analyze_conflict(&formula, conflict_idx, ImplicationPoint::DIP) {
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    post_clause_without_z,
                    ..
                } => (dip_a, dip_b, post_clause_without_z),
                _ => panic!("Expected DIP result"),
            };

        assert_unique_literals(&post_clause_without_z);

        // The xMaple middle heuristic picks the pair nearest the middle of
        // the two complete source-to-conflict paths.
        assert_eq!(unordered_pair(&dip_a, &dip_b), unordered_pair(&c, &d));

        // Post-clause should contain the lower-level inputs to the post-DIP region.
        let r = Literal::new(9);
        let post_set = lit_set(&post_clause_without_z);
        let expected_post: HashSet<_> = [lit_key(&r)].into_iter().collect();
        assert_eq!(post_set, expected_post);
    }

    #[test]
    fn paper_fig1_middle_dip_extracts_expected_pre_and_post_clauses() {
        use crate::formula::Formula;
        use crate::formula::literal::Literal;
        use crate::history::History;
        use crate::history::conflict_analysis::analyze_conflict_graph;
        use crate::history::{dip_clause, two_vertex_bottlenecks};
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

        // Previous-level assignments grouped as in the paper. Keeping them
        // above level zero makes the expected pre/post boundaries observable.
        let previous_levels = [
            (y(2).negated(), vec![]),
            (y(3), vec![y(4), y(6).negated()]),
            (y(1).negated(), vec![y(5)]),
        ];
        for (decision, implications) in previous_levels {
            formula.assignment.assign_history(&decision, &mut history);
            for literal in implications {
                formula
                    .assignment
                    .assign(literal.get_index().abs() as usize, !literal.is_negated());
                history.add_implication(&literal, None);
            }
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

        let analysis = analyze_conflict_graph(&history, &formula, conflict_idx)
            .expect("Figure 1 conflict analysis");
        let pair =
            two_vertex_bottlenecks::find_middle_pair(&analysis.predecessors, &analysis.pred_index)
                .expect("Figure 1 middle DIP");
        let (dip_a, dip_b, clauses) =
            dip_clause::extract(&analysis, &history, &formula, conflict_idx, pair)
                .expect("Figure 1 DIP clauses");
        let post = clauses.post;

        // The middle heuristic chooses the third row of Figure 2.
        assert_eq!(
            unordered_pair(&dip_a, &dip_b),
            unordered_pair(&x(10).negated(), &x(11))
        );

        assert_unique_literals(&post);

        // Figure 2 third row:
        // post-DIP: ¬z

        let expected_post = HashSet::new();

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

        let (dip_a, dip_b, post_clause_without_z) =
            match history.analyze_conflict(&formula, conflict_idx, ImplicationPoint::DIP) {
                ConflictLearnResult::Dip {
                    dip_a,
                    dip_b,
                    post_clause_without_z,
                    ..
                } => (dip_a, dip_b, post_clause_without_z),
                _ => panic!("Expected DIP result"),
            };

        assert_unique_literals(&post_clause_without_z);

        // DIPs should still be {c, d}
        assert_eq!(unordered_pair(&dip_a, &dip_b), unordered_pair(&c, &d));

        // Post-clause should contain ¬y (y is level 2, conflict contains ¬y)
        let not_y = y.negated();
        let post_set = lit_set(&post_clause_without_z);
        let expected_post: HashSet<_> = [lit_key(&not_y)].into_iter().collect();
        assert_eq!(post_set, expected_post);
    }

    #[test]
    fn assigned_reused_extension_falls_back_to_uip() {
        let clauses = vec![
            vec![-3, -2, 4],  // ¬f ∨ ¬p ∨ a
            vec![-3, 5],      // ¬f ∨ b
            vec![-4, -5, -1], // ¬a ∨ ¬b ∨ ¬d
        ];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let d = Literal::new(1);
        let p = Literal::new(2);
        let f = Literal::new(3);
        let a = Literal::new(4);
        let b = Literal::new(5);

        formula.assignment.assign_history(&d, &mut history);
        formula.assignment.assign_history(&p, &mut history);
        formula.assignment.assign_history(&f, &mut history);
        formula
            .assignment
            .assign(a.get_index().abs() as usize, true);
        history.add_implication(&a, Some(0));
        formula
            .assignment
            .assign(b.get_index().abs() as usize, true);
        history.add_implication(&b, Some(1));

        let z = formula.add_literal();
        formula.extensions.add_substitution(&a, &b, &z);
        formula
            .assignment
            .assign(z.get_index().abs() as usize, false);
        history.add_implication(&z.negated(), None);

        assert!(matches!(
            history.analyze_conflict(&formula, 2, ImplicationPoint::DIP),
            ConflictLearnResult::Uip { .. }
        ));
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
    fn find_dip_backtracks_to_post_clause_level() {
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
        // xMapleLCM backjumps to lD, making the post-DIP clause asserting.
        // The pre-DIP clause is not necessarily asserting when lC > lD.

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

        let (dip_a, dip_b, post_clause_without_z) = match result {
            ConflictLearnResult::Dip {
                dip_a,
                dip_b,
                post_clause_without_z,
                ..
            } => (dip_a, dip_b, post_clause_without_z),
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

        // Introduce z as if solve_cdcl had created the extension:
        //
        // z <-> a ∧ b
        //
        // pre-DIP:  z ∨ ¬f ∨ ¬p
        // post-DIP: ¬z ∨ ¬d
        let z = formula.add_literal();

        let mut post_lits = vec![z.negated()];
        post_lits.extend(post_clause_without_z.clone());
        let post_dip = Clause::from_literals(post_lits, -1);

        // Backjump to lD.
        history.revert_decision(l_d + 1, &mut formula.assignment);

        // d survives at DL1.
        assert_eq!(
            formula.assignment.get_value(d.get_index().abs() as usize),
            Some(true)
        );

        // p is removed because lC is above the post-clause backtrack level.
        assert_eq!(
            formula.assignment.get_value(p.get_index().abs() as usize),
            None
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
    }
}
