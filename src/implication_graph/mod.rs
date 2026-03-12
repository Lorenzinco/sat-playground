use std::collections::{HashMap, HashSet, VecDeque};

use crate::formula::clause::Clause;
use crate::formula::literal::Literal;

/// Stores both:
/// - backward edges: implied literal -> literals that imply it
/// - forward edges: predecessor literal -> literals implied by it
pub struct ImplicationGraph {
    backward: HashMap<Literal, HashSet<(Literal, bool)>>,
    forward: HashMap<Literal, HashSet<Literal>>,
}

impl ImplicationGraph {
    pub fn new() -> Self {
        Self {
            backward: HashMap::new(),
            forward: HashMap::new(),
        }
    }

    /// Adds a single implication edge.
    ///
    /// `implied` is the literal being implied.
    /// `predecessor` is one of the literals implying it.
    /// `arbitrary == true` means `predecessor` is an arbitrary choice / decision.
    pub fn add_neighbour(&mut self, implied: Literal, predecessor: Literal, arbitrary: bool) {
        self.backward
            .entry(implied.clone())
            .or_insert_with(HashSet::new)
            .insert((predecessor.clone(), arbitrary));

        self.forward
            .entry(predecessor)
            .or_insert_with(HashSet::new)
            .insert(implied);
    }

    /// Adds multiple predecessors for the same implied literal.
    pub fn add_neighbours(&mut self, implied: Literal, predecessors: Vec<(Literal, bool)>) {
        for (pred, arbitrary) in predecessors {
            self.add_neighbour(implied.clone(), pred, arbitrary);
        }
    }

    /// Returns the predecessors of `literal`.
    pub fn get_predecessors(&self, literal: &Literal) -> Option<Vec<Literal>> {
        self.backward
            .get(literal)
            .map(|preds| preds.iter().map(|(lit, _)| lit.clone()).collect())
    }

    /// Returns the literals directly implied by `literal`.
    pub fn get_implied(&self, literal: &Literal) -> Option<Vec<Literal>> {
        self.forward
            .get(literal)
            .map(|implied| implied.iter().cloned().collect())
    }

    fn get_cut(&self, literal: &Literal) -> Option<Vec<(Literal, bool)>> {
        let opposite_literal = Literal::new(literal.get_variable(), !literal.is_negated());

        let left = self
            .backward
            .get(literal)
            .map(|s| s.iter().cloned().collect::<HashSet<_>>())
            .unwrap_or_default();

        let right = self
            .backward
            .get(&opposite_literal)
            .map(|s| s.iter().cloned().collect::<HashSet<_>>())
            .unwrap_or_default();

        let cut = left.union(&right).cloned().collect();
        Some(cut)
    }

    pub fn get_conflict_clause(&self, literal: &Literal) -> Option<Clause> {
        let cut = self.get_cut(literal)?;

        let mut conflict_clause = Clause::new();
        for (lit, _) in cut {
            conflict_clause.add_literal(lit).ok()?;
        }

        Some(conflict_clause)
    }

    pub fn is_conflicting(&self, literal: &Literal) -> bool {
        let opposite_literal = Literal::new(literal.get_variable(), !literal.is_negated());
        self.backward.contains_key(literal) && self.backward.contains_key(&opposite_literal)
    }

    /// Returns one literal involved in a conflict, if any.
    pub fn there_is_conflict(&self) -> Option<Literal> {
        for literal in self.backward.keys() {
            if self.is_conflicting(literal) {
                return Some(literal.clone());
            }
        }
        None
    }

    /// Starting from `literal` and its opposite, walks backwards through
    /// predecessors and returns the closest arbitrary choice.
    pub fn closest_arbitrary_implication(&self, literal: &Literal) -> Option<Literal> {
        let opposite_literal = Literal::new(literal.get_variable(), !literal.is_negated());

        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();

        for start in [literal.clone(), opposite_literal] {
            if visited.insert(start.clone()) {
                queue.push_back(start);
            }
        }

        while let Some(current) = queue.pop_front() {
            if let Some(predecessors) = self.backward.get(&current) {
                for (pred, arbitrary) in predecessors {
                    if *arbitrary {
                        return Some(pred.clone());
                    }

                    if visited.insert(pred.clone()) {
                        queue.push_back(pred.clone());
                    }
                }
            }
        }

        None
    }

    /// Returns all literals implied, directly or indirectly, by `decision`.
    ///
    /// The returned vector does NOT include `decision` itself.
    pub fn backtrack(&self, decision: &Literal) -> Vec<Literal> {
        let mut result = Vec::new();
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        visited.insert(decision.clone());
        queue.push_back(decision.clone());

        while let Some(current) = queue.pop_front() {
            if let Some(implied_set) = self.forward.get(&current) {
                for implied in implied_set {
                    if visited.insert(implied.clone()) {
                        result.push(implied.clone());
                        queue.push_back(implied.clone());
                    }
                }
            }
        }

        result
    }

    /// Removes a literal from both maps.
    ///
    /// Useful when undoing assignments during backtracking.
    pub fn remove_literal(&mut self, literal: &Literal) {
        if let Some(predecessors) = self.backward.remove(literal) {
            for (pred, _) in predecessors {
                if let Some(implied_set) = self.forward.get_mut(&pred) {
                    implied_set.remove(literal);
                    if implied_set.is_empty() {
                        self.forward.remove(&pred);
                    }
                }
            }
        }

        if let Some(implied_set) = self.forward.remove(literal) {
            for implied in implied_set {
                if let Some(preds) = self.backward.get_mut(&implied) {
                    preds.retain(|(pred, _)| pred != literal);
                    if preds.is_empty() {
                        self.backward.remove(&implied);
                    }
                }
            }
        }
    }

    /// Clears all literals implied by `decision`, plus optionally the decision itself.
    pub fn backtrack_and_remove(
        &mut self,
        decision: &Literal,
        remove_decision: bool,
    ) -> Vec<Literal> {
        let implied = self.backtrack(decision);

        for lit in &implied {
            self.remove_literal(lit);
        }

        if remove_decision {
            self.remove_literal(decision);
        }

        implied
    }

    /// Checks if `literal` is an arbitrary choice (i.e., a decision) in the implication graph, returns false if it is an implication.
    pub fn is_arbitrary(&self, literal: &Literal) -> bool {
        self.backward
            .get(literal)
            .map(|preds| {
                preds
                    .iter()
                    .any(|(pred, arbitrary)| pred == literal && *arbitrary)
            })
            .unwrap_or(false)
    }

    /// For each literal in `literals`, checks if it is an arbitrary choice (i.e., a decision) in the implication graph, returns a vector of tuples (literal, is_arbitrary).
    pub fn classify_literals(&self, literals: Vec<Literal>) -> Vec<(Literal, bool)> {
        literals
            .into_iter()
            .map(|lit| {
                let arbitrary = self.is_arbitrary(&lit);
                (lit, arbitrary)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::variable::Variable;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn lit(var: u64, neg: bool) -> Literal {
        let variable = Variable::new(var, None);
        Literal::new(Rc::new(RefCell::new(variable)), neg)
    }

    fn assert_same_literals(mut got: Vec<Literal>, mut expected: Vec<Literal>) {
        got.sort_by_key(|l| (l.get_index(), l.is_negated()));
        expected.sort_by_key(|l| (l.get_index(), l.is_negated()));
        assert_eq!(got, expected);
    }

    fn assert_same_pairs(mut got: Vec<(Literal, bool)>, mut expected: Vec<(Literal, bool)>) {
        got.sort_by_key(|(l, a)| (l.get_index(), l.is_negated(), *a));
        expected.sort_by_key(|(l, a)| (l.get_index(), l.is_negated(), *a));
        assert_eq!(got, expected);
    }

    /// Helper to extract literals from a Clause
    fn clause_literals(clause: &Clause) -> Vec<Literal> {
        clause.get_literals().unwrap_or_default()
    }

    #[test]
    fn add_single_implication_populates_both_directions() {
        let mut ig = ImplicationGraph::new();

        let a = lit(1, false);
        let b = lit(2, false);

        ig.add_neighbour(b.clone(), a.clone(), false);

        assert_same_literals(ig.get_predecessors(&b).unwrap(), vec![a.clone()]);

        assert_same_literals(ig.get_implied(&a).unwrap(), vec![b.clone()]);

        assert_eq!(ig.get_predecessors(&a), None);
        assert_eq!(ig.get_implied(&b), None);
    }

    #[test]
    fn add_multiple_predecessors_for_same_literal() {
        let mut ig = ImplicationGraph::new();

        let a = lit(1, false);
        let b = lit(2, false);
        let c = lit(3, false);

        ig.add_neighbours(c.clone(), vec![(a.clone(), false), (b.clone(), true)]);

        assert_same_literals(ig.get_predecessors(&c).unwrap(), vec![a.clone(), b.clone()]);

        assert_same_literals(ig.get_implied(&a).unwrap(), vec![c.clone()]);

        assert_same_literals(ig.get_implied(&b).unwrap(), vec![c.clone()]);

        // Note: b is not arbitrary just because (b, true) is in c's predecessors
        // A literal is arbitrary only if it has itself as a predecessor with arbitrary=true
        assert!(!ig.is_arbitrary(&b));
        assert!(!ig.is_arbitrary(&a));
        assert!(!ig.is_arbitrary(&c));
    }

    #[test]
    fn duplicate_edges_do_not_duplicate_entries() {
        let mut ig = ImplicationGraph::new();

        let a = lit(1, false);
        let b = lit(2, false);

        ig.add_neighbour(b.clone(), a.clone(), false);
        ig.add_neighbour(b.clone(), a.clone(), false);
        ig.add_neighbour(b.clone(), a.clone(), false);

        let preds = ig.get_predecessors(&b).unwrap();
        let implied = ig.get_implied(&a).unwrap();

        assert_eq!(preds.len(), 1);
        assert_eq!(implied.len(), 1);
        assert_eq!(preds[0], a);
        assert_eq!(implied[0], b);
    }

    #[test]
    fn detects_simple_conflict_between_literal_and_opposite() {
        let mut ig = ImplicationGraph::new();

        let d = lit(1, false);
        let x = lit(2, false);
        let not_x = lit(2, true);

        ig.add_neighbour(x.clone(), d.clone(), true);
        ig.add_neighbour(not_x.clone(), d.clone(), true);

        assert!(ig.is_conflicting(&x));
        assert!(ig.is_conflicting(&not_x));

        let found = ig.there_is_conflict();
        assert!(found == Some(x.clone()) || found == Some(not_x.clone()));
    }

    #[test]
    fn no_conflict_when_only_one_polarity_exists() {
        let mut ig = ImplicationGraph::new();

        let a = lit(1, false);
        let x = lit(2, false);

        ig.add_neighbour(x.clone(), a.clone(), true);

        assert!(!ig.is_conflicting(&x));
        assert_eq!(ig.there_is_conflict(), None);
    }

    #[test]
    fn closest_arbitrary_returns_nearest_decision_not_any_random_ancestor() {
        let mut ig = ImplicationGraph::new();

        let d1 = lit(1, false);
        let d2 = lit(2, false);
        let a = lit(3, false);
        let b = lit(4, false);
        let x = lit(5, false);
        let not_x = lit(5, true);

        // decisions
        ig.add_neighbour(d1.clone(), d1.clone(), true);
        ig.add_neighbour(d2.clone(), d2.clone(), true);

        // chain:
        // d1 -> a -> x
        // d2 -> b -> !x
        ig.add_neighbour(a.clone(), d1.clone(), false);
        ig.add_neighbour(x.clone(), a.clone(), false);

        ig.add_neighbour(b.clone(), d2.clone(), false);
        ig.add_neighbour(not_x.clone(), b.clone(), false);

        let closest = ig.closest_arbitrary_implication(&x).unwrap();

        // BFS starts from x and !x and should reach d1 or d2 first depending on traversal order,
        // but it must be one of the actual closest decisions.
        assert!(closest == d1 || closest == d2);
    }

    #[test]
    fn backtrack_collects_all_transitively_implied_literals_without_decision_itself() {
        let mut ig = ImplicationGraph::new();

        let d = lit(1, false);
        let a = lit(2, false);
        let b = lit(3, false);
        let c = lit(4, false);
        let e = lit(5, false);

        ig.add_neighbour(d.clone(), d.clone(), true);
        ig.add_neighbour(a.clone(), d.clone(), false);
        ig.add_neighbour(b.clone(), a.clone(), false);
        ig.add_neighbour(c.clone(), a.clone(), false);
        ig.add_neighbour(e.clone(), c.clone(), false);

        let implied = ig.backtrack(&d);

        assert_same_literals(implied, vec![a, b, c, e]);
    }

    #[test]
    fn backtrack_and_remove_keeps_unrelated_component_intact() {
        let mut ig = ImplicationGraph::new();

        let d1 = lit(1, false);
        let a1 = lit(2, false);
        let b1 = lit(3, false);

        let d2 = lit(10, false);
        let a2 = lit(11, false);

        ig.add_neighbour(d1.clone(), d1.clone(), true);
        ig.add_neighbour(a1.clone(), d1.clone(), false);
        ig.add_neighbour(b1.clone(), a1.clone(), false);

        ig.add_neighbour(d2.clone(), d2.clone(), true);
        ig.add_neighbour(a2.clone(), d2.clone(), false);

        let removed = ig.backtrack_and_remove(&d1, true);
        assert_same_literals(removed, vec![a1.clone(), b1.clone()]);

        assert_eq!(ig.get_predecessors(&d1), None);
        assert_eq!(ig.get_predecessors(&a1), None);
        assert_eq!(ig.get_predecessors(&b1), None);

        // d2 should still be in the graph as a decision
        assert!(ig.is_arbitrary(&d2));
        assert_same_literals(ig.get_predecessors(&a2).unwrap(), vec![d2.clone()]);
        // d2 might also imply itself (self-referential decision edge)
        let d2_implied = ig.get_implied(&d2).unwrap();
        assert!(d2_implied.contains(&a2) || d2_implied.contains(&d2));
    }

    #[test]
    fn remove_literal_cleans_both_backward_and_forward_edges() {
        let mut ig = ImplicationGraph::new();

        let a = lit(1, false);
        let b = lit(2, false);
        let c = lit(3, false);

        ig.add_neighbour(b.clone(), a.clone(), false);
        ig.add_neighbour(c.clone(), b.clone(), false);

        ig.remove_literal(&b);

        assert_eq!(ig.get_predecessors(&b), None);
        assert_eq!(ig.get_implied(&b), None);

        // a should no longer imply b
        assert_eq!(ig.get_implied(&a), None);

        // c should no longer have b as predecessor
        assert_eq!(ig.get_predecessors(&c), None);
    }

    #[test]
    fn classify_literals_distinguishes_decisions_from_implications_and_absent_literals() {
        let mut ig = ImplicationGraph::new();

        let d = lit(1, false);
        let a = lit(2, false);
        let orphan = lit(99, false);

        ig.add_neighbour(d.clone(), d.clone(), true);
        ig.add_neighbour(a.clone(), d.clone(), false);

        let classified = ig.classify_literals(vec![d.clone(), a.clone(), orphan.clone()]);

        assert_same_pairs(classified, vec![(d, true), (a, false), (orphan, false)]);
    }

    #[test]
    fn get_conflict_clause_contains_union_of_both_sides_predecessors() {
        let mut ig = ImplicationGraph::new();

        let d1 = lit(1, false);
        let d2 = lit(2, false);
        let a = lit(3, false);
        let b = lit(4, false);
        let x = lit(5, false);
        let not_x = lit(5, true);

        ig.add_neighbour(d1.clone(), d1.clone(), true);
        ig.add_neighbour(d2.clone(), d2.clone(), true);

        // x <- {a, d1}
        ig.add_neighbour(a.clone(), d1.clone(), false);
        ig.add_neighbour(x.clone(), a.clone(), false);
        ig.add_neighbour(x.clone(), d1.clone(), true);

        // !x <- {b, d2}
        ig.add_neighbour(b.clone(), d2.clone(), false);
        ig.add_neighbour(not_x.clone(), b.clone(), false);
        ig.add_neighbour(not_x.clone(), d2.clone(), true);

        let clause = ig.get_conflict_clause(&x).unwrap();
        let lits = clause_literals(&clause);

        assert_same_literals(lits, vec![a, d1, b, d2]);
    }

    #[test]
    fn get_conflict_clause_for_direct_binary_conflict_is_exact() {
        let mut ig = ImplicationGraph::new();

        let d1 = lit(1, false);
        let d2 = lit(2, false);
        let x = lit(3, false);
        let not_x = lit(3, true);

        ig.add_neighbour(x.clone(), d1.clone(), true);
        ig.add_neighbour(not_x.clone(), d2.clone(), true);

        let clause = ig.get_conflict_clause(&x).unwrap();
        let lits = clause_literals(&clause);

        assert_same_literals(lits, vec![d1, d2]);
    }

    #[test]
    fn get_cut_like_conflict_clause_handles_shared_predecessors_without_duplication() {
        let mut ig = ImplicationGraph::new();

        let d = lit(1, false);
        let a = lit(2, false);
        let x = lit(3, false);
        let not_x = lit(3, true);

        ig.add_neighbour(d.clone(), d.clone(), true);
        ig.add_neighbour(a.clone(), d.clone(), false);

        ig.add_neighbour(x.clone(), a.clone(), false);
        ig.add_neighbour(not_x.clone(), a.clone(), false);

        let clause = ig.get_conflict_clause(&x).unwrap();
        let lits = clause_literals(&clause);

        // since both sides share predecessor a, it must appear only once
        assert_same_literals(lits, vec![a]);
    }

    #[test]
    fn backtrack_and_remove_without_removing_decision_preserves_the_decision_only() {
        let mut ig = ImplicationGraph::new();

        let d = lit(1, false);
        let a = lit(2, false);
        let b = lit(3, false);

        ig.add_neighbour(d.clone(), d.clone(), true);
        ig.add_neighbour(a.clone(), d.clone(), false);
        ig.add_neighbour(b.clone(), a.clone(), false);

        let removed = ig.backtrack_and_remove(&d, false);
        assert_same_literals(removed, vec![a.clone(), b.clone()]);

        assert!(ig.is_arbitrary(&d));
        assert_eq!(ig.get_predecessors(&a), None);
        assert_eq!(ig.get_predecessors(&b), None);

        // After removing the implied literals, d still has a self-referential edge
        // so get_implied might return d itself
        let implied = ig.get_implied(&d).unwrap_or_default();
        // The only thing that can be implied now is d itself (the decision edge)
        assert!(implied.is_empty() || (implied.len() == 1 && implied[0] == d));
    }

    #[test]
    fn massive_diamond_graph_backtracks_everything_once() {
        let mut ig = ImplicationGraph::new();

        let d = lit(1, false);
        let a = lit(2, false);
        let b = lit(3, false);
        let c = lit(4, false);
        let e = lit(5, false);
        let f = lit(6, false);

        ig.add_neighbour(d.clone(), d.clone(), true);
        ig.add_neighbour(a.clone(), d.clone(), false);
        ig.add_neighbour(b.clone(), d.clone(), false);
        ig.add_neighbour(c.clone(), a.clone(), false);
        ig.add_neighbour(c.clone(), b.clone(), false);
        ig.add_neighbour(e.clone(), c.clone(), false);
        ig.add_neighbour(f.clone(), c.clone(), false);

        let implied = ig.backtrack(&d);

        // c has two incoming edges, but must appear only once
        assert_same_literals(implied, vec![a, b, c, e, f]);
    }
}
