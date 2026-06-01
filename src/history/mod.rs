pub mod clause_minimization;
pub mod conflict_graph;
pub mod decision_level;
pub mod dip;
pub mod implication_level;
pub mod uip;

use pyo3::prelude::*;
use std::collections::HashSet;
use std::time::Duration;

use crate::history::decision_level::DecisionLevel;
use crate::history::dip::find_dip;
use crate::history::implication_level::ImplicationLevels;
use crate::history::uip::find_1uip;

use crate::formula::Formula;
use crate::formula::assignment::Assignment;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;

#[derive(Clone, Copy)]
pub enum ImplicationPoint {
    UIP,
    DIP,
}

pub enum ConflictLearnResult {
    Uip {
        clause: Clause,
        backtrack_level: usize,
        minimized_literals: usize,
        minimization_time: Duration,
    },
    Dip {
        dip_a: Literal,
        dip_b: Literal,
        pre_clause_without_z: Vec<Literal>,  // ¬f ∨ ¬C
        post_clause_without_z: Vec<Literal>, // ¬D
        pre_lbd: i64,
        post_lbd: i64,
        backtrack_level: usize, // = max(l_C, l_D)
    },
}

impl FromPyObject<'_, '_> for ImplicationPoint {
    type Error = PyErr;

    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let implication_point = obj.extract::<String>()?;
        match implication_point.as_str() {
            "uip" => Ok(ImplicationPoint::UIP),
            "dip" => Ok(ImplicationPoint::DIP),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                "Unknown implication point for cdcl solver {}, allowed values are: uip, dip",
                implication_point
            ))),
        }
    }
}

pub struct History {
    pub decision_levels: Vec<DecisionLevel>,
    pub implication_levels_indexes: implication_level::ImplicationLevels,
}

impl History {
    /// History contains the pile of decisions made, as well as a hashmap that goes from literal to eventually which level it was implied.
    pub fn new() -> Self {
        let mut decision_levels: Vec<DecisionLevel> = Vec::new();
        decision_levels.push(DecisionLevel::empty());
        Self {
            decision_levels: decision_levels,
            implication_levels_indexes: ImplicationLevels::new(),
        }
    }

    /// Adds a decision and a new decision level, a decision is an arbitrary value choice for a variable.
    pub fn add_decision(&mut self, literal: &Literal) {
        self.decision_levels.push(DecisionLevel::new(literal));
        self.implication_levels_indexes
            .set_level(literal, self.get_decision_level());
    }

    /// Adds an implication inside the last level of decision, also keeps track of which clause this implication appears in
    /// Returns a literal if this decision created a conflict with that literal
    pub fn add_implication(
        &mut self,
        literal: &Literal,
        clause_index: Option<usize>,
    ) -> Option<Literal> {
        if self.implication_levels_indexes.get_level(literal).is_some() {
            return Some(literal.negated());
        }

        let level = self.decision_levels.last_mut().expect("No decisions yet!");

        level.add_implied_literal(literal, clause_index);
        self.implication_levels_indexes.set_level(
            literal,
            self.decision_levels
                .len()
                .checked_sub(1)
                .expect("No decisions yet!"),
        );

        None
    }

    /// Unsets inside the assignments all of the implications starting from level <level> onwards, also modifies the decision levels and implication levels undoing what's beyond <level>.
    pub fn revert_decision(&mut self, level: usize, assignment: &mut Assignment) {
        self.revert_decision_collect_reasons(level, assignment);
    }

    pub fn revert_decision_collect_reasons(
        &mut self,
        level: usize,
        assignment: &mut Assignment,
    ) -> Vec<usize> {
        if level == 0 {
            return Vec::new();
        }

        let to_revert = self.decision_levels.split_off(level);
        let mut removed_reasons = Vec::new();

        for decision in to_revert {
            if let Some(lit) = decision.get_decision_literal() {
                assignment.unset(lit.get_index().abs() as usize);
                self.implication_levels_indexes.unset_level(lit);
            }

            for reason_idx in decision.reason_indices() {
                removed_reasons.push(reason_idx);
            }

            for implication in decision.implied_literals_iter() {
                assignment.unset(implication.get_index().abs() as usize);
                self.implication_levels_indexes.unset_level(implication);
            }
        }

        removed_reasons
    }

    pub fn revert_last_decision(&mut self, assignment: &mut Assignment) {
        self.revert_decision(self.get_decision_level(), assignment);
    }

    pub fn get_decision_level(&self) -> usize {
        self.decision_levels.len() - 1
    }

    pub fn get_literal_level(&self, lit: &Literal) -> Option<usize> {
        self.get_literal_and_level(lit).map(|(_, level)| level)
    }

    pub fn get_literal_and_level(&self, lit: &Literal) -> Option<(Literal, usize)> {
        self.implication_levels_indexes
            .get_level(lit)
            .map(|level| (lit.clone(), level))
    }

    pub fn last_decision_literal(&self) -> Option<&Literal> {
        self.decision_levels
            .last()
            .expect("at least one")
            .get_decision_literal()
    }

    pub fn active_reason_indices(&self) -> HashSet<usize> {
        self.decision_levels
            .iter()
            .flat_map(|level| level.reason_indices())
            .collect()
    }

    pub fn remap_clause_indices(&mut self, old_to_new: &[Option<usize>]) {
        for level in &mut self.decision_levels {
            level.remap_clause_indices(old_to_new);
        }
    }

    /// Returns the learned minimized clause at 1UIP and the conflict level the clause was found at.
    pub fn analyze_conflict(
        &self,
        formula: &Formula,
        conflict_clause_index: usize,
        implication_point: ImplicationPoint,
    ) -> ConflictLearnResult {
        match implication_point {
            ImplicationPoint::UIP => find_1uip(self, formula, conflict_clause_index),
            ImplicationPoint::DIP => find_dip(self, formula, conflict_clause_index),
        }
    }
}

#[cfg(test)]
mod history {
    use super::*;
    use crate::formula::Formula;

    #[test]
    fn no_decisions() {
        let mut history = History::new();

        let lit = Literal::new(-1);

        history.add_implication(&lit, None);
        assert_eq!(history.get_decision_level(), 0);
    }

    #[test]
    fn conflict() {
        let mut history = History::new();

        let lit = Literal::new(-1);
        let neg = lit.negated();

        history.add_decision(&lit);
        let conflict = history.add_implication(&neg, Some(2));
        assert!(conflict.is_some());
        assert_eq!(conflict.unwrap(), lit);
    }

    #[test]
    fn revert_decision() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, -3], vec![3, -4]];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let lit1 = Literal::new(1);

        formula.assignment.assign_history(&lit1, &mut history);
        assert!(formula.pure_literals_propagate(Some(&mut history)));
        println!("{:?}", formula);

        assert!(formula.assignment.get_value(1).is_some());
        assert!(formula.assignment.get_value(2).is_some());
        assert!(formula.assignment.get_value(3).is_some());
        assert!(formula.assignment.get_value(4).is_some());

        history.revert_last_decision(&mut formula.assignment);

        assert!(formula.assignment.get_value(1).is_none());
        assert!(formula.assignment.get_value(2).is_none());
        assert!(formula.assignment.get_value(3).is_none());
        assert!(formula.assignment.get_value(4).is_none());
    }

    #[test]
    fn implication_level() {
        let clauses: Vec<Vec<i32>> = vec![vec![-1, 2], vec![-2, -3], vec![3, -4]];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();
        let lit1 = Literal::new(1);

        formula.assignment.assign_history(&lit1, &mut history);
        assert!(formula.pure_literals_propagate(Some(&mut history)));
        println!("{:?}", formula);

        assert!(formula.assignment.get_value(1).is_some());
        assert!(formula.assignment.get_value(2).is_some());
        assert!(formula.assignment.get_value(3).is_some());
        assert!(formula.assignment.get_value(4).is_some());

        let lit2 = Literal::new(2);
        assert!(
            history
                .implication_levels_indexes
                .get_level(&lit2)
                .is_some_and(|level| level == 1)
        );
        assert!(
            history
                .add_implication(&lit2.negated(), Some(2))
                .is_some_and(|conflict| conflict == lit2)
        );
    }

    #[test]
    fn analyze_conflict_basic_uip() {
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],  // 0: -x1 v x2
            vec![-2, 3],  // 1: -x2 v x3
            vec![-3, 4],  // 2: -x3 v x4
            vec![-1, -4], // 3: -x1 v -x4  (conflict)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let x1 = Literal::new(1); // x1

        formula.assignment.assign_history(&x1, &mut history);

        let x2 = Literal::new(2);
        formula
            .assignment
            .assign(x2.get_index().abs() as usize, true);
        history.add_implication(&x2, Some(0)); // Reason: C0 (-1, 2)

        let x3 = Literal::new(3);
        formula
            .assignment
            .assign(x3.get_index().abs() as usize, true);
        history.add_implication(&x3, Some(1)); // Reason: C1 (-2, 3)

        let x4 = Literal::new(4);
        formula
            .assignment
            .assign(x4.get_index().abs() as usize, true);
        history.add_implication(&x4, Some(2)); // Reason: C2 (-3, 4)

        let (learned, backtrack_level) =
            match history.analyze_conflict(&formula, 3, ImplicationPoint::UIP) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                    ..
                } => (clause, backtrack_level),
                _ => {
                    panic!("Non-Uip")
                }
            };

        println!("Learned clause: {}", learned);

        assert_eq!(learned.len(), 1);
        let lit = learned.iter().next().unwrap();
        assert_eq!(lit.get_index(), -1);
        assert!(lit.is_negated()); // -x1

        assert_eq!(learned.lbd, 1);
        assert_eq!(backtrack_level, 0);
    }

    #[test]
    fn analyze_conflict_with_backtrack_uip() {
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],     // 0: -x1 v x2
            vec![-3, -2, 4], // 1: -x3 v -x2 v x4
            vec![-3, -4],    // 2: -x3 v -x4 (Conflict)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let x1 = Literal::new(1);
        formula.assignment.assign_history(&x1, &mut history);

        let x2 = Literal::new(2);
        formula
            .assignment
            .assign(x2.get_index().abs() as usize, true);
        history.add_implication(&x2, Some(0));

        let x3 = Literal::new(3);
        formula.assignment.assign_history(&x3, &mut history);

        let x4 = Literal::new(4);
        formula
            .assignment
            .assign(x4.get_index().abs() as usize, true);
        history.add_implication(&x4, Some(1));

        let (learned, backtrack_level) =
            match history.analyze_conflict(&formula, 2, ImplicationPoint::UIP) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                    ..
                } => (clause, backtrack_level),
                _ => {
                    panic!("Non-Uip")
                }
            };

        println!("Learned: {}", learned);

        assert_eq!(learned.len(), 2);
        assert_eq!(learned.lbd, 2);
        assert_eq!(backtrack_level, 1);
    }

    #[test]
    fn conflict_analysis_unsat_uip() {
        let history = History::new();
        let clauses: Vec<Vec<i32>> = vec![vec![1], vec![-1]]; // Unsat immediately
        let formula = Formula::from_vec(clauses);

        let (clause, level) = match history.analyze_conflict(&formula, 0, ImplicationPoint::UIP) {
            ConflictLearnResult::Uip {
                clause,
                backtrack_level,
                ..
            } => (clause, backtrack_level),
            _ => {
                panic!("Non-Uip")
            }
        };
        assert!(clause.len() == 0);
        assert_eq!(level, 0);
    }

    #[test]
    fn conflict_analysis_simple_uip() {
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],
            vec![-2, 3],
            vec![-3, 4],
            vec![-4, -5],
            vec![-4, 5],
        ];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let lit1 = Literal::new(1); // 1
        history.add_decision(&lit1);
        formula
            .assignment
            .assign(lit1.get_index().abs() as usize, true);

        // 1 implies 2
        let lit2 = Literal::new(2);
        formula
            .assignment
            .assign(lit2.get_index().abs() as usize, true);
        history.add_implication(&lit2, Some(0));

        // 2 implies 3
        let lit3 = Literal::new(3);
        formula
            .assignment
            .assign(lit3.get_index().abs() as usize, true);
        history.add_implication(&lit3, Some(1));

        // 3 implies 4
        let lit4 = Literal::new(4);
        formula
            .assignment
            .assign(lit4.get_index().abs() as usize, true);
        history.add_implication(&lit4, Some(2));

        // 4 implies -5
        let lit5_neg = Literal::new(-5); // -5
        formula
            .assignment
            .assign(lit5_neg.get_index().abs() as usize, false);
        history.add_implication(&lit5_neg, Some(3));

        let (learned_clause, backtrack_level) =
            match history.analyze_conflict(&formula, 4, ImplicationPoint::UIP) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                    ..
                } => (clause, backtrack_level),
                _ => {
                    panic!("Non-Uip")
                }
            };

        // 1-UIP Analysis:
        // Resolution on 5 (from C4 and C3): -4 v -4 = -4
        // Resolution on 4 (from -4 and C2): -3
        // Resolution on 3 (from -3 and C1): -2
        // Resolution on 2 (from -2 and C0): -1
        // 1 is decision literal, stop.
        // Learned: {-1}

        assert_eq!(learned_clause.len(), 1);
        let lits = learned_clause.get_literals();
        println!("{:?}", learned_clause);
        assert_eq!(lits[0].get_index(), -4);
        assert!(lits[0].is_negated());
        assert_eq!(backtrack_level, 0);
    }

    #[test]
    fn analyze_conflict_basic_dip() {
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],  // 0: -x1 v x2
            vec![-2, 3],  // 1: -x2 v x3
            vec![-3, 4],  // 2: -x3 v x4
            vec![-1, -4], // 3: -x1 v -x4  (conflict)
        ];

        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let x1 = Literal::new(1);
        formula.assignment.assign_history(&x1, &mut history);

        let x2 = Literal::new(2);
        formula
            .assignment
            .assign(x2.get_index().abs() as usize, true);
        history.add_implication(&x2, Some(0));

        let x3 = Literal::new(3);
        formula
            .assignment
            .assign(x3.get_index().abs() as usize, true);
        history.add_implication(&x3, Some(1));

        let x4 = Literal::new(4);
        formula
            .assignment
            .assign(x4.get_index().abs() as usize, true);
        history.add_implication(&x4, Some(2));

        let (learned, backtrack_level) =
            match history.analyze_conflict(&formula, 3, ImplicationPoint::DIP) {
                ConflictLearnResult::Uip {
                    clause,
                    backtrack_level,
                    ..
                } => (clause, backtrack_level),
                _ => {
                    panic!("Non-Uip")
                }
            };

        assert_eq!(learned.len(), 1);
        assert_eq!(learned.get_literals()[0], x1.negated());
        assert_eq!(backtrack_level, 0);
    }

    #[test]
    fn conflict_analysis_simple_dip() {
        let clauses: Vec<Vec<i32>> = vec![
            vec![-1, 2],
            vec![-2, 3],
            vec![-3, 4],
            vec![-4, -5],
            vec![-4, 5],
        ];
        let mut formula = Formula::from_vec(clauses);
        let mut history = History::new();

        let lit1 = Literal::new(1); // 1
        history.add_decision(&lit1);
        formula
            .assignment
            .assign(lit1.get_index().abs() as usize, true);

        // 1 implies 2
        let lit2 = Literal::new(2);
        formula
            .assignment
            .assign(lit2.get_index().abs() as usize, true);
        history.add_implication(&lit2, Some(0));

        // 2 implies 3
        let lit3 = Literal::new(3);
        formula
            .assignment
            .assign(lit3.get_index().abs() as usize, true);
        history.add_implication(&lit3, Some(1));

        // 3 implies 4
        let lit4 = Literal::new(4);
        formula
            .assignment
            .assign(lit4.get_index().abs() as usize, true);
        history.add_implication(&lit4, Some(2));

        // 4 implies -5
        let lit5_neg = Literal::new(-5); // -5
        formula
            .assignment
            .assign(lit5_neg.get_index().abs() as usize, false);
        history.add_implication(&lit5_neg, Some(3));

        // Conflict on C4 (-4 v 5)
        let result = history.analyze_conflict(&formula, 4, ImplicationPoint::DIP);

        match result {
            ConflictLearnResult::Dip {
                pre_clause_without_z,
                backtrack_level,
                ..
            } => {
                // If DIP is returned, it must be meaningful (non-empty post in the new logic).
                assert!(!pre_clause_without_z.is_empty());
                assert_eq!(backtrack_level, 0);
            }
            ConflictLearnResult::Uip {
                clause,
                backtrack_level,
                ..
            } => {
                // Expected after the new fallback: UIP on -x4
                assert_eq!(backtrack_level, 0);
                assert_eq!(clause.len(), 1);
                let lit = clause.get_literals()[0].clone();
                assert_eq!(lit.get_index(), -4);
                assert!(lit.is_negated());
            }
        }
    }
}
