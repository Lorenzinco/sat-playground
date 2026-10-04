pub mod clause_minimization;
pub mod conflict_analysis;
pub mod conflict_graph;

pub mod dip;
mod dip_clause;

mod lbd;
pub mod two_vertex_bottlenecks;
pub mod uip;

use pyo3::prelude::*;
use std::cell::RefCell;
use std::collections::HashSet;
use std::time::Duration;

use crate::history::conflict_analysis::analyze_conflict;

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
        post_clause_without_z: Vec<Literal>, // ¬D
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
    trail: Vec<Literal>,
    // Start of each nonroot level; root has no decision or limit entry.
    limits: Vec<usize>,
    reasons: Vec<Option<usize>>,
    levels: Vec<Option<usize>>,
    removed_reasons: Vec<usize>,
    // Each LBD operation borrows only this scratch, leaving level lookups shared.
    lbd_scratch: RefCell<lbd::LevelCounter>,
    analysis_scratch: RefCell<conflict_analysis::AnalysisScratch>,
    dip_scratch: RefCell<dip::DipScratch>,
    minimization_scratch: RefCell<clause_minimization::MinimizationScratch>,
}

impl History {
    pub fn new() -> Self {
        Self {
            trail: Vec::new(),
            limits: Vec::new(),
            reasons: Vec::new(),
            levels: Vec::new(),
            removed_reasons: Vec::new(),
            lbd_scratch: RefCell::default(),
            analysis_scratch: RefCell::default(),
            dip_scratch: RefCell::default(),
            minimization_scratch: RefCell::default(),
        }
    }

    pub fn trail(&self) -> &[Literal] {
        &self.trail
    }

    /// Includes the decision at nonroot levels and all root implications at zero.
    /// Panics if `level` is beyond the current decision level.
    pub fn level_trail(&self, level: usize) -> &[Literal] {
        assert!(level <= self.get_decision_level(), "invalid decision level");
        let start = if level == 0 {
            0
        } else {
            self.limits[level - 1]
        };
        let end = self.limits.get(level).copied().unwrap_or(self.trail.len());
        &self.trail[start..end]
    }

    pub fn get_reason(&self, literal: &Literal) -> Option<usize> {
        self.reasons
            .get(literal.get_index().unsigned_abs() as usize)
            .copied()
            .flatten()
    }

    fn append_literal(&mut self, literal: &Literal, reason: Option<usize>) {
        let variable = literal.get_index().unsigned_abs() as usize;
        if variable >= self.levels.len() {
            let len = variable + 1;
            self.levels.resize(len, None);
            self.reasons.resize(len, None);
        }
        self.levels[variable] = Some(self.get_decision_level());
        self.reasons[variable] = reason;

        self.trail.push(*literal);
    }

    /// Adds a decision and a new decision level, a decision is an arbitrary value choice for a variable.
    pub fn add_decision(&mut self, literal: &Literal) {
        assert!(
            self.get_literal_level(literal).is_none(),
            "decision variable already on trail"
        );
        self.limits.push(self.trail.len());
        self.append_literal(literal, None);
    }

    /// Append at the current level. A missing reason supports root facts and
    /// multiple vivification assumptions sharing one level.
    /// Returns the negation if the variable is already recorded (either polarity).
    pub fn add_implication(
        &mut self,
        literal: &Literal,
        clause_index: Option<usize>,
    ) -> Option<Literal> {
        if self.get_literal_level(literal).is_some() {
            return Some(literal.negated());
        }
        self.append_literal(literal, clause_index);

        None
    }

    pub fn backtrack_until_not_conflicting(
        &mut self,
        clause: &Clause,
        preferred_level: usize,
        formula: &mut Formula,
    ) -> Option<usize> {
        let mut level = preferred_level;
        loop {
            formula.revert_decision(level + 1, self);
            if !clause.is_empty(&formula.assignment) {
                return Some(level);
            }
            if level == 0 {
                return None;
            }
            level -= 1;
        }
    }

    /// Remove level `level` and higher, retaining root. Zero is a no-op.
    /// Formula callers must use the reason-collecting variant to release locks.
    pub fn revert_decision(&mut self, level: usize, assignment: &mut Assignment) {
        self.revert_decision_collect_reasons(level, assignment);
    }

    /// Clear root implications so inprocessing can retire their reason clauses.
    /// The caller must replay unit propagation before search resumes.
    pub(crate) fn rewind_root_implications(&mut self, assignment: &mut Assignment) -> &[usize] {
        assert_eq!(
            self.get_decision_level(),
            0,
            "backtrack before rewinding root implications"
        );
        self.truncate_trail(0, assignment)
    }

    /// Returned indices preserve lock multiplicity and borrow a reusable buffer.
    /// Consume them before the next mutation of History.
    pub fn revert_decision_collect_reasons(
        &mut self,
        level: usize,
        assignment: &mut Assignment,
    ) -> &[usize] {
        if level == 0 {
            self.removed_reasons.clear();
            return &self.removed_reasons;
        }

        assert!(level - 1 <= self.limits.len(), "invalid rollback level");
        let start = self
            .limits
            .get(level - 1)
            .copied()
            .unwrap_or(self.trail.len());
        self.limits.truncate(level - 1);
        self.truncate_trail(start, assignment)
    }

    fn truncate_trail(&mut self, start: usize, assignment: &mut Assignment) -> &[usize] {
        self.removed_reasons.clear();
        for literal in &self.trail[start..] {
            let variable = literal.get_index().unsigned_abs() as usize;
            assignment.unset(variable);
            if let Some(reason) = self.reasons[variable].take() {
                // Locks count assignments, so repeated clause indices must survive.
                self.removed_reasons.push(reason);
            }
            self.levels[variable] = None;
        }
        self.trail.truncate(start);
        &self.removed_reasons
    }

    pub fn revert_last_decision(&mut self, assignment: &mut Assignment) {
        self.revert_decision(self.get_decision_level(), assignment);
    }

    pub fn get_decision_level(&self) -> usize {
        self.limits.len()
    }

    pub fn get_literal_level(&self, lit: &Literal) -> Option<usize> {
        self.levels
            .get(lit.get_index().unsigned_abs() as usize)
            .copied()
            .flatten()
    }

    pub(crate) fn snapshot_literal_levels(&self, variable_count: usize) -> Vec<Option<usize>> {
        let mut levels = self.levels[..variable_count.min(self.levels.len())].to_vec();
        levels.resize(variable_count, None);
        if let Some(zero) = levels.first_mut() {
            *zero = None;
        }
        levels
    }

    pub fn last_decision_literal(&self) -> Option<&Literal> {
        self.limits
            .last()
            .and_then(|&position| self.trail.get(position))
    }

    pub fn active_reason_indices(&self) -> HashSet<usize> {
        self.trail
            .iter()
            .filter_map(|literal| self.get_reason(literal))
            .collect()
    }

    pub fn replace_reason_clause(&mut self, old_index: usize, new_index: usize) {
        for literal in &self.trail {
            let reason = &mut self.reasons[literal.get_index().unsigned_abs() as usize];
            if *reason == Some(old_index) {
                *reason = Some(new_index);
            }
        }
    }

    pub fn remap_clause_indices(&mut self, old_to_new: &[Option<usize>]) {
        for literal in &self.trail {
            let reason = &mut self.reasons[literal.get_index().unsigned_abs() as usize];
            if let Some(index) = *reason {
                *reason = old_to_new.get(index).copied().flatten();
            }
        }
    }

    /// Returns the learned minimized clause at 1UIP and the conflict level the clause was found at.
    pub fn analyze_conflict(
        &self,
        formula: &mut Formula,
        conflict_clause_index: usize,
        implication_point: ImplicationPoint,
    ) -> ConflictLearnResult {
        analyze_conflict(self, formula, conflict_clause_index, implication_point)
    }
}

#[cfg(test)]
mod history {
    use super::*;
    use crate::formula::Formula;

    #[test]
    fn flat_lifecycle_preserves_root_and_collects_repeated_locks() {
        let mut history = History::new();
        let mut assignment = Assignment::new(8);
        let literals = [1, -2, 3, -4, 5, -6].map(Literal::new);
        for literal in &literals {
            assignment.assign_literal(*literal);
        }
        history.add_implication(&literals[0], Some(7));
        history.add_implication(&literals[1], Some(7));
        history.add_decision(&literals[2]);
        history.add_implication(&literals[3], None);
        history.add_implication(&literals[4], Some(8));
        history.add_decision(&literals[5]);
        assert_eq!(history.level_trail(0), &literals[..2]);
        assert_eq!(history.level_trail(1), &literals[2..5]);
        assert_eq!(history.level_trail(2), &literals[5..]);
        assert_eq!(history.last_decision_literal(), Some(&literals[5]));
        assert!(
            history
                .revert_decision_collect_reasons(0, &mut assignment)
                .is_empty()
        );
        assert!(
            history
                .revert_decision_collect_reasons(3, &mut assignment)
                .is_empty()
        );
        assert_eq!(
            history.revert_decision_collect_reasons(1, &mut assignment),
            vec![8]
        );
        assert_eq!(history.trail(), &literals[..2]);
        assert_eq!(history.get_decision_level(), 0);
        assert_eq!(history.last_decision_literal(), None);
        for literal in &literals[2..] {
            assert_eq!(history.get_literal_level(literal), None);
            assert_eq!(history.get_reason(literal), None);

            assert_eq!(
                assignment.get_value(literal.get_index().unsigned_abs() as usize),
                None
            );
        }
        assert_eq!(
            history.rewind_root_implications(&mut assignment),
            vec![7, 7]
        );
        assert!(history.trail().is_empty());
        assert!(history.active_reason_indices().is_empty());
        assert_eq!(assignment.get_value(1), None);
        assert_eq!(assignment.get_value(2), None);
    }

    #[test]
    fn formula_rollback_releases_each_reason_lock() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        let mut history = History::new();
        formula.assign_implication(Literal::new(1), &mut history, Some(0));
        formula.add_decision(&Literal::new(-2), &mut history);
        formula.assign_implication(Literal::new(3), &mut history, Some(0));
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 2);
        formula.revert_decision(1, &mut history);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 1);
        assert_eq!(history.get_reason(&Literal::new(-1)), Some(0));
        assert_eq!(history.get_reason(&Literal::new(-3)), None);
        formula.rewind_root_implications(&mut history);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 0);
        assert!(history.trail().is_empty());
    }

    #[test]
    fn flat_metadata_growth_polarity_replacement_and_remapping() {
        let mut history = History::new();
        let root = Literal::new(-1);
        let extension = Literal::new(-100_000);
        history.add_implication(&root, Some(2));
        history.add_decision(&Literal::new(2));
        history.add_implication(&extension, Some(2));
        assert_eq!(history.levels.len(), 100_001);
        assert_eq!(history.get_literal_level(&extension.negated()), Some(1));
        assert_eq!(history.get_reason(&extension.negated()), Some(2));

        assert_eq!(history.get_reason(&Literal::new(3)), None);

        assert_eq!(
            history.add_implication(&extension, None),
            Some(extension.negated())
        );
        assert_eq!(history.trail().len(), 3);
        history.replace_reason_clause(2, 4);
        assert_eq!(history.active_reason_indices(), HashSet::from([4]));
        history.remap_clause_indices(&[None, None, None, None, Some(1)]);
        assert_eq!(history.get_reason(&root), Some(1));
        assert_eq!(history.get_reason(&extension), Some(1));
        assert_eq!(
            history.snapshot_literal_levels(4),
            vec![None, Some(0), Some(1), None]
        );
        assert!(history.snapshot_literal_levels(0).is_empty());
        let grown_snapshot = history.snapshot_literal_levels(history.levels.len() + 2);
        assert_eq!(grown_snapshot[100_000], Some(1));
        assert_eq!(&grown_snapshot[history.levels.len()..], &[None, None]);
        history.remap_clause_indices(&[Some(0), None]);
        assert_eq!(history.get_reason(&root), None);
        assert_eq!(history.get_reason(&extension), None);
    }

    #[test]
    fn flat_rollback_and_root_rewind_reuse_allocations() {
        let mut history = History::new();
        let mut assignment = Assignment::new(100_001);
        let root = Literal::new(1);
        let high = Literal::new(-100_000);
        assignment.assign_literal(root);
        assignment.assign_literal(high);
        assignment.assign_literal(Literal::new(2));
        history.add_implication(&root, Some(3));
        history.add_decision(&high);
        history.add_implication(&Literal::new(2), Some(9));
        let pointers = (
            history.trail.as_ptr(),
            history.limits.as_ptr(),
            history.reasons.as_ptr(),
            history.levels.as_ptr(),
        );
        let capacities = (
            history.trail.capacity(),
            history.limits.capacity(),
            history.reasons.capacity(),
            history.levels.capacity(),
        );
        assert_eq!(
            history.revert_decision_collect_reasons(1, &mut assignment),
            vec![9]
        );
        let removed_reasons_pointer = history.removed_reasons.as_ptr();
        let removed_reasons_capacity = history.removed_reasons.capacity();
        assert_eq!(history.rewind_root_implications(&mut assignment), &[3]);
        assert_eq!(history.removed_reasons.as_ptr(), removed_reasons_pointer);
        assert_eq!(history.removed_reasons.capacity(), removed_reasons_capacity);
        assert!(
            history
                .revert_decision_collect_reasons(0, &mut assignment)
                .is_empty()
        );
        assert_eq!(history.removed_reasons.as_ptr(), removed_reasons_pointer);
        assert_eq!(history.removed_reasons.capacity(), removed_reasons_capacity);
        assignment.assign_literal(high);
        history.add_decision(&high);
        assignment.assign_literal(root);
        history.add_implication(&root, None);
        assignment.assign_literal(Literal::new(2));
        history.add_implication(&Literal::new(2), None);
        assert_eq!(history.get_reason(&root), None);
        assert_eq!(history.get_literal_level(&root.negated()), Some(1));

        assert_eq!(
            pointers,
            (
                history.trail.as_ptr(),
                history.limits.as_ptr(),
                history.reasons.as_ptr(),
                history.levels.as_ptr()
            )
        );
        assert_eq!(
            capacities,
            (
                history.trail.capacity(),
                history.limits.capacity(),
                history.reasons.capacity(),
                history.levels.capacity()
            )
        );
        history.revert_decision(1, &mut assignment);
        assignment.assign_literal(high);
        assignment.assign_literal(root);
        history.add_decision(&high);
        history.add_implication(&root, Some(9));
        assert_eq!(
            history.revert_decision_collect_reasons(1, &mut assignment),
            &[9]
        );
        assert_eq!(history.removed_reasons.as_ptr(), removed_reasons_pointer);
        assert_eq!(history.removed_reasons.capacity(), removed_reasons_capacity);
    }

    #[test]
    #[should_panic(expected = "backtrack before rewinding root implications")]
    fn root_rewind_rejects_nonroot_history() {
        let mut history = History::new();
        history.add_decision(&Literal::new(1));
        history.rewind_root_implications(&mut Assignment::new(2));
    }

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
                .get_literal_level(&lit2)
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
        for (_, clause) in formula.get_clauses_mut() {
            clause.lbd = 7;
            clause.activity = 0;
        }
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
            match history.analyze_conflict(&mut formula, 3, ImplicationPoint::UIP) {
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
        assert!(
            formula
                .get_clauses()
                .all(|(_, clause)| { clause.lbd == 1 && clause.activity == Clause::MAX_ACTIVITY })
        );
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
            match history.analyze_conflict(&mut formula, 2, ImplicationPoint::UIP) {
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
        let mut formula = Formula::from_vec(clauses);

        let (clause, level) = match history.analyze_conflict(&mut formula, 0, ImplicationPoint::UIP)
        {
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
            match history.analyze_conflict(&mut formula, 4, ImplicationPoint::UIP) {
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
            match history.analyze_conflict(&mut formula, 3, ImplicationPoint::DIP) {
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
        let result = history.analyze_conflict(&mut formula, 4, ImplicationPoint::DIP);

        match result {
            ConflictLearnResult::Dip { .. } => {
                unreachable!()
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
