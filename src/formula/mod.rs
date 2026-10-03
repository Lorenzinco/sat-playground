pub mod assignment;
pub mod clause;
pub mod extension;
pub mod garbage;
pub mod literal;

use crate::drat::DratLogger;
use crate::formula::extension::ExtensionMap;
use crate::formula::garbage::Garbage;
use crate::heuristics::vsids::Vsids;
use crate::history::History;
use crate::process;
use crate::process::ClauseScope;
use crate::process::Process;
use crate::python::signal_checker;
use crate::python::stats::Stats;
use crate::watchlist::Watch;
use assignment::AssignResult;
use assignment::Assignment;
use clause::Clause;
use literal::Literal;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::VecDeque;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::io::Write;
use std::time::Instant;

const DB_REDUCTION_MIN_REMOVABLE_CLAUSES: usize = 15_000;
const DB_REDUCTION_GARBAGE_RATIO: usize = 12;

#[derive(Clone)]
pub struct Formula {
    clauses: Vec<Clause>,
    garbage: Garbage,
    pub assignment: Assignment,
    watch: Watch,
    occurrence: Vec<Vec<usize>>,
    occurrence_stale: Vec<usize>,
    pub stats: Stats,
    pub extensions: ExtensionMap,
    retired_extension_variables: HashSet<usize>,
    pub(crate) vsids: Vsids,
    self_subsuming: bool,
    pub(crate) ges_cursor: usize,
    pub(crate) ges_clause_budget: usize,
    pub(crate) ges_feedback_used: u64,
    pub(crate) ges_feedback_deleted_unused: u64,
    ges_trail_tracking: bool,
    pub(crate) ges_trail_touched: Vec<usize>,
    ges_trail_seen: Vec<bool>,
    pub(crate) bva_preprocessing_budget: usize,
    pub(crate) bva_inprocessing_budget: usize,
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (clause_position, (_, clause)) in self.get_clauses().enumerate() {
            if clause_position > 0 {
                write!(f, "∧")?;
            }
            write!(f, "(")?;
            for (literal_position, literal) in clause.into_iter().enumerate() {
                if literal_position > 0 {
                    write!(f, "∨")?;
                }
                let color = match literal.eval(&self.assignment) {
                    Some(true) => "\x1b[34m",
                    Some(false) => "\x1b[31m",
                    None => "\x1b[2m",
                };
                write!(f, "{}{:?}\x1b[0m", color, literal)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (position, (_, clause)) in self.get_clauses().enumerate() {
            if position > 0 {
                write!(f, "∧")?;
            }
            write!(f, "{}", clause)?;
        }
        Ok(())
    }
}

impl Formula {
    /// Creates a new empty formula, to create one starting from a dimacs file see from_dimacs(dimacs: &str).
    ///
    /// ```
    /// use clsat::formula::Formula;
    ///
    /// let literals: usize = 10000;
    ///
    /// let phi = Formula::new(literals);
    /// ```
    pub fn new(size: usize) -> Self {
        let storage = size + 1;
        Formula {
            clauses: vec![],
            garbage: Garbage::new(0),
            assignment: Assignment::new(storage),
            watch: Watch::new(storage),
            occurrence: vec![Vec::new(); storage * 2],
            occurrence_stale: vec![0; storage * 2],
            stats: Stats::new(),
            extensions: ExtensionMap::new(),
            retired_extension_variables: HashSet::new(),
            vsids: Vsids::new(storage),
            self_subsuming: false,
            ges_cursor: 0,
            ges_clause_budget: 0,
            ges_feedback_used: 0,
            ges_feedback_deleted_unused: 0,
            ges_trail_tracking: false,
            ges_trail_touched: Vec::new(),
            ges_trail_seen: Vec::new(),
            bva_preprocessing_budget: 0,
            bva_inprocessing_budget: 0,
        }
    }

    pub fn from_clauses(clauses: impl Into<Vec<Clause>>) -> Self {
        let clauses = clauses.into();
        let clause_count = clauses.len();
        let max_index = clauses
            .iter()
            .flat_map(|clause| clause.iter())
            .map(|lit| lit.get_index().abs())
            .max()
            .expect("No literal in any formula found!");

        let mut formula = Formula {
            clauses,
            garbage: Garbage::new(clause_count),
            assignment: Assignment::new(max_index as usize + 1),
            watch: Watch::new(max_index as usize + 1),
            occurrence: vec![Vec::new(); (max_index as usize + 1) * 2],
            occurrence_stale: vec![0; (max_index as usize + 1) * 2],
            stats: Stats::new(),
            extensions: ExtensionMap::new(),
            retired_extension_variables: HashSet::new(),
            vsids: Vsids::new(max_index as usize + 1),
            self_subsuming: false,
            ges_cursor: 0,
            ges_clause_budget: 0,
            ges_feedback_used: 0,
            ges_feedback_deleted_unused: 0,
            ges_trail_tracking: false,
            ges_trail_touched: Vec::new(),
            ges_trail_seen: vec![false; clause_count],
            bva_preprocessing_budget: 0,
            bva_inprocessing_budget: 0,
        };

        formula.rebuild_clause_indices();
        formula.rebuild_vsids();
        formula
    }

    pub fn from_vec(raw_clauses: Vec<Vec<i32>>) -> Self {
        let mut clauses = Vec::new();
        for raw_clause in raw_clauses.iter() {
            let mut literals = Vec::with_capacity(raw_clause.len());
            for raw_lit in raw_clause.iter() {
                if *raw_lit == 0 {
                    panic!("0 indexing is not allowed on dimacs")
                }
                let lit = Literal::new(*raw_lit);
                assert!(
                    !literals.contains(&lit),
                    "Literal cannot be in the same clause twice"
                );
                literals.push(lit);
            }
            clauses.push(Clause::from_literals(literals, -1));
        }

        Formula::from_clauses(clauses)
    }

    /// Iterates over live clauses while preserving their physical indexes.
    pub fn get_clauses(&self) -> impl DoubleEndedIterator<Item = (usize, &Clause)> + '_ {
        self.clauses
            .iter()
            .enumerate()
            .filter(|(index, _)| !self.garbage.is_garbage(*index))
    }

    /// Iterates over every physical clause slot, including garbage.
    pub fn get_clauses_and_garbage(
        &self,
    ) -> impl DoubleEndedIterator<Item = (usize, &Clause)> + '_ {
        self.clauses.iter().enumerate()
    }

    /// Mutable access is for clause metadata. Change attached literals via
    /// add/delete so occurrence lists, watches, and cached blockers stay valid.
    pub fn get_clauses_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = (usize, &mut Clause)> + '_ {
        let garbage = &self.garbage;
        self.clauses
            .iter_mut()
            .enumerate()
            .filter(move |(index, _)| !garbage.is_garbage(*index))
    }

    pub fn clause_slots_len(&self) -> usize {
        self.clauses.len()
    }

    pub fn live_clause_count(&self) -> usize {
        self.clauses.len() - self.garbage.count()
    }

    pub fn garbage_clause_count(&self) -> usize {
        self.garbage.count()
    }

    pub fn is_clause_garbage(&self, index: usize) -> bool {
        self.garbage.is_garbage(index)
    }

    #[inline]
    pub fn get_clause_at_idx(&self, index: usize) -> &Clause {
        debug_assert!(!self.garbage.is_garbage(index), "Clause is garbage");
        self.clauses.get(index).expect("Clause not present")
    }

    /// Mutable access is for metadata; replace literals by adding a new clause
    /// and deleting the old clause, preserving proof and reason bookkeeping.
    #[inline]
    pub fn get_clause_at_idx_mut(&mut self, index: usize) -> &mut Clause {
        debug_assert!(!self.garbage.is_garbage(index), "Clause is garbage");
        self.clauses.get_mut(index).expect("Clause not present")
    }

    pub fn get_clause_and_garbage_at_idx(&self, index: usize) -> &Clause {
        self.clauses.get(index).expect("Clause not present")
    }

    /// Returns live, unsatisfied clauses together with their physical indexes.
    pub fn get_unsatisfied_clauses(&self) -> Vec<(usize, &Clause)> {
        self.get_clauses()
            .filter(|(_, clause)| !clause.is_satisfied(&self.assignment))
            .collect()
    }

    /// Returns mutable live, unsatisfied clauses together with their physical indexes.
    pub fn get_unsatisfied_clauses_mut(
        &mut self,
        assignment: &Assignment,
    ) -> Vec<(usize, &mut Clause)> {
        self.get_clauses_mut()
            .filter(|(_, clause)| !clause.is_satisfied(assignment))
            .collect()
    }

    pub fn get_stats(&self) -> Stats {
        self.stats.clone()
    }

    pub fn self_subsuming_enabled(&self) -> bool {
        self.self_subsuming
    }

    /// Updates the occurrence list of a literal inside a new clause
    pub fn add_to_occurrence(&mut self, clause_idx: usize, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;
        if idx >= self.occurrence.len() {
            self.occurrence.resize(idx + 1, Vec::new());
            self.occurrence_stale.resize(idx + 1, 0);
        }
        self.occurrence[idx].push(clause_idx);
    }

    /// Iterates over live clause indexes in which the literal occurs.
    pub fn occurrence_of<'a>(
        &'a self,
        lit: &Literal,
    ) -> impl DoubleEndedIterator<Item = usize> + 'a {
        let list_idx = lit.get_unsigned_index() as usize;
        let has_stale_entries = self
            .occurrence_stale
            .get(list_idx)
            .is_some_and(|&stale| stale != 0);
        self.occurrences_and_garbage(lit)
            .iter()
            .copied()
            .filter(move |&index| !has_stale_entries || !self.garbage.is_garbage(index))
    }

    /// Removes tombstoned entries from one occurrence list. Internal algorithms
    /// call this before scanning a list, so subsequent iteration needs no garbage checks.
    pub fn clean_occurrence(&mut self, lit: &Literal) {
        let list_idx = lit.get_unsigned_index() as usize;
        if self
            .occurrence_stale
            .get(list_idx)
            .is_none_or(|&stale| stale == 0)
        {
            return;
        }

        let garbage = &self.garbage;
        self.occurrence[list_idx].retain(|&clause_idx| !garbage.is_garbage(clause_idx));
        self.occurrence_stale[list_idx] = 0;
    }

    pub fn live_occurrence_len(&self, lit: &Literal) -> usize {
        let list_idx = lit.get_unsigned_index() as usize;
        self.occurrence
            .get(list_idx)
            .map_or(0, |entries| entries.len() - self.occurrence_stale[list_idx])
    }

    /// Returns occurrence indexes including entries for tombstoned clauses.
    pub fn occurrences_and_garbage(&self, lit: &Literal) -> &[usize] {
        self.occurrence
            .get(lit.get_unsigned_index() as usize)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn candidate_indices_for_clause(&mut self, clause: &Clause) -> Vec<usize> {
        for lit in clause.get_literals() {
            self.clean_occurrence(lit);
        }
        let Some(shortest_occurrence_lit) = clause
            .get_literals()
            .iter()
            .filter(|lit| self.live_occurrence_len(lit) > 0)
            .min_by_key(|lit| self.live_occurrence_len(lit))
        else {
            return Vec::new();
        };

        self.occurrence_of(shortest_occurrence_lit).collect()
    }

    pub fn occurrence_intersection(
        &mut self,
        watch_a: &Literal,
        watch_b: Option<&Literal>,
    ) -> Vec<usize> {
        self.clean_occurrence(watch_a);
        let Some(watch_b) = watch_b else {
            return self.occurrence_of(watch_a).collect();
        };
        self.clean_occurrence(watch_b);

        let mut a = self.occurrences_and_garbage(watch_a);
        let mut b = self.occurrences_and_garbage(watch_b);
        if a.len() > b.len() {
            std::mem::swap(&mut a, &mut b);
        }

        let mut out = Vec::new();
        let mut b_pos = 0;
        for &idx in a {
            while b_pos < b.len() && b[b_pos] < idx {
                b_pos += 1;
            }
            if b_pos < b.len() && b[b_pos] == idx {
                out.push(idx);
            }
        }

        out
    }

    pub fn add_clause<W: Write>(
        &mut self,
        clause: Clause,
        logger: &mut Option<DratLogger<W>>,
        _history: Option<&mut History>,
    ) -> usize {
        if self.self_subsuming && clause.lbd != 0 {
            let subsumption_start = Instant::now();
            let result = process::subsumption::check_new_clause(self, &clause);
            self.stats
                .record_subsumption_time(subsumption_start.elapsed());
            self.stats
                .add_subsumption_checks(result.subset_checks as u64);

            if let Some(existing_idx) = result.subsumed_by_existing {
                self.stats.add_subsumed_clauses(1);
                return existing_idx;
            }

            if !result.subsumed_existing.is_empty() {
                self.stats
                    .add_subsumed_clauses(result.subsumed_existing.len() as u64);
                self.delete_clauses::<W>(&result.subsumed_existing, logger);
            }
        }

        self.add_clause_unchecked(clause, logger)
    }

    pub fn add_clause_unchecked<W: Write>(
        &mut self,
        mut clause: Clause,
        logger: &mut Option<DratLogger<W>>,
    ) -> usize {
        clause.prioritize_unfalsified_watches(&self.assignment);
        let clause_idx = self.clauses.len();
        for lit in clause.get_literals() {
            self.add_to_occurrence(clause_idx, lit);
        }

        if let Some((first, second)) = clause.watched_literals() {
            self.watch
                .add_to_watchlist(clause_idx, first, *second.unwrap_or(first));
            if let Some(second) = second {
                self.watch.add_to_watchlist(clause_idx, second, *first);
            }
        }

        if let Some(log) = logger.as_mut() {
            let _ = log.log_add(clause.get_literals());
        }

        self.clauses.push(clause);
        self.garbage.push_live();
        self.ges_trail_seen.push(false);
        clause_idx
    }

    pub fn process<W: Write>(
        &mut self,
        methods: &[Process],
        scope: &ClauseScope,
        logger: &mut Option<DratLogger<W>>,
        signal: Option<(Python<'_>, &mut u64)>,
        replace_subsumption_setting: bool,
        history: Option<&mut History>,
        reasoning_levels: Option<&[Option<usize>]>,
    ) -> PyResult<()> {
        self.process_in_phase(
            methods,
            scope,
            logger,
            signal,
            replace_subsumption_setting,
            history,
            reasoning_levels,
            process::ProcessPhase::Preprocessing,
        )
    }

    pub fn process_in_phase<W: Write>(
        &mut self,
        methods: &[Process],
        scope: &ClauseScope,
        logger: &mut Option<DratLogger<W>>,
        signal: Option<(Python<'_>, &mut u64)>,
        replace_subsumption_setting: bool,
        mut history: Option<&mut History>,
        reasoning_levels: Option<&[Option<usize>]>,
        phase: process::ProcessPhase,
    ) -> PyResult<()> {
        if replace_subsumption_setting {
            self.self_subsuming = methods.contains(&Process::Subsumption);
        } else if methods.contains(&Process::Subsumption) {
            self.self_subsuming = true;
        }
        let mut signal = signal;
        let ges_options = process::ges::GesOptions {
            substitution_only: methods.contains(&Process::GESCompress),
            trail_first: methods.contains(&Process::GESTrail),
        };

        for &method in methods {
            match method {
                Process::BVA => {
                    let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                    process::bva::process_in_phase(self, scope, logger, signal, phase)?;
                }
                Process::BVE => {
                    let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                    process::bve::process(self, scope, logger, signal, history.as_deref_mut())?;
                }
                Process::GES
                | Process::GESAlways
                | Process::GESLBD
                | Process::GESPar
                | Process::GESRandom
                | Process::GESUtility
                | Process::GESVSIDS => {
                    let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                    if method == Process::GESPar {
                        process::ges_par::process_with_options(
                            self,
                            scope,
                            logger,
                            signal,
                            history.as_deref_mut(),
                            reasoning_levels,
                            ges_options,
                        )?;
                    } else {
                        let policy = match method {
                            Process::GESAlways => process::ges::Policy::Always,
                            Process::GESLBD => process::ges::Policy::Lbd,
                            Process::GESRandom => process::ges::Policy::Random,
                            Process::GESUtility => process::ges::Policy::Utility,
                            Process::GESVSIDS => process::ges::Policy::Vsids,
                            _ => process::ges::Policy::Cursor,
                        };
                        process::ges::process_with_policy(
                            self,
                            scope,
                            logger,
                            signal,
                            history.as_deref_mut(),
                            reasoning_levels,
                            policy,
                            ges_options,
                        )?;
                    }
                }
                Process::Preference if phase == process::ProcessPhase::Inprocessing => {
                    process::preference::process(self, logger)
                }
                Process::Preference => {}
                Process::GESCompress | Process::GESTrail => {}
                Process::Subsumption => process::subsumption::preprocess(self, scope, logger),
                _ => println!("Not yet implemented!"),
            }
        }

        Ok(())
    }

    pub fn delete_clause<W: Write>(
        &mut self,
        clause_index: usize,
        logger: &mut Option<DratLogger<W>>,
    ) {
        self.delete_clauses(&[clause_index], logger);
    }

    pub fn record_clause_removal(&mut self, clause_index: usize) {
        assert!(!self.garbage.is_garbage(clause_index));
        self.stats.remove_clause(&self.clauses[clause_index]);
    }

    pub fn delete_clauses<W: Write>(
        &mut self,
        clause_indices: &[usize],
        logger: &mut Option<DratLogger<W>>,
    ) -> usize {
        let mut to_delete = clause_indices.to_vec();
        to_delete.sort_unstable();
        to_delete.dedup();

        // Validate the complete batch before changing formula state or the proof.
        for &idx in &to_delete {
            assert!(idx < self.clauses.len());
            if !self.garbage.is_garbage(idx) {
                assert_eq!(
                    self.clauses[idx].lock_count, 0,
                    "cannot delete a clause that is locked as an active implication reason"
                );
            }
        }
        to_delete.retain(|&idx| !self.garbage.is_garbage(idx));

        if let Some(log) = logger.as_mut() {
            for &idx in &to_delete {
                let _ = log.log_delete(self.clauses[idx].get_literals());
            }
        }

        for &idx in &to_delete {
            let clause = &self.clauses[idx];
            if clause.ges_generated && !clause.ges_used {
                self.stats.ges_replacements_deleted_unused += 1;
            }
            for lit in clause.get_literals() {
                self.occurrence_stale[lit.get_unsigned_index() as usize] += 1;
            }
            if let Some((first, second)) = clause.watched_literals() {
                self.watch.mark_stale(first);
                if let Some(second) = second {
                    self.watch.mark_stale(second);
                }
            }
            self.garbage.delete(idx);
        }
        to_delete.len()
    }

    pub fn collect_garbage(&mut self, history: Option<&mut History>) -> Vec<Option<usize>> {
        assert!(
            history.is_some() || self.clauses.iter().all(|clause| clause.lock_count == 0),
            "cannot compact locked reason clauses without remapping history"
        );

        let old_len = self.clauses.len();
        let mut old_to_new = vec![None; old_len];

        if self.garbage.is_empty() {
            for (index, mapped) in old_to_new.iter_mut().enumerate() {
                *mapped = Some(index);
            }

            return old_to_new;
        }

        let old_clauses = std::mem::take(&mut self.clauses);

        self.clauses = old_clauses
            .into_iter()
            .enumerate()
            .filter(|(old_index, _)| !self.garbage.is_garbage(*old_index))
            .enumerate()
            .map(|(new_index, (old_index, clause))| {
                old_to_new[old_index] = Some(new_index);
                clause
            })
            .collect();

        // Resume at the first surviving slot at or after the old cursor,
        // wrapping if the cursor's suffix was entirely deleted.
        self.ges_cursor = old_to_new
            .iter()
            .skip(self.ges_cursor)
            .chain(old_to_new.iter().take(self.ges_cursor))
            .find_map(|&index| index)
            .unwrap_or(0);
        self.ges_trail_touched = self
            .ges_trail_touched
            .iter()
            .filter_map(|&old_index| old_to_new[old_index])
            .collect();
        self.ges_trail_seen = vec![false; self.clauses.len()];
        for &clause_idx in &self.ges_trail_touched {
            self.ges_trail_seen[clause_idx] = true;
        }
        self.garbage.reset(self.clauses.len());
        self.rebuild_clause_indices();

        if let Some(history) = history {
            history.remap_clause_indices(&old_to_new);
        }

        old_to_new
    }

    fn rebuild_clause_indices(&mut self) {
        self.watch = Watch::new(self.assignment.len());
        self.occurrence = vec![Vec::new(); self.assignment.len() * 2];
        self.occurrence_stale = vec![0; self.assignment.len() * 2];

        let clauses = &self.clauses;
        let occurrence = &mut self.occurrence;
        let watch = &mut self.watch;
        for (clause_idx, clause) in clauses.iter().enumerate() {
            for lit in clause.get_literals() {
                occurrence[lit.get_unsigned_index() as usize].push(clause_idx);
            }

            if let Some((first, second)) = clause.watched_literals() {
                watch.add_to_watchlist(clause_idx, first, *second.unwrap_or(first));
                if let Some(second) = second {
                    watch.add_to_watchlist(clause_idx, second, *first);
                }
            }
        }
    }

    pub fn add_literal(&mut self) -> Literal {
        let index = self.assignment.add_variable();
        self.vsids.add_variable();
        self.watch.add_literal();
        self.occurrence.push(Vec::new());
        self.occurrence.push(Vec::new());
        self.occurrence_stale.push(0);
        self.occurrence_stale.push(0);

        Literal::new(index as i32)
    }

    pub(crate) fn rebuild_vsids(&mut self) {
        let vsids = Vsids::from_formula(self);
        self.vsids = vsids;
    }

    pub fn set_variable(&mut self, index: usize, value: bool) {
        self.assignment.assign(index, value)
    }

    pub fn unset_variable(&mut self, index: usize) {
        self.assignment.unset(index);
    }

    pub fn add_decision(&mut self, literal: &Literal, history: &mut History) {
        self.assignment
            .assign(literal.get_index().abs() as usize, !literal.is_negated());
        history.add_decision(literal);
    }

    pub(crate) fn configure_ges_trail_tracking(&mut self, enabled: bool) {
        self.ges_trail_tracking = enabled;
        self.clear_ges_trail_touched();
    }

    pub(crate) fn clear_ges_trail_touched(&mut self) {
        for clause_idx in self.ges_trail_touched.drain(..) {
            if let Some(seen) = self.ges_trail_seen.get_mut(clause_idx) {
                *seen = false;
            }
        }
    }

    fn record_ges_trail_touch(&mut self, clause_idx: usize) {
        if self.ges_trail_tracking && !self.ges_trail_seen[clause_idx] {
            self.ges_trail_seen[clause_idx] = true;
            self.ges_trail_touched.push(clause_idx);
            self.stats.ges_trail_unique_touches += 1;
        }
    }

    pub(crate) fn record_ges_analysis_use(&mut self, clause_idx: usize) {
        self.record_ges_trail_touch(clause_idx);
        self.stats
            .record_ges_analysis_use(&mut self.clauses[clause_idx]);
    }

    pub(crate) fn record_conflict_literal_utilities(
        &mut self,
        literals: impl IntoIterator<Item = Literal>,
    ) {
        self.extensions.begin_conflict_utility();
        for literal in literals {
            self.extensions.bump_conflict_utility(&literal);
        }
        self.extensions.decay_literal_utility();
    }

    pub fn assign_implication(
        &mut self,
        literal: Literal,
        history: &mut History,
        reason_clause_idx: Option<usize>,
    ) -> AssignResult {
        let result = self
            .assignment
            .assign_implication(literal, history, reason_clause_idx);
        if let AssignResult::Assigned(literal) = &result {
            self.extensions.bump_propagation_utility(literal);
            if let Some(idx) = reason_clause_idx {
                self.record_ges_trail_touch(idx);
                self.clauses[idx].increment_lock_count();
                self.stats.record_ges_reason_use(&mut self.clauses[idx]);
            }
        }
        result
    }

    pub fn revert_decision(&mut self, level: usize, history: &mut History) {
        let removed_reasons = history.revert_decision_collect_reasons(level, &mut self.assignment);
        for idx in removed_reasons {
            if let Some(clause) = self.clauses.get_mut(idx) {
                clause.decrement_lock_count();
            }
        }
    }

    pub fn revert_last_decision(&mut self, history: &mut History) {
        self.revert_decision(history.get_decision_level(), history);
    }

    /// Rewind only the root trail; clause locks must follow the removed reasons.
    pub(crate) fn rewind_root_implications(&mut self, history: &mut History) {
        for index in history.rewind_root_implications(&mut self.assignment) {
            self.clauses[index].decrement_lock_count();
        }
    }

    /// Restore a closed root trail after clauses or their reasons were retired.
    /// Existing clauses must be scanned: new-clause-only propagation misses old units.
    pub(crate) fn rebuild_root_implications(&mut self, history: &mut History) -> bool {
        if self.get_clauses().any(|(_, clause)| clause.len() == 0) {
            return true;
        }
        let mut queue = VecDeque::new();
        let units = self
            .get_clauses()
            .filter(|(_, clause)| clause.len() == 1)
            .map(|(index, clause)| (index, clause.get_literals()[0]))
            .collect::<Vec<_>>();
        for (index, literal) in units {
            match self.assign_implication(literal, history, Some(index)) {
                AssignResult::Conflict => return true,
                AssignResult::Assigned(literal) => queue.push_back(literal),
                AssignResult::AlreadyAssigned => {}
            }
        }
        self.propagate_twl(history, &mut queue).is_some()
    }

    pub fn get_empty_clauses(&self) -> Option<Vec<&Clause>> {
        let empty_clauses: Vec<&Clause> = self
            .get_clauses()
            .map(|(_, clause)| clause)
            .filter(|clause| clause.is_empty(&self.assignment))
            .collect();
        if empty_clauses.len() > 0 {
            Some(empty_clauses)
        } else {
            None
        }
    }

    /// Picks a random literal from a live, non-empty clause.
    pub fn pick_literal(&self) -> Option<&Literal> {
        let candidate_count = self
            .get_clauses()
            .filter(|(_, clause)| !clause.get_literals().is_empty())
            .count();
        if candidate_count == 0 {
            return None;
        }

        let clause_offset = rand::random_range(0..candidate_count);
        let clause = self
            .get_clauses()
            .filter_map(|(_, clause)| (!clause.get_literals().is_empty()).then_some(clause))
            .nth(clause_offset)?;
        let literal_offset = rand::random_range(0..clause.len());
        clause.get_literals().get(literal_offset)
    }

    pub fn get_pure_literals(&mut self) -> Vec<Literal> {
        let assignment = &self.assignment;

        // variable_index -> bitmask
        // 0b01 = positive seen
        // 0b10 = negative seen
        let mut polarity: HashMap<usize, u8> = HashMap::new();

        for (_, clause) in self
            .get_clauses()
            .filter(|(_, clause)| !clause.is_satisfied(assignment))
        {
            for lit in clause.get_unassigned_literals(assignment) {
                let bit = if lit.is_negated() { 0b10 } else { 0b01 };
                polarity
                    .entry(lit.get_index().abs() as usize)
                    .and_modify(|mask| *mask |= bit)
                    .or_insert(bit);
            }
        }

        let mut pure_literals = Vec::new();

        for (var, mask) in polarity {
            match mask {
                0b01 => pure_literals.push(Literal::new(var as i32)),
                0b10 => pure_literals.push(Literal::new(-(var as i32))),
                _ => {}
            }
        }

        pure_literals
    }

    pub fn is_satisfied(&self) -> bool {
        self.get_clauses()
            .all(|(_, clause)| clause.is_satisfied(&self.assignment))
    }

    pub fn get_unit_clauses(&self) -> Vec<(usize, &Clause)> {
        self.get_clauses()
            .filter(|(_, clause)| {
                !clause.is_satisfied(&self.assignment) && clause.is_unit(&self.assignment)
            })
            .collect()
    }

    pub fn get_unit_clauses_mut(&mut self, assignment: &Assignment) -> Vec<(usize, &mut Clause)> {
        self.get_clauses_mut()
            .filter(|(_, clause)| !clause.is_satisfied(assignment) && clause.is_unit(assignment))
            .collect()
    }

    pub fn unit_propagate(&mut self, mut history: Option<&mut History>) -> bool {
        let mut progress = false;
        loop {
            let mut found = None;
            for (idx, clause) in self.get_clauses() {
                if let Some(unit) = clause.get_unit_literal(&self.assignment) {
                    found = Some((idx, *unit));
                    break;
                }
            }

            if let Some((idx, literal)) = found {
                if let Some(history) = history.as_deref_mut() {
                    self.assign_implication(literal, history, Some(idx));
                } else {
                    self.assignment.assign_literal(literal);
                }
                progress = true;
            } else {
                break;
            }
        }
        progress
    }

    pub fn pure_literals_propagate(&mut self, mut history: Option<&mut History>) -> bool {
        let mut progress = false;
        loop {
            let pure_literals = self.get_pure_literals();
            if let Some(pure) = pure_literals.into_iter().next() {
                if let Some(history) = history.as_deref_mut() {
                    self.assign_implication(pure, history, None);
                } else {
                    self.assignment.assign_literal(pure);
                }
                progress = true;
            } else {
                break;
            }
        }

        progress
    }

    pub fn propagate_twl(
        &mut self,
        history: &mut History,
        queue: &mut VecDeque<Literal>,
    ) -> Option<usize> {
        while let Some(lit) = queue.pop_front() {
            let false_lit = lit.negated();

            // Take ownership of this literal's watchlist. We reuse this same
            // allocation and compact surviving entries in place.
            let garbage = &self.garbage;
            let mut watching_clauses = self
                .watch
                .take_live(&false_lit, |clause_idx| !garbage.is_garbage(clause_idx));

            let original_len = watching_clauses.len();
            let mut read_idx = 0;
            let mut write_idx = 0;

            while read_idx < original_len {
                let mut entry = watching_clauses[read_idx];
                let clause_usize = entry.clause_idx;

                // take_live has removed garbage before this clause-body-free check.
                // A former watch is still a valid blocker after literal swaps.
                if entry.blocker.eval(&self.assignment) == Some(true) {
                    watching_clauses[write_idx] = entry;
                    write_idx += 1;
                    read_idx += 1;
                    continue;
                }

                // Unless we find a replacement watch, this clause remains in the
                // current watchlist.
                let mut keep_current_watch = true;
                let mut conflict_found = false;

                {
                    let clause = &mut self.clauses[clause_usize];

                    /*
                     * Clauses shorter than two literals cannot participate in the
                     * normal two-watched-literal procedure.
                     */
                    if clause.len() < 2 {
                        if clause
                            .get_literals()
                            .first()
                            .is_some_and(|watched| watched == &false_lit)
                        {
                            conflict_found = true;
                        }
                    } else {
                        /*
                         * Determine which of the first two entries is the watch
                         * that has just become false.
                         */
                        let false_idx = {
                            let literals = clause.get_literals();

                            if literals[0] == false_lit {
                                0
                            } else {
                                debug_assert_eq!(literals[1], false_lit);
                                1
                            }
                        };

                        let other_idx = 1 - false_idx;
                        let other_lit = clause.get_literals()[other_idx].clone();
                        let other_value = other_lit.eval(&self.assignment);
                        entry.blocker = other_lit;

                        /*
                         * If the other watched literal is true, the clause is
                         * already satisfied and remains on this watchlist.
                         */
                        if other_value != Some(true) {
                            /*
                             * Search for a non-false replacement watch.
                             *
                             * Do this with an explicit loop because this is a very
                             * hot path and it avoids iterator/closure machinery in
                             * profiles.
                             */
                            let mut replacement = None;

                            for candidate_idx in 2..clause.len() {
                                let candidate = &clause.get_literals()[candidate_idx];

                                if candidate.eval(&self.assignment) != Some(false) {
                                    replacement = Some(candidate_idx);
                                    break;
                                }
                            }

                            if let Some(replacement_idx) = replacement {
                                /*
                                 * Clone before modifying the clause because
                                 * replace_watched_literal mutably borrows it.
                                 */
                                let replacement_lit =
                                    clause.get_literals()[replacement_idx].clone();

                                clause.replace_watched_literal(false_idx, replacement_idx);

                                self.watch.add_to_watchlist(
                                    clause_usize,
                                    &replacement_lit,
                                    other_lit,
                                );

                                // The clause now watches replacement_lit instead
                                // of false_lit, so remove it from this watchlist.
                                keep_current_watch = false;
                            } else {
                                /*
                                 * No replacement exists:
                                 *
                                 * - other false      => conflict
                                 * - other unassigned => unit propagation
                                 */
                                match other_value {
                                    Some(false) => {
                                        conflict_found = true;
                                    }

                                    None => {
                                        self.assignment.assign(
                                            other_lit.get_index().abs() as usize,
                                            !other_lit.is_negated(),
                                        );

                                        history.add_implication(&other_lit, Some(clause_usize));
                                        self.extensions.bump_propagation_utility(&other_lit);

                                        if self.ges_trail_tracking
                                            && !self.ges_trail_seen[clause_usize]
                                        {
                                            self.ges_trail_seen[clause_usize] = true;
                                            self.ges_trail_touched.push(clause_usize);
                                            self.stats.ges_trail_unique_touches += 1;
                                        }
                                        clause.increment_lock_count();
                                        self.stats.record_ges_reason_use(clause);
                                        queue.push_back(other_lit);
                                    }

                                    Some(true) => {
                                        // Handled by the outer condition.
                                        unreachable!();
                                    }
                                }
                            }
                        }
                    }
                }

                /*
                 * Compact retained entries toward the beginning of the same
                 * allocation.
                 */
                if keep_current_watch {
                    watching_clauses[write_idx] = entry;

                    write_idx += 1;
                }

                read_idx += 1;

                if conflict_found {
                    /*
                     * All unprocessed clauses still watch false_lit. Preserve the
                     * entire remaining tail in one overlapping-safe bulk move
                     * instead of pushing each entry individually.
                     */
                    let remaining = original_len - read_idx;

                    if remaining != 0 && write_idx != read_idx {
                        watching_clauses.copy_within(read_idx..original_len, write_idx);
                    }

                    write_idx += remaining;
                    watching_clauses.truncate(write_idx);

                    self.watch.set(&false_lit, watching_clauses);

                    return Some(clause_usize);
                }
            }

            watching_clauses.truncate(write_idx);
            self.watch.set(&false_lit, watching_clauses);
        }

        None
    }

    pub fn contains_empty_clause(&self, assignment: &Assignment) -> bool {
        self.get_clauses()
            .any(|(_, clause)| clause.is_empty(assignment))
    }

    pub fn get_empty_clause(&self, assignment: &Assignment) -> Option<(usize, &Clause)> {
        self.get_clauses()
            .find(|(_idx, clause)| clause.is_empty(assignment))
    }

    pub(crate) fn is_retired_extension_variable(&self, variable: usize) -> bool {
        self.retired_extension_variables.contains(&variable)
    }

    pub(crate) fn retire_extension_variable(&mut self, variable: usize) {
        self.retired_extension_variables.insert(variable);
    }

    pub fn get_unassigned_literal(&self) -> Option<Literal> {
        for i in 1..self.assignment.len() {
            if self.assignment.get_value(i).is_none() && !self.is_retired_extension_variable(i) {
                return Some(Literal::new(i as i32));
            }
        }

        None
    }

    pub fn reduce_db<W: Write>(
        &mut self,
        history: &mut History,
        logger: &mut Option<DratLogger<W>>,
        mut signal: Option<(Python<'_>, &mut u64)>,
    ) -> PyResult<()> {
        let mut candidates: Vec<(usize, i16, usize)> = Vec::new();
        let garbage_pressure = !self.garbage.is_empty()
            && self
                .garbage
                .count()
                .saturating_mul(DB_REDUCTION_GARBAGE_RATIO)
                >= self.clauses.len();

        // `clauses_kept` is an upper bound on removable learned clauses. Avoid a
        // full database scan every 2,000 conflicts when reduction cannot fire.
        if self.stats.clauses_kept < DB_REDUCTION_MIN_REMOVABLE_CLAUSES as u64 {
            if garbage_pressure {
                self.collect_garbage(Some(history));
            }
            return Ok(());
        }

        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }

        for (idx, clause) in self.get_clauses_mut() {
            // Original, extension, and inprocessing clauses are permanent.
            if clause.lbd <= 0 || clause.lock_count > 0 || clause.len() <= 2 {
                continue;
            }

            let activity = clause.activity;
            clause.activity = clause.activity.saturating_sub(1);

            // Give a GES replacement several complete reduction intervals to
            // demonstrate usefulness before ordinary quality selection applies.
            if clause.ges_protection > 0 {
                clause.ges_protection -= 1;
                continue;
            }

            // Recently analyzed tier-one clauses survive while active. Tier-two
            // clauses get one additional reduction interval after being used.
            if clause.lbd <= 2 && activity > 0 {
                continue;
            }
            if clause.lbd <= 6 && activity >= Clause::MAX_ACTIVITY - 1 {
                continue;
            }

            candidates.push((idx, clause.lbd, clause.len()));
        }

        if candidates.len() < DB_REDUCTION_MIN_REMOVABLE_CLAUSES {
            if garbage_pressure {
                self.collect_garbage(Some(history));
            }
            return Ok(());
        }

        let delete_count = candidates.len() / 2; // Delete the lesser half based on lbd

        if delete_count == 0 && self.garbage.is_empty() {
            return Ok(());
        }

        // `sort_by` is stable: exact quality ties retain physical insertion
        // order, so older clauses are deleted before equally useful newer ones.
        candidates.sort_by(|(_, lbd_a, len_a), (_, lbd_b, len_b)| {
            lbd_b.cmp(lbd_a).then_with(|| len_b.cmp(len_a))
        });

        let mut to_delete: Vec<usize> = candidates
            .into_iter()
            .take(delete_count)
            .map(|(idx, _, _)| idx)
            .collect();
        to_delete.sort_unstable_by(|a, b| b.cmp(a));

        // Selection above is interruptible; commit is atomic with respect to
        // cancellation so statistics cannot get ahead of actual deletions.
        for &idx in &to_delete {
            self.stats.remove_clause(&self.clauses[idx]);
        }

        self.delete_clauses::<W>(&to_delete, logger);
        if !to_delete.is_empty() || garbage_pressure {
            self.collect_garbage(Some(history));
        }

        Ok(())
    }

    pub fn get_model(&self) -> Vec<bool> {
        self.assignment.to_model()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Empty;

    fn assert_watchlists_consistent(formula: &Formula) {
        let total_lists = formula.assignment.len() * 2;
        let mut expected: Vec<Vec<usize>> = vec![Vec::new(); total_lists];

        for (clause_idx, clause) in formula.get_clauses() {
            if let Some((first, second)) = clause.watched_literals() {
                expected[first.get_unsigned_index() as usize].push(clause_idx);
                if let Some(second) = second {
                    expected[second.get_unsigned_index() as usize].push(clause_idx);
                }
            }
        }

        for var_idx in 1..formula.assignment.len() {
            let var = var_idx as i32;
            for lit in [Literal::new(var), Literal::new(-var)] {
                let mut actual = formula
                    .watch
                    .get_watched(&lit)
                    .iter()
                    .map(|entry| {
                        assert!(
                            formula
                                .get_clause_at_idx(entry.clause_idx)
                                .get_literals()
                                .contains(&entry.blocker)
                        );
                        entry.clause_idx
                    })
                    .collect::<Vec<_>>();
                let mut expected_list = expected[lit.get_unsigned_index() as usize].clone();
                actual.sort_unstable();
                expected_list.sort_unstable();
                assert_eq!(actual, expected_list, "watchlist mismatch for {:?}", lit);
            }
        }
    }

    #[test]
    fn blocker_survives_watch_movement_and_backtracking() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        let mut history = History::new();
        formula.add_decision(&Literal::new(-2), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(-2)])),
            None
        );
        assert_eq!(
            formula.watch.get_watched(&Literal::new(1))[0].blocker,
            Literal::new(2)
        );
        assert_eq!(
            formula.get_clause_at_idx(0).get_literals(),
            &[Literal::new(1), Literal::new(3), Literal::new(2)]
        );
        assert_watchlists_consistent(&formula);
        formula.revert_last_decision(&mut history);

        // The cached blocker is true but is no longer one of the two watches.
        formula.add_decision(&Literal::new(2), &mut history);
        formula.add_decision(&Literal::new(-1), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(-1)])),
            None
        );
        assert_eq!(
            formula.get_clause_at_idx(0).get_literals(),
            &[Literal::new(1), Literal::new(3), Literal::new(2)]
        );
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 0);
        formula.revert_decision(1, &mut history);

        // Once the blocker becomes false, normal propagation must resume.
        formula.add_decision(&Literal::new(-2), &mut history);
        formula.add_decision(&Literal::new(-1), &mut history);
        assert_eq!(
            formula.propagate_twl(
                &mut history,
                &mut VecDeque::from([Literal::new(-2), Literal::new(-1)])
            ),
            None
        );
        assert_eq!(formula.assignment.get_value(3), Some(true));
        assert_eq!(
            history.decision_levels[2].get_reason(&Literal::new(3)),
            Some(0)
        );
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 1);
        assert_eq!(
            formula.watch.get_watched(&Literal::new(1))[0].blocker,
            Literal::new(3)
        );
        assert_watchlists_consistent(&formula);
        formula.revert_decision(1, &mut history);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 0);
    }

    #[test]
    fn true_blocker_does_not_keep_deleted_clause_or_hide_replacement() {
        let mut formula = Formula::from_vec(vec![vec![-1, 2, 3]]);
        let replacement = formula.add_clause_unchecked::<Empty>(
            Clause::from_literals(vec![Literal::new(-1), Literal::new(3)], -1),
            &mut None,
        );
        formula.delete_clause::<Empty>(0, &mut None);
        let mut history = History::new();
        formula.add_decision(&Literal::new(2), &mut history);
        formula.add_decision(&Literal::new(1), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(1)])),
            None
        );
        assert_eq!(formula.assignment.get_value(3), Some(true));
        assert_eq!(formula.watch.get_watched(&Literal::new(-1)).len(), 1);
        assert_eq!(
            formula.watch.get_watched(&Literal::new(-1))[0].clause_idx,
            replacement
        );
        assert_eq!(
            formula.collect_garbage(Some(&mut history)),
            vec![None, Some(0)]
        );
        assert_watchlists_consistent(&formula);
        assert_eq!(
            history.decision_levels[2].get_reason(&Literal::new(3)),
            Some(0)
        );
        formula.revert_decision(1, &mut history);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 0);
    }

    #[test]
    fn conflict_preserves_updated_entry_and_unprocessed_blockers_after_move() {
        let mut formula = Formula::from_vec(vec![vec![-1, 2, 3], vec![-1, 4], vec![-1, 5]]);
        let tail = formula.watch.get_watched(&Literal::new(-1))[2];
        let mut history = History::new();
        formula.add_decision(&Literal::new(-4), &mut history);
        formula.add_decision(&Literal::new(1), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(1)])),
            Some(1)
        );
        let entries = formula.watch.get_watched(&Literal::new(-1));
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].clause_idx, 1);
        assert_eq!(entries[0].blocker, Literal::new(4));
        assert_eq!(entries[1], tail);
        assert_watchlists_consistent(&formula);
        formula.revert_decision(1, &mut history);
        formula.add_decision(&Literal::new(1), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(1)])),
            None
        );
        assert_eq!(formula.assignment.get_value(4), Some(true));
        assert_eq!(formula.assignment.get_value(5), Some(true));
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn attachment_initializes_unit_and_opposite_watch_blockers() {
        let mut formula = Formula::new(3);
        for literals in [vec![], vec![1], vec![-1, 2, 3]] {
            formula.add_clause_unchecked::<Empty>(
                Clause::from_literals(literals.into_iter().map(Literal::new).collect(), -1),
                &mut None,
            );
        }
        assert_eq!(
            formula.watch.get_watched(&Literal::new(1))[0].blocker,
            Literal::new(1)
        );
        assert_eq!(
            formula.watch.get_watched(&Literal::new(-1))[0].blocker,
            Literal::new(2)
        );
        assert_eq!(
            formula.watch.get_watched(&Literal::new(2))[0].blocker,
            Literal::new(-1)
        );
        assert_watchlists_consistent(&formula);
        assert_watchlists_consistent(&formula.clone());
        let mut history = History::new();
        formula.add_decision(&Literal::new(-1), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(-1)])),
            Some(1)
        );
    }

    #[test]
    fn attachment_watches_unfalsified_literals_under_an_existing_assignment() {
        let mut formula = Formula::new(4);
        let mut history = History::new();
        for literal in [Literal::new(-1), Literal::new(-2)] {
            assert!(matches!(
                formula.assign_implication(literal, &mut history, None),
                AssignResult::Assigned(_)
            ));
        }

        let clause_idx = formula.add_clause_unchecked::<Empty>(
            Clause::from_literals([1, 2, 3, 4].map(Literal::new).to_vec(), 0),
            &mut None,
        );

        assert_eq!(
            formula.get_clause_at_idx(clause_idx).watched_literals(),
            Some((&Literal::new(3), Some(&Literal::new(4))))
        );
        formula.add_decision(&Literal::new(-3), &mut history);
        assert_eq!(
            formula.propagate_twl(&mut history, &mut VecDeque::from([Literal::new(-3)])),
            None
        );
        assert_eq!(formula.assignment.get_value(4), Some(true));
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn ges_reason_uses_count_only_successful_implications_and_survive_backtracking() {
        let mut formula = Formula::from_vec(vec![vec![-1, 2]]);
        formula.get_clause_at_idx_mut(0).ges_generated = true;
        let mut history = History::new();
        formula.add_decision(&Literal::new(1), &mut history);
        assert!(matches!(
            formula.assign_implication(Literal::new(2), &mut history, Some(0)),
            AssignResult::Assigned(_)
        ));
        assert!(matches!(
            formula.assign_implication(Literal::new(2), &mut history, Some(0)),
            AssignResult::AlreadyAssigned
        ));
        assert!(matches!(
            formula.assign_implication(Literal::new(-2), &mut history, Some(0)),
            AssignResult::Conflict
        ));
        assert_eq!(formula.stats.ges_replacement_reason_uses, 1);
        assert!(formula.get_clause_at_idx(0).ges_used);
        formula.revert_last_decision(&mut history);
        assert!(formula.get_clause_at_idx(0).ges_used);
        formula.add_decision(&Literal::new(1), &mut history);
        let mut queue = VecDeque::from([Literal::new(1)]);
        assert_eq!(formula.propagate_twl(&mut history, &mut queue), None);
        assert_eq!(formula.stats.ges_replacement_reason_uses, 2);
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 1);
        formula.revert_last_decision(&mut history);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.delete_clause(0, &mut logger);
        assert_eq!(formula.stats.ges_replacements_deleted_unused, 0);
    }

    #[test]
    fn ges_unused_deletions_count_once_and_metadata_survives_compaction() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4]]);
        for idx in 0..3 {
            formula.get_clause_at_idx_mut(idx).ges_generated = true;
        }
        formula.record_ges_analysis_use(1);
        formula.record_ges_analysis_use(1);
        assert_eq!(formula.stats.ges_replacement_analysis_uses, 2);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.record_clause_removal(0);
        assert_eq!(formula.stats.ges_replacements_deleted_unused, 0);
        assert_eq!(formula.delete_clauses(&[0, 0, 3], &mut logger), 2);
        formula.delete_clause(0, &mut logger);
        assert_eq!(formula.stats.ges_replacements_deleted_unused, 1);
        formula.collect_garbage(None);
        assert_eq!(formula.stats.ges_replacements_deleted_unused, 1);
        let cloned = formula.clone();
        assert!(cloned.get_clause_at_idx(0).ges_generated);
        assert!(cloned.get_clause_at_idx(0).ges_used);
        assert!(cloned.get_clause_at_idx(1).ges_generated);
        assert!(!cloned.get_clause_at_idx(1).ges_used);
        formula.delete_clauses(&[0, 1], &mut logger);
        formula.collect_garbage(None);
        assert_eq!(formula.stats.ges_replacements_deleted_unused, 2);
    }

    #[test]
    fn ges_trail_touches_are_deduplicated_cleared_and_remapped() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4], vec![5]]);
        formula.configure_ges_trail_tracking(true);
        for clause_idx in [4, 1, 4] {
            formula.record_ges_analysis_use(clause_idx);
        }
        assert_eq!(formula.ges_trail_touched, vec![4, 1]);
        assert_eq!(formula.stats.ges_trail_unique_touches, 2);

        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.delete_clauses(&[0, 4], &mut logger);
        formula.collect_garbage(None);
        assert_eq!(formula.ges_trail_touched, vec![0]);
        assert_eq!(formula.ges_trail_seen, vec![true, false, false]);

        formula.clear_ges_trail_touched();
        assert!(formula.ges_trail_touched.is_empty());
        assert_eq!(formula.ges_trail_seen, vec![false; 3]);
        formula.record_ges_analysis_use(2);
        assert_eq!(formula.ges_trail_touched, vec![2]);
        assert_eq!(formula.stats.ges_trail_unique_touches, 3);
    }

    #[test]
    fn ges_cursor_clones_and_remaps_to_next_live_slot() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4], vec![5]]);
        assert_eq!(formula.ges_cursor, 0);
        formula.ges_cursor = 2;
        assert_eq!(formula.clone().ges_cursor, 2);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.delete_clauses(&[0, 2], &mut logger);
        formula.collect_garbage(None);
        assert_eq!(formula.ges_cursor, 1);
        assert_eq!(
            formula.get_clause_at_idx(formula.ges_cursor).get_literals(),
            &[Literal::new(4)]
        );
        formula.ges_cursor = 2;
        formula.delete_clause(2, &mut logger);
        formula.collect_garbage(None);
        assert_eq!(formula.ges_cursor, 0);
        formula.delete_clauses(&[0, 1], &mut logger);
        formula.collect_garbage(None);
        assert_eq!(formula.ges_cursor, 0);
    }

    #[test]
    fn from_vec_initial_clauses_have_unknown_lbd() {
        let formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3], vec![2]]);

        assert!(formula.get_clauses().all(|(_, clause)| clause.lbd == -1));
    }

    #[test]
    fn unsatisfied_mutable_clauses_exclude_garbage() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2]]);
        formula.delete_clause::<Empty>(0, &mut None);
        let assignment = formula.assignment.clone();

        let indices = formula
            .get_unsatisfied_clauses_mut(&assignment)
            .into_iter()
            .map(|(index, _)| index)
            .collect::<Vec<_>>();

        assert_eq!(indices, vec![1]);
    }

    #[test]
    fn occurrence_access_cleans_only_the_encountered_list() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 3], vec![4, 5]]);
        formula.delete_clause::<Empty>(0, &mut None);

        assert_eq!(formula.occurrences_and_garbage(&Literal::new(1)), &[0, 1]);
        assert_eq!(formula.occurrences_and_garbage(&Literal::new(2)), &[0]);
        assert_eq!(formula.live_occurrence_len(&Literal::new(1)), 1);

        formula.clean_occurrence(&Literal::new(1));

        assert_eq!(formula.clause_slots_len(), 3);
        assert_eq!(formula.garbage_clause_count(), 1);
        assert_eq!(formula.occurrences_and_garbage(&Literal::new(1)), &[1]);
        assert_eq!(formula.occurrences_and_garbage(&Literal::new(2)), &[0]);
        assert_eq!(
            formula.occurrence_of(&Literal::new(1)).collect::<Vec<_>>(),
            vec![1]
        );
    }

    #[test]
    fn rejected_deletion_batch_does_not_partially_delete() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2]]);
        formula.get_clause_at_idx_mut(1).increment_lock_count();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            formula.delete_clauses::<Empty>(&[0, 1], &mut None);
        }));

        assert!(result.is_err());
        assert_eq!(formula.live_clause_count(), 2);
        assert_eq!(formula.garbage_clause_count(), 0);
        assert_eq!(formula.occurrences_and_garbage(&Literal::new(1)), &[0]);
    }

    #[test]
    fn propagation_skips_garbage_in_stale_watchlists() {
        let mut formula = Formula::from_vec(vec![vec![-1, 2], vec![-1, 3]]);
        formula.delete_clause::<Empty>(0, &mut None);
        let mut history = History::new();
        let decision = Literal::new(1);
        formula.add_decision(&decision, &mut history);
        let mut queue = VecDeque::from([decision]);

        assert_eq!(formula.propagate_twl(&mut history, &mut queue), None);

        assert_eq!(formula.assignment.get_value(2), None);
        assert_eq!(formula.assignment.get_value(3), Some(true));
        assert_eq!(
            history.decision_levels[1].get_reason(&Literal::new(3)),
            Some(1)
        );
    }

    #[test]
    fn conservative_reduction_collects_when_garbage_ratio_is_high() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4]]);
        formula.delete_clause::<Empty>(0, &mut None);
        let mut history = History::new();

        Python::initialize();
        Python::attach(|py| {
            let mut steps = 0;
            formula
                .reduce_db::<Empty>(&mut history, &mut None, Some((py, &mut steps)))
                .unwrap();
        });

        assert_eq!(formula.clause_slots_len(), 3);
        assert_eq!(formula.garbage_clause_count(), 0);
    }

    #[test]
    fn reduction_ages_tier_two_and_stably_deletes_oldest_quality_ties() {
        let count = DB_REDUCTION_MIN_REMOVABLE_CLAUSES;
        let clauses = (0..count)
            .map(|offset| {
                Clause::from_literals(
                    vec![
                        Literal::new(1),
                        Literal::new(2),
                        Literal::new((offset + 3) as i32),
                    ],
                    4,
                )
            })
            .collect::<Vec<_>>();
        let mut formula = Formula::from_clauses(clauses);
        formula.stats.clauses_kept = count as u64;
        let mut history = History::new();

        formula
            .reduce_db::<Empty>(&mut history, &mut None, None)
            .unwrap();
        assert_eq!(formula.live_clause_count(), count);
        assert!(
            formula
                .get_clauses()
                .all(|(_, clause)| clause.activity == Clause::MAX_ACTIVITY - 1)
        );

        formula
            .reduce_db::<Empty>(&mut history, &mut None, None)
            .unwrap();
        assert_eq!(formula.live_clause_count(), count);
        assert!(
            formula
                .get_clauses()
                .all(|(_, clause)| clause.activity == Clause::MAX_ACTIVITY - 2)
        );

        formula
            .reduce_db::<Empty>(&mut history, &mut None, None)
            .unwrap();

        assert_eq!(formula.live_clause_count(), count / 2);
        assert_eq!(
            formula.get_clause_at_idx(0).get_literals()[2],
            Literal::new((count / 2 + 3) as i32)
        );
    }

    #[test]
    fn reduction_preserves_bva_definitions_and_essential_quotients() {
        use crate::circuits::factorization::{definition_clause, quotient_clause};
        let count = DB_REDUCTION_MIN_REMOVABLE_CLAUSES;
        let literals = [1, 2, 3].map(Literal::new).to_vec();
        let mut clauses = vec![Clause::from_literals(literals.clone(), 7); count];
        clauses.push(definition_clause(literals.clone()));
        clauses.push(quotient_clause(literals.clone()));
        let mut rewritten = quotient_clause(literals);
        rewritten.ges_generated = true;
        rewritten.ges_protection = 0;
        clauses.push(rewritten);
        let mut formula = Formula::from_clauses(clauses);
        formula.stats.clauses_kept = count as u64;
        formula
            .reduce_db::<Empty>(&mut History::new(), &mut None, None)
            .unwrap();
        assert_eq!(formula.live_clause_count(), count / 2 + 3);
        let survivors: Vec<_> = formula
            .get_clauses()
            .filter(|(_, clause)| clause.bva_generated)
            .map(|(_, clause)| (clause.lbd, clause.ges_generated))
            .collect();
        assert_eq!(survivors, vec![(0, false), (-1, false), (-1, true)]);
    }

    #[test]
    fn reduction_protects_ges_replacements_for_five_complete_scans() {
        let count = DB_REDUCTION_MIN_REMOVABLE_CLAUSES;
        let clauses = (0..count)
            .map(|offset| {
                let mut clause = Clause::from_literals(
                    vec![
                        Literal::new(1),
                        Literal::new(2),
                        Literal::new((offset + 3) as i32),
                    ],
                    7,
                );
                clause.ges_generated = true;
                clause.ges_protection = 5;
                clause
            })
            .collect::<Vec<_>>();
        let mut formula = Formula::from_clauses(clauses);
        formula.stats.clauses_kept = count as u64;
        let mut history = History::new();

        for expected in (0..5).rev() {
            formula
                .reduce_db::<Empty>(&mut history, &mut None, None)
                .unwrap();
            assert_eq!(formula.live_clause_count(), count);
            assert!(
                formula
                    .get_clauses()
                    .all(|(_, clause)| clause.ges_protection == expected)
            );
        }

        formula
            .reduce_db::<Empty>(&mut history, &mut None, None)
            .unwrap();
        assert_eq!(formula.live_clause_count(), count / 2);
    }

    #[test]
    fn reduce_db_collects_existing_garbage_without_new_candidates() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3]]);
        formula.delete_clause::<Empty>(1, &mut None);
        let mut history = History::new();

        formula
            .reduce_db::<Empty>(&mut history, &mut None, None)
            .unwrap();

        assert_eq!(formula.clause_slots_len(), 2);
        assert_eq!(formula.live_clause_count(), 2);
        assert_eq!(formula.garbage_clause_count(), 0);
        assert_eq!(
            formula
                .get_clauses()
                .map(|(_, clause)| clause.get_literals()[0].get_index())
                .collect::<Vec<_>>(),
            vec![1, 3]
        );
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn delete_clause_marks_first_and_collect_garbage_reindexes() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 2],      // clause 0: watches x1, x2
            vec![-1, 3],     // clause 1: watches ¬x1, x3
            vec![2],         // clause 2: watches x2
            vec![-2, -3, 1], // clause 3: watches ¬x2, ¬x3
        ]);

        assert_watchlists_consistent(&formula);
        formula.delete_clause::<Empty>(1, &mut None);

        assert_eq!(formula.live_clause_count(), 3);
        assert_eq!(formula.clause_slots_len(), 4);
        assert!(formula.is_clause_garbage(1));
        assert_eq!(
            formula
                .get_clauses()
                .map(|(index, _)| index)
                .collect::<Vec<_>>(),
            vec![0, 2, 3]
        );
        assert_eq!(
            formula.get_clause_and_garbage_at_idx(2).get_literals(),
            &[Literal::new(2)]
        );

        formula.collect_garbage(None);

        assert_eq!(formula.clause_slots_len(), 3);
        assert_eq!(
            formula.get_clause_at_idx(1).get_literals(),
            &[Literal::new(2)]
        );
        assert_watchlists_consistent(&formula);

        // Explicitly verify reindexing for x2 watchlist
        let mut watched_x2 = formula
            .watch
            .get_watched(&Literal::new(2))
            .iter()
            .map(|entry| entry.clause_idx)
            .collect::<Vec<_>>();
        watched_x2.sort_unstable();
        assert_eq!(watched_x2, vec![0, 1]);

        // Deleted clause's watched literals should be gone
        assert!(formula.watch.get_watched(&Literal::new(-1)).is_empty());
        assert!(formula.watch.get_watched(&Literal::new(3)).is_empty());
    }
}
