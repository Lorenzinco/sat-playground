pub mod assignment;
pub mod clause;
pub mod extension;
pub mod garbage;
pub mod literal;

use crate::drat::DratLogger;
use crate::formula::extension::ExtensionMap;
use crate::formula::garbage::Garbage;
use crate::history::History;
use crate::process;
use crate::process::{Process, ProcessBudget};
use crate::python::signal_checker;
use crate::python::stats::Stats;
use crate::watchlist::Watch;
use assignment::AssignResult;
use assignment::Assignment;
use clause::Clause;
use literal::Literal;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt;
use std::io::Write;
use std::time::Instant;

const DB_REDUCTION_MIN_REMOVABLE_CLAUSES: usize = 50_000;
const DB_REDUCTION_GARBAGE_RATIO: usize = 12;

pub struct Formula {
    clauses: Vec<Clause>,
    garbage: Garbage,
    pub assignment: Assignment,
    watch: Watch,
    occurrence: Vec<Vec<usize>>,
    occurrence_stale: Vec<usize>,
    pub stats: Stats,
    pub extensions: ExtensionMap,
    self_subsuming: bool,
}

impl Clone for Formula {
    fn clone(&self) -> Self {
        Formula {
            clauses: self.clauses.clone(),
            garbage: self.garbage.clone(),
            assignment: self.assignment.clone(),
            watch: self.watch.clone(),
            occurrence: self.occurrence.clone(),
            occurrence_stale: self.occurrence_stale.clone(),
            stats: self.stats.clone(),
            extensions: self.extensions.clone(),
            self_subsuming: self.self_subsuming,
        }
    }
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
            self_subsuming: false,
        }
    }

    pub fn from_clauses(clauses: &[Clause]) -> Self {
        let max_index = clauses
            .iter()
            .flat_map(|clause| clause.iter())
            .map(|lit| lit.get_index().abs())
            .max()
            .expect("No literal in any formula found!");

        let mut formula = Formula {
            clauses: clauses.to_owned(),
            garbage: Garbage::new(clauses.len()),
            assignment: Assignment::new(max_index as usize + 1),
            watch: Watch::new(max_index as usize + 1),
            occurrence: vec![Vec::new(); (max_index as usize + 1) * 2],
            occurrence_stale: vec![0; (max_index as usize + 1) * 2],
            stats: Stats::new(),
            extensions: ExtensionMap::new(),
            self_subsuming: false,
        };

        formula.rebuild_clause_indices();
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

        Formula::from_clauses(&clauses)
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
        self.stats
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

    pub fn live_occurrences<'a>(
        &'a self,
        lit: &Literal,
    ) -> impl DoubleEndedIterator<Item = usize> + 'a {
        self.occurrence_of(lit)
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
        if self.self_subsuming && clause.lbd() != 0 {
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
        clause: Clause,
        logger: &mut Option<DratLogger<W>>,
    ) -> usize {
        let clause_idx = self.clauses.len();
        for lit in clause.get_literals() {
            self.add_to_occurrence(clause_idx, lit);
        }

        if let Some((first, second)) = clause.watched_literals() {
            self.watch.add_to_watchlist(clause_idx, first);
            if let Some(second) = second {
                self.watch.add_to_watchlist(clause_idx, second);
            }
        }

        if let Some(log) = logger.as_mut() {
            let _ = log.log_add(clause.get_literals());
        }

        self.clauses.push(clause);
        self.garbage.push_live();
        clause_idx
    }

    pub fn process<W: Write>(
        &mut self,
        methods: Vec<Process>,
        budget: f32,
        logger: &mut Option<DratLogger<W>>,
        signal: Option<(Python<'_>, &mut u64)>,
        replace_subsumption_setting: bool,
        mut history: Option<&mut History>,
    ) -> PyResult<()> {
        if replace_subsumption_setting {
            self.self_subsuming = methods.contains(&Process::Subsumption);
        } else if methods.contains(&Process::Subsumption) {
            self.self_subsuming = true;
        }
        let mut signal = signal;
        let budget = ProcessBudget::new(budget);

        let result: PyResult<()> = (|| -> PyResult<()> {
            for method in methods {
                if budget.exhausted() {
                    break;
                }

                match method {
                    Process::BVA => {
                        let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                        process::bva::process(
                            self,
                            &budget,
                            logger,
                            signal,
                            history.as_deref_mut(),
                        )?;
                    }
                    Process::BVE => {
                        let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                        process::bve::process(
                            self,
                            &budget,
                            logger,
                            signal,
                            history.as_deref_mut(),
                        )?;
                    }
                    Process::Subsumption => {}
                    _ => println!("Not yet implemented!"),
                }
            }

            Ok(())
        })();

        result
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
                    self.clauses[idx].lock_count(),
                    0,
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
            history.is_some() || self.clauses.iter().all(|clause| clause.lock_count() == 0),
            "cannot compact locked reason clauses without remapping history"
        );
        let mut old_to_new = vec![None; self.clauses.len()];
        if self.garbage.is_empty() {
            for (index, mapped) in old_to_new.iter_mut().enumerate() {
                *mapped = Some(index);
            }
            return old_to_new;
        }

        let mut new_index = 0;
        for (old_index, mapped) in old_to_new.iter_mut().enumerate() {
            if !self.garbage.is_garbage(old_index) {
                *mapped = Some(new_index);
                new_index += 1;
            }
        }

        let old_clauses = std::mem::take(&mut self.clauses);
        self.clauses = old_clauses
            .into_iter()
            .enumerate()
            .filter_map(|(index, clause)| (!self.garbage.is_garbage(index)).then_some(clause))
            .collect();
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
                watch.add_to_watchlist(clause_idx, first);
                if let Some(second) = second {
                    watch.add_to_watchlist(clause_idx, second);
                }
            }
        }
    }

    pub fn add_literal(&mut self) -> Literal {
        let index = self.assignment.add_variable();
        self.watch.add_literal();
        self.occurrence.push(Vec::new());
        self.occurrence.push(Vec::new());
        self.occurrence_stale.push(0);
        self.occurrence_stale.push(0);

        Literal::new(index as i32)
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

    pub fn assign_implication(
        &mut self,
        literal: Literal,
        history: &mut History,
        reason_clause_idx: Option<usize>,
    ) -> AssignResult {
        let result = self
            .assignment
            .assign_implication(literal, history, reason_clause_idx);
        if matches!(result, AssignResult::Assigned(_)) {
            if let Some(idx) = reason_clause_idx {
                self.clauses[idx].increment_lock_count();
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

    pub fn get_pure_literals(&mut self) -> Vec<Literal> {
        let clauses = self.get_unsatisfied_clauses();
        let assignment = &self.assignment;

        // variable_index -> bitmask
        // 0b01 = positive seen
        // 0b10 = negative seen
        let mut polarity: HashMap<usize, u8> = HashMap::new();

        for (_, clause) in clauses {
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
        self.get_unsatisfied_clauses()
            .into_iter()
            .filter(|(_, clause)| clause.is_unit(&self.assignment))
            .collect()
    }

    pub fn get_unit_clauses_mut(&mut self, assignment: &Assignment) -> Vec<(usize, &mut Clause)> {
        self.get_unsatisfied_clauses_mut(assignment)
            .into_iter()
            .filter(|(_, clause)| clause.is_unit(assignment))
            .collect()
    }

    pub fn unit_propagate(&mut self, mut history: Option<&mut History>) -> bool {
        let mut progress = false;
        loop {
            let mut found = None;
            for (idx, clause) in self.get_clauses() {
                if let Some(unit) = clause.get_unit_literal(&self.assignment) {
                    found = Some((idx, unit.clone()));
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
                .take_live(&false_lit, |clause_idx| {
                    !garbage.is_garbage(clause_idx)
                });
    
            let original_len = watching_clauses.len();
            let mut read_idx = 0;
            let mut write_idx = 0;
    
            while read_idx < original_len {
                let clause_idx = watching_clauses[read_idx];
                let clause_usize = clause_idx as usize;
    
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
    
                                clause.replace_watched_literal(
                                    false_idx,
                                    replacement_idx,
                                );
    
                                self.watch.add_to_watchlist(
                                    clause_usize,
                                    &replacement_lit,
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
    
                                        history.add_implication(
                                            &other_lit,
                                            Some(clause_usize),
                                        );
    
                                        clause.increment_lock_count();
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
                    if write_idx != read_idx {
                        watching_clauses[write_idx] = clause_idx;
                    }
    
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
                        watching_clauses.copy_within(
                            read_idx..original_len,
                            write_idx,
                        );
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

    pub fn get_unassigned_literal(&self) -> Option<Literal> {
        for i in 1..self.assignment.len() {
            if self.assignment.get_value(i).is_none() {
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
        let conservative = signal.is_some();
        let garbage_pressure = !self.garbage.is_empty()
            && self
                .garbage
                .count()
                .saturating_mul(DB_REDUCTION_GARBAGE_RATIO)
                >= self.clauses.len();

        // `clauses_kept` is an upper bound on removable learned clauses. Avoid a
        // full database scan every 2,000 conflicts when reduction cannot fire.
        if conservative && self.stats.clauses_kept < DB_REDUCTION_MIN_REMOVABLE_CLAUSES as u64 {
            if garbage_pressure {
                self.collect_garbage(Some(history));
            }
            return Ok(());
        }

        for (idx, clause) in self.get_clauses().rev() {
            if let Some((py, steps)) = signal.as_mut() {
                signal_checker(*py, *steps)?;
            }

            match clause.lbd() {
                // Original clauses and inprocessing resolvents are permanent, but
                // an inprocessing clause must not hide older learned clauses.
                -1 => continue,
                0 => continue,
                _ if clause.lock_count() > 0 => continue,
                _ if conservative && clause.len() <= 2 => continue,
                _ if conservative && clause.lbd() <= 2 && clause.len() <= 8 => continue,
                lbd => candidates.push((idx, lbd, clause.len())),
            }
        }

        if conservative && candidates.len() < DB_REDUCTION_MIN_REMOVABLE_CLAUSES {
            if garbage_pressure {
                self.collect_garbage(Some(history));
            }
            return Ok(());
        }

        let delete_count = if conservative {
            candidates.len() / 4
        } else {
            candidates.len() / 2
        };
        if delete_count == 0 && self.garbage.is_empty() {
            return Ok(());
        }

        candidates.sort_by(|(idx_a, lbd_a, len_a), (idx_b, lbd_b, len_b)| {
            lbd_b
                .cmp(lbd_a)
                .then_with(|| len_b.cmp(len_a))
                .then_with(|| idx_a.cmp(idx_b))
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
        if !to_delete.is_empty() || garbage_pressure || !conservative {
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
                let mut actual = formula.watch.get_watched(&lit).clone();
                let mut expected_list = expected[lit.get_unsigned_index() as usize].clone();
                actual.sort_unstable();
                expected_list.sort_unstable();
                assert_eq!(actual, expected_list, "watchlist mismatch for {:?}", lit);
            }
        }
    }

    #[test]
    fn zero_budget_process_skips_transformations() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
        let original_clauses: Vec<Vec<i32>> = formula
            .get_clauses()
            .map(|(_, clause)| {
                clause
                    .get_literals()
                    .iter()
                    .map(Literal::get_index)
                    .collect()
            })
            .collect();

        formula
            .process::<Empty>(vec![Process::BVE], 0.0, &mut None, None, true, None)
            .unwrap();

        let clauses: Vec<Vec<i32>> = formula
            .get_clauses()
            .map(|(_, clause)| {
                clause
                    .get_literals()
                    .iter()
                    .map(Literal::get_index)
                    .collect()
            })
            .collect();
        assert_eq!(clauses, original_clauses);
        assert_eq!(formula.stats.bve_eliminated_variables, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }

    #[test]
    fn from_vec_initial_clauses_have_unknown_lbd() {
        let formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3], vec![2]]);

        assert!(formula.get_clauses().all(|(_, clause)| clause.lbd() == -1));
    }

    fn test_clause(lit: i32, lbd: i16) -> Clause {
        Clause::from_literals(vec![Literal::new(lit)], lbd)
    }

    #[test]
    fn reduce_db_deletes_worst_lbd_quarter_and_preserves_originals_and_extensions() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![13]]);

        formula.add_clause::<Empty>(test_clause(3, 0), &mut None, None);
        formula.add_clause::<Empty>(test_clause(4, 1), &mut None, None);
        formula.add_clause::<Empty>(test_clause(5, 8), &mut None, None);
        formula.add_clause::<Empty>(test_clause(6, 3), &mut None, None);
        formula.add_clause::<Empty>(test_clause(7, 0), &mut None, None);
        formula.add_clause::<Empty>(test_clause(8, 7), &mut None, None);
        formula.add_clause::<Empty>(test_clause(9, 2), &mut None, None);
        formula.add_clause::<Empty>(test_clause(10, 6), &mut None, None);
        formula.add_clause::<Empty>(test_clause(11, 4), &mut None, None);
        formula.add_clause::<Empty>(test_clause(12, 5), &mut None, None);

        let mut history = History::new();
        formula
            .reduce_db::<std::io::Empty>(&mut history, &mut None, None)
            .unwrap();

        let remaining_lits: Vec<i32> = formula
            .get_clauses()
            .map(|(_, clause)| clause.get_literals()[0].get_index())
            .collect();
        let remaining_lbds: Vec<i16> = formula
            .get_clauses()
            .map(|(_, clause)| clause.lbd())
            .collect();

        assert!(remaining_lits.contains(&1));
        assert!(remaining_lits.contains(&2));
        assert!(remaining_lits.contains(&3));
        assert!(remaining_lits.contains(&7));
        assert!(!remaining_lits.contains(&5));
        assert!(!remaining_lits.contains(&8));
        assert_eq!(remaining_lbds.iter().filter(|&&lbd| lbd == -1).count(), 3);
        assert_eq!(remaining_lbds.iter().filter(|&&lbd| lbd == 0).count(), 2);
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn reduce_db_skips_locked_reason_clauses_and_remaps_history_reasons() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![30]]);
        formula.add_clause::<Empty>(test_clause(2, 1), &mut None, None); // idx 2
        formula.add_clause::<Empty>(test_clause(3, 8), &mut None, None); // idx 3, deleted
        formula.add_clause::<Empty>(test_clause(4, 2), &mut None, None); // idx 4
        formula.add_clause::<Empty>(test_clause(5, 3), &mut None, None); // idx 5
        formula.add_clause::<Empty>(test_clause(6, 10), &mut None, None); // idx 6, locked
        formula.add_clause::<Empty>(test_clause(7, 4), &mut None, None); // idx 7
        formula.add_clause::<Empty>(test_clause(8, 5), &mut None, None); // idx 8
        formula.add_clause::<Empty>(test_clause(9, 6), &mut None, None); // idx 9

        let mut history = History::new();
        let decision = Literal::new(1);
        formula.assignment.assign_history(&decision, &mut history);
        let locked_lit = Literal::new(20);
        formula.assign_implication(locked_lit.clone(), &mut history, Some(6));

        formula
            .reduce_db::<std::io::Empty>(&mut history, &mut None, None)
            .unwrap();

        let remaining_lits: Vec<i32> = formula
            .get_clauses()
            .map(|(_, clause)| clause.get_literals()[0].get_index())
            .collect();

        assert!(!remaining_lits.contains(&3));
        assert!(remaining_lits.contains(&6));
        assert_eq!(history.decision_levels[1].get_reason(&locked_lit), Some(5));
        assert_eq!(formula.stats.clauses_deleted, 3);
        assert_eq!(formula.get_clause_at_idx(5).lock_count(), 1);
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn permanent_inprocessing_clause_does_not_hide_older_learned_clauses() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![8]]);
        formula.add_clause::<Empty>(test_clause(2, 9), &mut None, None);
        formula.add_clause::<Empty>(test_clause(3, -1), &mut None, None);
        formula.add_clause::<Empty>(test_clause(4, 8), &mut None, None);
        formula.add_clause::<Empty>(test_clause(5, 7), &mut None, None);
        formula.add_clause::<Empty>(test_clause(6, 6), &mut None, None);
        formula.add_clause::<Empty>(test_clause(7, 5), &mut None, None);

        let mut history = History::new();
        let _ = formula.reduce_db::<std::io::Empty>(&mut history, &mut None, None);

        let remaining_lits: Vec<i32> = formula
            .get_clauses()
            .map(|(_, clause)| clause.get_literals()[0].get_index())
            .collect();

        assert!(!remaining_lits.contains(&2));
        assert!(remaining_lits.contains(&3));
        assert!(!remaining_lits.contains(&4));
        assert_watchlists_consistent(&formula);
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
        let mut watched_x2 = formula.watch.get_watched(&Literal::new(2)).clone();
        watched_x2.sort_unstable();
        assert_eq!(watched_x2, vec![0, 1]);

        // Deleted clause's watched literals should be gone
        assert!(formula.watch.get_watched(&Literal::new(-1)).is_empty());
        assert!(formula.watch.get_watched(&Literal::new(3)).is_empty());
    }
}
