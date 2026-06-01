pub mod assignment;
pub mod clause;
pub mod extension;
pub mod literal;

use crate::drat::DratLogger;
use crate::formula::extension::ExtensionMap;
use crate::history::History;
use crate::process;
use crate::process::Process;
use crate::python::signal_checker;
use crate::python::stats::Stats;
use crate::two_watched::Watch;
use crate::two_watched::Watched;
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

pub struct Formula {
    clauses: Vec<Clause>,
    pub assignment: Assignment,
    watch: Watch,
    pub occurrence: Vec<Vec<usize>>,
    pub stats: Stats,
    pub extensions: ExtensionMap,
    self_subsuming: bool,
}

impl Clone for Formula {
    fn clone(&self) -> Self {
        Formula {
            clauses: self.clauses.clone(),
            assignment: self.assignment.clone(),
            watch: self.watch.clone(),
            occurrence: self.occurrence.clone(),
            stats: self.stats.clone(),
            extensions: self.extensions.clone(),
            self_subsuming: self.self_subsuming,
        }
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let len = self.clauses.len();
        for (i, clause) in self.clauses.iter().enumerate() {
            write!(f, "(")?;
            for (j, literal) in clause.into_iter().enumerate() {
                let color = match literal.eval(&self.assignment) {
                    Some(true) => "\x1b[34m",
                    Some(false) => "\x1b[31m",
                    None => "\x1b[2m",
                };
                let trailing = if j < clause.into_iter().len() - 1 {
                    "∨"
                } else {
                    ""
                };
                let reset = "\x1b[0m";
                write!(f, "{}{:?}{}{}", color, literal, reset, trailing)?;
            }
            let trailing = if i < len - 1 { "∧" } else { "" };
            write!(f, "){}", trailing)?;
        }

        write!(f, "")
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let len = self.clauses.len();
        for (i, clause) in self.clauses.iter().enumerate() {
            let trailing = if i < len - 1 { "∧" } else { "" };
            write!(f, "{}{}", clause, trailing)?;
        }
        write!(f, "")
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
            assignment: Assignment::new(storage),
            watch: Watch::new(storage),
            occurrence: vec![Vec::new(); storage * 2],
            stats: Stats::new(),
            extensions: ExtensionMap::new(),
            self_subsuming: false,
        }
    }

    pub fn from_clauses(clauses: &Vec<Clause>) -> Self {
        let max_index = clauses
            .iter()
            .flat_map(|clause| clause.iter())
            .map(|lit| lit.get_index().abs())
            .max()
            .expect("No literal in any formula found!");

        let mut formula = Formula {
            clauses: clauses.to_owned(),
            assignment: Assignment::new(max_index as usize + 1),
            watch: Watch::new(max_index as usize + 1),
            occurrence: vec![Vec::new(); (max_index as usize + 1) * 2],
            stats: Stats::new(),
            extensions: ExtensionMap::new(),
            self_subsuming: false,
        };

        for i in 0..formula.clauses.len() {
            let clause = &formula.clauses[i];
            let occurrence_literals = clause.get_literals().clone();
            for lit in &occurrence_literals {
                formula.add_to_occurrence(i, lit);
            }

            let clause = &formula.clauses[i];
            match clause.watched {
                Watched::Two(idx1, idx2) => {
                    formula
                        .watch
                        .add_to_watchlist(i, &clause.get_literals()[idx1]);
                    formula
                        .watch
                        .add_to_watchlist(i, &clause.get_literals()[idx2]);
                }
                Watched::One(idx) => {
                    formula
                        .watch
                        .add_to_watchlist(i, &clause.get_literals()[idx]);
                }
                Watched::None => {}
            }
        }

        formula
    }

    pub fn from_vec(raw_clauses: Vec<Vec<i32>>) -> Self {
        let mut clauses = Vec::new();
        for raw_clause in raw_clauses.iter() {
            let mut clause = Clause::new();
            for raw_lit in raw_clause.iter() {
                if *raw_lit == 0 {
                    panic!("0 indexing is not allowed on dimacs")
                }
                let lit = Literal::new(*raw_lit);
                clause
                    .add_literal(&lit)
                    .expect("Literal cannot be in the same clause twice");
            }
            clauses.push(clause);
        }

        Formula::from_clauses(&clauses)
    }

    /// Returns a reference to the clauses of the formula.
    pub fn get_clauses(&self) -> &Vec<Clause> {
        &self.clauses
    }

    pub fn get_clause_at_idx(&self, index: usize) -> &Clause {
        self.clauses.get(index).expect("Clause not present")
    }

    pub fn get_clause_at_idx_mut(&mut self, index: usize) -> &mut Clause {
        self.clauses.get_mut(index).expect("Clause not present")
    }

    /// Returns a mutable reference to the Clause.
    pub fn get_clauses_mut(&mut self) -> &mut Vec<Clause> {
        &mut self.clauses
    }

    /// Returns a vector of mutable references to the unsatisfied clauses of the formula, this is used to modify the clauses during the solving process.
    pub fn get_unsatisfied_clauses(&self) -> Vec<(usize, &Clause)> {
        self.get_clauses()
            .iter()
            .enumerate()
            .filter(|(_, clause)| !clause.is_satisfied(&self.assignment))
            .collect()
    }

    ///
    pub fn get_unsatisfied_clauses_mut(
        &mut self,
        assignment: &Assignment,
    ) -> Vec<(usize, &mut Clause)> {
        self.get_clauses_mut()
            .into_iter()
            .enumerate()
            .filter(|(_, clause)| !clause.is_satisfied(&assignment))
            .collect()
    }

    pub fn get_stats(&self) -> Stats {
        self.stats
    }

    pub fn self_subsuming_enabled(&self) -> bool {
        self.self_subsuming
    }

    pub fn add_to_occurrence(&mut self, clause_idx: usize, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;
        if idx >= self.occurrence.len() {
            self.occurrence.resize(idx + 1, Vec::new());
        }
        self.occurrence[idx].push(clause_idx);
    }

    pub fn occurrence_of(&self, lit: &Literal) -> &[usize] {
        self.occurrence
            .get(lit.get_unsigned_index() as usize)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn occurrence_indices(&self, lit: &Literal) -> Vec<usize> {
        self.occurrence_of(lit)
            .iter()
            .copied()
            .filter(|&idx| idx < self.clauses.len())
            .collect()
    }

    pub fn candidate_indices_for_clause(&self, clause: &Clause) -> Vec<usize> {
        let Some(shortest_occurrence_lit) = clause
            .get_literals()
            .iter()
            .filter(|lit| !self.occurrence_of(lit).is_empty())
            .min_by_key(|lit| self.occurrence_of(lit).len())
        else {
            return Vec::new();
        };

        self.occurrence_of(shortest_occurrence_lit).to_vec()
    }

    pub fn occurrence_intersection(
        &self,
        watch_a: &Literal,
        watch_b: Option<&Literal>,
    ) -> Vec<usize> {
        let Some(watch_b) = watch_b else {
            return self.occurrence_of(watch_a).to_vec();
        };

        let mut a = self.occurrence_of(watch_a);
        let mut b = self.occurrence_of(watch_b);
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
        history: Option<&mut History>,
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
                let old_to_new = self.delete_clauses::<W>(&result.subsumed_existing, logger);
                if let Some(history) = history {
                    history.remap_clause_indices(&old_to_new);
                }
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

        match clause.watched {
            Watched::None => {}
            Watched::One(idx) => {
                self.watch
                    .add_to_watchlist(clause_idx, &clause.get_literals()[idx as usize]);
            }
            Watched::Two(idx1, idx2) => {
                self.watch
                    .add_to_watchlist(clause_idx, &clause.get_literals()[idx1 as usize]);
                self.watch
                    .add_to_watchlist(clause_idx, &clause.get_literals()[idx2 as usize]);
            }
        }

        if let Some(log) = logger.as_mut() {
            let _ = log.log_add(clause.get_literals());
        }

        self.clauses.push(clause);
        clause_idx
    }

    pub fn process<W: Write>(
        &mut self,
        methods: Vec<Process>,
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

        for method in methods {
            match method {
                Process::BVA => {
                    let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                    process::bva::process(self, logger, signal, history.as_deref_mut())?;
                }
                Process::BVE => {
                    let signal = signal.as_mut().map(|(py, steps)| (*py, &mut **steps));
                    process::bve::process(self, logger, signal, history.as_deref_mut())?;
                }
                Process::Subsumption => {}
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

    pub fn delete_clauses<W: Write>(
        &mut self,
        clause_indices: &[usize],
        logger: &mut Option<DratLogger<W>>,
    ) -> Vec<Option<usize>> {
        let mut old_to_new = vec![None; self.clauses.len()];
        if clause_indices.is_empty() {
            for idx in 0..self.clauses.len() {
                old_to_new[idx] = Some(idx);
            }
            return old_to_new;
        }

        let mut to_delete = clause_indices.to_vec();
        to_delete.sort_unstable();
        to_delete.dedup();

        let mut deleted = vec![false; self.clauses.len()];
        for &idx in &to_delete {
            assert!(idx < self.clauses.len());
            assert_eq!(
                self.clauses[idx].lock_count, 0,
                "cannot delete a clause that is locked as an active implication reason"
            );
            deleted[idx] = true;
        }

        if let Some(log) = logger {
            for &idx in &to_delete {
                let _ = log.log_delete(self.clauses[idx].get_literals());
            }
        }

        let mut new_idx = 0;
        for old_idx in 0..self.clauses.len() {
            if !deleted[old_idx] {
                old_to_new[old_idx] = Some(new_idx);
                new_idx += 1;
            }
        }

        let old_clauses = std::mem::take(&mut self.clauses);
        self.clauses = old_clauses
            .into_iter()
            .enumerate()
            .filter_map(|(idx, clause)| (!deleted[idx]).then_some(clause))
            .collect();
        self.rebuild_clause_indices();
        old_to_new
    }

    fn rebuild_clause_indices(&mut self) {
        self.watch = Watch::new(self.assignment.len());
        self.occurrence = vec![Vec::new(); self.assignment.len() * 2];

        for clause_idx in 0..self.clauses.len() {
            let occurrence_literals = self.clauses[clause_idx].get_literals().clone();
            for lit in &occurrence_literals {
                self.add_to_occurrence(clause_idx, lit);
            }

            let literals = self.clauses[clause_idx].get_literals().clone();
            match self.clauses[clause_idx].watched {
                Watched::None => {}
                Watched::One(idx) => self.watch.add_to_watchlist(clause_idx, &literals[idx]),
                Watched::Two(idx1, idx2) => {
                    self.watch.add_to_watchlist(clause_idx, &literals[idx1]);
                    self.watch.add_to_watchlist(clause_idx, &literals[idx2]);
                }
            }
        }
    }

    pub fn add_literal(&mut self) -> Literal {
        let index = self.assignment.add_variable();
        self.watch.add_literal();
        self.occurrence.push(Vec::new());
        self.occurrence.push(Vec::new());

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
                self.clauses[idx].lock_count += 1;
            }
        }
        result
    }

    pub fn revert_decision(&mut self, level: usize, history: &mut History) {
        let removed_reasons = history.revert_decision_collect_reasons(level, &mut self.assignment);
        for idx in removed_reasons {
            if let Some(clause) = self.clauses.get_mut(idx) {
                clause.lock_count = clause.lock_count.saturating_sub(1);
            }
        }
    }

    pub fn revert_last_decision(&mut self, history: &mut History) {
        self.revert_decision(history.get_decision_level(), history);
    }

    pub fn get_empty_clauses(&self) -> Option<Vec<&Clause>> {
        let empty_clauses: Vec<&Clause> = self
            .clauses
            .iter()
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
        self.clauses
            .iter()
            .all(|clause| clause.is_satisfied(&self.assignment))
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
            for (idx, clause) in self.clauses.iter().enumerate() {
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

            // take to avoid cloning
            let watching_clauses = self.watch.take(&false_lit);
            let mut keep_watchlist = Vec::new();
            let mut conflict = None;

            for &clause_idx in &watching_clauses {
                // If we already hit a conflict, just push the rest back
                if conflict.is_some() {
                    keep_watchlist.push(clause_idx);
                    continue;
                }

                let clause = &mut self.clauses[clause_idx as usize];

                let (false_idx, other_idx) = match clause.watched {
                    Watched::Two(i, j) => {
                        if clause.get_literals()[i as usize] == false_lit {
                            (i, j)
                        } else {
                            (j, i)
                        }
                    }
                    Watched::One(i) => {
                        keep_watchlist.push(clause_idx);
                        if clause.get_literals()[i as usize] == false_lit {
                            conflict = Some(clause_idx);
                        }
                        continue;
                    }
                    Watched::None => {
                        keep_watchlist.push(clause_idx);
                        continue;
                    }
                };

                let other_lit = clause.get_literals()[other_idx as usize].clone();

                // 1. If the other watched literal is True, the clause is already satisfied.
                if other_lit.eval(&self.assignment) == Some(true) {
                    keep_watchlist.push(clause_idx);
                    continue;
                }

                // 2. Try to find a new unassigned (or true) literal in the clause to watch
                let mut found_new_watch = false;
                for k in 0..clause.get_literals().len() {
                    if k == false_idx as usize || k == other_idx as usize {
                        continue;
                    }

                    let candidate = clause.get_literals()[k].clone();
                    if candidate.eval(&self.assignment) != Some(false) {
                        clause.watched = Watched::Two(k, other_idx);
                        // Add to candidate's watchlist (we don't remove from false_lit because we already took it!)
                        self.watch.add_to_watchlist(clause_idx as usize, &candidate);
                        found_new_watch = true;
                        break;
                    }
                }

                // 3. If we couldn't find a new literal to watch...
                if !found_new_watch {
                    keep_watchlist.push(clause_idx);
                    if other_lit.eval(&self.assignment) == Some(false) {
                        conflict = Some(clause_idx);
                    } else {
                        self.assignment.assign(
                            other_lit.get_index().abs() as usize,
                            !other_lit.is_negated(),
                        );
                        history.add_implication(&other_lit, Some(clause_idx as usize));
                        self.clauses[clause_idx as usize].lock_count += 1;
                        queue.push_back(other_lit);
                    }
                }
            }

            // Set the remaining watchlist back
            self.watch.set(&false_lit, keep_watchlist);

            if let Some(c) = conflict {
                return Some(c as usize);
            }
        }

        None
    }

    pub fn contains_empty_clause(&self, assignment: &Assignment) -> bool {
        self.clauses
            .iter()
            .any(|clause| clause.is_empty(assignment))
    }

    pub fn get_empty_clause(&self, assignment: &Assignment) -> Option<(usize, &Clause)> {
        self.clauses
            .iter()
            .enumerate()
            .filter(|(_idx, clause)| clause.is_empty(assignment))
            .next()
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
        let mut candidates: Vec<(usize, i64, usize)> = Vec::new();
        let conservative = signal.is_some();

        for (idx, clause) in self.clauses.iter().enumerate().rev() {
            if let Some((py, steps)) = signal.as_mut() {
                signal_checker(*py, *steps)?;
            }

            match clause.lbd {
                -1 => break,
                0 => continue,
                _ if clause.lock_count > 0 => continue,
                _ if conservative && clause.len() <= 2 => continue,
                _ if conservative && clause.lbd <= 2 && clause.len() <= 8 => continue,
                lbd => candidates.push((idx, lbd, clause.len())),
            }
        }

        if conservative && candidates.len() < 1_000 {
            return Ok(());
        }

        let delete_count = if conservative {
            candidates.len() / 4
        } else {
            candidates.len() / 2
        };
        if delete_count == 0 {
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

        for &idx in &to_delete {
            if let Some((py, steps)) = signal.as_mut() {
                signal_checker(*py, *steps)?;
            }
            self.stats.remove_clause(&self.clauses[idx]);
        }

        let old_to_new = self.delete_clauses::<W>(&to_delete, logger);
        history.remap_clause_indices(&old_to_new);

        Ok(())
    }

    pub fn get_model(&self) -> Vec<bool> {
        self.assignment.to_model()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::two_watched::Watched;
    use std::io::Empty;

    fn assert_watchlists_consistent(formula: &Formula) {
        let total_lists = formula.assignment.len() * 2;
        let mut expected: Vec<Vec<usize>> = vec![Vec::new(); total_lists];

        for (clause_idx, clause) in formula.get_clauses().iter().enumerate() {
            match clause.watched {
                Watched::None => {}
                Watched::One(i) => {
                    let lit = &clause.get_literals()[i as usize];
                    expected[lit.get_unsigned_index() as usize].push(clause_idx);
                }
                Watched::Two(i, j) => {
                    let lit_i = &clause.get_literals()[i as usize];
                    let lit_j = &clause.get_literals()[j as usize];
                    expected[lit_i.get_unsigned_index() as usize].push(clause_idx);
                    expected[lit_j.get_unsigned_index() as usize].push(clause_idx);
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
    fn from_vec_initial_clauses_have_unknown_lbd() {
        let formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3], vec![2]]);

        assert!(formula.get_clauses().iter().all(|clause| clause.lbd == -1));
    }

    fn test_clause(lit: i32, lbd: i64) -> Clause {
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
            .iter()
            .map(|clause| clause.get_literals()[0].get_index())
            .collect();
        let remaining_lbds: Vec<i64> = formula
            .get_clauses()
            .iter()
            .map(|clause| clause.lbd)
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
            .iter()
            .map(|clause| clause.get_literals()[0].get_index())
            .collect();

        assert!(!remaining_lits.contains(&3));
        assert!(remaining_lits.contains(&6));
        assert_eq!(history.decision_levels[1].get_reason(&locked_lit), Some(5));
        assert_eq!(formula.stats.clauses_deleted, 3);
        assert_eq!(formula.get_clause_at_idx(5).lock_count, 1);
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn reduce_db_stops_at_original_clause_boundary() {
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
            .iter()
            .map(|clause| clause.get_literals()[0].get_index())
            .collect();

        assert!(remaining_lits.contains(&2));
        assert!(remaining_lits.contains(&3));
        assert!(!remaining_lits.contains(&4));
        assert_watchlists_consistent(&formula);
    }

    #[test]
    fn delete_clause_removes_watched_literals_and_reindexes() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 2],      // clause 0: watches x1, x2
            vec![-1, 3],     // clause 1: watches ¬x1, x3
            vec![2],         // clause 2: watches x2
            vec![-2, -3, 1], // clause 3: watches ¬x2, ¬x3
        ]);

        assert_watchlists_consistent(&formula);
        // Remove clause 1
        formula.delete_clause::<Empty>(1, &mut None);

        assert_eq!(formula.get_clauses().len(), 3);
        assert_eq!(
            formula.get_clause_at_idx(1).get_literals(),
            &vec![Literal::new(2)]
        );

        // Global consistency check (ensures reindexing of watchlists)
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
