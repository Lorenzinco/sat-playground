pub mod clause;
pub mod literal;
pub mod assignment;
pub mod extension;

use std::io::{self, Write};
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::time::Instant;
use std::collections::HashMap;
use std::collections::VecDeque;
use crate::history::History;
use crate::solver::Algorithm;
use crate::history::ImplicationPoint;
use crate::solver::solve;
use crate::two_watched::Watch;
use crate::two_watched::Watched;
use crate::formula::extension::ExtensionMap;
use crate::python::stats::Stats;
use clause::Clause;
use literal::Literal;
use assignment::Assignment;

use pyo3::prelude::*;
use std::fmt;


pub struct Formula{
    clauses: Vec<Clause>,
    pub assignment: Assignment,
    watch: Watch,
    pub stats: Stats,
    pub extensions: ExtensionMap
}

impl Clone for Formula {
    fn clone(&self) -> Self {
        let new_assignment = self.assignment.clone();
        let new_watch = self.watch.clone();
        let stats = self.stats.clone();
        let new_extensions = self.extensions.clone();
        
        let mut new_clauses = Vec::new();
        for clause in &self.clauses {
            let new_clause = clause.clone();
            new_clauses.push(new_clause);
        }
        
        Formula {
            clauses: new_clauses,
            assignment: new_assignment,
            watch: new_watch,
            stats: stats,
            extensions: new_extensions
        }
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
        let len = self.clauses.len();
        for (i,clause) in self.clauses.iter().enumerate() {
            write!(f,"(")?;
            for (j, literal) in clause.into_iter().enumerate(){
                let color = match literal.eval(&self.assignment){
                    Some(true) => "\x1b[34m",
                    Some(false) => "\x1b[31m",
                    None => "\x1b[2m",
                };
                let trailing = if j < clause.into_iter().len() - 1 {"∨"} else {""};
                let reset = "\x1b[0m";
                write!(f,"{}{:?}{}{}",color,literal,reset,trailing)?;
            } 
            let trailing = if i < len-1 {"∧"} else {""};
            write!(f,"){}",trailing)?;
        }
        
        write!(f,"")
    }
}


impl fmt::Display for Formula{
    fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
        let len = self.clauses.len();
        for (i,clause) in self.clauses.iter().enumerate() {
            let trailing = if i < len-1 {"∧"} else {""};
            write!(f,"{}{}",clause,trailing)?;
        }
        write!(f,"")
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
    pub fn new(size: usize)->Self{
        
        Formula{
            clauses: vec!(),
            assignment: Assignment::new(size),
            watch: Watch::new(size as u64),
            stats: Stats::new(),
            extensions: ExtensionMap::new()
        }
    }
    
    pub fn from_clauses(clauses: &Vec<Clause>)->Self{
        let max_index = clauses
            .iter()
            .flat_map(|clause| clause.iter())
            .map(|lit| lit.get_index())
            .max()
            .expect("No literal in any formula found!");
        
        let mut formula = Formula{
            clauses: clauses.to_owned(),
            assignment: Assignment::new(max_index as usize +1),
            watch: Watch::new(max_index +1),
            stats: Stats::new(),
            extensions: ExtensionMap::new()
        };
        
        for (i, clause) in formula.clauses.iter().enumerate() {
            match clause.watched {
                Watched::Two(idx1, idx2) => {
                    formula.watch.add_to_watchlist(i, &clause.get_literals()[idx1 as usize]);
                    formula.watch.add_to_watchlist(i, &clause.get_literals()[idx2 as usize]);
                }
                Watched::One(idx) => {
                    formula.watch.add_to_watchlist(i, &clause.get_literals()[idx as usize]);
                }
                Watched::None => {}
            }
        }
        
        formula
    }
    
    pub fn from_vec(raw_clauses: Vec<Vec<i64>>)->Self {
        let mut clauses = Vec::new();
        for raw_clause in raw_clauses.iter(){
            let mut clause = Clause::new();
            for raw_lit in raw_clause.iter(){
                if *raw_lit == 0 as i64 { panic!("0 indexing is not allowed on dimacs") }
                let lit = Literal::new((raw_lit.abs()-1) as u64,raw_lit.is_negative());
                clause.add_literal(&lit).expect("Literal cannot be in the same clause twice");
            } 
            clauses.push(clause);
        }
        
        Formula::from_clauses(&clauses)
    }
    
    /// Returns a reference to the clauses of the formula.
    pub fn get_clauses(&self)->&Vec<Clause>{
        &self.clauses
    }
    
    pub fn get_clause_at_idx(&self, index: usize)->&Clause {
        self.clauses.get(index).expect("Clause not present")
    }
    
    pub fn get_clause_at_idx_mut(&mut self, index: usize)->&mut Clause {
        self.clauses.get_mut(index).expect("Clause not present")
    }
    
    /// Returns a mutable reference to the Clause.
    pub fn get_clauses_mut(&mut self)->&mut Vec<Clause>{
        &mut self.clauses
    }
    
    /// Returns a vector of mutable references to the unsatisfied clauses of the formula, this is used to modify the clauses during the solving process.
    pub fn get_unsatisfied_clauses(&self)->Vec<(usize,&Clause)>{
        self.get_clauses().iter().enumerate().filter(|(_,clause)| !clause.is_satisfied(&self.assignment)).collect()
    }
    
    /// 
    pub fn get_unsatisfied_clauses_mut(&mut self, assignment: &Assignment)->Vec<(usize, &mut Clause)>{
        self.get_clauses_mut().into_iter().enumerate().filter(|(_, clause)| !clause.is_satisfied(&assignment)).collect()
    }
    
    pub fn get_stats(&self)->Stats{
        self.stats
    }
    
    pub fn add_clause(&mut self, clause: Clause) {
        let clause_idx = self.clauses.len();
        match clause.watched {
            Watched::None => {},
            Watched::One(idx)=> {
                self.watch.add_to_watchlist(clause_idx,&clause.get_literals()[idx as usize]);
            },
            Watched::Two(idx1,idx2)=>{
                self.watch.add_to_watchlist(clause_idx,&clause.get_literals()[idx1 as usize]);
                self.watch.add_to_watchlist(clause_idx,&clause.get_literals()[idx2 as usize]);
            }
        }
        self.clauses.push(clause);
    }
    
    pub fn add_literal(&mut self)->Literal{
        let index = self.assignment.add_variable();
        self.watch.add_literal();
        
        Literal::new(index as u64,false)
    }
    
    pub fn set_variable(&mut self, index: u64, value: bool){
        self.assignment.assign(index, value)
    }
    
    pub fn unset_variable(&mut self, index: u64){
        self.assignment.unset(index);
    }
    
    pub fn solve<'py>(&mut self, algorithm: Algorithm, implication_point: ImplicationPoint) -> PyResult<Option<Vec<bool>>> {
        let stop = Arc::new(AtomicBool::new(false));
        let stop_for_thread = Arc::clone(&stop);
        let stats_ptr = &self.stats as *const _ as usize;
    
        let timer = thread::spawn(move || {
            let start = Instant::now();
    
            while !stop_for_thread.load(Ordering::Relaxed) {
                let elapsed = start.elapsed().as_secs();
                let time_str = if elapsed >= 60 {
                    let minutes = elapsed / 60;
                    let seconds = elapsed % 60;
                    format!("{}m {}s", minutes, seconds)
                } else {
                    format!("{}s", elapsed)
                };
            
                // We cast the pointer back to read the struct properties.
                // Technically a data race for printing purposes, but entirely benign.
                let stats = unsafe { &*(stats_ptr as *const crate::python::stats::Stats) };
                
                print!("\r\x1b[2K\x1b[31mTime: {}\x1b[0m | \x1b[31mConflicts: {}\x1b[0m | \x1b[34mLearnt: {}\x1b[0m | Lits: {} | AvgLen: {:.2}", 
                       time_str, stats.conflicts, stats.clauses_learnt, stats.literals_learnt, stats.avg_clause_length);
                io::stdout().flush().ok();
            
                thread::sleep(Duration::from_secs(1));
            }
    
            print!("\r\x1b[2K");
            io::stdout().flush().ok();
        });
    
        let result = solve(self, algorithm,implication_point);
    
        stop.store(true, Ordering::Relaxed);
        let _ = timer.join();
    
        result
    }
    
    pub fn get_empty_clauses(&self) -> Option<Vec<&Clause>> {
        let empty_clauses: Vec<&Clause> = self.clauses.iter().filter(|clause| clause.is_empty(&self.assignment)).collect();
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
           let mut polarity: HashMap<u64, u8> = HashMap::new();
   
           for (_,clause) in clauses {
               for lit in clause.get_unassigned_literals(assignment) {
                   let bit = if lit.is_negated() { 0b10 } else { 0b01 };
                   polarity
                       .entry(lit.get_index())
                       .and_modify(|mask| *mask |= bit)
                       .or_insert(bit);
               }
           }
   
           let mut pure_literals = Vec::new();
   
           for (var, mask) in polarity {
               match mask {
                   0b01 => pure_literals.push(Literal::new(var,false)),
                   0b10 => pure_literals.push(Literal::new(var,true)),
                   _ => {}
               }
           }
   
           pure_literals
       }
    
    pub fn is_satisfied(&self) -> bool {
        self.clauses.iter().all(|clause| clause.is_satisfied(&self.assignment))
    }
    
    pub fn get_unit_clauses(&self)->Vec<(usize,&Clause)>{
        self.get_unsatisfied_clauses().into_iter().filter(|(_,clause)| clause.is_unit(&self.assignment)).collect()
    }
    
    pub fn get_unit_clauses_mut(&mut self, assignment: &Assignment)->Vec<(usize, &mut Clause)> {
        self.get_unsatisfied_clauses_mut(assignment).into_iter().filter(|(_,clause)| clause.is_unit(assignment)).collect()
    }
    
    /// Performs unit propagation on the formula, to also update an implication graph use unit_propagate_with_graph(ig: &mut ImplicationGraph) instead, this is used in the DPLL algorithm.
    pub fn unit_propagate(&mut self) -> bool {
        let mut progress = false;
        loop {
            let mut found = None;
            for clause in self.clauses.iter() {
                if clause.is_unit(&self.assignment) {
                    found = Some(clause.get_unit_literal(&self.assignment).unwrap().clone());
                    break;
                }
            }
            if let Some(literal) = found {
                self.assignment.assign(literal.get_index(), !literal.is_negated());
                progress = true;
            } else {
                break;
            }
        }
        progress
    }
    

    pub fn unit_propagate_history(&mut self, history: &mut History)-> bool {
            let mut progress = false;
            loop {
                let mut found = None;
                for (i, clause) in self.clauses.iter().enumerate() {
                    if clause.is_unit(&self.assignment) {
                        found = Some((i, clause.get_unit_literal(&self.assignment).unwrap().clone()));
                        break;
                    }
                }
                if let Some((i, literal)) = found {
                    self.assignment.assign(literal.get_index(), !literal.is_negated());
                    history.add_implication(&literal, Some(i));
                    progress = true;
                } else {
                    break;
                }
            }
            progress
        }

    
    pub fn pure_literals_propagate(&mut self) -> bool {
        let mut progress = false;
        loop {
            let mut assignment = self.assignment.clone();
            let pure_literals = self.get_pure_literals();
            if let Some(pure) = pure_literals.into_iter().next() {
                assignment.assign(pure.get_index(), !pure.is_negated());
                progress = true;
            }
            else {
                break;
            }
            self.assignment = assignment;
        }
        
        progress
    }
    
    
    /// Propagates updating the history, thus adding implications to the current decision layer, returns true iff there has been implications
    pub fn pure_literals_propagate_history(&mut self, history: &mut History) -> bool {
        let mut progress = false;
        loop {
            let mut assignment = self.assignment.clone();
            let pure_literals = self.get_pure_literals();
            if let Some(pure) = pure_literals.into_iter().next() {
                assignment.assign(pure.get_index(), !pure.is_negated());
                history.add_implication(&pure, None);
                progress = true;
            }
            else {
                break;
            }
            self.assignment = assignment;
        }
        
        progress
    }
    
    pub fn propagate_twl(
        &mut self, 
        history: &mut History, 
        queue: &mut VecDeque<Literal>
    ) -> Option<usize> {
        while let Some(lit) = queue.pop_front() {
            let false_lit = lit.negated();
            
            // We TAKE the list of clauses watching this literal so we can mutate the 
            // formula's clause list and watchlist while iterating, ZERO allocations!
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
                        if clause.get_literals()[i as usize] == false_lit { (i, j) } else { (j, i) }
                    },
                    Watched::One(i) => {
                        keep_watchlist.push(clause_idx);
                        if clause.get_literals()[i as usize] == false_lit {
                            conflict = Some(clause_idx);
                        }
                        continue;
                    },
                    Watched::None => {
                        keep_watchlist.push(clause_idx);
                        continue;
                    },
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
                    if k == false_idx as usize || k == other_idx as usize { continue; }
                    
                    let candidate = clause.get_literals()[k].clone();
                    if candidate.eval(&self.assignment) != Some(false) {
                        clause.watched = Watched::Two(k as u64, other_idx);
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
                        self.assignment.assign(other_lit.get_index(), !other_lit.is_negated());
                        history.add_implication(&other_lit, Some(clause_idx as usize));
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
        self.clauses.iter().any(|clause| clause.is_empty(assignment))
    }
    
    pub fn get_empty_clause(&self, assignment: &Assignment)-> Option<(usize,&Clause)> {
        self.clauses.iter().enumerate().filter(|(_idx,clause)| clause.is_empty(assignment)).next()
    }
    
    pub fn get_unassigned_literal(&self) -> Option<Literal> {
        for i in 0..self.assignment.len(){
            if self.assignment.get_value(i as u64).is_none() {
                return Some(Literal::new(i as u64,true))
            }
        }
        
        None
    }
    
    pub fn get_model(&self) -> Vec<bool> {
        self.assignment.to_model()
    }
    
    
}

#[cfg(test)]
mod tests {
}