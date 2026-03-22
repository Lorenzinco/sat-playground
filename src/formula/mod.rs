pub mod clause;
pub mod literal;
pub mod assignment;

use std::collections::HashMap;
use crate::history::History;
use crate::solver::Algorithm;
use crate::solver::solve;
use clause::Clause;
use literal::Literal;
use assignment::Assignment;

use pyo3::prelude::*;
use std::fmt;


    pub struct Formula{
        clauses: Vec<Clause>,
        pub assignment: Assignment,
    }

impl Clone for Formula {
    fn clone(&self) -> Self {
        let new_assignment = self.assignment.clone();
        
        let mut new_clauses = Vec::new();
        for clause in &self.clauses {
            let new_clause = clause.clone();
            new_clauses.push(new_clause);
        }
        
        Formula {
            clauses: new_clauses,
            assignment: new_assignment,
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
            assignment: Assignment::new(size)
        }
    }
    
    pub fn from_clauses(clauses: &Vec<Clause>)->Self{
        let max_index = clauses
            .iter()
            .flat_map(|clause| clause.iter())
            .map(|lit| lit.get_index())
            .max()
            .expect("No literal in any formula found!");
        
        Self {
            clauses: clauses.to_owned(),
            assignment: Assignment::new(max_index as usize +1)
        }
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
    
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }
    
    pub fn set_variable(&mut self, index: u64, value: bool){
        self.assignment.assign(index, value)
    }
    
    pub fn unset_variable(&mut self, index: u64){
        self.assignment.unset(index);
    }
    
    pub fn solve<'py>(&mut self, algorithm: Algorithm) -> PyResult<Option<Vec<bool>>> {
        solve(self, algorithm)
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

    
    pub fn contains_empty_clause(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().any(|clause| clause.is_empty(assignment))
    }
    
    pub fn get_empty_clause(&self, assignment: &Assignment)-> Option<(usize,&Clause)> {
        self.clauses.iter().enumerate().filter(|(_idx,clause)| clause.is_empty(assignment)).next()
    }
    
    pub fn get_unassigned_literal(&self, assignment: &Assignment) -> Option<Literal> {
        for clause in self.clauses.iter() {
            let literals = clause.get_unassigned_literals(assignment);
            if literals.len() > 0 {
                return Some(literals[0].clone());
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