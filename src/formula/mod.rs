pub mod clause;
pub mod literal;
pub mod variable;

use crate::python::interrupts::InterruptChecker;
use crate::solver;
use std::cell::RefCell;
use std::rc::Rc;
use clause::Clause;
use literal::Literal;
use variable::Variable;
use pyo3::prelude::*;
use std::fmt;


pub struct Formula{
	clauses: Vec<Clause>,
	variables: Vec<Rc<RefCell<Variable>>>
}

impl Clone for Formula {
    fn clone(&self) -> Self {
        let new_variables: Vec<Rc<RefCell<Variable>>> = self.variables
            .iter()
            .map(|var_ref| {
                let var = var_ref.borrow().clone();
                Rc::new(RefCell::new(var))
            })
            .collect();
        
        let mut new_clauses = Vec::new();
        for clause in &self.clauses {
            let mut new_clause = Clause::new();
            if let Some(literals) = clause.get_literals() {
                for lit in literals {
                    let index = lit.get_index();
                    let negated = lit.is_negated();
                    let new_var_ref = new_variables[index as usize].clone();
                    let new_lit = Literal::new(new_var_ref, negated);
                    new_clause.add_literal(new_lit).ok();
                }
            }
            new_clauses.push(new_clause);
        }
        
        Formula {
            clauses: new_clauses,
            variables: new_variables,
        }
    }
}

impl fmt::Debug for Formula {
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let len = self.clauses.len();
		for (i,clause) in self.clauses.iter().enumerate() {
			let trailing = if i < len-1 {"∧"} else {""};
			write!(f,"{:?}{}",clause,trailing)?;
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
	/// use sat_playground::formula::Formula;
	/// 
	/// let phi = Formula::new();
	/// ```
	pub fn new()->Self{

		Formula{
			clauses: vec!(),
			variables: vec!()
		}
	}
	
	pub fn from_clauses(clauses: Vec<Clause>, variables: Vec<Rc<RefCell<Variable>>>)->Self{
		Self {
			clauses: clauses.to_owned(),
			variables: variables.to_owned()
		}
	}
	
	pub fn get_variables(&self)->&Vec<Rc<RefCell<Variable>>>{
		&self.variables
	}
	
	/// Returns a mutable reference to the clauses of the formula, this is used to modify the clauses during the solving process.
	pub fn get_clauses(&mut self)->&mut Vec<Clause>{
	    &mut self.clauses
	}
	
	/// Returns a vector of mutable references to the unsatisfied clauses of the formula, this is used to modify the clauses during the solving process.
	pub fn get_unsatisfied_clauses(&mut self)->Vec<&mut Clause>{
        self.get_clauses().iter_mut().filter(|clause| !clause.is_satisfied()).collect()
    }
	
	pub fn add_clause(&mut self, clause: Clause) {
		self.clauses.push(clause);
	}
	
	pub fn set_variable(&mut self, index: u64, value: bool)->Result<(),&str>{
		let rc = self.variables.get(index as usize).ok_or("Variable index out of bounds")?;
		let mut variable = rc.borrow_mut();
		Ok(variable.assign(value))
	}
	
	pub fn solve<'py>(&mut self, ic: &mut InterruptChecker<'py>) -> PyResult<Option<Vec<bool>>> {
        solver::solve(self, solver::Algorithm::DPLL, ic)
    }
    
    pub fn contains_unit_clause(&mut self) -> bool {
        self.get_unsatisfied_clauses().iter().any(|clause| clause.is_unit())
    }
    
    pub fn get_pure_literals(&mut self) -> Vec<(Rc<RefCell<Variable>>, bool)> {
        let clauses = self.get_unsatisfied_clauses();
        let mut seen: std::collections::HashMap<u64,(bool,bool)> = std::collections::HashMap::new();
        
        for clause in clauses {
            let literals = clause.get_unassigned_literals();
                for literal in literals {
                    let index = literal.get_index();
                    let negated = literal.is_negated();
                    match seen.entry(index) {
                        std::collections::hash_map::Entry::Occupied(mut entry) => {
                            let (neg,pure) = entry.get();
                            if !pure{
                                continue;
                            }
                            if negated & *neg {
                                continue;
                            }
                            if !negated & !*neg {
                                continue;
                            }
                            entry.insert((negated,false));
                        }
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            let sign = literal.is_negated();
                            entry.insert((sign,true));
                        }
                    }
                }
        }
        
        
        let mut pure_literals: Vec<(Rc<RefCell<Variable>>,bool)> = Vec::new();
        for (index,(neg,pure)) in seen {
            if pure {
                let var_ref = self.variables.get(index as usize).unwrap().clone();
                pure_literals.push((var_ref.clone(), !neg));
            }
        }
        
        pure_literals
    }
    
    pub fn is_empty(&self) -> bool {
        self.clauses.iter().all(|clause| clause.get_unassigned_literals().is_empty()) || self.clauses.len() == 0
    }
    
    pub fn unit_propagate(&mut self) {
        let clauses = self.get_unsatisfied_clauses();
        for clause in clauses {
            if clause.is_unit() {
                clause.unit_propagate();
            }
        }
    }
    
    pub fn contains_empty_clause(&self) -> bool {
        self.clauses.iter().any(|clause| clause.is_empty())
    }
    
    pub fn get_unassigned_literal(&self) -> Option<Literal> {
        for clause in self.clauses.iter() {
            let literals = clause.get_unassigned_literals();
            if literals.len() > 0 {
                return Some(literals[0].clone());
            }
        }
        None
    }
    
    pub fn get_model(&self) -> Vec<bool> {
        self.variables.iter().map(|var| var.borrow().get_value().unwrap_or(false)).collect()
    }
    
}