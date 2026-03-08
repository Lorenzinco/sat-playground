pub mod clause;
pub mod literal;
pub mod variable;


use crate::dimacs::parse_dimacs;
use clause::Clause;
use variable::Variable;
use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;

#[derive(Clone)]
pub struct Formula{
	clauses: Vec<Clause>,
	variables: Vec<Rc<RefCell<Variable>>>
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
	
	pub fn get_clauses(&self)->&Vec<Clause>{
		&self.clauses
	}
	
	pub fn add_clause(&mut self, clause: Clause) {
		self.clauses.push(clause);
	}
	
	pub fn set_variable(&mut self, index: u64, value: bool)->Result<(),&str>{
		let variable = self.variables.get_mut(index as usize).unwrap();
		Ok(variable.borrow_mut().assign(value))
	}
	
	/// Creates a new formula starting from a dimacs string <dimacs>.
	/// # Example:
	/// ```
	/// use sat_playground::formula::Formula;
	/// 
	/// let dimacs = "c Dimacs formatted string
	/// p cnf 2 2
	/// 1 -2 0
	/// -1 2 0";
	/// let phi = Formula::from_dimacs(dimacs);
	/// ```
	pub fn from_dimacs(dimacs: &str)->Result<Self,String>{
		
		parse_dimacs(dimacs)
	}
}