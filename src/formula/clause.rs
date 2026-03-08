use super::literal::Literal;
use std::fmt;
use std::collections::HashMap;
use std::collections::hash_map::Entry;

#[derive(Clone)]
pub struct Clause{
	pub literals: HashMap<u64,Literal>
}

impl fmt::Display for Clause{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let len = self.literals.len();
		write!(f,"(")?;
		for (i,lit) in self.literals.values().enumerate(){
			let trailing = if i < len-1 {"∨"} else {""};
			write!(f,"{}{}",lit,trailing)?;
		}
		write!(f,")")
	}
}

impl fmt::Debug for Clause{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let len = self.literals.len();
		write!(f,"(")?;
		for (i,lit) in self.literals.values().enumerate(){
			let trailing = if i < len-1 {","} else {""};
			write!(f,"{:?}{}",lit,trailing)?;
		}
		write!(f,")")
	}
}

impl Clause {
	pub fn new()->Self{
		Self{
			literals: HashMap::new()
		}
	}
	
	pub fn from_literals(literals: Vec<Literal>)->Self{
		let mut map = HashMap::new();
		for lit in literals{
			map.insert(lit.get_index(),lit);
		}
		Self{
			literals: map
		}
	}
	
 	/// Assigns <value> to x_<index> if present and not already assigned, otherwhise returns an error
 	/// To set the value regardless of already assigned values please use pub fn set_value(index: u64, value: bool).
	pub fn assign(&mut self, index: u64, value: bool)->Result<(),&str>{

		match self.literals.entry(index) {
			Entry::Occupied (mut entry) => {
				let lit = entry.get_mut();
				if lit.already_assigned(){
					return Err("Already assigned")
				}
				lit.assign(value);
				return Ok(());
			}
			Entry::Vacant(_)=>{
				return Err("Literal not found")
			}
		}
	}
	

	/// Sets the value <value> to literal x_<index> if present, otherwhise returns an error.
	pub fn set_value(&mut self, index: u64, value: bool)->Result<(),&str>{
		match self.literals.entry(index) {
			Entry::Occupied (mut entry) => {
				entry.get_mut().assign(value);
				return Ok(())
			}
			Entry::Vacant(_)=>{
				return Err("Literal not found")
			}
		}
	}
	
	/// Adds a literal to the clause, returns an Error if the literal is already present inside the clause
	pub fn add_literal(&mut self, literal: Literal)->Result<(),&str>{
		let index = literal.get_index();
		match self.literals.entry(index) {
			Entry::Occupied (_) => {
				return Err("Literal already in clause")
			}
			Entry::Vacant(_)=>{
				self.literals.insert(index, literal);
				return Ok(())
			}
		}
	}

	///  Removes from this clause all of the literals which value has already been assigned, this method in-place modifies this clause.
	pub fn simplify(&mut self){

		self.literals.retain(|_,lit|!lit.already_assigned());
	}
	
}