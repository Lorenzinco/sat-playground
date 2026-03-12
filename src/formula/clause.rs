use std::collections::hash_map::Entry;
use super::literal::Literal;
use std::collections::HashMap;
use std::fmt;


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
	
	/// Returns a reference to the literals of this clause, if there are no literals returns None.
	pub fn get_literals(&self)->Option<Vec<Literal>>{
        if self.literals.len() == 0 {
            return None
        }
        Some(self.literals.values().cloned().collect())
    }
    
    /// Returns a vector of the unassigned literals of this clause, if there are no unassigned literals returns an empty vector.
    pub fn get_unassigned_literals(&self)->Vec<Literal>{
        
        
        self.literals.values().filter(|lit| !lit.already_assigned()).cloned().collect()
    }

	///  Removes from this clause all of the literals which value has already been assigned, this method in-place modifies this clause.
	pub fn simplify(&mut self){
		self.literals.retain(|_,lit|!lit.already_assigned());
	}
	
	/// Returns true if this clause contains a literal with index <index>, false otherwise.
	pub fn contains_literal(&self, index: u64)->bool{
        self.literals.contains_key(&index)
    }
    
    /// Returns true if this clause is satisfied, false otherwise. A clause is satisfied if at least one of its literals resolves to true.
    pub fn is_satisfied(&self)->bool{
        self.literals.values().any(|lit| lit.eval() == Some(true))
    }
    
    /// Returns true if this clause is a unit clause, false otherwise. A unit clause is a clause that contains exactly one unassigned literal.
    pub fn is_unit(&self)->bool{
        return self.get_unassigned_literals().len() == 1 && !self.is_satisfied()
    }
    
    pub fn negate(&self)->Self{
        let negated_literals = self.literals.values().map(|lit| lit.negated()).collect();
        Self::from_literals(negated_literals)
    }
    
    pub fn get_unit_literal(&self)->Option<Literal>{
        if self.is_unit() {
            return self.get_unassigned_literals().pop()
        }
        None
    }
    
    /// Returns true is this clause is empty, the clause is empty where it is not satisfied and contains no unassigned literals, false otherwise.
    pub fn is_empty(&self)->bool{
        self.literals.values().all(|lit| lit.already_assigned() && lit.eval() == Some(false))
    }
    
    /// Unit propagates this clause, this method in-place modifies this clause and returns the literal that was propagated, if this clause is not a unit clause this method panics.
    pub fn unit_propagate(&mut self)->Option<Literal>{
        if !self.is_unit() {
            return None
        }
        
        if let Some(lit) = self.get_unit_literal(){
            self.set_value(lit.get_index(), !lit.is_negated()).unwrap();
            
            return Some(lit)
        }
        
        None
    }
    
    pub fn unit_propagate_with_graph(&mut self, ig: &mut crate::implication_graph::ImplicationGraph)->Option<Literal>{
        if !self.is_unit() {
            return None  
        }
        
        if let Some(implied) = self.get_unit_literal(){
            let mut impliant = Vec::new();
            for other_lit in self.get_literals().unwrap_or_else(|| Vec::new()){
                if other_lit.get_index() != implied.get_index() {
                    impliant.push(other_lit);
                }
            }
            
            self.set_value(implied.get_index(), !implied.is_negated()).unwrap();
            ig.add_neighbours(implied.clone(), ig.classify_literals(impliant));
            
            return Some(implied)
        }
        
        None
    }
}