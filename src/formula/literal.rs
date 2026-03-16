use std::fmt;

use crate::formula::assignment::Assignment;

#[derive(Clone,Hash, PartialEq, Eq)]
pub struct Literal{
	variable_index: u64,
	negative: bool,
}


impl fmt::Display for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let sign = if self.negative {"¬"} else {""};
		
		write!(f,"{}x{}",sign,self.to_subscript())
	}
}

impl fmt::Debug for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let sign = if self.negative {"¬"} else {""};
		
		write!(f,"{}x{}",sign,self.to_subscript())
	}
}

impl Literal{
    
   	fn to_subscript(&self) -> String {
		let subs = ['₀','₁','₂','₃','₄','₅','₆','₇','₈','₉'];
		
		self.get_index().to_string()
			.chars()
			.map(|c| subs[c.to_digit(10).unwrap() as usize])
			.collect()
	}
    
	pub fn eval(&self, assignment: &Assignment)->Option<bool>{
	    if let Some(value) = assignment.get_value(self.get_index()){
			return Some(self.is_negated() ^ value)
		}
	    
		None
	}
	
	pub fn new(variable_index: u64, negative: bool)->Self{
		Self {
			variable_index: variable_index,
			negative: negative
		}
	}
	
	pub fn negated(&self)->Self{
        Self {
            variable_index: self.get_index(),
            negative: !self.negative
        }
    }

	
	pub fn get_index(&self)->u64{
	    self.variable_index
	}
	
	pub fn is_negated(&self)->bool{
        self.negative
    }
}