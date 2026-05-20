use std::fmt;

use crate::formula::assignment::Assignment;

#[derive(Clone,Hash, PartialEq, Eq)]
pub struct Literal{
	literal: i32,
}


impl fmt::Display for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let sign = if self.literal.is_negative() {"¬"} else {""};
		
		write!(f,"{}x{}",sign,self.to_subscript())
	}
}

impl fmt::Debug for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let sign = if self.literal.is_negative() {"¬"} else {""};
		
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
	    if let Some(value) = assignment.get_value(self.get_index().abs() as usize){
			return Some(self.is_negated() ^ value)
		}
	    
		None
	}
	
	pub fn new(literal: i32)->Self{
	    if literal == 0 {panic!("literal index is 0 but literal index is sign sensitive now!")}
		Self {
		literal: literal
		}
	}
	
	pub fn negated(&self)->Self{
	    Self { literal: -self.get_index() }
    }
    
    pub fn from_unsigned_index(unsigned_index: u32) -> Literal {
        if unsigned_index == 0 {
            panic!("unsigned index 0 would map to literal 0");
        }
    
        let idx = ((unsigned_index + 1) / 2) as i32;
    
        if unsigned_index.is_multiple_of(2) {
            Literal::new(-idx)
        } else {
            Literal::new(idx)
        }
    }
    
    pub fn get_unsigned_index(&self) -> u32 {
        let idx = self.literal.abs() as u32;
    
        if self.is_negated() {
            idx * 2
        } else {
            idx * 2 - 1
        }
    }
	
	pub fn get_index(&self)->i32{
	    self.literal
	}
	
	pub fn is_negated(&self)->bool{
        self.literal.is_negative()
    }
}