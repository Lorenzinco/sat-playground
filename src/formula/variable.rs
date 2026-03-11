use std::fmt;

#[derive(Clone)]
pub struct Variable{
	index: u64,
	value: Option<bool>
}
	

impl fmt::Display for Variable{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		write!(f,"x{}",self.to_subscript())
	}
}

impl fmt::Debug for Variable{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		write!(f,"x{}",self.to_subscript())
	}
}

impl Variable{
	/// Creates a new variable with a given index meaning the variable is x_<index>, 
	/// with value <value> = {true,false,None} (put None if not yet assigned) 
	pub fn new(index: u64, value: Option<bool>)->Self{
	
		Self {
			index: index,
			value: value,
		}
	}
	
	fn to_subscript(&self) -> String {
		let subs = ['₀','₁','₂','₃','₄','₅','₆','₇','₈','₉'];
		
		self.get_index().to_string()
			.chars()
			.map(|c| subs[c.to_digit(10).unwrap() as usize])
			.collect()
	}
	
	/// Assigns the value to the variable, nothing happens if it is already assigned, use already_assigned() to check
	pub fn assign(&mut self, value: bool){
		self.value = Some(value);
	}
	
	pub fn get_value(&self)->Option<bool> {
		self.value
	}
	
	pub fn already_assigned(&self)->bool{
	    if self.value.is_some() {
            return true;
        }
        
        false
	}
	
	pub fn get_index(&self)->u64{
		self.index
	}
}