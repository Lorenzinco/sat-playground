use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;
use crate::formula::variable::Variable;

#[derive(Clone)]
pub struct Literal{
	variable: Rc<RefCell<Variable>>,
	negative: bool,
}

impl fmt::Display for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let sign = if self.negative {"¬"} else {""};
		
		write!(f,"{}{}",sign,self.variable.borrow())
	}
}

impl fmt::Debug for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let color: &str;
		match self.eval(){
			Some(value)=>{
				color = if value{"\x1b[34m"} else {"\x1b[31m"};
			}
			None=>{
				color = "\x1b[31m";
			}
		}
		let reset = "\x1b[0m";
		let sign = if self.negative {"¬"} else {""};
		
		write!(f,"{}{}{:?}{}",color,sign,self.variable.borrow(),reset)
	}
}

impl Literal{
	pub fn new(variable: Rc<RefCell<Variable>>, negative: bool)->Self{
		Self {
			variable: variable,
			negative: negative
		}
	}
	
	pub fn eval(&self)->Option<bool>{
		let variable = self.variable.borrow();
		if let Some(value) = variable.get_value() {
			return Some(self.negative ^ value)
		}
		
		None
	}
	
	pub fn get_index(&self)->u64{
		let variable = self.variable.borrow();
		
		variable.get_index()
	}
	
	pub fn assign(&mut self,value: bool){
		let mut variable = self.variable.borrow_mut();
		
		variable.assign(value);
	}
	
	pub fn is_negated(&self)->bool{
        self.negative
    }
	
	pub fn already_assigned(&self)->bool{
		let variable = self.variable.borrow();
		
		variable.already_assigned()
	}
}