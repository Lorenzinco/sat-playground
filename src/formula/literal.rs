use std::fmt;
use std::hash;
use std::rc::Rc;
use std::cell::RefCell;
use crate::formula::variable::Variable;

#[derive(Clone)]
pub struct Literal{
	variable: Rc<RefCell<Variable>>,
	negative: bool,
}

impl hash::Hash for Literal {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.variable.borrow().get_index().hash(state);
        self.negative.hash(state);
    }    
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.variable.borrow().get_index() == other.variable.borrow().get_index() &&
        self.negative == other.negative
    }
}

impl Eq for Literal {}

impl fmt::Display for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let sign = if self.negative {"¬"} else {""};
		
		write!(f,"{}{}",sign,self.variable.borrow())
	}
}

impl fmt::Debug for Literal{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let color = match self.eval(){
		    Some(true) => "\x1b[34m",
            Some(false) => "\x1b[31m",
            None => "\x1b[2m",
		};
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
	
	pub fn negated(&self)->Self{
        Self {
            variable: self.variable.clone(),
            negative: !self.negative
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
	
	/// Returns a clone of the variable reference contained in the literal, the variable itself is not cloned so the reference count is increased by one.
	pub fn get_variable(&self)->Rc<RefCell<Variable>>{
        self.variable.clone()
    }
	
	pub fn assign(&mut self,value: bool){
		let mut variable = self.variable.borrow_mut();
		
		variable.assign(value);
	}
	
	/// Removes the assignment of the variable contained in the literal, if it is already assigned, nothing happens otherwise, use already_assigned() to check
    pub fn unset(&mut self){
        let mut variable = self.variable.borrow_mut();
        
        variable.unset();
    }
	
	pub fn is_negated(&self)->bool{
        self.negative
    }
    
	
	pub fn already_assigned(&self)->bool{
		let variable = self.variable.borrow();
		
		variable.already_assigned()
	}
}