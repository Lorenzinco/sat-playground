use fastbit::BitWrite;
use fastbit::BitRead;
use fastbit::BitVec;

use crate::formula::literal::Literal;
use crate::history::History;

pub struct Assignment {
    assigned: BitVec<u64>,
    value: BitVec<u64>,
}

impl Clone for Assignment {
    fn clone(&self)->Self {
        let mut assignment = BitVec::new(self.assigned.len());
        let mut values = BitVec::new(self.value.len());
        
        for i in 0..self.value.len() {
            if self.assigned.test(i){assignment.set(i)}
            if self.value.test(i){values.set(i)}
        }
        
        Self {
            assigned: assignment,
            value: values
        }
    }
}

impl Assignment {
    pub fn new(length: usize)->Self{
        Self {
            assigned: BitVec::new(length),
            value: BitVec::new(length)
        }
    }
    
    pub fn len(&self)->usize{
        self.assigned.len()
    }
    
    pub fn assign(&mut self, index: usize, value: bool){
        self.assigned.set(index);
        if value {
            self.value.set(index);
        }
        else {
            self.value.reset(index);
        }
    }
    
    pub fn assign_history(&mut self, literal: &Literal, history: &mut History) {
        self.assign(literal.get_index().abs() as usize, !literal.is_negated());
        history.add_decision(literal);
    }
    
    pub fn unset(&mut self, index: usize){
        self.assigned.reset(index);
    }
    
    fn is_already_assigned(&self, index: usize)->bool{
        self.assigned.test(index)
    }
    
    pub fn to_model(&self)->Vec<bool> {
        let mut result = Vec::new();
        for i in 0..self.value.len(){
            result.push(self.value.test(i));
        }
        
        result
    }
    
    pub fn get_value(&self, index: usize)->Option<bool>{
        if self.is_already_assigned(index){
            return Some(self.value.test(index))
        }
        
        None
    }
    
    /// Adds a variable to the assignment returning the index to be put inside the literal, thus len-1
    pub fn add_variable(&mut self)->usize{
        let idx = self.value.len();
        self.value.resize(idx+1);
        self.assigned.resize(idx+1);
        
        idx
    }
}