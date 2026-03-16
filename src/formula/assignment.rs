use fastbit::BitRead;
use fastbit::BitVec;
use fastbit::BitWrite;

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
    
    pub fn assign(&mut self, index: u64, value: bool){
        self.assigned.set(index as usize);
        if value {
            self.value.set(index as usize);
        }
        else {
            self.value.reset(index as usize);
        }
    }
    
    pub fn assign_history(&mut self, literal: &Literal, history: &mut History) {
        self.assign(literal.get_index(), !literal.is_negated());
        history.add_decision(literal);
    }
    
    pub fn unset(&mut self, index: u64){
        self.assigned.reset(index as usize);
    }
    
    fn is_already_assigned(&self, index: u64)->bool{
        self.assigned.test(index as usize)
    }
    
    pub fn to_model(&self)->Vec<bool> {
        let mut result = Vec::new();
        for i in 0..self.value.len(){
            result.push(self.value.test(i));
        }
        
        result
    }
    
    pub fn get_value(&self, index: u64)->Option<bool>{
        if self.is_already_assigned(index){
            return Some(self.value.test(index as usize))
        }
        
        None
    }
}