use std::collections::HashMap;
use crate::formula::literal::Literal;

#[derive(Clone)]
pub struct ExtensionMap {
    map: HashMap<(u64,u64),u64>
}

impl ExtensionMap {
    pub fn new()->Self{
        Self {
            map: HashMap::new()
        }
    }
    
    pub fn substitute(&self, lit1: &Literal, lit2: &Literal)->Option<Literal>{
        let idx1 = lit1.get_signed_index();
        let idx2 = lit2.get_signed_index();
        let index = if idx1 > idx2 {self.map.get(&(idx1,idx2))} else {self.map.get(&(idx2,idx1))};
        match index {
            Some(&idx)=>{
                Some(Literal::from_real_index(idx))
            }
            _=>{ None }
        }
    }
    
    pub fn add_substitution(&mut self, lit1: &Literal, lit2: &Literal, substitute: &Literal){
        let idx1 = lit1.get_signed_index();
        let idx2 = lit2.get_signed_index();
        if idx1 > idx2 {self.map.insert((idx1,idx2), substitute.get_signed_index());} else {self.map.insert((idx2,idx1), substitute.get_signed_index());}
    }
}