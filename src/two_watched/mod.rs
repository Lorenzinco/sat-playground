use crate::formula::literal::Literal;
use std::mem::take;

#[derive(Clone,Copy)]
pub enum Watched {
    None,
    One(u64),
    Two(u64,u64)
}

#[derive(Clone)]
pub struct Watch {
    watchlist: Vec<Vec<u64>> 
}

impl Watch {
    pub fn new(n_lits: u64)->Self{
        let mut watchlist:Vec<Vec<u64>> = Vec::new();
        for _i in 0..n_lits{
            watchlist.push(Vec::new());
            watchlist.push(Vec::new());
        }
        
        Self{
            watchlist: watchlist
        }
    }
    
    /// Returns the clauses watched by the literal with index
    pub fn get_watched(&self, lit: &Literal)->&Vec<u64>{
        let idx = lit.get_signed_index() as usize;
        
        self.watchlist.get(idx).expect("watchlist for this literal is unitialized")
    }
    
    /// Pushes the clause index inside the watchlist of the given lit
    pub fn add_to_watchlist(&mut self, clause_idx: usize, lit: &Literal){
        let idx = lit.get_signed_index() as usize;
        
        self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized").push(clause_idx as u64)
    }
    
    
    /// Creates space for a new literal inside the watchlist
    pub fn add_literal(&mut self){
        self.watchlist.push(Vec::new());
        self.watchlist.push(Vec::new());
    }
    
    /// Removes the clause index from the watchlist of the given lit if present
    pub fn remove_from_watchlist(&mut self, clause_idx: usize, lit: &Literal){
        let idx = lit.get_signed_index() as usize;
        
        self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized").retain(|&idx| idx != clause_idx as u64);
    }
    
    pub fn take(&mut self, lit: &Literal)-> Vec<u64> {
        let idx = lit.get_signed_index() as usize;
        take(self.watchlist.get_mut(idx as usize).expect("Watchlist for this literal is unitialized"))
    }
    
    pub fn set(&mut self, lit: &Literal, new_list: Vec<u64>) {
        let idx = lit.get_signed_index() as usize;
        *self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized") = new_list;
    }
    
}