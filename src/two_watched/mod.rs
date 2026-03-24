use crate::formula::literal::Literal;
use std::mem::take;

#[derive(Clone,Copy)]
pub enum Watched {
    None,
    One(usize),
    Two(usize,usize)
}

#[derive(Clone)]
pub struct Watch {
    watchlist: Vec<Vec<usize>> 
}

impl Watch {
    pub fn new(n_lits: usize)->Self{
        let mut watchlist:Vec<Vec<usize>> = Vec::new();
        for _i in 0..n_lits{
            watchlist.push(Vec::new());
            watchlist.push(Vec::new());
        }
        
        Self{
            watchlist: watchlist
        }
    }
    
    /// Returns the correct index inside the watchlist for a given lit
    fn get_lits_watchlist_idx(&self, lit: &Literal)->usize{
         if lit.is_negated() {(lit.get_index() * 2 + 1) as usize} else {(lit.get_index() * 2) as usize}
    }
    
    /// Returns the clauses watched by the literal with index
    pub fn get_watched(&self, lit: &Literal)->&Vec<usize>{
        
        self.watchlist.get(self.get_lits_watchlist_idx(lit)).expect("watchlist for this literal is unitialized")
    }
    
    /// Pushes the clause index inside the watchlist of the given lit
    pub fn add_to_watchlist(&mut self, clause_idx: usize, lit: &Literal){
        let idx = self.get_lits_watchlist_idx(lit);
        
        self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized").push(clause_idx)
    }
    
    /// Removes the clause index from the watchlist of the given lit if present
    pub fn remove_from_watchlist(&mut self, clause_idx: usize, lit: &Literal){
        let idx = self.get_lits_watchlist_idx(lit);
        
        self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized").retain(|&idx| idx != clause_idx);
    }
    
    pub fn take(&mut self, lit: &Literal)-> Vec<usize> {
        let idx = self.get_lits_watchlist_idx(lit);
        take(self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized"))
    }
    
    pub fn set(&mut self, lit: &Literal, new_list: Vec<usize>) {
        let idx = self.get_lits_watchlist_idx(lit);
        *self.watchlist.get_mut(idx).expect("Watchlist for this literal is unitialized") = new_list;
    }
    
}