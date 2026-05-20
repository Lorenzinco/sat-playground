use crate::formula::literal::Literal;
use std::mem::take;

#[derive(Clone, Copy)]
pub enum Watched {
    None,
    One(usize),
    Two(usize, usize),
}

#[derive(Clone)]
pub struct Watch {
    watchlist: Vec<Vec<usize>>,
}

impl Watch {
    pub fn new(n_lits: usize) -> Self {
        let mut watchlist: Vec<Vec<usize>> = Vec::new();
        for _i in 0..n_lits {
            watchlist.push(Vec::new());
            watchlist.push(Vec::new());
        }

        Self {
            watchlist: watchlist,
        }
    }

    /// Returns the clauses watched by the literal with index
    pub fn get_watched(&self, lit: &Literal) -> &Vec<usize> {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get(idx)
            .expect(format!("watchlist for this literal is unitialized. {:?}",idx).as_str())
    }

    /// Pushes the clause index inside the watchlist of the given lit
    pub fn add_to_watchlist(&mut self, clause_idx: usize, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get_mut(idx)
            .expect(format!("watchlist for this literal is unitialized. {:?}",idx).as_str())
            .push(clause_idx)
    }

    /// Creates space for a new literal inside the watchlist
    pub fn add_literal(&mut self) {
        self.watchlist.push(Vec::new());
        self.watchlist.push(Vec::new());
    }

    /// Removes the clause index from the watchlist of the given lit if present
    pub fn remove_from_watchlist(&mut self, clause_idx: usize, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get_mut(idx)
            .expect(format!("watchlist for this literal is unitialized. {:?}",idx).as_str())
            .retain(|&idx| idx != clause_idx);
    }

    pub fn take(&mut self, lit: &Literal) -> Vec<usize> {
        let idx = lit.get_unsigned_index() as usize;
        take(
            self.watchlist
                .get_mut(idx)
                .expect(format!("watchlist for this literal is unitialized. {:?}",idx).as_str()),
        )
    }

    pub fn set(&mut self, lit: &Literal, new_list: Vec<usize>) {
        let idx = lit.get_unsigned_index() as usize;
        *self
            .watchlist
            .get_mut(idx)
            .expect(format!("watchlist for this literal is unitialized. {:?}",idx).as_str()) = new_list;
    }

    /// Shifts all the clause indexes by one (backwards) from a clause index onwards, this is done after clause deletition
    pub fn shift_by_one_from_index(&mut self, clause_index: usize) {
        let deleted = clause_index;

        for lit_watchlist in self.watchlist.iter_mut() {
            lit_watchlist.retain_mut(|idx| {
                if *idx == deleted {
                    false
                } else {
                    if *idx > deleted {
                        *idx -= 1;
                    }
                    true
                }
            });
        }
    }
}
