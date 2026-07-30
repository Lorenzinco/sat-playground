use crate::formula::literal::Literal;
use std::mem::take;

#[derive(Clone)]
pub struct Watch {
    watchlist: Vec<Vec<usize>>,
    stale: Vec<usize>,
}

impl Watch {
    pub fn new(n_lits: usize) -> Self {
        let mut watchlist: Vec<Vec<usize>> = Vec::new();
        for _i in 0..n_lits {
            watchlist.push(Vec::new());
            watchlist.push(Vec::new());
        }

        Self {
            stale: vec![0; watchlist.len()],
            watchlist,
        }
    }

    /// Returns the clauses watched by the literal with index
    pub fn get_watched(&self, lit: &Literal) -> &Vec<usize> {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}"))
    }

    /// Pushes the clause index inside the watchlist of the given lit
    pub fn add_to_watchlist(&mut self, clause_idx: usize, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get_mut(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}"))
            .push(clause_idx)
    }

    /// Creates space for a new literal inside the watchlist
    pub fn add_literal(&mut self) {
        self.watchlist.push(Vec::new());
        self.watchlist.push(Vec::new());
        self.stale.push(0);
        self.stale.push(0);
    }

    /// Removes the clause index from the watchlist of the given lit if present
    pub fn remove_from_watchlist(&mut self, clause_idx: usize, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get_mut(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}"))
            .retain(|&idx| idx != clause_idx);
    }

    pub fn mark_stale(&mut self, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;
        self.stale[idx] += 1;
    }

    pub fn take_live(
        &mut self,
        lit: &Literal,
        mut is_live: impl FnMut(usize) -> bool,
    ) -> Vec<usize> {
        let idx = lit.get_unsigned_index() as usize;
        let mut entries = take(
            self.watchlist
                .get_mut(idx)
                .unwrap_or_else(|| panic!("uninitialized watchlist {idx}")),
        );
        if self.stale[idx] != 0 {
            entries.retain(|&clause_idx| is_live(clause_idx));
            self.stale[idx] = 0;
        }
        entries
    }

    pub fn set(&mut self, lit: &Literal, new_list: Vec<usize>) {
        let idx = lit.get_unsigned_index() as usize;
        *self
            .watchlist
            .get_mut(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}")) =
            new_list;
        self.stale[idx] = 0;
    }

    pub fn retain_clause_indices(&mut self, mut keep: impl FnMut(usize) -> bool) {
        for watchlist in &mut self.watchlist {
            watchlist.retain(|&clause_idx| keep(clause_idx));
        }
        self.stale.fill(0);
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
