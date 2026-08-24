use crate::formula::literal::Literal;
use std::mem::take;

/// A cached blocker must belong to the clause, but need not still be watched.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WatchEntry {
    pub clause_idx: usize,
    pub blocker: Literal,
}

#[derive(Clone)]
pub struct Watch {
    watchlist: Vec<Vec<WatchEntry>>,
    stale: Vec<usize>,
}

impl Watch {
    pub fn new(n_lits: usize) -> Self {
        let mut watchlist: Vec<Vec<WatchEntry>> = Vec::new();
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
    pub fn get_watched(&self, lit: &Literal) -> &Vec<WatchEntry> {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}"))
    }

    /// Attaches a watch. Both `lit` and `blocker` must be members of the clause.
    pub fn add_to_watchlist(&mut self, clause_idx: usize, lit: &Literal, blocker: Literal) {
        let idx = lit.get_unsigned_index() as usize;

        self.watchlist
            .get_mut(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}"))
            .push(WatchEntry {
                clause_idx,
                blocker,
            })
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
            .retain(|entry| entry.clause_idx != clause_idx);
    }

    pub fn mark_stale(&mut self, lit: &Literal) {
        let idx = lit.get_unsigned_index() as usize;
        self.stale[idx] += 1;
    }

    pub fn take_live(
        &mut self,
        lit: &Literal,
        mut is_live: impl FnMut(usize) -> bool,
    ) -> Vec<WatchEntry> {
        let idx = lit.get_unsigned_index() as usize;
        let mut entries = take(
            self.watchlist
                .get_mut(idx)
                .unwrap_or_else(|| panic!("uninitialized watchlist {idx}")),
        );
        if self.stale[idx] != 0 {
            entries.retain(|entry| is_live(entry.clause_idx));
            self.stale[idx] = 0;
        }
        entries
    }

    pub fn set(&mut self, lit: &Literal, new_list: Vec<WatchEntry>) {
        let idx = lit.get_unsigned_index() as usize;
        *self
            .watchlist
            .get_mut(idx)
            .unwrap_or_else(|| panic!("uninitialized watchlist {idx}")) = new_list;
        self.stale[idx] = 0;
    }

    pub fn retain_clause_indices(&mut self, mut keep: impl FnMut(usize) -> bool) {
        for watchlist in &mut self.watchlist {
            watchlist.retain(|entry| keep(entry.clause_idx));
        }
        self.stale.fill(0);
    }

    /// Shifts all the clause indexes by one (backwards) from a clause index onwards, this is done after clause deletition
    pub fn shift_by_one_from_index(&mut self, clause_index: usize) {
        let deleted = clause_index;

        for lit_watchlist in self.watchlist.iter_mut() {
            lit_watchlist.retain_mut(|entry| {
                if entry.clause_idx == deleted {
                    false
                } else {
                    if entry.clause_idx > deleted {
                        entry.clause_idx -= 1;
                    }
                    true
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maintenance_preserves_blockers_and_remaps_only_clause_indices() {
        let lit = Literal::new(1);
        let mut watch = Watch::new(4);
        for (idx, blocker) in [(0, -2), (1, 3), (2, -3)] {
            watch.add_to_watchlist(idx, &lit, Literal::new(blocker));
        }
        watch.mark_stale(&lit);
        let entries = watch.take_live(&lit, |idx| idx != 1);
        assert_eq!(
            entries,
            vec![
                WatchEntry {
                    clause_idx: 0,
                    blocker: Literal::new(-2)
                },
                WatchEntry {
                    clause_idx: 2,
                    blocker: Literal::new(-3)
                },
            ]
        );
        watch.set(&lit, entries.clone());
        assert_eq!(watch.clone().get_watched(&lit), &entries);
        watch.shift_by_one_from_index(0);
        assert_eq!(
            watch.get_watched(&lit),
            &vec![WatchEntry {
                clause_idx: 1,
                blocker: Literal::new(-3)
            }]
        );
        watch.add_to_watchlist(2, &lit, Literal::new(2));
        watch.retain_clause_indices(|idx| idx != 2);
        assert_eq!(watch.get_watched(&lit)[0].blocker, Literal::new(-3));
        assert_eq!(watch.get_watched(&lit).len(), 1);
        watch.remove_from_watchlist(1, &lit);
        assert!(watch.get_watched(&lit).is_empty());
        watch.add_literal();
        watch.add_to_watchlist(3, &Literal::new(-4), Literal::new(1));
        assert_eq!(
            watch.get_watched(&Literal::new(-4))[0].blocker,
            Literal::new(1)
        );
    }
}
