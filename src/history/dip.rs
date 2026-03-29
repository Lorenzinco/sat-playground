use crate::formula::clause::Clause;
use crate::formula::Formula;
use crate::history::History;

pub fn find_dip(_history: &History, _formula: &Formula, _conflict_clause_index: usize) -> (Clause, usize) {
    unimplemented!("DIP extended resolution is not yet implemented")
}
