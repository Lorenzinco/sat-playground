pub mod bva;
pub mod bve;
pub mod ges;

pub mod ges_par;

pub mod preference;
pub mod subsumption;
pub mod vivification;

use crate::formula::clause::Clause;
use pyo3::prelude::*;
use std::collections::HashSet;
use std::ops::Range;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Process {
    BVA,
    BVE,
    GES,
    GESAlways,
    GESLBD,
    GESPar,
    GESRandom,
    GESUtility,
    GESVSIDS,
    GESCompress,
    GESTrail,
    Preference,
    Subsumption,
    Vivification,
    Others,
}

pub type Preprocess = Process;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProcessPhase {
    Preprocessing,
    Inprocessing,
}

#[derive(Clone, Debug)]
pub enum ClauseScope {
    Range(Range<usize>),
    Indices(HashSet<usize>),
}

impl ClauseScope {
    pub fn range(range: Range<usize>) -> Self {
        Self::Range(range)
    }

    pub fn indices(indices: impl IntoIterator<Item = usize>) -> Self {
        Self::Indices(indices.into_iter().collect())
    }

    pub fn includes(&self, index: usize, clause: &Clause) -> bool {
        clause.lbd <= 0
            || match self {
                Self::Range(range) => range.contains(&index),
                Self::Indices(indices) => indices.contains(&index),
            }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Formula;

    fn scoped_formula() -> Formula {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4]]);
        formula.get_clause_at_idx_mut(1).lbd = 2;
        formula.get_clause_at_idx_mut(2).lbd = 4;
        formula.get_clause_at_idx_mut(3).lbd = 7;
        formula
    }

    #[test]
    fn range_and_index_scopes_always_include_permanent_clauses() {
        let formula = scoped_formula();
        let range = ClauseScope::range(2..4);
        let indices = ClauseScope::indices([3]);

        assert!(range.includes(0, formula.get_clause_at_idx(0)));
        assert!(!range.includes(1, formula.get_clause_at_idx(1)));
        assert!(range.includes(2, formula.get_clause_at_idx(2)));
        assert!(indices.includes(0, formula.get_clause_at_idx(0)));
        assert!(!indices.includes(2, formula.get_clause_at_idx(2)));
        assert!(indices.includes(3, formula.get_clause_at_idx(3)));
    }
}

impl FromPyObject<'_, '_> for Process {
    type Error = PyErr;

    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let preprocess = obj.extract::<String>()?;
        match preprocess.as_str() {
            "bva" => Ok(Process::BVA),
            "bve" => Ok(Process::BVE),
            "ges" => Ok(Process::GES),
            "ges_always" => Ok(Process::GESAlways),
            "ges_lbd" => Ok(Process::GESLBD),
            "ges_par" => Ok(Process::GESPar),
            "ges_random" => Ok(Process::GESRandom),
            "ges_utility" => Ok(Process::GESUtility),
            "ges_vsids" => Ok(Process::GESVSIDS),
            "ges_compress" => Ok(Process::GESCompress),
            "ges_trail" => Ok(Process::GESTrail),
            "preference" => Ok(Process::Preference),
            "subsumption" => Ok(Process::Subsumption),
            "vivification" | "vivify" => Ok(Process::Vivification),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                "Unknown process technique for cdcl solver {}, allowed values are: bva, bve, ges, ges_always, ges_lbd, ges_par, ges_random, ges_vsids, ges_utility, ges_compress, ges_trail, preference, subsumption, vivification, vivify",
                preprocess
            ))),
        }
    }
}
