pub mod bva;
pub mod bve;
pub mod ges;
pub mod subsumption;

use crate::formula::Formula;
use crate::formula::clause::Clause;
use pyo3::prelude::*;
use std::collections::HashSet;
use std::ops::Range;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Process {
    BVA,
    BVE,
    GES,
    Subsumption,
    Others,
}

pub type Preprocess = Process;

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

#[derive(Clone, Copy, Debug)]
pub struct TierProbabilities {
    pub tier1: f64,
    pub tier2: f64,
    pub tier3: f64,
}

impl TierProbabilities {
    pub const fn new(tier1: f64, tier2: f64, tier3: f64) -> Self {
        Self {
            tier1,
            tier2,
            tier3,
        }
    }

    fn for_lbd(self, lbd: i16) -> f64 {
        if lbd <= 2 {
            self.tier1
        } else if lbd <= 6 {
            self.tier2
        } else {
            self.tier3
        }
    }
}

pub const DEFAULT_INPROCESSING_TIERS: TierProbabilities = TierProbabilities::new(0.5, 1.0, 0.5);

pub fn sample_tier_scope(formula: &Formula, probabilities: TierProbabilities) -> ClauseScope {
    let scope = sample_tier_scope_with(formula, probabilities, rand::random::<f64>);
    let mut total = [0usize; 3];
    let mut selected = [0usize; 3];

    for (index, clause) in formula.get_clauses() {
        if clause.lbd <= 0 {
            continue;
        }
        let tier = if clause.lbd <= 2 {
            0
        } else if clause.lbd <= 6 {
            1
        } else {
            2
        };
        total[tier] += 1;
        if scope.includes(index, clause) {
            selected[tier] += 1;
        }
    }

    println!(
        "c inprocessing clause tiers: tier1={}/{} tier2={}/{} tier3={}/{} (selected/total)",
        selected[0], total[0], selected[1], total[1], selected[2], total[2]
    );

    scope
}

fn sample_tier_scope_with(
    formula: &Formula,
    probabilities: TierProbabilities,
    mut sample: impl FnMut() -> f64,
) -> ClauseScope {
    for probability in [
        probabilities.tier1,
        probabilities.tier2,
        probabilities.tier3,
    ] {
        assert!(
            probability.is_finite() && (0.0..=1.0).contains(&probability),
            "tier probabilities must be finite values between zero and one"
        );
    }

    ClauseScope::indices(formula.get_clauses().filter_map(|(index, clause)| {
        (clause.lbd > 0 && sample() < probabilities.for_lbd(clause.lbd)).then_some(index)
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tiered_formula() -> Formula {
        let mut formula = Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4]]);
        formula.get_clause_at_idx_mut(1).lbd = 2;
        formula.get_clause_at_idx_mut(2).lbd = 4;
        formula.get_clause_at_idx_mut(3).lbd = 7;
        formula
    }

    #[test]
    fn range_and_index_scopes_always_include_permanent_clauses() {
        let formula = tiered_formula();
        let range = ClauseScope::range(2..4);
        let indices = ClauseScope::indices([3]);

        assert!(range.includes(0, formula.get_clause_at_idx(0)));
        assert!(!range.includes(1, formula.get_clause_at_idx(1)));
        assert!(range.includes(2, formula.get_clause_at_idx(2)));
        assert!(indices.includes(0, formula.get_clause_at_idx(0)));
        assert!(!indices.includes(2, formula.get_clause_at_idx(2)));
        assert!(indices.includes(3, formula.get_clause_at_idx(3)));
    }

    #[test]
    fn tier_sampling_is_per_clause_and_probabilities_are_exchangeable() {
        let formula = tiered_formula();
        let mut samples = [0.99, 0.60, 0.20].into_iter();
        let default_scope = sample_tier_scope_with(&formula, DEFAULT_INPROCESSING_TIERS, || {
            samples.next().unwrap()
        });

        assert!(default_scope.includes(0, formula.get_clause_at_idx(0)));
        assert!(default_scope.includes(1, formula.get_clause_at_idx(1)));
        assert!(!default_scope.includes(2, formula.get_clause_at_idx(2)));
        assert!(default_scope.includes(3, formula.get_clause_at_idx(3)));

        let tier3_only =
            sample_tier_scope_with(&formula, TierProbabilities::new(0.0, 0.0, 1.0), || 0.5);
        assert!(tier3_only.includes(0, formula.get_clause_at_idx(0)));
        assert!(!tier3_only.includes(1, formula.get_clause_at_idx(1)));
        assert!(!tier3_only.includes(2, formula.get_clause_at_idx(2)));
        assert!(tier3_only.includes(3, formula.get_clause_at_idx(3)));
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
            "subsumption" => Ok(Process::Subsumption),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                "Unknown process technique for cdcl solver {}, allowed values are: bva, bve, ges, subsumption",
                preprocess
            ))),
        }
    }
}
