pub mod random;
pub mod vsids;

use crate::formula::Formula;
use crate::formula::literal::Literal;
use pyo3::prelude::*;

#[derive(Clone)]
pub enum Heuristics {
    VSIDS,
    Random,
    None,
}

impl FromPyObject<'_, '_> for Heuristics {
    type Error = PyErr;

    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let heuristics = obj.extract::<String>()?;
        match heuristics.as_str() {
            "vsids" => Ok(Heuristics::VSIDS),
            "random" => Ok(Heuristics::Random),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                "Unknown heuristics for cdcl solver {}, allowed values are: vsids",
                heuristics
            ))),
        }
    }
}

impl Heuristics {
    pub fn bump(&self, formula: &mut Formula, literals: &[Literal]) {
        if matches!(self, Heuristics::VSIDS) {
            for literal in literals {
                formula.vsids.bump(literal);
            }
        }
    }

    pub fn decay(&self, formula: &mut Formula) {
        if matches!(self, Heuristics::VSIDS) {
            formula.vsids.decay_all();
        }
    }

    pub fn get_decision_literal(&self, formula: &mut Formula) -> Option<Literal> {
        match self {
            Heuristics::VSIDS => formula.vsids.get_best_unassigned(formula),
            Heuristics::Random => random::get_random_unassigned_literal(formula),
            Heuristics::None => formula.get_unassigned_literal(),
        }
    }
}
