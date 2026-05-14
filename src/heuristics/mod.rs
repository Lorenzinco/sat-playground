pub mod vsids;
pub mod random;

use crate::formula::literal::Literal;
use crate::formula::Formula;
use pyo3::prelude::*;

#[derive(Clone)]
pub enum Heuristics {
    VSIDS(vsids::Vsids),
    Random,
    None
}

impl FromPyObject<'_,'_> for Heuristics {
    type Error = PyErr;
    
    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let heuristics = obj.extract::<String>()?;
        match heuristics.as_str() {
            "vsids" => Ok(Heuristics::VSIDS(vsids::Vsids::empty())),
            "random" => Ok(Heuristics::Random),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!("Unknown heuristics for cdcl solver {}, allowed values are: vsids", heuristics))),
        }
    }
}

impl Heuristics {
    pub fn bump(&mut self, literals: &Vec<Literal>){
        match self {
            Heuristics::VSIDS(vsids) => {
                for literal in literals { vsids.bump(literal)}
            },
            _ => {}
        }
    }

    pub fn decay(&mut self) {
        match self {
            Heuristics::VSIDS(vsids) => {
                vsids.decay_all();
            },
            _ => {}
        }
    }

    
    pub fn get_decision_literal(&mut self, formula: &mut Formula) -> Option<Literal> {
        match self {
            Heuristics::VSIDS(vsids) => vsids.get_best_unassigned(formula),
            Heuristics::Random => random::get_random_unassigned_literal(formula),
            _ => formula.get_unassigned_literal(),
        }
    }
}