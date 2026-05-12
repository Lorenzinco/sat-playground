pub mod dpll;
pub mod cdcl;

use std::io::Write;

use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::heuristics::Heuristics;
use crate::history::ImplicationPoint;
use pyo3::prelude::*;
use pyo3::FromPyObject;

pub enum Algorithm {
    DPLL,
    CDCL
}

impl FromPyObject<'_,'_> for Algorithm {
    type Error = PyErr;
    
    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let algo = obj.extract::<String>()?;
        match algo.as_str() {
            "dpll" => Ok(Algorithm::DPLL),
            "cdcl" => Ok(Algorithm::CDCL),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!("Unknown algorithm: {}, allowed values are: dpll, cdcl", algo))),
        }
}
    
}

pub fn solve<'py,W: Write>(formula: &mut Formula, py: Python<'_>, algorithm: Algorithm,implication_point: ImplicationPoint, heuristics: &mut Heuristics, logger: &mut Option<DratLogger<W>>) -> PyResult<Option<Vec<bool>>> {
    formula.stats.start();
    let result = match algorithm {
        Algorithm::DPLL => dpll::solve_dpll(py,formula),
        Algorithm::CDCL => cdcl::solve_cdcl(py,formula,implication_point, heuristics, logger)
    };
    formula.stats.stop();
    
    result
}