pub mod dpll;
pub mod cdcl;

use crate::formula::Formula;
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

pub fn solve<'py>(formula: &mut Formula, algorithm: Algorithm,implication_point: ImplicationPoint) -> PyResult<Option<Vec<bool>>> {
    formula.stats.start();
    let result = match algorithm {
        Algorithm::DPLL => dpll::solve_dpll(formula),
        Algorithm::CDCL => cdcl::solve_cdcl(formula,implication_point)
    };
    formula.stats.stop();
    
    result
}