pub mod bve;
pub mod bva;

use pyo3::prelude::*;

pub enum Preprocess {
    BVA,
    BVE,
    Others,
}

impl FromPyObject<'_,'_> for Preprocess {
    type Error = PyErr;
    
    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let preprocess = obj.extract::<String>()?;
        match preprocess.as_str() {
            "bva" => Ok(Preprocess::BVA),
            "bve" => Ok(Preprocess::BVE),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!("Unknown preprocess technique for cdcl solver {}, allowed values are: bva, bve", preprocess))),
        }
    }
}