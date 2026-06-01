pub mod bva;
pub mod bve;
pub mod subsumption;

use pyo3::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Process {
    BVA,
    BVE,
    Subsumption,
    Others,
}

pub type Preprocess = Process;

impl FromPyObject<'_, '_> for Process {
    type Error = PyErr;

    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let preprocess = obj.extract::<String>()?;
        match preprocess.as_str() {
            "bva" => Ok(Process::BVA),
            "bve" => Ok(Process::BVE),
            "subsumption" => Ok(Process::Subsumption),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                "Unknown process technique for cdcl solver {}, allowed values are: bva, bve, subsumption",
                preprocess
            ))),
        }
    }
}
