pub mod drat;
pub mod formula;
pub mod guidance;
pub mod heuristics;
pub mod history;
pub mod process;
pub use process as preprocess;
pub mod circuits;
pub mod python;
pub mod solver;
pub mod watchlist;

#[pyo3::pymodule]
mod clsat {
    use pyo3::prelude::*;

    #[pymodule_init]
    fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
        // Arbitrary code to run at the module initialization
        m.add_class::<crate::python::Sat>()?;
        Ok(())
    }
}
