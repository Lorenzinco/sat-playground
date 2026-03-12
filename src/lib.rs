pub mod formula;
pub mod solver;
pub mod python;
pub mod implication_graph;

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
