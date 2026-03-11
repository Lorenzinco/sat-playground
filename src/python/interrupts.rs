use pyo3::prelude::*;

pub struct InterruptChecker<'py> {
    py: Python<'py>,
    counter: usize,
    every: usize,
}

impl<'py> InterruptChecker<'py> {
    pub fn new(py: Python<'py>, every: usize) -> Self {
        Self {
            py,
            counter: 0,
            every,
        }
    }

    pub fn checkpoint(&mut self) -> PyResult<()> {
        self.counter += 1;
        if self.counter % self.every == 0 {
            self.py.check_signals()?;
        }
        Ok(())
    }
}