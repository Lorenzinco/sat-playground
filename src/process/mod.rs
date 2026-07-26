pub mod bva;
pub mod bve;
pub mod subsumption;

use pyo3::prelude::*;
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug)]
pub(crate) struct ProcessBudget {
    deadline: Option<Instant>,
}

impl ProcessBudget {
    pub(crate) fn new(seconds: f32) -> Self {
        if !seconds.is_finite() || seconds <= 0.0 {
            return Self { deadline: None };
        }

        let now = Instant::now();
        let mut duration = Duration::try_from_secs_f32(seconds).unwrap_or(Duration::MAX);
        let deadline = loop {
            if let Some(deadline) = now.checked_add(duration) {
                break deadline;
            }
            duration /= 2;
        };

        Self {
            deadline: Some(deadline),
        }
    }

    pub(crate) fn exhausted(&self) -> bool {
        self.deadline
            .is_none_or(|deadline| Instant::now() >= deadline)
    }
}

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

#[cfg(test)]
mod tests {
    use super::ProcessBudget;

    #[test]
    fn invalid_or_nonpositive_budgets_are_immediately_exhausted() {
        for seconds in [0.0, -1.0, f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
            assert!(ProcessBudget::new(seconds).exhausted());
        }
    }

    #[test]
    fn positive_budget_has_a_future_deadline() {
        assert!(!ProcessBudget::new(60.0).exhausted());
    }
}
