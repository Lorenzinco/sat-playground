pub mod sat;
pub mod stats;

use crate::guidance::GuidanceSpec;
use crate::heuristics::Heuristics;
use crate::history::ImplicationPoint;
use crate::process::Process;
use crate::python::stats::Stats;
use crate::solver::Algorithm;
use pyo3::prelude::*;

/// Python bindings for the Sat struct, allocate an instance to then add clauses.
#[pyclass]
pub struct Sat {
    #[pyo3(get)]
    pub clauses: Vec<Vec<i32>>,
    #[pyo3(get)]
    model: Option<Vec<bool>>,
    #[pyo3(get)]
    stats: Option<Stats>,
}

#[pymethods]
impl Sat {
    /// Creates a sat instance with <clauses> as clauses, if None is passed instead creates an empty sat instance.
    #[new]
    #[pyo3(signature = (clauses = None),text_signature = "clauses: list[list[int]] | None = None")]
    pub fn new(clauses: Option<Vec<Vec<i32>>>) -> Self {
        if let Some(clauses) = clauses {
            for lit in clauses.iter().flatten() {
                if *lit == 0 {
                    panic!("Literal cannot be 0");
                }
            }
            Sat {
                clauses: clauses,
                model: None,
                stats: None,
            }
        } else {
            Sat {
                clauses: vec![],
                model: None,
                stats: None,
            }
        }
    }
    /// Adds a clause to the sat instance, the clause is a list of integers where positive integers represent positive literals and negative integers represent negated literals.
    #[pyo3(signature = (clause: "list[int]") ,text_signature = "clause: list[int]")]
    pub fn add_clause(&mut self, clause: Vec<i32>) {
        for lit in clause.iter() {
            if *lit == 0 {
                panic!("Literal cannot be 0");
            }
        }
        self.clauses.push(clause);
    }

    fn __str__(&self) -> String {
        format!("{}", self)
    }

    fn __repr__(&self) -> String {
        format!("{}", self)
    }

    /// Returns a model that satisfies the clauses if the instance is satisfiable, otherwise returns None. The model is a list of booleans where the i-th element represents the value of the variable x_i (True for positive literals and False for negated literals).
    #[pyo3(
        signature = (
            algorithm,
            implication_point,
            preprocess,
            inprocessing,
            heuristics,
            drat_path=None,
            extension_guidance=None,
            extension_guidance_log_path=None,
            *,
            preprocessing_budget=5.0,
            inprocessing_budget=0.075,
        ),
        text_signature = "(algorithm, implication_point, preprocess, inprocessing, heuristics, drat_path=None, extension_guidance=None, extension_guidance_log_path=None, *, preprocessing_budget=5.0, inprocessing_budget=0.075)"
    )]
    pub fn solve(
        &mut self,
        py: Python<'_>,
        algorithm: Algorithm,
        implication_point: ImplicationPoint,
        preprocess: Vec<Process>,
        inprocessing: Vec<Process>,
        heuristics: Heuristics,
        drat_path: Option<String>,
        extension_guidance: Option<GuidanceSpec>,
        extension_guidance_log_path: Option<String>,
        preprocessing_budget: f32,
        inprocessing_budget: f32,
    ) -> PyResult<()> {
        for (name, budget) in [
            ("preprocessing_budget", preprocessing_budget),
            ("inprocessing_budget", inprocessing_budget),
        ] {
            if !budget.is_finite() || budget < 0.0 {
                return Err(pyo3::exceptions::PyValueError::new_err(format!(
                    "{name} must be finite and non-negative"
                )));
            }
        }

        let (result, stats) = self.solve_rs(
            py,
            algorithm,
            implication_point,
            preprocess,
            inprocessing,
            heuristics,
            drat_path,
            extension_guidance,
            extension_guidance_log_path,
            preprocessing_budget,
            inprocessing_budget,
        )?;
        self.stats = Some(stats);
        self.model = result;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve_with_budgets(py: Python<'_>, preprocessing: f32, inprocessing: f32) -> PyResult<()> {
        Sat::new(Some(vec![vec![1]])).solve(
            py,
            Algorithm::DPLL,
            ImplicationPoint::UIP,
            Vec::new(),
            Vec::new(),
            Heuristics::None,
            None,
            None,
            None,
            preprocessing,
            inprocessing,
        )
    }

    #[test]
    fn solve_rejects_negative_and_nonfinite_budgets() {
        Python::initialize();
        Python::attach(|py| {
            for invalid in [-1.0, f32::NAN, f32::INFINITY, f32::NEG_INFINITY] {
                let preprocessing_error = solve_with_budgets(py, invalid, 0.0).unwrap_err();
                assert!(preprocessing_error.is_instance_of::<pyo3::exceptions::PyValueError>(py));
                assert!(
                    preprocessing_error
                        .to_string()
                        .contains("preprocessing_budget")
                );

                let inprocessing_error = solve_with_budgets(py, 0.0, invalid).unwrap_err();
                assert!(inprocessing_error.is_instance_of::<pyo3::exceptions::PyValueError>(py));
                assert!(
                    inprocessing_error
                        .to_string()
                        .contains("inprocessing_budget")
                );
            }
        });
    }

    #[test]
    fn solve_accepts_zero_budgets() {
        Python::initialize();
        Python::attach(|py| solve_with_budgets(py, 0.0, 0.0).unwrap());
    }
}

pub fn signal_checker(py: Python<'_>, steps: &mut u64) -> PyResult<()> {
    *steps += 1;
    if steps.is_multiple_of(100) {
        py.check_signals()?;
    }

    Ok(())
}
