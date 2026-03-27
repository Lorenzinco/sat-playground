pub mod sat;
pub mod stats;

use crate::python::stats::Stats;
use crate::solver::Algorithm;
use pyo3::prelude::*;
use ctrlc;

/// Python bindings for the Sat struct, allocate an instance to then add clauses.
#[pyclass]
pub struct Sat {
    #[pyo3(get)]
    pub clauses: Vec<Vec<i64>>,
    #[pyo3(get)]
    model : Option<Vec<bool>>,
    #[pyo3(get)]
    stats: Option<Stats>
}

#[pymethods]
impl Sat {
    /// Creates a sat instance with <clauses> as clauses, if None is passed instead creates an empty sat instance.
    #[new]
    #[pyo3(signature = (clauses = None),text_signature = "clauses: list[list[int]] | None = None")]
    pub fn new(clauses: Option<Vec<Vec<i64>>>) -> Self {
        if let Some(clauses) = clauses {
            for lit in clauses.iter().flatten() {
                if *lit == 0 {
                    panic!("Literal cannot be 0");
                }
            }
            Sat {
                clauses: clauses,
                model: None,
                stats: None
            }
        }
        else {
            Sat {
                clauses: vec!(),
                model: None,
                stats: None
            }
        }
    }
    /// Adds a clause to the sat instance, the clause is a list of integers where positive integers represent positive literals and negative integers represent negated literals.
   #[pyo3(signature = (clause: "list[int]") ,text_signature = "clause: list[int]")]
    pub fn add_clause(&mut self, clause: Vec<i64>) {
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
    #[pyo3(signature = (algorithm) ,text_signature = "algorithm")]
    pub fn solve(&mut self, algorithm: Algorithm)->PyResult<()> {
        ctrlc::set_handler(|| std::process::exit(2)).unwrap();
        let (result,stats) = self.solve_rs(algorithm)?;
        self.stats = Some(stats);
        self.model = result;
        Ok(())
    }
}