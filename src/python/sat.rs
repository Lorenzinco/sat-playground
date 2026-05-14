use crate::preprocess::Preprocess;
use crate::solver::Algorithm;
use crate::history::ImplicationPoint;
use crate::formula::Formula;
use crate::heuristics::Heuristics;
use crate::python::Sat;
use crate::python::Stats;
use crate::drat::DratLogger;
use crate::solver::solve;

use std::fs::File;
use pyo3::prelude::*;
use std::fmt;



impl Sat {
   	pub fn to_subscript(&self, index: usize) -> String {
		let subs = ['₀','₁','₂','₃','₄','₅','₆','₇','₈','₉'];
		
		index.to_string()
			.chars()
			.map(|c| subs[c.to_digit(10).unwrap() as usize])
			.collect()
	}
	
	pub fn solve_rs<'py>(&mut self, py: Python<'_>, algorithm: Algorithm, implication_point: ImplicationPoint, preprocess: Vec<Preprocess>, heuristics: Heuristics, drat_path: Option<String>) -> PyResult<(Option<Vec<bool>>,Stats)> {

        let raw_clauses = self.clauses.clone();
        let mut formula = Formula::from_vec(raw_clauses);
        let mut logger = match drat_path {
            Some(path) => { Some(DratLogger::new(File::create(path).unwrap()))},
            None => { None }
        };
        
        let result = solve(&mut formula, py,algorithm,implication_point, preprocess, heuristics,&mut logger);
        
        match result {
            Ok(Some(model)) => {
                self.model = Some(model.clone());
                Ok((Some(model),formula.get_stats()))
            },
            Ok(None) => {
                self.model = None;
                Ok((None,formula.get_stats()))
            }
            Err(e) => Err(e)
        }
    }
}



impl fmt::Display for Sat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SAT Instance:\n")?;
        for (i,clause) in self.clauses.iter().enumerate() {
            write!(f,"(")?;
            for (j, literal) in clause.iter().enumerate() {
                let sign = if *literal > 0 { "" } else { "¬" };
                write!(f, "{}x{}", sign, self.to_subscript(literal.abs() as usize))?;
                if j < clause.len() - 1 {
                    write!(f, " ∨ ")?;
                }
            }
            write!(f,")")?;
            if i < self.clauses.len() - 1 {
                write!(f, "∧")?;
            }
        }
        
        write!(f,"\n")
    }
}