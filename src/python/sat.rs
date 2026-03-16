use crate::solver::Algorithm;
use crate::formula::Formula;
use crate::python::Sat;
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
	
	pub fn solve_rs<'py>(&mut self, algorithm: Algorithm) -> PyResult<Option<Vec<bool>>> {

        let raw_clauses = self.clauses.clone();
        let mut formula = Formula::from_vec(raw_clauses);
        
        let result = formula.solve(algorithm);
        match result {
            Ok(Some(model)) => {
                self.model = Some(model.clone());
                Ok(Some(model))
            },
            Ok(None) => {
                self.model = None;
                Ok(None)
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