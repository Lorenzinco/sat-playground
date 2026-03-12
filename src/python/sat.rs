use crate::formula::variable::Variable;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::python::Sat;
use crate::solver::Algorithm;
use std::cell::RefCell;
use pyo3::prelude::*;
use std::rc::Rc;
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
        
        let max = self.clauses.iter().flatten().map(|lit| lit.abs()).max().unwrap_or(0) as usize;
        let mut variables: Vec<Variable> = Vec::new();
        
        for i in 0..max {
            variables.push(Variable::new(i as u64,None));
        }
        
        let variable_refs: Vec<Rc<RefCell<Variable>>> = variables.iter().map(|var| Rc::new(RefCell::new(var.clone()))).collect();
        
        
        let mut clauses: Vec<Clause> = Vec::new();
        for clause_ in self.clauses.iter() {
            let mut clause = Clause::new();
            for lit in clause_.iter() {
                let mut var_index = lit.abs() as usize;
                var_index -= 1;
                let negated = *lit < 0;
                let refcount = variable_refs.get(var_index)
                                .unwrap_or_else(|| panic!("Variable {} not found", var_index))
                                .clone();
                let literal = Literal::new(refcount, negated);
                clause.add_literal(literal).expect(format!("Failed to add literal {}, already in clause.",lit).as_str());
            }
            clauses.push(clause);
            
        }
        
        let mut formula = Formula::from_clauses(clauses, variable_refs);
        
        
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