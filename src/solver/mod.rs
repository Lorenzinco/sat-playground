use crate::python::interrupts::InterruptChecker;
use crate::formula::Formula;
use pyo3::prelude::*;

pub enum Algorithm {
    DPLL,
    CDCL
}

pub fn solve<'py>(formula: &mut Formula, algorithm: Algorithm, ic: &mut InterruptChecker<'py>) -> PyResult<Option<Vec<bool>>> {
    match algorithm {
        Algorithm::DPLL => return solve_dpll(formula,ic),
        Algorithm::CDCL => return solve_cdcl(formula,ic)
    }
}

pub fn solve_dpll<'py>(formula: &mut Formula, ic: &mut InterruptChecker<'py>) -> PyResult<Option<Vec<bool>>> {
    ic.checkpoint()?;
    
    
    while formula.contains_unit_clause() {
        formula.unit_propagate();
    }
    
    let mut pure_literals = formula.get_pure_literals();
    while pure_literals.len() > 0 {
         for (pure_literal,sign) in pure_literals {
             let index = pure_literal.borrow().get_index();
             formula.set_variable(index, sign).unwrap();
        }
        pure_literals = formula.get_pure_literals();
    }
    
    if formula.is_empty() {
        return Ok(Some(formula.get_model()));
    }
    
    if formula.contains_empty_clause() {
        return Ok(None);
    }
    
    let lit = formula.get_unassigned_literal().unwrap();
    
    let mut formula_true = formula.clone();
    formula_true.set_variable(lit.get_index(), true).unwrap();
    if let Ok(Some(model)) = solve_dpll(&mut formula_true, ic) {
        return Ok(Some(model));
    }
    
    let mut formula_false = formula.clone();
    formula_false.set_variable(lit.get_index(), false).unwrap();
    if let Ok(Some(model)) = solve_dpll(&mut formula_false, ic) {
        return Ok(Some(model));
    }
    Ok(None)
}

pub fn solve_cdcl<'py>(formula: &Formula, ic: &mut InterruptChecker<'py>) -> PyResult<Option<Vec<bool>>> {
    // Placeholder for the CDCL algorithm implementation.
    Ok(None)
}