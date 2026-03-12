use crate::formula::Formula;
use pyo3::prelude::PyResult;

pub fn solve_dpll<'py>(formula: &mut Formula) -> PyResult<Option<Vec<bool>>> {
    
    
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
    };
    
    if formula.is_satisfied() {
        return Ok(Some(formula.get_model()));
    }
    
    if formula.contains_empty_clause() {
        return Ok(None);
    }
    
    let lit = formula.get_unassigned_literal().unwrap();
    
    let mut formula_true = formula.clone();
    formula_true.set_variable(lit.get_index(), true).unwrap();
    if let Ok(Some(model)) = solve_dpll(&mut formula_true) {
        return Ok(Some(model));
    }
    
    let mut formula_false = formula.clone();
    formula_false.set_variable(lit.get_index(), false).unwrap();
    if let Ok(Some(model)) = solve_dpll(&mut formula_false) {
        return Ok(Some(model));
    }
    Ok(None)
}