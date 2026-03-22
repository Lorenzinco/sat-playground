use crate::formula::Formula;
use crate::history::History;
use pyo3::prelude::PyResult;

fn propagate(formula: &mut Formula, history: &mut History) {
    while formula.unit_propagate_history(history) {}
    
}

pub fn solve_cdcl<'py>(formula: &mut Formula) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();
    propagate(formula, &mut history);

    loop {
        while let Some((index, _clause)) = formula.get_empty_clause(&formula.assignment) {
            if history.get_decision_level() == 0 {
                return Ok(None); // UNSAT
            }
            let (learned, backtrack_level) = history.analyze_conflict(formula, index);
            history.revert_decision(backtrack_level + 1, &mut formula.assignment);
            assert!(learned.is_unit(&formula.assignment));
            formula.add_clause(learned);
            propagate(formula, &mut history);
            continue;
        }

        if formula.is_satisfied() {
            return Ok(Some(formula.get_model()));
        }

        let lit = match formula.get_unassigned_literal(&formula.assignment) {
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        history.add_decision(&lit);
        formula.assignment.assign(lit.get_index(), !lit.is_negated());

        propagate(formula, &mut history);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::Formula;

    #[test]
    fn test_cdcl_simple_sat() {
        // (x1 v x2) ^ (-x1 v x3)
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);

        let res = solve_cdcl(&mut formula).unwrap();
        assert!(res.is_some());
    }

    #[test]
    fn test_cdcl_simple_unsat() {
        // (x1) ^ (-x1)
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);

        let res = solve_cdcl(&mut formula).unwrap();
        assert!(res.is_none());
    }

    #[test]
    fn test_cdcl_inner_conflict_loop() {
        // (x1 v x2) ^ (x1 v -x2) ^ (-x1 v x3) ^ (-x1 v -x3)
        let mut formula =
            Formula::from_vec(vec![vec![1, 2], vec![1, -2], vec![-1, 3], vec![-1, -3]]);

        let res = solve_cdcl(&mut formula).unwrap();
        assert!(res.is_none());
    }
}
