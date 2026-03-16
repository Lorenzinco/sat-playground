use crate::formula::literal::Literal;
use crate::formula::Formula;
use crate::history::History;
use pyo3::prelude::PyResult;

fn propagate(formula: &mut Formula, history: &mut History) {
    loop {
        if !formula.unit_propagate_history(history) && !formula.pure_literals_propagate_history(history) { break }
    }
}

fn backtrack(formula: &mut Formula, history: &mut History) -> bool {
    loop {
        if history.get_decision_level() == 0{
            return false;
        }

        let last_decision = history
            .last_decision_literal()
            .expect("history should contain root")
            .clone();

        history.revert_last_decision(&mut formula.assignment);

        if !last_decision.is_negated() {
            let flipped = last_decision.negated();
            history.add_decision(&flipped);
            formula.assignment.assign(flipped.get_index(), !flipped.is_negated());
            return true;
        }
    }
}

pub fn solve_dpll(formula: &mut Formula) -> PyResult<Option<Vec<bool>>> {
    let mut history = History::new();

    loop {
        propagate(formula, &mut history);

        if formula.is_satisfied() {
            return Ok(Some(formula.get_model()));
        }

        if formula.contains_empty_clause(&formula.assignment) {
            if !backtrack(formula, &mut history) {
                return Ok(None);
            }
            continue;
        }

        let lit = match formula.get_unassigned_literal(&formula.assignment) {
            Some(lit) => lit,
            None => return Ok(Some(formula.get_model())),
        };

        let decision = Literal::new(lit.get_index(), false);

        history.add_decision(&decision);
        formula.assignment.assign(decision.get_index(), true);
    }
}