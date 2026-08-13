use crate::circuits::and_gate::AndGate;
use crate::circuits::factorization::{Factorization, live_factor_clause};
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::process::ClauseScope;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::io::Write;

/// Attempts local BVA factorization around VSIDS-weighted literals.
///
/// Each attempt samples a variable with inverse VSIDS-activity weighting,
/// chooses one of its live polarities, and atomically applies the better
/// profitable gate candidate.
pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {
    // Try BVA around lower-activity variables first.
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let Some(start) = formula
        .vsids
        .sample_literal(formula, true)
        .map(|literal| literal.get_index())
    else {
        return Ok(());
    };
    factorize_literal(formula, scope, logger, start);

    Ok(())
}

fn factorize_literal<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    start: i32,
) -> bool {
    let initial_clause_limit = formula.clause_slots_len();
    let mut pending_deleted = (0..initial_clause_limit)
        .map(|clause_idx| {
            formula.is_clause_garbage(clause_idx)
                || !scope.includes(
                    clause_idx,
                    formula.get_clause_and_garbage_at_idx(clause_idx),
                )
        })
        .collect::<Vec<_>>();

    let and_gate = AndGate::find(formula, start, &pending_deleted);
    let variable = start.unsigned_abs() as usize;
    let gate = if formula.assignment.get_value(variable).is_none()
        && formula
            .occurrence_of(&Literal::new(-start))
            .any(|clause_idx| live_factor_clause(formula, clause_idx, &pending_deleted))
    {
        Gate::find(formula, &pending_deleted, start)
    } else {
        None
    };

    let Some(candidate) = Factorization::select(and_gate, gate) else {
        return false;
    };

    let mut deletion_indices = Vec::new();
    candidate.apply(formula, logger, &mut pending_deleted, &mut deletion_indices);
    finalize_deletions(formula, logger, &mut deletion_indices);
    true
}

fn finalize_deletions<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    deletion_indices: &mut Vec<usize>,
) {
    deletion_indices.sort_unstable();
    deletion_indices.dedup();

    for &clause_idx in deletion_indices.iter() {
        formula.record_clause_removal(clause_idx);
    }

    let deleted = formula.delete_clauses(deletion_indices, logger);
    debug_assert_eq!(deleted, deletion_indices.len());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::extension::ExtensionDefinition;

    #[test]
    fn empty_formula_is_a_noop() {
        let mut formula = Formula::new(0);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;

        let scope = ClauseScope::range(0..formula.clause_slots_len());
        process(&mut formula, &scope, &mut logger, None, None).unwrap();

        assert_eq!(formula.stats.bva_literals, 0);
        assert!(formula.extensions.is_empty());
    }

    #[test]
    fn selected_and_grid_is_applied_and_finalized() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
        ]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(factorize_literal(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.live_clause_count(), 6);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(
            formula.extensions.definition(&Literal::new(7)),
            Some(&ExtensionDefinition::And(vec![
                Literal::new(1),
                Literal::new(2),
            ]))
        );
        for source_index in 0..8 {
            assert!(formula.is_clause_garbage(source_index));
        }
    }

    #[test]
    fn selected_ite_gate_is_applied_and_registered() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 2, 10],
            vec![-1, 3, 10],
            vec![1, 2, 11],
            vec![-1, 3, 11],
            vec![1, 2, 12],
            vec![-1, 3, 12],
            vec![1, -2, 13],
            vec![-1, -3, 13],
            vec![1, -2, 14],
            vec![-1, -3, 14],
        ]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(factorize_literal(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.live_clause_count(), 9);
        assert_eq!(formula.stats.clauses_deleted, 10);
        assert_eq!(
            formula.extensions.definition(&Literal::new(15)),
            Some(&ExtensionDefinition::Ite {
                condition: Literal::new(1),
                when_true: Literal::new(-3),
                when_false: Literal::new(-2),
            })
        );
    }

    #[test]
    fn unprofitable_seed_does_not_change_the_formula() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 3]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let initial_slots = formula.clause_slots_len();
        let initial_variables = formula.assignment.len();
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        assert!(!factorize_literal(&mut formula, &scope, &mut logger, 1));

        assert_eq!(formula.clause_slots_len(), initial_slots);
        assert_eq!(formula.assignment.len(), initial_variables);
        assert!(formula.extensions.is_empty());
    }
}
