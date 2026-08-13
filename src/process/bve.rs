use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::process::ClauseScope;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::HashSet;
use std::io::Write;

/// Attempts one BVE step on a variable sampled with inverse VSIDS weighting.
/// Lower-activity variables are therefore more likely to be eliminated, while
/// every live variable with both polarities retains a non-zero probability.
pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let Some(var) = formula.vsids.sample_low_activity_variable(formula) else {
        return Ok(());
    };
    let Some(candidate) = elimination_candidate(formula, scope, var)? else {
        return Ok(());
    };
    let EliminationCandidate {
        to_delete,
        resolvents,
        ..
    } = candidate;

    // Candidate construction is the interruptible phase. Commit the selected
    // elimination atomically so cancellation cannot leave statistics or clause
    // indices partially updated.
    for clause in resolvents {
        formula.add_clause_unchecked(clause, logger);
        formula.stats.add_bve_resolvent();
    }

    for &idx in &to_delete {
        formula.record_clause_removal(idx);
    }
    let newly_deleted = formula.delete_clauses(&to_delete, logger);
    debug_assert_eq!(newly_deleted, to_delete.len());

    formula.extensions.remove_substitution_variable(var);
    formula.stats.add_bve_eliminated_variable();
    Ok(())
}

struct EliminationCandidate {
    to_delete: Vec<usize>,
    resolvents: Vec<Clause>,
}

fn elimination_candidate(
    formula: &mut Formula,
    scope: &ClauseScope,
    var: usize,
) -> PyResult<Option<EliminationCandidate>> {
    let positive_literal = Literal::new(var as i32);
    let negative_literal = Literal::new(-(var as i32));
    formula.clean_occurrence(&positive_literal);
    formula.clean_occurrence(&negative_literal);
    let pos = formula
        .live_occurrences(&positive_literal)
        .collect::<Vec<_>>();
    let neg = formula
        .live_occurrences(&negative_literal)
        .collect::<Vec<_>>();

    if pos.is_empty() || neg.is_empty() {
        return Ok(None);
    }
    if pos
        .iter()
        .chain(&neg)
        .any(|&clause_idx| !scope.includes(clause_idx, formula.get_clause_at_idx(clause_idx)))
    {
        return Ok(None);
    }

    let mut to_delete = pos.iter().chain(neg.iter()).copied().collect::<Vec<_>>();
    to_delete.sort_unstable();
    to_delete.dedup();

    let mut resolvents = Vec::new();
    let mut seen = HashSet::new();
    let mut deleted_literals = 0usize;

    for &idx in &to_delete {
        let clause = formula.get_clause_at_idx(idx);
        if clause.lock_count > 0 || clause.lbd == 0 {
            return Ok(None);
        }
        deleted_literals += clause.len();
    }

    for &pos_idx in &pos {
        for &neg_idx in &neg {
            let Some(resolvent) = formula
                .get_clause_at_idx(pos_idx)
                .resolve_on(formula.get_clause_at_idx(neg_idx), var as i32)
            else {
                continue;
            };

            if seen.insert(resolvent.sorted_literal_indices()) {
                resolvents.push(resolvent);
            }
        }
    }

    if resolvents.is_empty() {
        return Ok(None);
    }

    let mut added_literals = 0;
    for resolvent in &resolvents {
        added_literals += resolvent.len();
    }
    let saving = deleted_literals as isize - added_literals as isize;

    if resolvents.len() <= to_delete.len() && saving > 0 {
        Ok(Some(EliminationCandidate {
            to_delete,
            resolvents,
        }))
    } else {
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bve_eliminates_when_it_saves_literals() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
        let mut logger = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        process::<std::io::Empty>(&mut formula, &scope, &mut logger, None, None).unwrap();

        assert_eq!(formula.live_clause_count(), 1);
        assert_eq!(formula.clause_slots_len(), 3);
        assert_eq!(formula.get_clauses_and_garbage().count(), 3);
        assert_eq!(
            formula.get_clause_at_idx(2).get_literals(),
            &vec![Literal::new(2), Literal::new(3)]
        );
        assert_eq!(formula.stats.bve_eliminated_variables, 1);
        assert_eq!(formula.stats.bve_resolvents, 1);
        assert_eq!(formula.stats.clauses_deleted, 2);
    }

    #[test]
    fn bve_preserves_unit_contradiction_as_empty_clause() {
        let mut formula = Formula::from_vec(vec![vec![1], vec![-1]]);
        let mut logger = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        process::<std::io::Empty>(&mut formula, &scope, &mut logger, None, None).unwrap();

        assert_eq!(formula.live_clause_count(), 1);
        assert_eq!(formula.clause_slots_len(), 3);
        assert_eq!(formula.get_clause_at_idx(2).len(), 0);
        assert_eq!(formula.stats.bve_eliminated_variables, 1);
        assert_eq!(formula.stats.bve_resolvents, 1);
        assert_eq!(formula.stats.clauses_deleted, 2);
    }

    #[test]
    fn bve_is_noop_when_resolution_would_grow_formula() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 3], vec![-1, 4], vec![-1, 5]]);
        let mut logger = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        process::<std::io::Empty>(&mut formula, &scope, &mut logger, None, None).unwrap();

        assert_eq!(formula.live_clause_count(), 4);
        assert_eq!(formula.stats.bve_eliminated_variables, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }

    #[test]
    fn skips_variable_with_any_learned_occurrence_outside_scope() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
        formula.get_clause_at_idx_mut(0).lbd = 1;
        formula.get_clause_at_idx_mut(1).lbd = 1;
        let scope = ClauseScope::indices([0]);

        assert!(
            elimination_candidate(&mut formula, &scope, 1)
                .unwrap()
                .is_none()
        );
        assert_eq!(formula.live_clause_count(), 2);
    }

    #[test]
    fn eliminating_a_substitution_variable_invalidates_its_reuse() {
        let mut formula = Formula::from_vec(vec![vec![3, 4], vec![-3, 5]]);
        let x = Literal::new(1);
        let y = Literal::new(2);
        let substitute = Literal::new(3);
        formula.extensions.add_substitution(&x, &y, &substitute);
        let mut logger = None;
        let scope = ClauseScope::range(0..formula.clause_slots_len());

        process::<std::io::Empty>(&mut formula, &scope, &mut logger, None, None).unwrap();

        assert_eq!(formula.extensions.substitute(&x, &y), None);
        assert!(formula.extensions.definition(&substitute).is_some());
        assert_eq!(formula.stats.bve_eliminated_variables, 1);
    }
}
