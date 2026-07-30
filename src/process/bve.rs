use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::process::ProcessBudget;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::HashSet;
use std::io::Write;

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    budget: &ProcessBudget,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    _history: Option<&mut History>,
) -> PyResult<()> {
    while !budget.exhausted() && apply_best_bve_step(formula, budget, logger, &mut signal)? {}
    Ok(())
}

fn apply_best_bve_step<W: Write>(
    formula: &mut Formula,
    budget: &ProcessBudget,
    logger: &mut Option<DratLogger<W>>,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<bool> {
    if budget.exhausted() {
        return Ok(false);
    }

    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let mut best = None;
    let mut best_saving = 0isize;

    for var in 1..formula.assignment.len() {
        if budget.exhausted() {
            return Ok(false);
        }

        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }

        let Some(candidate) = elimination_candidate(formula, var, budget, signal)? else {
            if budget.exhausted() {
                return Ok(false);
            }
            continue;
        };

        if candidate.saving > best_saving {
            best_saving = candidate.saving;
            best = Some(candidate);
        }
    }

    if budget.exhausted() {
        return Ok(false);
    }

    let Some(candidate) = best else {
        return Ok(false);
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

    formula.stats.add_bve_eliminated_variable();
    Ok(true)
}

struct EliminationCandidate {
    to_delete: Vec<usize>,
    resolvents: Vec<Clause>,
    saving: isize,
}

fn elimination_candidate(
    formula: &mut Formula,
    var: usize,
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Option<EliminationCandidate>> {
    if budget.exhausted() {
        return Ok(None);
    }

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

    let mut to_delete = pos.iter().chain(neg.iter()).copied().collect::<Vec<_>>();
    to_delete.sort_unstable();
    to_delete.dedup();

    let mut resolvents = Vec::new();
    let mut seen = HashSet::new();
    let mut deleted_literals = 0usize;

    for &idx in &to_delete {
        if budget.exhausted() {
            return Ok(None);
        }

        let clause = formula.get_clause_at_idx(idx);
        if clause.lock_count() > 0 || clause.lbd() == 0 {
            return Ok(None);
        }
        deleted_literals += clause.len();
    }

    for &pos_idx in &pos {
        if budget.exhausted() {
            return Ok(None);
        }

        for &neg_idx in &neg {
            if budget.exhausted() {
                return Ok(None);
            }

            if let Some((py, steps)) = signal.as_mut() {
                signal_checker(*py, *steps)?;
            }

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
        if budget.exhausted() {
            return Ok(None);
        }
        added_literals += resolvent.len();
    }
    let saving = deleted_literals as isize - added_literals as isize;

    if resolvents.len() <= to_delete.len() && saving > 0 {
        Ok(Some(EliminationCandidate {
            to_delete,
            resolvents,
            saving,
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
        let budget = ProcessBudget::new(60.0);

        process::<std::io::Empty>(&mut formula, &budget, &mut logger, None, None).unwrap();

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
        let budget = ProcessBudget::new(60.0);

        process::<std::io::Empty>(&mut formula, &budget, &mut logger, None, None).unwrap();

        assert_eq!(formula.live_clause_count(), 1);
        assert_eq!(formula.clause_slots_len(), 3);
        assert_eq!(formula.get_clause_at_idx(2).len(), 0);
        assert_eq!(formula.stats.bve_eliminated_variables, 1);
        assert_eq!(formula.stats.bve_resolvents, 1);
        assert_eq!(formula.stats.clauses_deleted, 2);
    }

    #[test]
    fn bve_zero_budget_skips_elimination() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![-1, 3]]);
        let mut logger = None;
        let budget = ProcessBudget::new(0.0);

        process::<std::io::Empty>(&mut formula, &budget, &mut logger, None, None).unwrap();

        assert_eq!(formula.live_clause_count(), 2);
        assert_eq!(formula.stats.bve_eliminated_variables, 0);
        assert_eq!(formula.stats.bve_resolvents, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }

    #[test]
    fn bve_is_noop_when_resolution_would_grow_formula() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 3], vec![-1, 4], vec![-1, 5]]);
        let mut logger = None;
        let budget = ProcessBudget::new(60.0);

        process::<std::io::Empty>(&mut formula, &budget, &mut logger, None, None).unwrap();

        assert_eq!(formula.live_clause_count(), 4);
        assert_eq!(formula.stats.bve_eliminated_variables, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }
}
