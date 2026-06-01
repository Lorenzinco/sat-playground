use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::HashSet;
use std::io::Write;

pub fn process<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    mut history: Option<&mut History>,
) -> PyResult<()> {
    while apply_best_bve_step(formula, logger, &mut signal, history.as_deref_mut())? {}
    Ok(())
}

fn apply_best_bve_step<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    signal: &mut Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
) -> PyResult<bool> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let mut best = None;
    let mut best_saving = 0isize;

    for var in 1..formula.assignment.len() {
        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }

        let Some(candidate) = elimination_candidate(formula, var, signal)? else {
            continue;
        };

        if candidate.saving > best_saving {
            best_saving = candidate.saving;
            best = Some(candidate);
        }
    }

    let Some(candidate) = best else {
        return Ok(false);
    };

    for clause in &candidate.resolvents {
        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }
        formula.add_clause_unchecked(clause.clone(), logger);
        formula.stats.add_bve_resolvent();
    }

    for &idx in &candidate.to_delete {
        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }
        let deleted = formula.get_clauses()[idx].clone();
        formula.stats.remove_clause(&deleted);
    }
    let old_to_new = formula.delete_clauses(&candidate.to_delete, logger);
    if let Some(history) = history {
        history.remap_clause_indices(&old_to_new);
    }

    formula.stats.add_bve_eliminated_variable();
    Ok(true)
}

struct EliminationCandidate {
    to_delete: Vec<usize>,
    resolvents: Vec<Clause>,
    saving: isize,
}

fn elimination_candidate(
    formula: &Formula,
    var: usize,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Option<EliminationCandidate>> {
    let pos = formula.occurrence_indices(&Literal::new(var as i32));
    let neg = formula.occurrence_indices(&Literal::new(-(var as i32)));

    if pos.is_empty() || neg.is_empty() {
        return Ok(None);
    }

    let mut to_delete = pos.iter().chain(neg.iter()).copied().collect::<Vec<_>>();
    to_delete.sort_unstable();
    to_delete.dedup();

    if to_delete.iter().any(|&idx| {
        let clause = &formula.get_clauses()[idx];
        clause.lock_count > 0 || clause.lbd == 0
    }) {
        return Ok(None);
    }

    let mut resolvents = Vec::new();
    let mut seen = HashSet::new();
    let mut deleted_literals = 0usize;

    for &idx in &to_delete {
        deleted_literals += formula.get_clauses()[idx].len();
    }

    for &pos_idx in &pos {
        for &neg_idx in &neg {
            if let Some((py, steps)) = signal.as_mut() {
                signal_checker(*py, *steps)?;
            }

            let Some(resolvent) = formula.get_clauses()[pos_idx]
                .resolve_on(&formula.get_clauses()[neg_idx], var as i32)
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

    let added_literals = resolvents.iter().map(Clause::len).sum::<usize>();
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

        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.get_clauses().len(), 1);
        assert_eq!(
            formula.get_clauses()[0].get_literals(),
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

        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.get_clauses().len(), 1);
        assert_eq!(formula.get_clauses()[0].len(), 0);
        assert_eq!(formula.stats.bve_eliminated_variables, 1);
        assert_eq!(formula.stats.bve_resolvents, 1);
        assert_eq!(formula.stats.clauses_deleted, 2);
    }

    #[test]
    fn bve_is_noop_when_resolution_would_grow_formula() {
        let mut formula = Formula::from_vec(vec![vec![1, 2], vec![1, 3], vec![-1, 4], vec![-1, 5]]);
        let mut logger = None;

        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.get_clauses().len(), 4);
        assert_eq!(formula.stats.bve_eliminated_variables, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }
}
