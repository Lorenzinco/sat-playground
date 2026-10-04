//! Retire exact AND extensions expanded more often than selected by GES.
//! Clause additions precede all deletions so DRAT can check the rewrites while
//! the extension definition is still present.
use std::collections::{HashMap, HashSet};
use std::io::Write;

use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::extension::ExtensionDefinition;
use crate::formula::literal::Literal;
use crate::history::History;

/// Rewind a fully recorded root trail once, retire extensions, then replay all
/// live unit clauses before any later inprocessing phase sees the new formula.
/// Returns true if rebuilding the root trail finds a conflict.
pub(crate) fn process_at_restart<W: Write>(
    formula: &mut Formula,
    history: &mut History,
    logger: &mut Option<DratLogger<W>>,
) -> bool {
    let dependent_inputs = formula
        .extensions
        .iter()
        .flat_map(|(_, definition)| definition_inputs(definition))
        .collect::<HashSet<_>>();
    let root_candidates = formula
        .stats
        .ges_extension_preference
        .iter()
        .filter_map(|(&signed, &(_, unrolled, chosen))| {
            (signed < 0
                && unrolled > chosen
                && !dependent_inputs.contains(&signed.unsigned_abs())
                && formula
                    .extensions
                    .substitution_inputs(&Literal::new(-signed))
                    .is_some())
            .then(|| formula.assignment.get_value((-signed) as usize))
            .flatten()
            .map(|value| (signed.unsigned_abs() as usize, value))
        })
        .collect::<Vec<_>>();
    for &(variable, value) in &root_candidates {
        formula
            .stats
            .record_preference_root_assignment(variable, value);
    }
    let rewind = !root_candidates.is_empty()
        && history.get_decision_level() == 0
        && history.trail().len()
            == (1..formula.assignment.len())
                .filter(|&var| formula.assignment.get_value(var).is_some())
                .count()
        && history
            .trail()
            .iter()
            .all(|literal| history.get_reason(literal).is_some());
    if rewind {
        formula.rewind_root_implications(history);
        formula.stats.preference_root_rebuilds += 1;
    }
    process_with_replay(formula, logger, rewind);
    rewind && formula.rebuild_root_implications(history)
}

pub(crate) fn process<W: Write>(formula: &mut Formula, logger: &mut Option<DratLogger<W>>) {
    process_with_replay(formula, logger, false);
}

fn process_with_replay<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    root_replay: bool,
) {
    formula.stats.preference_passes += 1;
    // Scan definitions once. Descending variable order retires newly created
    // dependents before their inputs; a retained dependent protects its inputs.
    let mut dependents = HashMap::<u32, usize>::new();
    for (_, definition) in formula.extensions.iter() {
        for input in definition_inputs(definition) {
            *dependents.entry(input).or_default() += 1;
        }
    }

    let candidates: Vec<_> = formula
        .stats
        .ges_extension_preference
        .iter()
        .filter_map(|(&signed, &(_, unrolled, chosen))| {
            (signed < 0 && unrolled > chosen).then_some(-signed)
        })
        .collect();

    for variable in candidates {
        let z = Literal::new(variable);
        let Some((a, b)) = formula.extensions.substitution_inputs(&z) else {
            continue;
        };
        formula.stats.preference_candidates += 1;
        if dependents
            .get(&z.get_index().unsigned_abs())
            .copied()
            .unwrap_or(0)
            != 0
        {
            formula.stats.preference_skipped_dependents += 1;
            continue;
        }
        if formula.assignment.get_value(variable as usize).is_some() {
            formula.stats.preference_skipped_assigned += 1;
            continue;
        }
        let indices = occurrences(formula, z);

        // Prepare the entire batch before touching the formula: a locked reason
        // cannot be deleted, and a newly asserting clause needs explicit
        // propagation which this pass does not perform.
        let Some(replacements) = prepare(formula, &indices, z, a, b, root_replay) else {
            formula.stats.preference_skipped_unsafe += 1;
            continue;
        };
        formula.stats.preference_clauses_added += replacements.len() as u64;
        formula.stats.preference_clauses_removed += indices.len() as u64;
        formula.stats.preference_learned_positive_dropped += indices
            .iter()
            .filter(|&&index| {
                let clause = formula.get_clause_at_idx(index);
                clause.lbd > 0
                    && clause.get_literals().contains(&z)
                    && !clause.get_literals().contains(&z.negated())
            })
            .count() as u64;
        for clause in replacements {
            if clause.lbd > 0 {
                formula.stats.add_learnt_clause(&clause);
            }
            formula.add_clause_unchecked(clause, logger);
        }
        for &index in &indices {
            formula.record_clause_removal(index);
        }
        formula.delete_clauses(&indices, logger);
        formula.extensions.retire_exact_extension(&z);
        formula.retire_extension_variable(variable as usize);
        formula.stats.preference_extensions_retired += 1;

        let first = a.get_index().unsigned_abs();
        let second = b.get_index().unsigned_abs();
        if let Some(count) = dependents.get_mut(&first) {
            *count -= 1;
        }
        if second != first
            && let Some(count) = dependents.get_mut(&second)
        {
            *count -= 1;
        }
    }
}

fn definition_inputs(definition: &ExtensionDefinition) -> HashSet<u32> {
    match definition {
        ExtensionDefinition::And(inputs) => inputs
            .iter()
            .map(|literal| literal.get_index().unsigned_abs())
            .collect(),
        ExtensionDefinition::Ite {
            condition,
            when_true,
            when_false,
        } => [condition, when_true, when_false]
            .into_iter()
            .map(|literal| literal.get_index().unsigned_abs())
            .collect(),
    }
}

fn occurrences(formula: &Formula, z: Literal) -> Vec<usize> {
    let mut indices = formula
        .occurrence_of(&z)
        .chain(formula.occurrence_of(&z.negated()))
        .collect::<Vec<_>>();
    indices.sort_unstable();
    indices.dedup();
    indices
}

fn prepare(
    formula: &Formula,
    indices: &[usize],
    z: Literal,
    a: Literal,
    b: Literal,
    root_replay: bool,
) -> Option<Vec<Clause>> {
    let mut output = Vec::new();
    for &index in indices {
        let source = formula.get_clause_at_idx(index);
        if source.lock_count != 0 {
            return None;
        }
        let positive = source.get_literals().contains(&z);
        let negative = source.get_literals().contains(&z.negated());
        if positive && negative {
            // The source is tautological, so it needs no replacement.
            continue;
        }
        if positive && source.lbd > 0 {
            // Deleting a learned clause is sound; never do this to a permanent
            // original/BVA quotient clause or to an active implication reason.
            continue;
        }
        let rest: Vec<_> = source
            .get_literals()
            .iter()
            .copied()
            .filter(|&literal| literal != z && literal != z.negated())
            .collect();
        if positive {
            // C ∨ z, with z = a ∧ b, becomes (C ∨ a) ∧ (C ∨ b).
            for input in [a, b] {
                push_replacement(formula, source, &rest, &[input], &mut output, root_replay)?;
            }
        } else {
            // C ∨ ¬z becomes C ∨ ¬a ∨ ¬b.
            push_replacement(
                formula,
                source,
                &rest,
                &[a.negated(), b.negated()],
                &mut output,
                root_replay,
            )?;
        }
    }
    Some(output)
}

fn push_replacement(
    formula: &Formula,
    source: &Clause,
    rest: &[Literal],
    added: &[Literal],
    output: &mut Vec<Clause>,
    root_replay: bool,
) -> Option<()> {
    let mut literals = Vec::with_capacity(rest.len() + added.len());
    let mut seen = HashSet::new();
    for &literal in rest.iter().chain(added) {
        if seen.contains(&literal.negated().get_index()) {
            return Some(()); // Tautology: no replacement clause required.
        }
        if seen.insert(literal.get_index()) {
            literals.push(literal);
        }
    }
    let mut replacement = Clause::from_literals(literals, source.lbd);
    // Standalone passes cannot enqueue new units; the restart path replays the
    // root trail immediately after rewriting and can accept them.
    if !root_replay
        && (replacement.is_unit(&formula.assignment) || replacement.is_empty(&formula.assignment))
    {
        return None;
    }
    replacement.activity = source.activity;
    replacement.bva_generated = source.bva_generated;
    output.push(replacement);
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Empty;

    fn setup() -> Formula {
        let mut formula = Formula::from_vec(vec![
            vec![-3, 1],
            vec![-3, 2],
            vec![3, -1, -2],
            vec![-3, 4],
            vec![3, 5],
        ]);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(3));
        formula
            .stats
            .ges_extension_preference
            .insert(-3, ("bva".into(), 10, 0));
        formula
    }

    fn live(formula: &Formula) -> Vec<Vec<i32>> {
        formula
            .get_clauses()
            .map(|(_, clause)| {
                clause
                    .get_literals()
                    .iter()
                    .map(|lit| lit.get_index())
                    .collect()
            })
            .collect()
    }

    #[test]
    fn expansion_must_outnumber_choices_strictly() {
        for (unrolled, chosen, eligible) in [
            (0, 0, false),
            (1, 0, true),
            (2, 1, true),
            (1, 1, false),
            (1, 2, false),
            (u64::MAX, u64::MAX - 1, true),
        ] {
            let mut formula = setup();
            formula
                .stats
                .ges_extension_preference
                .insert(-3, ("bva".into(), unrolled, chosen));
            process::<Empty>(&mut formula, &mut None);
            assert_eq!(formula.is_retired_extension_variable(3), eligible);
        }
    }

    #[test]
    fn chosen_extensions_can_be_retired_and_equal_counts_are_not() {
        for (unrolled, chosen, expected) in [(2, 1, true), (1, 1, false), (1, 2, false)] {
            let mut formula = setup();
            formula
                .stats
                .ges_extension_preference
                .insert(-3, ("bva".into(), unrolled, chosen));
            process::<Empty>(&mut formula, &mut None);
            assert_eq!(formula.is_retired_extension_variable(3), expected);
            assert_eq!(formula.stats.preference_candidates, u64::from(expected));
        }
    }

    #[test]
    fn chosen_root_extension_triggers_rewind_only_above_threshold() {
        for (unrolled, chosen, should_retire) in [(2, 1, true), (1, 1, false)] {
            let mut formula = setup();
            formula
                .stats
                .ges_extension_preference
                .insert(-3, ("dip".into(), unrolled, chosen));
            formula.add_clause_unchecked::<Empty>(
                Clause::from_literals(vec![Literal::new(1)], -1),
                &mut None,
            );
            formula.add_clause_unchecked::<Empty>(
                Clause::from_literals(vec![Literal::new(2)], -1),
                &mut None,
            );
            let mut history = History::new();
            assert!(!formula.rebuild_root_implications(&mut history));
            assert_eq!(formula.assignment.get_value(3), Some(true));
            assert!(!process_at_restart::<Empty>(
                &mut formula,
                &mut history,
                &mut None
            ));
            assert_eq!(formula.is_retired_extension_variable(3), should_retire);
            assert_eq!(
                formula.stats.preference_root_rebuilds,
                u64::from(should_retire)
            );
            assert_eq!(
                formula.stats.preference_extensions_retired,
                u64::from(should_retire)
            );
        }
    }

    #[test]
    fn rewrites_both_polarities_and_removes_definition_and_indices() {
        let mut formula = setup();
        process::<Empty>(&mut formula, &mut None);
        assert!(formula.extensions.definition(&Literal::new(3)).is_none());
        assert!(
            formula
                .extensions
                .substitute(&Literal::new(1), &Literal::new(2))
                .is_none()
        );
        assert!(formula.is_retired_extension_variable(3));
        assert_eq!(formula.stats.preference_passes, 1);
        assert_eq!(formula.stats.preference_candidates, 1);
        assert_eq!(formula.stats.preference_extensions_retired, 1);
        assert_eq!(formula.stats.preference_clauses_removed, 5);
        assert_eq!(formula.stats.preference_clauses_added, 3);
        assert_eq!(formula.stats.preference_learned_positive_dropped, 0);
        formula.collect_garbage(None);
        let clauses = live(&formula);
        assert!(clauses.contains(&vec![4, -2, -1]), "{clauses:?}");
        assert!(clauses.contains(&vec![5, 1]));
        assert!(clauses.contains(&vec![5, 2]));
        assert!(
            clauses
                .iter()
                .all(|clause| !clause.contains(&3) && !clause.contains(&-3))
        );
        assert_eq!(formula.occurrence_of(&Literal::new(3)).count(), 0);
        assert_eq!(formula.occurrence_of(&Literal::new(-3)).count(), 0);
    }

    #[test]
    fn drops_learned_positive_but_not_permanent_positive() {
        let mut formula = setup();
        formula.get_clause_at_idx_mut(4).lbd = 3;
        process::<Empty>(&mut formula, &mut None);
        assert_eq!(formula.stats.preference_learned_positive_dropped, 1);
        assert_eq!(formula.stats.preference_clauses_added, 1);
        formula.collect_garbage(None);
        let clauses = live(&formula);
        assert!(!clauses.contains(&vec![5, 1]));
        assert!(!clauses.contains(&vec![5, 2]));
        assert!(clauses.contains(&vec![4, -2, -1]), "{clauses:?}");
    }

    #[test]
    fn protects_dependent_extensions() {
        let mut formula = setup();
        formula
            .extensions
            .add_and_definition(vec![Literal::new(3), Literal::new(4)], &Literal::new(5));
        process::<Empty>(&mut formula, &mut None);
        assert_eq!(formula.stats.preference_skipped_dependents, 1);
        assert!(formula.extensions.definition(&Literal::new(3)).is_some());
    }

    #[test]
    fn protects_assigned_extensions() {
        let mut formula = setup();
        formula.assignment.assign_literal(Literal::new(3));
        process::<Empty>(&mut formula, &mut None);
        assert_eq!(formula.stats.preference_skipped_assigned, 1);
        assert!(formula.extensions.definition(&Literal::new(3)).is_some());
    }

    #[test]
    fn rewinds_root_reasons_and_repropagates_both_polarities() {
        for (unit, root_z, implied) in [
            (vec![vec![1], vec![2]], true, 4),
            (vec![vec![-1]], false, 5),
        ] {
            let mut formula = setup();
            for literals in unit {
                formula.add_clause_unchecked::<Empty>(
                    Clause::from_literals(literals.into_iter().map(Literal::new).collect(), -1),
                    &mut None,
                );
            }
            let mut history = History::new();
            assert!(!formula.rebuild_root_implications(&mut history));
            assert_eq!(formula.assignment.get_value(3), Some(root_z));
            assert_eq!(formula.assignment.get_value(implied), Some(true));
            assert!(
                formula
                    .get_clauses()
                    .any(|(_, clause)| clause.lock_count > 0)
            );

            assert!(!process_at_restart::<Empty>(
                &mut formula,
                &mut history,
                &mut None
            ));
            assert!(formula.is_retired_extension_variable(3));
            assert_eq!(formula.assignment.get_value(3), None);
            assert_eq!(formula.assignment.get_value(implied), Some(true));
            assert_eq!(formula.stats.preference_root_rebuilds, 1);
            assert_eq!(formula.stats.preference_root_assigned_unique, 1);
            assert_eq!(
                formula.stats.preference_root_assigned_true,
                u64::from(root_z)
            );
            assert_eq!(
                formula.stats.preference_root_assigned_false,
                u64::from(!root_z)
            );
            assert_eq!(formula.stats.preference_extensions_retired, 1);
            assert_eq!(history.active_reason_indices().len() > 0, true);
            assert!(history.active_reason_indices().into_iter().all(|index| {
                !formula.is_clause_garbage(index) && formula.get_clause_at_idx(index).lock_count > 0
            }));
            assert!(formula.get_clauses().all(|(_, clause)| {
                clause
                    .get_literals()
                    .iter()
                    .all(|lit| lit.get_index().unsigned_abs() != 3)
            }));
            formula.collect_garbage(Some(&mut history));
        }
    }

    #[test]
    fn rewrites_root_unit_extensions_and_replays_new_units() {
        let mut formula = setup();
        formula.add_clause_unchecked::<Empty>(
            Clause::from_literals(vec![Literal::new(3)], -1),
            &mut None,
        );
        let mut history = History::new();
        assert!(!formula.rebuild_root_implications(&mut history));
        assert_eq!(formula.assignment.get_value(3), Some(true));
        assert!(!process_at_restart::<Empty>(
            &mut formula,
            &mut history,
            &mut None
        ));
        assert_eq!(formula.assignment.get_value(3), None);
        assert_eq!(formula.assignment.get_value(1), Some(true));
        assert_eq!(formula.assignment.get_value(2), Some(true));
        assert_eq!(formula.stats.preference_skipped_unsafe, 0);
        assert!(formula.get_clauses().all(|(_, clause)| {
            clause
                .get_literals()
                .iter()
                .all(|lit| lit.get_index().unsigned_abs() != 3)
        }));
    }

    #[test]
    fn leaves_unrecorded_root_assignments_untouched() {
        let mut formula = setup();
        formula.assignment.assign_literal(Literal::new(3));
        let mut history = History::new();
        assert!(!process_at_restart::<Empty>(
            &mut formula,
            &mut history,
            &mut None
        ));
        assert_eq!(formula.stats.preference_root_assigned_unique, 1);
        assert_eq!(formula.stats.preference_root_rebuilds, 0);
        assert_eq!(formula.stats.preference_skipped_assigned, 1);
    }

    #[test]
    fn preserves_reasonless_root_facts() {
        let mut formula = setup();
        let mut history = History::new();
        assert!(matches!(
            formula.assign_implication(Literal::new(3), &mut history, None),
            crate::formula::assignment::AssignResult::Assigned(_)
        ));
        assert!(!process_at_restart::<Empty>(
            &mut formula,
            &mut history,
            &mut None
        ));
        assert_eq!(formula.assignment.get_value(3), Some(true));
        assert_eq!(formula.stats.preference_root_rebuilds, 0);
        assert_eq!(formula.stats.preference_skipped_assigned, 1);
    }

    #[test]
    fn retires_low_preference_dependents_before_inputs() {
        let mut formula = setup();
        let dependent = formula.add_literal();
        assert_eq!(dependent.get_index(), 6);
        formula
            .extensions
            .add_substitution(&Literal::new(3), &Literal::new(4), &dependent);
        formula
            .stats
            .ges_extension_preference
            .insert(-6, ("dip".into(), 1, 0));
        process::<Empty>(&mut formula, &mut None);
        assert!(formula.extensions.is_empty());
        assert!(formula.is_retired_extension_variable(6));
        assert!(formula.is_retired_extension_variable(3));
    }

    #[test]
    fn skips_locked_occurrences() {
        let mut formula = setup();
        formula.get_clause_at_idx_mut(3).increment_lock_count();
        process::<Empty>(&mut formula, &mut None);
        assert_eq!(formula.stats.preference_skipped_unsafe, 1);
        assert!(formula.extensions.definition(&Literal::new(3)).is_some());
        assert_eq!(formula.live_clause_count(), 5);
    }

    #[test]
    fn proof_logs_replacements_before_removing_their_sources() {
        let mut formula = setup();
        formula.add_literal();
        formula.add_literal();
        for clause in [[-4, 6], [-4, -6], [-5, 7], [-5, -7]] {
            formula.add_clause_unchecked::<Empty>(
                Clause::from_literals(clause.map(Literal::new).to_vec(), -1),
                &mut None,
            );
        }
        let mut proof = Vec::new();
        {
            let mut logger = Some(DratLogger::new(&mut proof));
            process(&mut formula, &mut logger);
            logger
                .as_mut()
                .unwrap()
                .log_add(&[Literal::new(-4)])
                .unwrap();
            logger
                .as_mut()
                .unwrap()
                .log_add(&[Literal::new(-5)])
                .unwrap();
            logger.as_mut().unwrap().log_empty_clause().unwrap();
        }
        let proof_text = String::from_utf8(proof).unwrap();
        let first_delete = proof_text
            .lines()
            .position(|line| line.starts_with("d "))
            .unwrap();
        assert!(first_delete > 0);
        assert!(
            proof_text
                .lines()
                .take(first_delete)
                .all(|line| !line.starts_with("d "))
        );
        assert_eq!(proof_text.lines().last(), Some("0"));
        if let Some(directory) = std::env::var_os("PREFERENCE_PROOF_DIR") {
            let directory = std::path::PathBuf::from(directory);
            std::fs::write(
                directory.join("preference.cnf"),
                "p cnf 7 9\n-3 1 0\n-3 2 0\n3 -1 -2 0\n-3 4 0\n3 5 0\n-4 6 0\n-4 -6 0\n-5 7 0\n-5 -7 0\n",
            )
            .unwrap();
            std::fs::write(directory.join("preference.drat"), proof_text).unwrap();
        }
    }

    #[test]
    fn removes_tautological_occurrences_without_adding_constraints() {
        let mut formula = setup();
        let clause =
            Clause::from_literals(vec![Literal::new(3), Literal::new(-3), Literal::new(5)], -1);
        formula.add_clause_unchecked::<Empty>(clause, &mut None);
        process::<Empty>(&mut formula, &mut None);
        formula.collect_garbage(None);
        assert!(
            live(&formula)
                .iter()
                .all(|clause| !clause.contains(&3) && !clause.contains(&-3))
        );
    }
}
