use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::HashMap;
use std::io::Write;

// CaDiCaL-FX's default factor bound requires a reduction of at least one clause.
const FACTOR_BOUND: usize = 1;
const GATE_DEFINITION_CLAUSES: usize = 4;
const MIN_GATE_MATCHES: usize = GATE_DEFINITION_CLAUSES + FACTOR_BOUND;

pub fn process<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    mut history: Option<&mut History>,
) -> PyResult<()> {
    let initial_clause_limit = formula.get_clauses().len();
    let initial_variable_limit = formula.assignment.len();
    let index = AndIndex::new(formula, initial_clause_limit, initial_variable_limit);
    let schedule = initial_literal_schedule(formula, initial_clause_limit, initial_variable_limit);
    let mut pending_deleted = vec![false; initial_clause_limit];
    let mut deletion_indices = Vec::new();
    let mut gate_variables_seen = vec![false; initial_variable_limit];
    let mut and_workspace = AndWorkspace::new(initial_variable_limit, initial_clause_limit);
    let mut gate_workspace = GateWorkspace::new(initial_variable_limit, initial_clause_limit);

    for start in schedule {
        let search_result = (|| {
            check_signal(&mut signal)?;
            let and_candidate = build_and_candidate(
                &index,
                start,
                &pending_deleted,
                &mut and_workspace,
                &mut signal,
            )?;

            let variable = start.unsigned_abs() as usize;
            let gate_candidate = if !gate_variables_seen[variable] {
                gate_variables_seen[variable] = true;
                if formula.assignment.get_value(variable).is_none()
                    && has_live_eligible_occurrence(
                        formula,
                        -start,
                        initial_clause_limit,
                        &pending_deleted,
                    )
                {
                    let pairs = extract_pairs(
                        formula,
                        initial_clause_limit,
                        &pending_deleted,
                        start,
                        &mut gate_workspace,
                        &mut signal,
                    )?;
                    prefilter_candidates(&mut gate_workspace);
                    group_pairs(
                        &pairs,
                        start,
                        initial_clause_limit,
                        &mut gate_workspace,
                        &mut signal,
                    )?
                } else {
                    None
                }
            } else {
                None
            };

            Ok(match (and_candidate, gate_candidate) {
                (Some(and_candidate), Some(gate_candidate)) => {
                    if gate_candidate.clause_saving >= and_candidate.clause_saving {
                        Some(FactorCandidate::Gate(gate_candidate))
                    } else {
                        Some(FactorCandidate::And(and_candidate))
                    }
                }
                (Some(candidate), None) => Some(FactorCandidate::And(candidate)),
                (None, Some(candidate)) => Some(FactorCandidate::Gate(candidate)),
                (None, None) => None,
            })
        })();

        let candidate = match search_result {
            Ok(candidate) => candidate,
            Err(error) => {
                finalize_pending_deletions(
                    formula,
                    logger,
                    history.as_deref_mut(),
                    &pending_deleted,
                    &mut deletion_indices,
                );
                return Err(error);
            }
        };

        if let Some(candidate) = candidate {
            apply_factorization_candidate(
                formula,
                logger,
                &index,
                &mut pending_deleted,
                &mut deletion_indices,
                candidate,
            );
        }
    }

    finalize_pending_deletions(
        formula,
        logger,
        history.as_deref_mut(),
        &pending_deleted,
        &mut deletion_indices,
    );
    Ok(())
}

fn initial_literal_schedule(
    formula: &Formula,
    initial_clause_limit: usize,
    initial_variable_limit: usize,
) -> Vec<i32> {
    let mut schedule = Vec::new();
    for variable in 1..initial_variable_limit {
        for literal in [variable as i32, -(variable as i32)] {
            let count = formula
                .occurrence_of(&Literal::new(literal))
                .iter()
                .copied()
                .filter(|&idx| {
                    idx < initial_clause_limit
                        && factor_eligible_clause(&formula.get_clauses()[idx])
                })
                .count();
            if count > 1 {
                schedule.push((literal, count));
            }
        }
    }
    schedule.sort_by(|(lit_a, count_a), (lit_b, count_b)| {
        count_a
            .cmp(count_b)
            .then_with(|| literal_tie_key(*lit_a).cmp(&literal_tie_key(*lit_b)))
    });
    schedule.into_iter().map(|(literal, _)| literal).collect()
}

fn has_live_eligible_occurrence(
    formula: &Formula,
    literal: i32,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
) -> bool {
    formula
        .occurrence_of(&Literal::new(literal))
        .iter()
        .copied()
        .any(|idx| {
            idx < initial_clause_limit
                && !pending_deleted[idx]
                && factor_eligible_clause(&formula.get_clauses()[idx])
        })
}

/// Algorithm 1 from the paper: pair clauses containing `target` with clauses
/// containing `-target` that have the same size and exactly one other
/// unmatched literal on either side.
fn extract_pairs(
    formula: &Formula,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
    target: i32,
    workspace: &mut GateWorkspace,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Vec<ExtractedPair>> {
    let mut pairs = Vec::new();
    workspace.begin_variable_counts();
    let target_occurrences = formula.occurrence_of(&Literal::new(target));
    let opposite_occurrences = formula.occurrence_of(&Literal::new(-target));

    for &first_clause in target_occurrences {
        check_signal(signal)?;
        if !live_gate_clause(formula, first_clause, initial_clause_limit, pending_deleted) {
            continue;
        }
        let first = &formula.get_clauses()[first_clause];
        if first.len() < 3 {
            continue;
        }

        for &second_clause in opposite_occurrences {
            check_signal(signal)?;
            if !live_gate_clause(
                formula,
                second_clause,
                initial_clause_limit,
                pending_deleted,
            ) {
                continue;
            }
            let second = &formula.get_clauses()[second_clause];
            if second.len() != first.len() || second.len() < 3 {
                continue;
            }

            let Some((first_branch, second_branch)) =
                exact_pair_differences(first, second, target, &mut workspace.literal_marks)
            else {
                continue;
            };

            workspace.record_variable(second_branch.unsigned_abs() as usize);
            pairs.push(ExtractedPair {
                first_clause,
                second_clause,
                first_branch,
                second_branch,
            });
        }
    }

    Ok(pairs)
}

fn live_gate_clause(
    formula: &Formula,
    clause_idx: usize,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
) -> bool {
    clause_idx < initial_clause_limit
        && !pending_deleted[clause_idx]
        && factor_eligible_clause(&formula.get_clauses()[clause_idx])
}

fn exact_pair_differences(
    first: &Clause,
    second: &Clause,
    target: i32,
    marks: &mut LiteralMarks,
) -> Option<(i32, i32)> {
    let first_stamp = marks.next_stamp();
    for literal in first {
        marks.marks[signed_literal_index(literal.get_index())] = first_stamp;
    }

    let mut second_branch = None;
    let mut saw_opposite_target = false;
    let mut second_differences = 0usize;
    for literal in second {
        let literal = literal.get_index();
        if marks.marks[signed_literal_index(literal)] == first_stamp {
            continue;
        }
        second_differences += 1;
        if literal == -target {
            saw_opposite_target = true;
        } else if second_branch.replace(literal).is_some() {
            return None;
        }
    }
    if second_differences != 2 || !saw_opposite_target {
        return None;
    }

    let second_stamp = marks.next_stamp();
    for literal in second {
        marks.marks[signed_literal_index(literal.get_index())] = second_stamp;
    }

    let mut first_branch = None;
    let mut saw_target = false;
    let mut first_differences = 0usize;
    for literal in first {
        let literal = literal.get_index();
        if marks.marks[signed_literal_index(literal)] == second_stamp {
            continue;
        }
        first_differences += 1;
        if literal == target {
            saw_target = true;
        } else if first_branch.replace(literal).is_some() {
            return None;
        }
    }
    if first_differences != 2 || !saw_target {
        return None;
    }

    Some((first_branch?, second_branch?))
}

/// Algorithm 2 from the paper: discard variables whose phase-oblivious pair
/// count cannot meet the factor bound after paying for the four gate clauses.
fn prefilter_candidates(workspace: &mut GateWorkspace) {
    let candidate_stamp = workspace.next_candidate_stamp();
    for position in 0..workspace.counted_variables.len() {
        let variable = workspace.counted_variables[position];
        if workspace.variable_counts[variable] >= MIN_GATE_MATCHES {
            workspace.candidate_variables[variable] = candidate_stamp;
        }
    }
}

/// Algorithm 3 from the paper: normalize simultaneous polarity flips, select
/// the largest group, and claim each physical clause at most once.
fn group_pairs(
    pairs: &[ExtractedPair],
    target: i32,
    initial_clause_limit: usize,
    workspace: &mut GateWorkspace,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Option<GateCandidate>> {
    workspace.group_entries.clear();
    for (pair_idx, pair) in pairs.iter().enumerate() {
        check_signal(signal)?;
        let variable = pair.second_branch.unsigned_abs() as usize;
        if workspace.candidate_variables[variable] != workspace.candidate_stamp {
            continue;
        }
        let normalized_first = if pair.second_branch.is_positive() {
            pair.first_branch
        } else {
            -pair.first_branch
        };
        workspace
            .group_entries
            .push((variable as u32, normalized_first, pair_idx));
    }
    workspace
        .group_entries
        .sort_unstable_by_key(|&(variable, literal, _)| (variable, literal_tie_key(literal)));

    // Rank groups by physically disjoint matches rather than raw extracted
    // pairs. Duplicate clauses otherwise create a Cartesian product that can
    // hide another profitable group.
    let mut best_group = None;
    let mut position = 0;
    while position < workspace.group_entries.len() {
        let (variable, literal, _) = workspace.group_entries[position];
        let mut end = position + 1;
        while end < workspace.group_entries.len()
            && workspace.group_entries[end].0 == variable
            && workspace.group_entries[end].1 == literal
        {
            end += 1;
        }

        let claim_stamp = workspace.next_claim_stamp();
        let mut count = 0;
        for entry in &workspace.group_entries[position..end] {
            let pair = pairs[entry.2];
            if workspace.claimed_clauses[pair.first_clause] == claim_stamp
                || workspace.claimed_clauses[pair.second_clause] == claim_stamp
            {
                continue;
            }
            workspace.claimed_clauses[pair.first_clause] = claim_stamp;
            workspace.claimed_clauses[pair.second_clause] = claim_stamp;
            count += 1;
        }

        if best_group.is_none_or(|(best_count, best_variable, best_literal)| {
            group_is_better(
                count,
                variable,
                literal,
                best_count,
                best_variable,
                best_literal,
            )
        }) {
            best_group = Some((count, variable, literal));
        }
        position = end;
    }

    let Some((best_count, best_variable, best_second)) = best_group else {
        return Ok(None);
    };
    if best_count < MIN_GATE_MATCHES {
        return Ok(None);
    }

    let best_third = best_variable as i32;
    let claim_stamp = workspace.next_claim_stamp();
    let mut matches = Vec::with_capacity(best_count);
    for pair in pairs {
        check_signal(signal)?;
        let output_positive =
            if pair.second_branch == best_third && pair.first_branch == best_second {
                false
            } else if pair.second_branch == -best_third && pair.first_branch == -best_second {
                true
            } else {
                continue;
            };

        if workspace.claimed_clauses[pair.first_clause] == claim_stamp
            || workspace.claimed_clauses[pair.second_clause] == claim_stamp
        {
            continue;
        }
        workspace.claimed_clauses[pair.first_clause] = claim_stamp;
        workspace.claimed_clauses[pair.second_clause] = claim_stamp;
        matches.push(GateMatch {
            first_clause: pair.first_clause,
            second_clause: pair.second_clause,
            output_positive,
        });
    }

    let clause_saving = matches.len() as isize - GATE_DEFINITION_CLAUSES as isize;
    if clause_saving < FACTOR_BOUND as isize {
        return Ok(None);
    }

    debug_assert!(matches.iter().all(|gate_match| {
        gate_match.first_clause < initial_clause_limit
            && gate_match.second_clause < initial_clause_limit
    }));

    Ok(Some(GateCandidate {
        target,
        second: best_second,
        third: best_third,
        matches,
        clause_saving,
    }))
}

fn group_is_better(
    count: usize,
    variable: u32,
    literal: i32,
    best_count: usize,
    best_variable: u32,
    best_literal: i32,
) -> bool {
    let is_ite = literal != -(variable as i32);
    let best_is_ite = best_literal != -(best_variable as i32);
    count > best_count
        || (count == best_count
            && (is_ite > best_is_ite
                || (is_ite == best_is_ite
                    && (variable, literal_tie_key(literal))
                        < (best_variable, literal_tie_key(best_literal)))))
}

fn build_and_candidate(
    index: &AndIndex,
    start: i32,
    pending_deleted: &[bool],
    workspace: &mut AndWorkspace,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Option<AndCandidate>> {
    let start_index = signed_literal_index(start);
    let Some(start_partials) = index.literal_to_partials.get(start_index) else {
        return Ok(None);
    };

    let selected_stamp = workspace.next_selected_stamp();
    workspace.selected_literals[start_index] = selected_stamp;
    let mut literals = vec![start];
    let mut partial_ids = start_partials
        .iter()
        .copied()
        .filter(|&partial_id| index.has_live_clause_for(start, partial_id, pending_deleted))
        .collect::<Vec<_>>();
    let mut touched_literals = Vec::new();
    let mut best = None;

    loop {
        check_signal(signal)?;
        let count_stamp = workspace.next_count_stamp();
        touched_literals.clear();
        for &partial_id in &partial_ids {
            for &candidate_lit in &index.partial_to_literals[partial_id] {
                let candidate_index = signed_literal_index(candidate_lit);
                if workspace.selected_literals[candidate_index] == selected_stamp
                    || !index.has_live_clause_for(candidate_lit, partial_id, pending_deleted)
                {
                    continue;
                }
                if workspace.count_stamps[candidate_index] != count_stamp {
                    workspace.count_stamps[candidate_index] = count_stamp;
                    workspace.literal_counts[candidate_index] = 0;
                    touched_literals.push(candidate_lit);
                }
                workspace.literal_counts[candidate_index] += 1;
            }
        }

        let Some((next_lit, remaining_partials)) =
            choose_next_literal(&touched_literals, &workspace.literal_counts)
        else {
            break;
        };
        if remaining_partials <= 1 {
            break;
        }

        workspace.selected_literals[signed_literal_index(next_lit)] = selected_stamp;
        literals.push(next_lit);
        partial_ids
            .retain(|&partial_id| index.has_live_clause_for(next_lit, partial_id, pending_deleted));

        let deleted_clauses =
            index.live_source_count(&literals, &partial_ids, pending_deleted, workspace);
        let clause_saving =
            deleted_clauses as isize - (literals.len() + partial_ids.len()) as isize;

        // The best quotient can occur after a temporary plateau or decline, so
        // keep extending the greedy factor chain and remember its best prefix.
        if best
            .as_ref()
            .is_none_or(|candidate: &AndCandidate| clause_saving > candidate.clause_saving)
        {
            best = Some(AndCandidate {
                literals: literals.clone(),
                partial_ids: partial_ids.clone(),
                clause_saving,
            });
        }
    }

    Ok(best.filter(|candidate| candidate.clause_saving >= FACTOR_BOUND as isize))
}

fn choose_next_literal(literals: &[i32], counts: &[usize]) -> Option<(i32, usize)> {
    let mut best = None;
    for &literal in literals {
        let count = counts[signed_literal_index(literal)];
        if count == 0 {
            continue;
        }
        if best.is_none_or(|(best_literal, best_count)| {
            count > best_count
                || (count == best_count && literal_tie_key(literal) < literal_tie_key(best_literal))
        }) {
            best = Some((literal, count));
        }
    }
    best
}

fn apply_factorization_candidate<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    index: &AndIndex,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
    candidate: FactorCandidate,
) {
    match candidate {
        FactorCandidate::And(candidate) => apply_and_candidate(
            formula,
            logger,
            index,
            pending_deleted,
            deletion_indices,
            candidate,
        ),
        FactorCandidate::Gate(candidate) => apply_gate_candidate(
            formula,
            logger,
            pending_deleted,
            deletion_indices,
            candidate,
        ),
    }
}

fn apply_and_candidate<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    index: &AndIndex,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
    candidate: AndCandidate,
) {
    let z = formula.add_literal();
    formula.stats.add_bva_literal();

    for &partial_id in &candidate.partial_ids {
        let partial = &index.partials[partial_id];
        let mut literals = Vec::with_capacity(partial.len() + 1);
        literals.push(z.clone());
        literals.extend(partial.iter().map(|&literal| Literal::new(literal)));
        formula.add_clause_unchecked(factor_clause(literals), logger);
    }
    for &literal in &candidate.literals {
        formula.add_clause_unchecked(
            factor_clause(vec![z.negated(), Literal::new(literal)]),
            logger,
        );
    }

    for &literal in &candidate.literals {
        for &partial_id in &candidate.partial_ids {
            let cell_id = index
                .cell_id(literal, partial_id)
                .expect("selected AND grid has every cell");
            for &clause_idx in &index.cells[cell_id] {
                claim_clause(clause_idx, pending_deleted, deletion_indices);
            }
        }
    }
}

fn apply_gate_candidate<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
    candidate: GateCandidate,
) {
    let z = formula.add_literal();
    formula.stats.add_bva_literal();

    // x <-> ITE(target, -third, -second). Every resolvent between a
    // positive-x and a negative-x definition clause is tautological, so these
    // clauses are valid blocked/RAT additions in this order.
    let definitions = [
        vec![
            z.clone(),
            Literal::new(candidate.target),
            Literal::new(candidate.second),
        ],
        vec![
            z.clone(),
            Literal::new(-candidate.target),
            Literal::new(candidate.third),
        ],
        vec![
            z.negated(),
            Literal::new(candidate.target),
            Literal::new(-candidate.second),
        ],
        vec![
            z.negated(),
            Literal::new(-candidate.target),
            Literal::new(-candidate.third),
        ],
    ];
    for definition in definitions {
        formula.add_clause_unchecked(factor_clause(definition), logger);
    }

    for gate_match in &candidate.matches {
        let output = if gate_match.output_positive {
            z.clone()
        } else {
            z.negated()
        };
        let first_branch = if gate_match.output_positive {
            -candidate.second
        } else {
            candidate.second
        };
        let first_source = &formula.get_clauses()[gate_match.first_clause];
        let mut quotient = Vec::with_capacity(first_source.len() - 1);
        quotient.push(output.clone());
        quotient.extend(first_source.iter().filter_map(|literal| {
            let literal_index = literal.get_index();
            (literal_index != candidate.target && literal_index != first_branch)
                .then(|| literal.clone())
        }));

        // The paper records these two resolvents as proof-only clauses. They
        // make the quotient RUP even after quotients of the opposite output
        // polarity have already been added to the formula.
        let proof_intermediates = logger.is_some().then(|| {
            let mut first = Vec::with_capacity(quotient.len() + 1);
            let mut second = Vec::with_capacity(quotient.len() + 1);
            first.push(output.clone());
            first.push(Literal::new(candidate.target));
            second.push(output.clone());
            second.push(Literal::new(-candidate.target));
            first.extend(quotient.iter().skip(1).cloned());
            second.extend(quotient.iter().skip(1).cloned());
            (first, second)
        });
        if let (Some(log), Some((first, second))) = (logger.as_mut(), proof_intermediates.as_ref())
        {
            let _ = log.log_add(first);
            let _ = log.log_add(second);
        }

        formula.add_clause_unchecked(factor_clause(quotient), logger);

        if let (Some(log), Some((first, second))) = (logger.as_mut(), proof_intermediates.as_ref())
        {
            let _ = log.log_delete(first);
            let _ = log.log_delete(second);
        }
    }

    // Source clauses remain available until every proof-safe addition above is
    // complete, but become invisible to all later searches in this pass.
    for gate_match in &candidate.matches {
        claim_clause(gate_match.first_clause, pending_deleted, deletion_indices);
        claim_clause(gate_match.second_clause, pending_deleted, deletion_indices);
    }
}

fn claim_clause(
    clause_idx: usize,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
) {
    if !pending_deleted[clause_idx] {
        pending_deleted[clause_idx] = true;
        deletion_indices.push(clause_idx);
    }
}

fn finalize_pending_deletions<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    history: Option<&mut History>,
    pending_deleted: &[bool],
    deletion_indices: &mut Vec<usize>,
) {
    if deletion_indices.is_empty() {
        return;
    }
    deletion_indices.sort_unstable();

    debug_assert_eq!(
        pending_deleted.iter().filter(|&&pending| pending).count(),
        deletion_indices.len()
    );
    for &idx in deletion_indices.iter() {
        debug_assert!(pending_deleted[idx]);
        formula.record_clause_removal(idx);
    }
    let old_to_new = formula.delete_clauses(deletion_indices, logger);
    if let Some(history) = history {
        history.remap_clause_indices(&old_to_new);
    }
}

fn factor_clause(literals: Vec<Literal>) -> Clause {
    let mut clause = Clause::from_literals(literals, 0);
    clause.bva_generated = true;
    clause
}

fn check_signal(signal: &mut Option<(Python<'_>, &mut u64)>) -> PyResult<()> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }
    Ok(())
}

fn literal_tie_key(literal: i32) -> (u32, bool) {
    (literal.unsigned_abs(), literal.is_negative())
}

fn signed_literal_index(literal: i32) -> usize {
    let variable = literal.unsigned_abs() as usize;
    if literal.is_negative() {
        variable * 2
    } else {
        variable * 2 - 1
    }
}

fn sorted_without(sorted_clause: &[i32], literal_to_remove: i32) -> Vec<i32> {
    sorted_clause
        .iter()
        .copied()
        .filter(|&literal| literal != literal_to_remove)
        .collect()
}

fn is_tautological(sorted_clause: &[i32]) -> bool {
    sorted_clause
        .iter()
        .any(|&literal| sorted_clause.binary_search(&-literal).is_ok())
}

fn factor_eligible_clause(clause: &Clause) -> bool {
    clause.lock_count == 0 && clause.len() >= 2 && (clause.lbd != 0 || clause.bva_generated)
}

enum FactorCandidate {
    And(AndCandidate),
    Gate(GateCandidate),
}

#[derive(Clone, Copy)]
struct ExtractedPair {
    first_clause: usize,
    second_clause: usize,
    first_branch: i32,
    second_branch: i32,
}

struct GateMatch {
    first_clause: usize,
    second_clause: usize,
    output_positive: bool,
}

struct GateCandidate {
    target: i32,
    second: i32,
    third: i32,
    matches: Vec<GateMatch>,
    clause_saving: isize,
}

struct AndCandidate {
    literals: Vec<i32>,
    partial_ids: Vec<usize>,
    clause_saving: isize,
}

struct AndIndex {
    partials: Vec<Vec<i32>>,
    partial_to_literals: Vec<Vec<i32>>,
    partial_to_cells: Vec<Vec<usize>>,
    literal_to_partials: Vec<Vec<usize>>,
    cells: Vec<Vec<usize>>,
}

impl AndIndex {
    fn new(formula: &Formula, initial_clause_limit: usize, initial_variable_limit: usize) -> Self {
        let dense_literal_limit = initial_variable_limit.saturating_mul(2).saturating_add(1);
        let mut partial_ids = HashMap::<Vec<i32>, usize>::new();
        let mut cell_ids = HashMap::<(usize, usize), usize>::new();
        let mut partial_to_literals = Vec::<Vec<i32>>::new();
        let mut partial_to_cells = Vec::<Vec<usize>>::new();
        let mut literal_to_partials = vec![Vec::new(); dense_literal_limit];
        let mut cells = Vec::<Vec<usize>>::new();

        for (clause_idx, clause) in formula
            .get_clauses()
            .iter()
            .take(initial_clause_limit)
            .enumerate()
        {
            if !factor_eligible_clause(clause) {
                continue;
            }
            let sorted_clause = clause.sorted_literal_indices();
            if is_tautological(&sorted_clause) {
                continue;
            }

            for &literal in &sorted_clause {
                let partial = sorted_without(&sorted_clause, literal);
                let partial_id = if let Some(&partial_id) = partial_ids.get(&partial) {
                    partial_id
                } else {
                    let partial_id = partial_ids.len();
                    partial_ids.insert(partial, partial_id);
                    partial_to_literals.push(Vec::new());
                    partial_to_cells.push(Vec::new());
                    partial_id
                };

                let literal_index = signed_literal_index(literal);
                let cell_id = if let Some(&cell_id) = cell_ids.get(&(literal_index, partial_id)) {
                    cell_id
                } else {
                    let cell_id = cells.len();
                    cell_ids.insert((literal_index, partial_id), cell_id);
                    cells.push(Vec::new());
                    partial_to_literals[partial_id].push(literal);
                    partial_to_cells[partial_id].push(cell_id);
                    literal_to_partials[literal_index].push(partial_id);
                    cell_id
                };
                cells[cell_id].push(clause_idx);
            }
        }

        let mut partials = vec![Vec::new(); partial_ids.len()];
        for (partial, partial_id) in partial_ids {
            partials[partial_id] = partial;
        }

        for partial_id in 0..partials.len() {
            let literals = std::mem::take(&mut partial_to_literals[partial_id]);
            let cell_list = std::mem::take(&mut partial_to_cells[partial_id]);
            let mut adjacency = literals.into_iter().zip(cell_list).collect::<Vec<_>>();
            adjacency.sort_unstable_by_key(|(literal, _)| literal_tie_key(*literal));
            for (literal, cell_id) in adjacency {
                partial_to_literals[partial_id].push(literal);
                partial_to_cells[partial_id].push(cell_id);
            }
        }
        for partials in &mut literal_to_partials {
            partials.sort_unstable();
        }

        Self {
            partials,
            partial_to_literals,
            partial_to_cells,
            literal_to_partials,
            cells,
        }
    }

    fn cell_id(&self, literal: i32, partial_id: usize) -> Option<usize> {
        let position = self.partial_to_literals[partial_id]
            .binary_search_by_key(&literal_tie_key(literal), |candidate| {
                literal_tie_key(*candidate)
            })
            .ok()?;
        Some(self.partial_to_cells[partial_id][position])
    }

    fn has_live_clause_for(
        &self,
        literal: i32,
        partial_id: usize,
        pending_deleted: &[bool],
    ) -> bool {
        self.cell_id(literal, partial_id).is_some_and(|cell_id| {
            self.cells[cell_id]
                .iter()
                .any(|&clause_idx| !pending_deleted[clause_idx])
        })
    }

    fn live_source_count(
        &self,
        literals: &[i32],
        partial_ids: &[usize],
        pending_deleted: &[bool],
        workspace: &mut AndWorkspace,
    ) -> usize {
        let stamp = workspace.next_clause_stamp();
        let mut count = 0;
        for &literal in literals {
            for &partial_id in partial_ids {
                let Some(cell_id) = self.cell_id(literal, partial_id) else {
                    continue;
                };
                for &clause_idx in &self.cells[cell_id] {
                    if !pending_deleted[clause_idx] && workspace.clause_stamps[clause_idx] != stamp
                    {
                        workspace.clause_stamps[clause_idx] = stamp;
                        count += 1;
                    }
                }
            }
        }
        count
    }
}

struct LiteralMarks {
    marks: Vec<u32>,
    stamp: u32,
}

impl LiteralMarks {
    fn new(initial_variable_limit: usize) -> Self {
        Self {
            marks: vec![0; initial_variable_limit.saturating_mul(2).saturating_add(1)],
            stamp: 0,
        }
    }

    fn next_stamp(&mut self) -> u32 {
        next_dense_stamp(&mut self.stamp, &mut self.marks)
    }
}

struct AndWorkspace {
    literal_counts: Vec<usize>,
    count_stamps: Vec<u32>,
    count_stamp: u32,
    selected_literals: Vec<u32>,
    selected_stamp: u32,
    clause_stamps: Vec<u32>,
    clause_stamp: u32,
}

impl AndWorkspace {
    fn new(initial_variable_limit: usize, initial_clause_limit: usize) -> Self {
        let dense_literal_limit = initial_variable_limit.saturating_mul(2).saturating_add(1);
        Self {
            literal_counts: vec![0; dense_literal_limit],
            count_stamps: vec![0; dense_literal_limit],
            count_stamp: 0,
            selected_literals: vec![0; dense_literal_limit],
            selected_stamp: 0,
            clause_stamps: vec![0; initial_clause_limit],
            clause_stamp: 0,
        }
    }

    fn next_count_stamp(&mut self) -> u32 {
        next_dense_stamp(&mut self.count_stamp, &mut self.count_stamps)
    }

    fn next_selected_stamp(&mut self) -> u32 {
        next_dense_stamp(&mut self.selected_stamp, &mut self.selected_literals)
    }

    fn next_clause_stamp(&mut self) -> u32 {
        next_dense_stamp(&mut self.clause_stamp, &mut self.clause_stamps)
    }
}

struct GateWorkspace {
    literal_marks: LiteralMarks,
    variable_counts: Vec<usize>,
    variable_count_stamps: Vec<u32>,
    variable_count_stamp: u32,
    counted_variables: Vec<usize>,
    candidate_variables: Vec<u32>,
    candidate_stamp: u32,
    group_entries: Vec<(u32, i32, usize)>,
    claimed_clauses: Vec<u32>,
    claim_stamp: u32,
}

impl GateWorkspace {
    fn new(initial_variable_limit: usize, initial_clause_limit: usize) -> Self {
        Self {
            literal_marks: LiteralMarks::new(initial_variable_limit),
            variable_counts: vec![0; initial_variable_limit],
            variable_count_stamps: vec![0; initial_variable_limit],
            variable_count_stamp: 0,
            counted_variables: Vec::new(),
            candidate_variables: vec![0; initial_variable_limit],
            candidate_stamp: 0,
            group_entries: Vec::new(),
            claimed_clauses: vec![0; initial_clause_limit],
            claim_stamp: 0,
        }
    }

    fn begin_variable_counts(&mut self) {
        next_dense_stamp(
            &mut self.variable_count_stamp,
            &mut self.variable_count_stamps,
        );
        self.counted_variables.clear();
    }

    fn record_variable(&mut self, variable: usize) {
        if self.variable_count_stamps[variable] != self.variable_count_stamp {
            self.variable_count_stamps[variable] = self.variable_count_stamp;
            self.variable_counts[variable] = 0;
            self.counted_variables.push(variable);
        }
        self.variable_counts[variable] += 1;
    }

    fn next_candidate_stamp(&mut self) -> u32 {
        next_dense_stamp(&mut self.candidate_stamp, &mut self.candidate_variables)
    }

    fn next_claim_stamp(&mut self) -> u32 {
        next_dense_stamp(&mut self.claim_stamp, &mut self.claimed_clauses)
    }
}

fn next_dense_stamp(stamp: &mut u32, marks: &mut [u32]) -> u32 {
    if *stamp == u32::MAX {
        marks.fill(0);
        *stamp = 1;
    } else {
        *stamp += 1;
    }
    *stamp
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sorted_clauses(formula: &Formula) -> Vec<Vec<i32>> {
        let mut clauses = formula
            .get_clauses()
            .iter()
            .map(Clause::sorted_literal_indices)
            .collect::<Vec<_>>();
        clauses.sort();
        clauses
    }

    fn contains_clause(clauses: &[Vec<i32>], mut expected: Vec<i32>) -> bool {
        expected.sort_unstable();
        clauses.contains(&expected)
    }

    fn ite_formula() -> Formula {
        Formula::from_vec(vec![
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
        ])
    }

    fn ite_formula_with_schedule_padding() -> Formula {
        let mut clauses = ite_formula()
            .get_clauses()
            .iter()
            .map(|clause| clause.iter().map(Literal::get_index).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for remainder in 10..=14 {
            for _ in 0..4 {
                clauses.push(vec![remainder, 4, -4]);
            }
        }
        Formula::from_vec(clauses)
    }

    fn gate_candidate(formula: &Formula, target: i32) -> GateCandidate {
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let mut workspace = GateWorkspace::new(formula.assignment.len(), initial_clause_limit);
        let mut signal = None;
        let pairs = extract_pairs(
            formula,
            initial_clause_limit,
            &pending_deleted,
            target,
            &mut workspace,
            &mut signal,
        )
        .unwrap();
        prefilter_candidates(&mut workspace);
        group_pairs(
            &pairs,
            target,
            initial_clause_limit,
            &mut workspace,
            &mut signal,
        )
        .unwrap()
        .unwrap()
    }

    #[test]
    fn extract_prefilter_and_group_pairs_follow_the_paper_algorithms() {
        let formula = ite_formula();
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let mut workspace = GateWorkspace::new(formula.assignment.len(), initial_clause_limit);
        let mut signal = None;

        let pairs = extract_pairs(
            &formula,
            initial_clause_limit,
            &pending_deleted,
            1,
            &mut workspace,
            &mut signal,
        )
        .unwrap();
        assert_eq!(pairs.len(), 5);
        assert_eq!(workspace.variable_counts[3], 5);
        assert_eq!(pairs[0].first_branch, 2);
        assert_eq!(pairs[0].second_branch, 3);

        prefilter_candidates(&mut workspace);
        assert_eq!(workspace.candidate_variables[3], workspace.candidate_stamp);

        let candidate = group_pairs(&pairs, 1, initial_clause_limit, &mut workspace, &mut signal)
            .unwrap()
            .unwrap();
        assert_ne!(candidate.second, -candidate.third);
        assert_eq!(candidate.second, 2);
        assert_eq!(candidate.third, 3);
        assert_eq!(candidate.matches.len(), 5);
        assert_eq!(candidate.clause_saving, 1);
        assert_eq!(
            candidate
                .matches
                .iter()
                .filter(|gate_match| gate_match.output_positive)
                .count(),
            2
        );
    }

    #[test]
    fn gate_factorization_introduces_ite_definition_and_quotients() {
        let mut formula = ite_formula_with_schedule_padding();
        let mut logger = None;

        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), 16);
        assert_eq!(formula.get_clauses().len(), 29);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 10);

        let clauses = sorted_clauses(&formula);
        assert!(contains_clause(&clauses, vec![15, 1, 2]));
        assert!(contains_clause(&clauses, vec![15, -1, 3]));
        assert!(contains_clause(&clauses, vec![-15, 1, -2]));
        assert!(contains_clause(&clauses, vec![-15, -1, -3]));
        for remainder in 10..=12 {
            assert!(contains_clause(&clauses, vec![-15, remainder]));
        }
        for remainder in 13..=14 {
            assert!(contains_clause(&clauses, vec![15, remainder]));
        }
        assert_eq!(
            formula
                .get_clauses()
                .iter()
                .filter(|clause| clause.lbd == 0 && clause.bva_generated)
                .count(),
            9
        );
    }

    #[test]
    fn complementary_branches_are_classified_as_xor() {
        let formula = Formula::from_vec(
            (10..=14)
                .flat_map(|remainder| [vec![1, -3, remainder], vec![-1, 3, remainder]])
                .collect(),
        );
        let candidate = gate_candidate(&formula, 1);

        assert_eq!(candidate.second, -candidate.third);
        assert_eq!(candidate.second, -3);
        assert_eq!(candidate.third, 3);
    }

    #[test]
    fn grouping_does_not_reuse_a_physical_clause() {
        let formula = Formula::from_vec(vec![
            vec![1, 2, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
        ]);
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let mut workspace = GateWorkspace::new(formula.assignment.len(), initial_clause_limit);
        let mut signal = None;
        let pairs = extract_pairs(
            &formula,
            initial_clause_limit,
            &pending_deleted,
            1,
            &mut workspace,
            &mut signal,
        )
        .unwrap();
        assert_eq!(pairs.len(), 5);
        prefilter_candidates(&mut workspace);

        assert!(
            group_pairs(&pairs, 1, initial_clause_limit, &mut workspace, &mut signal,)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn grouping_uses_a_profitable_group_after_duplicate_inflation() {
        let mut clauses = vec![
            vec![1, 2, 10],
            vec![1, 2, 10],
            vec![1, 2, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
        ];
        for remainder in 20..=24 {
            clauses.push(vec![1, 4, remainder]);
            clauses.push(vec![-1, 5, remainder]);
        }
        let formula = Formula::from_vec(clauses);

        let candidate = gate_candidate(&formula, 1);

        assert_eq!(candidate.second, 4);
        assert_eq!(candidate.third, 5);
        assert_eq!(candidate.matches.len(), 5);
    }

    #[test]
    fn gate_definition_is_logged_before_quotients_and_deletions() {
        let mut formula = ite_formula_with_schedule_padding();
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));

        process(&mut formula, &mut logger, None, None).unwrap();
        drop(logger);
        let proof = String::from_utf8(proof).unwrap();

        assert!(
            proof.starts_with(concat!(
                "15 1 2 0\n",
                "15 -1 3 0\n",
                "-15 1 -2 0\n",
                "-15 -1 -3 0\n",
                "-15 1 10 0\n",
                "-15 -1 10 0\n",
                "-15 10 0\n",
                "d -15 1 10 0\n",
                "d -15 -1 10 0\n",
            )),
            "{proof}"
        );
    }

    #[test]
    fn classical_bva_keeps_searching_after_a_savings_plateau() {
        let formula = Formula::from_vec(vec![
            vec![1, 10],
            vec![1, 11],
            vec![1, 12],
            vec![2, 10],
            vec![2, 11],
            vec![2, 12],
            vec![3, 10],
            vec![3, 11],
            vec![4, 10],
            vec![4, 11],
        ]);
        let initial_clause_limit = formula.get_clauses().len();
        let index = AndIndex::new(&formula, initial_clause_limit, formula.assignment.len());
        let pending_deleted = vec![false; initial_clause_limit];
        let mut workspace = AndWorkspace::new(formula.assignment.len(), initial_clause_limit);
        let mut signal = None;

        let candidate =
            build_and_candidate(&index, 1, &pending_deleted, &mut workspace, &mut signal)
                .unwrap()
                .unwrap();

        assert_eq!(candidate.clause_saving, 2);
        assert_eq!(candidate.literals, vec![1, 2, 3, 4]);
        assert_eq!(
            candidate
                .partial_ids
                .iter()
                .map(|&partial_id| index.partials[partial_id].clone())
                .collect::<Vec<_>>(),
            vec![vec![10], vec![11]]
        );
    }

    #[test]
    fn bva_rewrites_complete_literal_partial_grid_when_it_saves_clauses() {
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

        let mut logger = None;
        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), 8);
        assert_eq!(formula.get_clauses().len(), 6);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.extension_literals, 0);
        assert_eq!(formula.stats.literals_learnt, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);

        let clauses = sorted_clauses(&formula);
        assert!(clauses.contains(&vec![1, 7]));
        assert!(clauses.contains(&vec![2, 7]));
        assert!(clauses.contains(&vec![-7, 3]));
        assert!(clauses.contains(&vec![-7, 4]));
        assert!(clauses.contains(&vec![-7, 5]));
        assert!(clauses.contains(&vec![-7, 6]));
    }

    #[test]
    fn bva_is_noop_when_grid_does_not_save_clauses() {
        let mut formula = Formula::from_vec(vec![vec![1, 3], vec![1, 4], vec![2, 3], vec![2, 4]]);

        let mut logger = None;
        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), 5);
        assert_eq!(formula.get_clauses().len(), 4);
        assert_eq!(formula.stats.bva_literals, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }

    #[test]
    fn bva_does_not_treat_a_repeated_literal_pair_as_a_grid() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 2, 3],
            vec![1, 2, 4],
            vec![1, 2, 5],
            vec![1, 2, 6],
        ]);

        let mut logger = None;
        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), 7);
        assert_eq!(formula.get_clauses().len(), 4);
        assert_eq!(formula.stats.bva_literals, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }

    #[test]
    fn bva_handles_non_binary_partial_clauses() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3, 4],
            vec![1, 3, 5],
            vec![1, 6],
            vec![1, 7],
            vec![2, 3, 4],
            vec![2, 3, 5],
            vec![2, 6],
            vec![2, 7],
        ]);

        let mut logger = None;
        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.get_clauses().len(), 6);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);

        let aux = (formula.assignment.len() - 1) as i32;
        let clauses = sorted_clauses(&formula);
        assert!(clauses.contains(&vec![-aux, 1]));
        assert!(clauses.contains(&vec![-aux, 2]));
        assert!(clauses.contains(&vec![3, 4, aux]));
        assert!(clauses.contains(&vec![3, 5, aux]));
        assert!(clauses.contains(&vec![6, aux]));
        assert!(clauses.contains(&vec![7, aux]));
    }

    #[test]
    fn two_independent_transformations_are_finalized_together() {
        let mut clauses = Vec::new();
        for literal in [1, 2] {
            for partial in 10..=13 {
                clauses.push(vec![literal, partial]);
            }
        }
        for literal in [3, 4] {
            for partial in 20..=23 {
                clauses.push(vec![literal, partial]);
            }
        }
        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;

        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        assert_eq!(formula.stats.bva_literals, 2);
        assert_eq!(formula.stats.clauses_deleted, 16);
        assert_eq!(formula.get_clauses().len(), 12);
    }

    #[test]
    fn stale_overlapping_and_cells_are_not_reused() {
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
        let initial_clause_limit = formula.get_clauses().len();
        let index = AndIndex::new(&formula, initial_clause_limit, formula.assignment.len());
        let mut pending_deleted = vec![false; initial_clause_limit];
        let mut deletion_indices = Vec::new();
        let mut workspace = AndWorkspace::new(formula.assignment.len(), initial_clause_limit);
        let mut signal = None;
        let candidate =
            build_and_candidate(&index, 3, &pending_deleted, &mut workspace, &mut signal)
                .unwrap()
                .unwrap();
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        apply_and_candidate(
            &mut formula,
            &mut logger,
            &index,
            &mut pending_deleted,
            &mut deletion_indices,
            candidate,
        );

        assert!(
            build_and_candidate(&index, 4, &pending_deleted, &mut workspace, &mut signal,)
                .unwrap()
                .is_none()
        );
        assert_eq!(deletion_indices.len(), initial_clause_limit);
    }

    #[test]
    fn buffered_finalization_remaps_a_surviving_history_reason_once() {
        let mut formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![1, 6],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
            vec![2, 6],
            vec![8],
        ]);
        let reason_literal = Literal::new(8);
        let mut history = History::new();
        formula.assign_implication(reason_literal.clone(), &mut history, Some(8));
        let mut logger = None;

        process::<std::io::Empty>(&mut formula, &mut logger, None, Some(&mut history)).unwrap();

        assert_eq!(
            history.decision_levels[0].get_reason(&reason_literal),
            Some(0)
        );
        assert_eq!(formula.get_clause_at_idx(0).lock_count, 1);
        assert_eq!(
            formula.get_clause_at_idx(0).get_literals(),
            &vec![reason_literal]
        );
    }

    #[test]
    fn finalization_rebuilds_consistent_formula_occurrences() {
        let mut formula = ite_formula();
        let mut logger = None;
        process::<std::io::Empty>(&mut formula, &mut logger, None, None).unwrap();

        for variable in 1..formula.assignment.len() {
            for literal in [variable as i32, -(variable as i32)] {
                let expected = formula
                    .get_clauses()
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, clause)| {
                        clause
                            .iter()
                            .any(|candidate| candidate.get_index() == literal)
                            .then_some(idx)
                    })
                    .collect::<Vec<_>>();
                assert_eq!(formula.occurrence_of(&Literal::new(literal)), expected);
            }
        }
    }
}
