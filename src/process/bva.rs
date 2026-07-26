use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::process::ProcessBudget;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::{BTreeMap, HashMap};
use std::io::Write;

// CaDiCaL-FX's default factor bound requires a reduction of at least one clause.
const FACTOR_BOUND: usize = 1;
const GATE_DEFINITION_CLAUSES: usize = 4;
const MIN_GATE_MATCHES: usize = GATE_DEFINITION_CLAUSES + FACTOR_BOUND;
const MAX_FACTOR_CLAUSE_SIZE: usize = 20;

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    budget: &ProcessBudget,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    mut history: Option<&mut History>,
) -> PyResult<()> {
    if budget.exhausted() {
        return Ok(());
    }

    let initial_clause_limit = formula.get_clauses().len();
    let initial_variable_limit = formula.assignment.len();
    let schedule = match initial_literal_schedule(
        formula,
        initial_clause_limit,
        initial_variable_limit,
        budget,
        &mut signal,
    )? {
        BudgetResult::Complete(schedule) => schedule,
        BudgetResult::Exhausted => return Ok(()),
    };
    if budget.exhausted() {
        return Ok(());
    }

    let mut pending_deleted = vec![false; initial_clause_limit];
    let mut deletion_indices = Vec::new();
    let mut gate_variables_seen = vec![false; initial_variable_limit];

    let run_result = (|| -> PyResult<()> {
        for start in schedule {
            if !continue_search(budget, &mut signal)? {
                break;
            }

            let and_candidate = match build_and_candidate(
                formula,
                initial_clause_limit,
                start,
                &pending_deleted,
                budget,
                &mut signal,
            )? {
                BudgetResult::Complete(candidate) => candidate,
                BudgetResult::Exhausted => break,
            };

            let variable = start.unsigned_abs() as usize;
            let gate_candidate = if !gate_variables_seen[variable] {
                gate_variables_seen[variable] = true;
                let has_opposite = match has_live_eligible_occurrence(
                    formula,
                    -start,
                    initial_clause_limit,
                    &pending_deleted,
                    budget,
                    &mut signal,
                )? {
                    BudgetResult::Complete(has_opposite) => has_opposite,
                    BudgetResult::Exhausted => break,
                };
                if formula.assignment.get_value(variable).is_none() && has_opposite {
                    match build_gate_candidate(
                        formula,
                        initial_clause_limit,
                        &pending_deleted,
                        start,
                        budget,
                        &mut signal,
                    )? {
                        BudgetResult::Complete(candidate) => candidate,
                        BudgetResult::Exhausted => break,
                    }
                } else {
                    None
                }
            } else {
                None
            };

            let candidate = match (and_candidate, gate_candidate) {
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
            };

            // Applying a selected candidate is deliberately atomic. Once this
            // check succeeds, definition clauses, quotients, and source claims
            // are completed without consulting the deadline.
            if !continue_search(budget, &mut signal)? {
                break;
            }
            if let Some(candidate) = candidate {
                apply_factorization_candidate(
                    formula,
                    logger,
                    &mut pending_deleted,
                    &mut deletion_indices,
                    candidate,
                );
            }
        }
        Ok(())
    })();

    // This is the only compaction point, including cancellation and ordinary
    // budget exhaustion.
    finalize_pending_deletions(
        formula,
        logger,
        history.as_deref_mut(),
        &pending_deleted,
        &mut deletion_indices,
    );
    run_result
}

fn initial_literal_schedule(
    formula: &Formula,
    initial_clause_limit: usize,
    initial_variable_limit: usize,
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<Vec<i32>>> {
    if !continue_search(budget, signal)? {
        return Ok(BudgetResult::Exhausted);
    }

    let mut schedule = Vec::new();
    for variable in 1..initial_variable_limit {
        for literal in [variable as i32, -(variable as i32)] {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            let mut count = 0;
            for &idx in formula.occurrence_of(&Literal::new(literal)) {
                if !continue_search(budget, signal)? {
                    return Ok(BudgetResult::Exhausted);
                }
                if idx < initial_clause_limit && factor_eligible_clause(&formula.get_clauses()[idx])
                {
                    count += 1;
                }
            }
            if count > 1 {
                schedule.push((literal, count));
            }
        }
    }

    if !continue_search(budget, signal)? {
        return Ok(BudgetResult::Exhausted);
    }
    schedule.sort_by(|(lit_a, count_a), (lit_b, count_b)| {
        count_a
            .cmp(count_b)
            .then_with(|| literal_tie_key(*lit_a).cmp(&literal_tie_key(*lit_b)))
    });
    if !continue_search(budget, signal)? {
        return Ok(BudgetResult::Exhausted);
    }
    Ok(BudgetResult::Complete(
        schedule.into_iter().map(|(literal, _)| literal).collect(),
    ))
}

fn has_live_eligible_occurrence(
    formula: &Formula,
    literal: i32,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<bool>> {
    for &idx in formula.occurrence_of(&Literal::new(literal)) {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        if live_factor_clause(formula, idx, initial_clause_limit, pending_deleted) {
            return Ok(BudgetResult::Complete(true));
        }
    }
    Ok(BudgetResult::Complete(false))
}

fn build_and_candidate(
    formula: &Formula,
    initial_clause_limit: usize,
    start: i32,
    pending_deleted: &[bool],
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<Option<AndCandidate>>> {
    let mut partials = Vec::<LocalAndPartial>::new();
    let mut partial_hash_buckets = HashMap::<u64, Vec<usize>>::new();
    let mut sorted_clause = Vec::new();

    // Only clauses containing this scheduled literal seed the local search.
    // Equal partials are interned, preserving physical duplicate clauses in
    // the cell discovered below rather than duplicating quotient clauses.
    for &clause_idx in formula.occurrence_of(&Literal::new(start)) {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        if !live_factor_clause(formula, clause_idx, initial_clause_limit, pending_deleted) {
            continue;
        }
        sorted_clause.clear();
        sorted_clause.extend(
            formula.get_clauses()[clause_idx]
                .iter()
                .map(Literal::get_index),
        );
        sorted_clause.sort_unstable();
        if is_tautological(&sorted_clause) {
            continue;
        }
        let partial = sorted_without(&sorted_clause, start);
        let hash = stable_signature_hash(&partial);
        if find_exact_vector(&partials, &partial_hash_buckets, hash, &partial).is_none() {
            let partial_id = partials.len();
            partials.push(LocalAndPartial {
                literals: partial,
                cells: Vec::new(),
            });
            partial_hash_buckets
                .entry(hash)
                .or_default()
                .push(partial_id);
        }
    }
    if partials.is_empty() {
        return Ok(BudgetResult::Complete(None));
    }

    // Discover each row lazily through the shortest Formula occurrence list.
    // Candidate clauses are sorted into a reused scratch vector, then compared
    // with the partial by a linear two-pointer subset-plus-one check.
    for partial in &mut partials {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        let anchor = *partial
            .literals
            .iter()
            .min_by_key(|&&literal| {
                (
                    formula.occurrence_of(&Literal::new(literal)).len(),
                    literal_tie_key(literal),
                )
            })
            .expect("eligible factor clauses have non-empty partials");
        let mut cells = BTreeMap::<i32, Vec<usize>>::new();
        for &clause_idx in formula.occurrence_of(&Literal::new(anchor)) {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            if !live_factor_clause(formula, clause_idx, initial_clause_limit, pending_deleted) {
                continue;
            }
            let clause = &formula.get_clauses()[clause_idx];
            if clause.len() != partial.literals.len() + 1 {
                continue;
            }
            sorted_clause.clear();
            sorted_clause.extend(clause.iter().map(Literal::get_index));
            sorted_clause.sort_unstable();
            if is_tautological(&sorted_clause) {
                continue;
            }
            let Some(extra) = one_extra_literal(&partial.literals, &sorted_clause) else {
                continue;
            };
            cells.entry(extra).or_default().push(clause_idx);
        }
        partial.cells = cells
            .into_iter()
            .map(|(literal, source_indices)| LocalAndCell {
                literal,
                source_indices,
            })
            .collect();
        partial
            .cells
            .sort_unstable_by_key(|cell| literal_tie_key(cell.literal));
    }

    let mut literals = vec![start];
    let mut partial_ids = partials
        .iter()
        .enumerate()
        .filter_map(|(partial_id, partial)| partial.cell(start).is_some().then_some(partial_id))
        .collect::<Vec<_>>();
    let mut best = None;

    loop {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        let mut counts = BTreeMap::<i32, usize>::new();
        for &partial_id in &partial_ids {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            for cell in &partials[partial_id].cells {
                if literals.contains(&cell.literal) {
                    continue;
                }
                *counts.entry(cell.literal).or_default() += 1;
            }
        }

        let Some((next_literal, remaining_partials)) = choose_next_literal(&counts) else {
            break;
        };
        if remaining_partials <= 1 {
            break;
        }
        literals.push(next_literal);
        partial_ids.retain(|&partial_id| partials[partial_id].cell(next_literal).is_some());

        let mut source_indices = Vec::new();
        for &literal in &literals {
            for &partial_id in &partial_ids {
                if !continue_search(budget, signal)? {
                    return Ok(BudgetResult::Exhausted);
                }
                let cell = partials[partial_id]
                    .cell(literal)
                    .expect("selected AND grid has every cell");
                source_indices.extend_from_slice(&cell.source_indices);
            }
        }
        source_indices.sort_unstable();
        source_indices.dedup();
        let clause_saving =
            source_indices.len() as isize - (literals.len() + partial_ids.len()) as isize;

        // The best quotient can occur after a temporary plateau or decline, so
        // keep extending the greedy factor chain and remember its best prefix.
        if best
            .as_ref()
            .is_none_or(|candidate: &AndCandidate| clause_saving > candidate.clause_saving)
        {
            best = Some(AndCandidate {
                literals: literals.clone(),
                partials: partial_ids
                    .iter()
                    .map(|&partial_id| partials[partial_id].literals.clone())
                    .collect(),
                source_indices,
                clause_saving,
            });
        }
    }

    Ok(BudgetResult::Complete(best.filter(|candidate| {
        candidate.clause_saving >= FACTOR_BOUND as isize
    })))
}

fn choose_next_literal(counts: &BTreeMap<i32, usize>) -> Option<(i32, usize)> {
    let mut best = None;
    for (&literal, &count) in counts {
        if best.is_none_or(|(best_literal, best_count)| {
            count > best_count
                || (count == best_count && literal_tie_key(literal) < literal_tie_key(best_literal))
        }) {
            best = Some((literal, count));
        }
    }
    best
}

fn build_gate_candidate(
    formula: &Formula,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
    target: i32,
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<Option<GateCandidate>>> {
    let pairs = match extract_signature_pairs(
        formula,
        initial_clause_limit,
        pending_deleted,
        target,
        budget,
        signal,
    )? {
        BudgetResult::Complete(pairs) => pairs,
        BudgetResult::Exhausted => return Ok(BudgetResult::Exhausted),
    };
    group_pairs(&pairs, target, initial_clause_limit, budget, signal)
}

/// Algorithms 1 and 2 from the paper, indexed by exact common remainders.
/// Clauses are first bucketed by size. Within a bucket, every possible branch
/// is removed with the target, and equal remainders are interned by a stable
/// hash plus an exact equality check. Duplicate physical clauses are paired
/// one-to-one rather than expanded into a Cartesian product.
fn extract_signature_pairs(
    formula: &Formula,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
    target: i32,
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<Vec<ExtractedPair>>> {
    if !continue_search(budget, signal)? {
        return Ok(BudgetResult::Exhausted);
    }
    let mut first_by_size: [Vec<usize>; MAX_FACTOR_CLAUSE_SIZE + 1] =
        std::array::from_fn(|_| Vec::new());
    let mut second_by_size: [Vec<usize>; MAX_FACTOR_CLAUSE_SIZE + 1] =
        std::array::from_fn(|_| Vec::new());

    for &clause_idx in formula.occurrence_of(&Literal::new(target)) {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        if live_gate_clause(formula, clause_idx, initial_clause_limit, pending_deleted) {
            let size = formula.get_clauses()[clause_idx].len();
            first_by_size[size].push(clause_idx);
        }
    }
    for &clause_idx in formula.occurrence_of(&Literal::new(-target)) {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        if live_gate_clause(formula, clause_idx, initial_clause_limit, pending_deleted) {
            let size = formula.get_clauses()[clause_idx].len();
            second_by_size[size].push(clause_idx);
        }
    }

    let mut pairs = Vec::new();
    let mut sorted_clause = Vec::new();
    let mut remainder = Vec::new();
    for size in 3..=MAX_FACTOR_CLAUSE_SIZE {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        if first_by_size[size].is_empty() || second_by_size[size].is_empty() {
            continue;
        }
        let mut signatures = Vec::<GateSignature>::new();
        let mut hash_buckets = HashMap::<u64, Vec<usize>>::new();

        for &clause_idx in &first_by_size[size] {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            sorted_clause.clear();
            sorted_clause.extend(
                formula.get_clauses()[clause_idx]
                    .iter()
                    .map(Literal::get_index),
            );
            sorted_clause.sort_unstable();
            if is_tautological(&sorted_clause) {
                continue;
            }
            for &branch in &sorted_clause {
                if branch == target {
                    continue;
                }
                if !continue_search(budget, signal)? {
                    return Ok(BudgetResult::Exhausted);
                }
                sorted_without_two_into(&sorted_clause, target, branch, &mut remainder);
                let hash = stable_signature_hash(&remainder);
                let signature_id =
                    intern_gate_signature(&mut signatures, &mut hash_buckets, hash, &remainder);
                signatures[signature_id]
                    .first_branches
                    .entry(branch)
                    .or_default()
                    .push(clause_idx);
            }
        }

        for &clause_idx in &second_by_size[size] {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            sorted_clause.clear();
            sorted_clause.extend(
                formula.get_clauses()[clause_idx]
                    .iter()
                    .map(Literal::get_index),
            );
            sorted_clause.sort_unstable();
            if is_tautological(&sorted_clause) {
                continue;
            }
            for &branch in &sorted_clause {
                if branch == -target {
                    continue;
                }
                if !continue_search(budget, signal)? {
                    return Ok(BudgetResult::Exhausted);
                }
                sorted_without_two_into(&sorted_clause, -target, branch, &mut remainder);
                let hash = stable_signature_hash(&remainder);
                let signature_id =
                    intern_gate_signature(&mut signatures, &mut hash_buckets, hash, &remainder);
                signatures[signature_id]
                    .second_branches
                    .entry(branch)
                    .or_default()
                    .push(clause_idx);
            }
        }

        for signature in signatures {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            for (first_branch, first_clauses) in &signature.first_branches {
                for (second_branch, second_clauses) in &signature.second_branches {
                    if !continue_search(budget, signal)? {
                        return Ok(BudgetResult::Exhausted);
                    }
                    for (&first_clause, &second_clause) in first_clauses.iter().zip(second_clauses)
                    {
                        pairs.push(ExtractedPair {
                            first_clause,
                            second_clause,
                            first_branch: *first_branch,
                            second_branch: *second_branch,
                        });
                    }
                }
            }
        }
    }

    Ok(BudgetResult::Complete(pairs))
}

fn live_gate_clause(
    formula: &Formula,
    clause_idx: usize,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
) -> bool {
    live_factor_clause(formula, clause_idx, initial_clause_limit, pending_deleted)
        && formula.get_clauses()[clause_idx].len() >= 3
}

fn live_factor_clause(
    formula: &Formula,
    clause_idx: usize,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
) -> bool {
    clause_idx < initial_clause_limit
        && !pending_deleted[clause_idx]
        && factor_eligible_clause(&formula.get_clauses()[clause_idx])
}

/// Algorithm 3 from the paper: normalize simultaneous polarity flips, select
/// the largest group, and claim each physical clause at most once.
fn group_pairs(
    pairs: &[ExtractedPair],
    target: i32,
    initial_clause_limit: usize,
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<BudgetResult<Option<GateCandidate>>> {
    let mut variable_counts = BTreeMap::<u32, usize>::new();
    for pair in pairs {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        *variable_counts
            .entry(pair.second_branch.unsigned_abs())
            .or_default() += 1;
    }

    let mut groups = BTreeMap::<(u32, u32, bool), Vec<ExtractedPair>>::new();
    for &pair in pairs {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        let variable = pair.second_branch.unsigned_abs();
        if variable_counts.get(&variable).copied().unwrap_or_default() < MIN_GATE_MATCHES {
            continue;
        }
        let normalized_first = if pair.second_branch.is_positive() {
            pair.first_branch
        } else {
            -pair.first_branch
        };
        let (literal_variable, literal_negative) = literal_tie_key(normalized_first);
        groups
            .entry((variable, literal_variable, literal_negative))
            .or_default()
            .push(pair);
    }

    let mut claimed = vec![false; initial_clause_limit];
    let mut best_group: Option<(u32, i32, Vec<GateMatch>)> = None;
    for ((variable, literal_variable, literal_negative), group) in groups {
        if !continue_search(budget, signal)? {
            return Ok(BudgetResult::Exhausted);
        }
        let literal = if literal_negative {
            -(literal_variable as i32)
        } else {
            literal_variable as i32
        };
        let mut matches = Vec::new();
        let mut claimed_here = Vec::new();
        for pair in group {
            if !continue_search(budget, signal)? {
                return Ok(BudgetResult::Exhausted);
            }
            if claimed[pair.first_clause] || claimed[pair.second_clause] {
                continue;
            }
            claimed[pair.first_clause] = true;
            claimed[pair.second_clause] = true;
            claimed_here.push(pair.first_clause);
            claimed_here.push(pair.second_clause);
            matches.push(GateMatch {
                first_clause: pair.first_clause,
                second_clause: pair.second_clause,
                output_positive: pair.second_branch.is_negative(),
            });
        }
        for clause_idx in claimed_here {
            claimed[clause_idx] = false;
        }

        if best_group
            .as_ref()
            .is_none_or(|(best_variable, best_literal, best_matches)| {
                group_is_better(
                    matches.len(),
                    variable,
                    literal,
                    best_matches.len(),
                    *best_variable,
                    *best_literal,
                )
            })
        {
            best_group = Some((variable, literal, matches));
        }
    }

    let Some((best_variable, best_second, matches)) = best_group else {
        return Ok(BudgetResult::Complete(None));
    };
    let clause_saving = matches.len() as isize - GATE_DEFINITION_CLAUSES as isize;
    if clause_saving < FACTOR_BOUND as isize {
        return Ok(BudgetResult::Complete(None));
    }
    debug_assert!(matches.iter().all(|gate_match| {
        gate_match.first_clause < initial_clause_limit
            && gate_match.second_clause < initial_clause_limit
    }));

    Ok(BudgetResult::Complete(Some(GateCandidate {
        target,
        second: best_second,
        third: best_variable as i32,
        matches,
        clause_saving,
    })))
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

fn apply_factorization_candidate<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
    candidate: FactorCandidate,
) {
    match candidate {
        FactorCandidate::And(candidate) => apply_and_candidate(
            formula,
            logger,
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
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
    candidate: AndCandidate,
) {
    let z = formula.add_literal();
    formula.stats.add_bva_literal();

    for partial in candidate.partials {
        let mut literals = Vec::with_capacity(partial.len() + 1);
        literals.push(z.clone());
        literals.extend(partial.into_iter().map(Literal::new));
        formula.add_clause_unchecked(factor_clause(literals), logger);
    }
    for literal in candidate.literals {
        formula.add_clause_unchecked(
            factor_clause(vec![z.negated(), Literal::new(literal)]),
            logger,
        );
    }
    for clause_idx in candidate.source_indices {
        claim_clause(clause_idx, pending_deleted, deletion_indices);
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
    for gate_match in candidate.matches {
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

fn continue_search(
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<bool> {
    if budget.exhausted() {
        return Ok(false);
    }
    check_signal(signal)?;
    Ok(true)
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

fn sorted_without(sorted_clause: &[i32], literal_to_remove: i32) -> Vec<i32> {
    sorted_clause
        .iter()
        .copied()
        .filter(|&literal| literal != literal_to_remove)
        .collect()
}

fn sorted_without_two_into(
    sorted_clause: &[i32],
    first_to_remove: i32,
    second_to_remove: i32,
    output: &mut Vec<i32>,
) {
    output.clear();
    output.extend(
        sorted_clause
            .iter()
            .copied()
            .filter(|&literal| literal != first_to_remove && literal != second_to_remove),
    );
}

fn one_extra_literal(partial: &[i32], clause: &[i32]) -> Option<i32> {
    if clause.len() != partial.len() + 1 {
        return None;
    }
    let mut partial_position = 0;
    let mut clause_position = 0;
    let mut extra = None;
    while clause_position < clause.len() {
        if partial_position < partial.len() && partial[partial_position] == clause[clause_position]
        {
            partial_position += 1;
            clause_position += 1;
        } else if extra.is_none() {
            extra = Some(clause[clause_position]);
            clause_position += 1;
        } else {
            return None;
        }
    }
    if partial_position == partial.len() {
        extra
    } else {
        None
    }
}

fn is_tautological(sorted_clause: &[i32]) -> bool {
    sorted_clause
        .iter()
        .any(|&literal| sorted_clause.binary_search(&-literal).is_ok())
}

fn factor_eligible_clause(clause: &Clause) -> bool {
    clause.lock_count == 0
        && (2..=MAX_FACTOR_CLAUSE_SIZE).contains(&clause.len())
        && (clause.lbd != 0 || clause.bva_generated)
}

// Explicit FNV-1a-style hashing keeps scheduling and grouping deterministic.
// Hash equality is only a lookup hint; every intern operation also compares the
// complete vector before reusing an entry.
fn stable_signature_hash(literals: &[i32]) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    hash ^= literals.len() as u64;
    hash = hash.wrapping_mul(0x100000001b3);
    for &literal in literals {
        hash ^= literal as u32 as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn intern_gate_signature(
    signatures: &mut Vec<GateSignature>,
    hash_buckets: &mut HashMap<u64, Vec<usize>>,
    hash: u64,
    remainder: &[i32],
) -> usize {
    if let Some(signature_ids) = hash_buckets.get(&hash) {
        for &signature_id in signature_ids {
            if signatures[signature_id].remainder == remainder {
                return signature_id;
            }
        }
    }
    let signature_id = signatures.len();
    signatures.push(GateSignature {
        remainder: remainder.to_vec(),
        first_branches: BTreeMap::new(),
        second_branches: BTreeMap::new(),
    });
    hash_buckets.entry(hash).or_default().push(signature_id);
    signature_id
}

fn find_exact_vector(
    partials: &[LocalAndPartial],
    hash_buckets: &HashMap<u64, Vec<usize>>,
    hash: u64,
    candidate: &[i32],
) -> Option<usize> {
    hash_buckets
        .get(&hash)?
        .iter()
        .copied()
        .find(|&id| partials[id].literals == candidate)
}

enum BudgetResult<T> {
    Complete(T),
    Exhausted,
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

struct GateSignature {
    remainder: Vec<i32>,
    first_branches: BTreeMap<i32, Vec<usize>>,
    second_branches: BTreeMap<i32, Vec<usize>>,
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
    partials: Vec<Vec<i32>>,
    source_indices: Vec<usize>,
    clause_saving: isize,
}

struct LocalAndPartial {
    literals: Vec<i32>,
    cells: Vec<LocalAndCell>,
}

impl LocalAndPartial {
    fn cell(&self, literal: i32) -> Option<&LocalAndCell> {
        self.cells.iter().find(|cell| cell.literal == literal)
    }
}

struct LocalAndCell {
    literal: i32,
    source_indices: Vec<usize>,
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_BUDGET: f32 = 60.0;

    fn process_with_budget<W: Write>(
        formula: &mut Formula,
        budget_seconds: f32,
        logger: &mut Option<DratLogger<W>>,
        signal: Option<(Python<'_>, &mut u64)>,
        history: Option<&mut History>,
    ) -> PyResult<()> {
        let budget = ProcessBudget::new(budget_seconds);
        process(formula, &budget, logger, signal, history)
    }

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
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;
        match build_gate_candidate(
            formula,
            initial_clause_limit,
            &pending_deleted,
            target,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(Some(candidate)) => candidate,
            BudgetResult::Complete(None) => panic!("expected gate candidate"),
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        }
    }

    fn and_candidate(formula: &Formula, start: i32) -> Option<AndCandidate> {
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;
        match build_and_candidate(
            formula,
            initial_clause_limit,
            start,
            &pending_deleted,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(candidate) => candidate,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        }
    }

    #[test]
    fn signature_extraction_and_grouping_follow_the_paper_algorithms() {
        let formula = ite_formula();
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;
        let pairs = match extract_signature_pairs(
            &formula,
            initial_clause_limit,
            &pending_deleted,
            1,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(pairs) => pairs,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        };
        assert_eq!(pairs.len(), 5);
        assert_eq!(pairs[0].first_branch, 2);
        assert_eq!(pairs[0].second_branch, 3);

        let candidate =
            match group_pairs(&pairs, 1, initial_clause_limit, &budget, &mut signal).unwrap() {
                BudgetResult::Complete(Some(candidate)) => candidate,
                _ => panic!("expected gate candidate"),
            };
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

        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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
    fn ite_group_wins_an_equal_sized_xor_group() {
        let mut pairs = Vec::new();
        for offset in 0..5 {
            pairs.push(ExtractedPair {
                first_clause: offset * 2,
                second_clause: offset * 2 + 1,
                first_branch: -3,
                second_branch: 3,
            });
            pairs.push(ExtractedPair {
                first_clause: 10 + offset * 2,
                second_clause: 10 + offset * 2 + 1,
                first_branch: 2,
                second_branch: 4,
            });
        }
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;

        let candidate = match group_pairs(&pairs, 1, 20, &budget, &mut signal).unwrap() {
            BudgetResult::Complete(Some(candidate)) => candidate,
            _ => panic!("expected gate candidate"),
        };

        assert_eq!(candidate.matches.len(), 5);
        assert_eq!(candidate.second, 2);
        assert_eq!(candidate.third, 4);
        assert_ne!(candidate.second, -candidate.third);
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
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;
        let pairs = match extract_signature_pairs(
            &formula,
            initial_clause_limit,
            &pending_deleted,
            1,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(pairs) => pairs,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        };
        assert_eq!(pairs.len(), 1);
        assert!(matches!(
            group_pairs(&pairs, 1, initial_clause_limit, &budget, &mut signal,).unwrap(),
            BudgetResult::Complete(None)
        ));
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

        process_with_budget(&mut formula, TEST_BUDGET, &mut logger, None, None).unwrap();
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

        let candidate = and_candidate(&formula, 1).unwrap();

        assert_eq!(candidate.clause_saving, 2);
        assert_eq!(candidate.literals, vec![1, 2, 3, 4]);
        assert_eq!(candidate.partials, vec![vec![10], vec![11]]);
        assert_eq!(candidate.source_indices.len(), 8);
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
        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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
        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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
        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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
        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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
    fn duplicate_and_cells_preserve_physical_clause_savings() {
        let mut clauses = Vec::new();
        for literal in [1, 2] {
            for partial in [10, 11] {
                clauses.push(vec![literal, partial]);
                clauses.push(vec![literal, partial]);
            }
        }
        let mut formula = Formula::from_vec(clauses);
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.clauses_deleted, 8);
        assert_eq!(formula.get_clauses().len(), 4);
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

        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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
        let mut pending_deleted = vec![false; initial_clause_limit];
        let mut deletion_indices = Vec::new();
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;
        let candidate = match build_and_candidate(
            &formula,
            initial_clause_limit,
            3,
            &pending_deleted,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(Some(candidate)) => candidate,
            _ => panic!("expected AND candidate"),
        };
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        apply_and_candidate(
            &mut formula,
            &mut logger,
            &mut pending_deleted,
            &mut deletion_indices,
            candidate,
        );

        assert!(matches!(
            build_and_candidate(
                &formula,
                initial_clause_limit,
                4,
                &pending_deleted,
                &budget,
                &mut signal,
            )
            .unwrap(),
            BudgetResult::Complete(None)
        ));
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

        process_with_budget::<std::io::Empty>(
            &mut formula,
            TEST_BUDGET,
            &mut logger,
            None,
            Some(&mut history),
        )
        .unwrap();

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
        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

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

    #[test]
    fn zero_budget_skips_a_profitable_and_grid() {
        let clauses = [1, 2]
            .into_iter()
            .flat_map(|literal| (10..=13).map(move |partial| vec![literal, partial]))
            .collect::<Vec<_>>();
        let mut formula = Formula::from_vec(clauses);
        let original = sorted_clauses(&formula);
        let original_variables = formula.assignment.len();
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, 0.0, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), original_variables);
        assert_eq!(sorted_clauses(&formula), original);
        assert_eq!(formula.stats.bva_literals, 0);
    }

    #[test]
    fn zero_budget_skips_a_profitable_gate() {
        let mut formula = ite_formula();
        let original = sorted_clauses(&formula);
        let original_variables = formula.assignment.len();
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, 0.0, &mut logger, None, None).unwrap();

        assert_eq!(formula.assignment.len(), original_variables);
        assert_eq!(sorted_clauses(&formula), original);
        assert_eq!(formula.stats.bva_literals, 0);
    }

    #[test]
    fn clauses_over_factor_size_limit_are_skipped() {
        let common = (100..=119).collect::<Vec<_>>();
        let mut clauses = Vec::new();
        for literal in [1, 2] {
            for extra in 10..=13 {
                let mut clause = common.clone();
                clause.push(literal);
                clause.push(extra);
                clauses.push(clause);
            }
        }
        let mut formula = Formula::from_vec(clauses);
        let original = sorted_clauses(&formula);
        let mut logger = None;

        process_with_budget::<std::io::Empty>(&mut formula, TEST_BUDGET, &mut logger, None, None)
            .unwrap();

        assert_eq!(sorted_clauses(&formula), original);
        assert_eq!(formula.stats.bva_literals, 0);
        assert_eq!(formula.stats.clauses_deleted, 0);
    }

    #[test]
    fn gate_clauses_over_factor_size_limit_are_skipped() {
        let common = (100..=117).collect::<Vec<_>>();
        let mut clauses = Vec::new();
        for remainder in 10..=14 {
            let mut first = common.clone();
            first.extend([1, 2, remainder]);
            clauses.push(first);
            let mut second = common.clone();
            second.extend([-1, 3, remainder]);
            clauses.push(second);
        }
        let formula = Formula::from_vec(clauses);
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;

        let pairs = match extract_signature_pairs(
            &formula,
            initial_clause_limit,
            &pending_deleted,
            1,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(pairs) => pairs,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        };

        assert!(pairs.is_empty());
    }

    #[test]
    fn gate_size_buckets_do_not_cross_match() {
        let formula = Formula::from_vec(vec![
            vec![1, 2, 10],
            vec![1, 2, 11],
            vec![1, 2, 12],
            vec![1, 2, 13],
            vec![1, 2, 14],
            vec![-1, 3, 10, 20],
            vec![-1, 3, 11, 20],
            vec![-1, 3, 12, 20],
            vec![-1, 3, 13, 20],
            vec![-1, 3, 14, 20],
        ]);
        let initial_clause_limit = formula.get_clauses().len();
        let pending_deleted = vec![false; initial_clause_limit];
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;

        let pairs = match extract_signature_pairs(
            &formula,
            initial_clause_limit,
            &pending_deleted,
            1,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(pairs) => pairs,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        };
        assert!(pairs.is_empty());
    }

    #[test]
    fn signature_hash_collisions_require_exact_remainder_equality() {
        let mut signatures = Vec::new();
        let mut buckets = HashMap::new();

        let first = intern_gate_signature(&mut signatures, &mut buckets, 7, &[2, 10]);
        let collision = intern_gate_signature(&mut signatures, &mut buckets, 7, &[3, 10]);
        let repeated = intern_gate_signature(&mut signatures, &mut buckets, 7, &[2, 10]);

        assert_eq!(first, 0);
        assert_eq!(collision, 1);
        assert_eq!(repeated, first);
        assert_eq!(signatures.len(), 2);
    }
}
