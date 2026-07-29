use crate::circuits::factorization::{
    BudgetResult, FACTOR_BOUND, claim_clause, continue_search, generated_clause, is_tautological,
    literal_tie_key, live_factor_clause, stable_signature_hash,
};
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::process::ProcessBudget;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::{BTreeMap, HashMap};
use std::io::Write;

pub(crate) struct AndGate {
    literals: Vec<i32>,
    partials: Vec<Vec<i32>>,
    source_indices: Vec<usize>,
    clause_saving: isize,
}

impl AndGate {
    pub(crate) fn find(
        formula: &Formula,
        initial_clause_limit: usize,
        start: i32,
        pending_deleted: &[bool],
        budget: &ProcessBudget,
        signal: &mut Option<(Python<'_>, &mut u64)>,
    ) -> PyResult<BudgetResult<Option<AndGate>>> {
        let mut partials = Vec::<AndPartial>::new();
        let mut partial_hash_buckets = HashMap::<u64, Vec<usize>>::new();
        let mut sorted_clause = Vec::new();

        // Only clauses containing the scheduled literal seed this local search.
        // Equal partials are interned, while duplicate physical clauses remain in
        // the cells discovered below and therefore contribute to the savings.
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

            let literals = sorted_without(&sorted_clause, start);
            let hash = stable_signature_hash(&literals);
            intern_partial(&mut partials, &mut partial_hash_buckets, hash, &literals);
        }
        if partials.is_empty() {
            return Ok(BudgetResult::Complete(None));
        }

        // Discover each row through its shortest occurrence list. A candidate
        // clause belongs to a cell exactly when it is the partial plus one literal.
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

                if let Some(extra) = one_extra_literal(&partial.literals, &sorted_clause) {
                    cells.entry(extra).or_default().push(clause_idx);
                }
            }

            partial.cells = cells
                .into_iter()
                .map(|(literal, source_indices)| AndCell {
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
                    if !literals.contains(&cell.literal) {
                        *counts.entry(cell.literal).or_default() += 1;
                    }
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

            // A better quotient can occur after a plateau or decline, so extend
            // the full greedy chain while retaining its best prefix.
            if best
                .as_ref()
                .is_none_or(|gate: &Self| clause_saving > gate.clause_saving)
            {
                best = Some(Self {
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

        Ok(BudgetResult::Complete(best.filter(|gate| {
            gate.clause_saving >= FACTOR_BOUND as isize
        })))
    }

    pub(crate) fn clause_saving(&self) -> isize {
        self.clause_saving
    }

    pub(crate) fn apply<W: Write>(
        self,
        formula: &mut Formula,
        logger: &mut Option<DratLogger<W>>,
        pending_deleted: &mut [bool],
        deletion_indices: &mut Vec<usize>,
    ) {
        let auxiliary = formula.add_literal();
        formula.stats.add_bva_literal();

        for partial in self.partials {
            let mut literals = Vec::with_capacity(partial.len() + 1);
            literals.push(auxiliary.clone());
            literals.extend(partial.into_iter().map(Literal::new));
            formula.add_clause_unchecked(generated_clause(literals), logger);
        }
        for literal in self.literals {
            formula.add_clause_unchecked(
                generated_clause(vec![auxiliary.negated(), Literal::new(literal)]),
                logger,
            );
        }

        for clause_idx in self.source_indices {
            claim_clause(clause_idx, pending_deleted, deletion_indices);
        }
    }
}

struct AndPartial {
    literals: Vec<i32>,
    cells: Vec<AndCell>,
}

impl AndPartial {
    fn cell(&self, literal: i32) -> Option<&AndCell> {
        self.cells.iter().find(|cell| cell.literal == literal)
    }
}

struct AndCell {
    literal: i32,
    source_indices: Vec<usize>,
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

fn sorted_without(sorted_clause: &[i32], literal_to_remove: i32) -> Vec<i32> {
    sorted_clause
        .iter()
        .copied()
        .filter(|&literal| literal != literal_to_remove)
        .collect()
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

fn intern_partial(
    partials: &mut Vec<AndPartial>,
    hash_buckets: &mut HashMap<u64, Vec<usize>>,
    hash: u64,
    literals: &[i32],
) -> usize {
    if let Some(partial_id) = find_exact_partial(partials, hash_buckets, hash, literals) {
        return partial_id;
    }

    let partial_id = partials.len();
    partials.push(AndPartial {
        literals: literals.to_vec(),
        cells: Vec::new(),
    });
    hash_buckets.entry(hash).or_default().push(partial_id);
    partial_id
}

fn find_exact_partial(
    partials: &[AndPartial],
    hash_buckets: &HashMap<u64, Vec<usize>>,
    hash: u64,
    literals: &[i32],
) -> Option<usize> {
    hash_buckets
        .get(&hash)?
        .iter()
        .copied()
        .find(|&partial_id| partials[partial_id].literals == literals)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_BUDGET: f32 = 60.0;

    fn find(formula: &Formula, start: i32, pending_deleted: &[bool]) -> Option<AndGate> {
        let budget = ProcessBudget::new(TEST_BUDGET);
        let mut signal = None;
        match AndGate::find(
            formula,
            pending_deleted.len(),
            start,
            pending_deleted,
            &budget,
            &mut signal,
        )
        .unwrap()
        {
            BudgetResult::Complete(gate) => gate,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        }
    }

    fn sorted_generated_clauses(formula: &Formula, initial_clause_limit: usize) -> Vec<Vec<i32>> {
        let mut clauses = formula.get_clauses()[initial_clause_limit..]
            .iter()
            .map(|clause| clause.sorted_literal_indices())
            .collect::<Vec<_>>();
        clauses.sort();
        clauses
    }

    fn apply(gate: AndGate, formula: &mut Formula, pending_deleted: &mut [bool]) -> Vec<usize> {
        let mut deletion_indices = Vec::new();
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        gate.apply(formula, &mut logger, pending_deleted, &mut deletion_indices);
        deletion_indices
    }

    #[test]
    fn greedy_search_continues_past_a_savings_plateau() {
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
        let pending_deleted = vec![false; formula.get_clauses().len()];

        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");

        assert_eq!(gate.clause_saving(), 2);
        assert_eq!(gate.literals, vec![1, 2, 3, 4]);
        assert_eq!(gate.partials, vec![vec![10], vec![11]]);
        assert_eq!(gate.source_indices.len(), 8);
    }

    #[test]
    fn profitable_complete_grid_is_applied_atomically() {
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
        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");

        let deletion_indices = apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(formula.assignment.len(), 8);
        assert_eq!(formula.stats.bva_literals, 1);
        assert!(pending_deleted.iter().all(|pending| *pending));
        assert_eq!(
            deletion_indices,
            (0..initial_clause_limit).collect::<Vec<_>>()
        );
        assert_eq!(
            sorted_generated_clauses(&formula, initial_clause_limit),
            vec![
                vec![-7, 1],
                vec![-7, 2],
                vec![3, 7],
                vec![4, 7],
                vec![5, 7],
                vec![6, 7],
            ]
        );
        assert!(
            formula.get_clauses()[initial_clause_limit..]
                .iter()
                .all(|clause| clause.bva_generated)
        );
    }

    #[test]
    fn unprofitable_grid_is_a_noop() {
        let formula = Formula::from_vec(vec![vec![1, 3], vec![1, 4], vec![2, 3], vec![2, 4]]);
        let pending_deleted = vec![false; formula.get_clauses().len()];

        assert!(find(&formula, 1, &pending_deleted).is_none());
        assert_eq!(formula.assignment.len(), 5);
        assert_eq!(formula.get_clauses().len(), 4);
        assert_eq!(formula.stats.bva_literals, 0);
    }

    #[test]
    fn repeated_literal_pair_is_not_a_grid() {
        let formula = Formula::from_vec(vec![
            vec![1, 2, 3],
            vec![1, 2, 4],
            vec![1, 2, 5],
            vec![1, 2, 6],
        ]);
        let pending_deleted = vec![false; formula.get_clauses().len()];

        for start in 1..=6 {
            assert!(find(&formula, start, &pending_deleted).is_none());
        }
    }

    #[test]
    fn non_binary_partials_are_preserved_on_application() {
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
        let initial_clause_limit = formula.get_clauses().len();
        let mut pending_deleted = vec![false; initial_clause_limit];
        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");
        assert_eq!(gate.clause_saving(), 2);

        apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(
            sorted_generated_clauses(&formula, initial_clause_limit),
            vec![
                vec![-8, 1],
                vec![-8, 2],
                vec![3, 4, 8],
                vec![3, 5, 8],
                vec![6, 8],
                vec![7, 8],
            ]
        );
    }

    #[test]
    fn duplicate_physical_cells_contribute_to_savings_and_are_claimed_once() {
        let clauses = [1, 2]
            .into_iter()
            .flat_map(|literal| {
                [10, 11]
                    .into_iter()
                    .flat_map(move |partial| [vec![literal, partial], vec![literal, partial]])
            })
            .collect::<Vec<_>>();
        let mut formula = Formula::from_vec(clauses);
        let initial_clause_limit = formula.get_clauses().len();
        let mut pending_deleted = vec![false; initial_clause_limit];

        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");
        assert_eq!(gate.clause_saving(), 4);
        assert_eq!(gate.source_indices.len(), 8);

        let deletion_indices = apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(deletion_indices.len(), 8);
        assert_eq!(deletion_indices, (0..8).collect::<Vec<_>>());
        assert_eq!(formula.get_clauses().len(), 12);
        assert_eq!(formula.stats.bva_literals, 1);
    }

    #[test]
    fn stale_claimed_cells_are_not_reused() {
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
        let gate = find(&formula, 3, &pending_deleted).expect("expected profitable grid");

        let deletion_indices = apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(deletion_indices.len(), initial_clause_limit);
        assert!(find(&formula, 4, &pending_deleted).is_none());
    }

    #[test]
    fn clauses_over_the_factor_size_limit_are_ignored() {
        let common = (100..=119).collect::<Vec<_>>();
        let clauses = [1, 2]
            .into_iter()
            .flat_map(|literal| {
                let common = common.clone();
                (10..=13).map(move |extra| {
                    let mut clause = common.clone();
                    clause.extend([literal, extra]);
                    clause
                })
            })
            .collect::<Vec<_>>();
        let formula = Formula::from_vec(clauses);
        let pending_deleted = vec![false; formula.get_clauses().len()];

        assert!(find(&formula, 1, &pending_deleted).is_none());
    }

    #[test]
    fn hash_collisions_still_require_exact_partial_equality() {
        let mut partials = Vec::new();
        let mut hash_buckets = HashMap::new();

        let first = intern_partial(&mut partials, &mut hash_buckets, 7, &[2, 10]);
        let collision = intern_partial(&mut partials, &mut hash_buckets, 7, &[3, 10]);
        let repeated = intern_partial(&mut partials, &mut hash_buckets, 7, &[2, 10]);

        assert_eq!(first, 0);
        assert_eq!(collision, 1);
        assert_eq!(repeated, first);
        assert_eq!(partials.len(), 2);
    }
}
