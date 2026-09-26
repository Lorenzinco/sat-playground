use crate::circuits::factorization::{
    BvaBudget, FACTOR_BOUND, FactorSearch, claim_clause, definition_clause, is_tautological,
    literal_tie_key, live_factor_clause, quotient_clause, stable_signature_hash,
};
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;

use std::collections::{BTreeMap, HashMap};
use std::io::Write;

pub(crate) struct AndGate {
    literals: Vec<i32>,
    partials: Vec<Vec<i32>>,
    source_indices: Vec<usize>,
    factor_score: isize,
    clause_saving: isize,
}

impl AndGate {
    pub(crate) fn find(
        formula: &Formula,
        start: i32,
        pending_deleted: &[bool],
        budget: &mut BvaBudget,
        index: &RemainderIndex,
    ) -> FactorSearch<AndGate> {
        let mut partials = Vec::<AndPartial>::new();
        let mut partial_hash_buckets = HashMap::<u64, Vec<usize>>::new();
        let mut sorted_clause = Vec::new();

        // Only clauses containing the scheduled literal seed this local search.
        // Equal partials are interned, while duplicate physical clauses remain in
        // the cells discovered below and therefore contribute to the savings.
        for clause_idx in formula.occurrence_of(&Literal::new(start)) {
            if !budget.visit_clause() {
                return FactorSearch::BudgetExhausted;
            }
            if !live_factor_clause(formula, clause_idx, pending_deleted) {
                continue;
            }

            sorted_clause.clear();
            sorted_clause.extend(
                formula
                    .get_clause_at_idx(clause_idx)
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
            return FactorSearch::NotFound;
        }

        // Hashes only narrow the lookup; exact remainders decide membership.
        for partial in &mut partials {
            let mut cells = BTreeMap::<i32, Vec<usize>>::new();
            for &(clause_idx, extra) in index.lookup(&partial.literals) {
                if !budget.visit_clause() {
                    return FactorSearch::BudgetExhausted;
                }
                if !live_factor_clause(formula, clause_idx, pending_deleted) {
                    continue;
                }

                cells.entry(extra).or_default().push(clause_idx);
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
            let mut counts = BTreeMap::<i32, usize>::new();
            for &partial_id in &partial_ids {
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
                    let cell = partials[partial_id]
                        .cell(literal)
                        .expect("selected AND grid has every cell");
                    source_indices.extend_from_slice(&cell.source_indices);
                }
            }
            source_indices.sort_unstable();
            source_indices.dedup();
            // Keep the historical BVA score for candidate acceptance and
            // comparison. Exact binary factors emit one additional definition
            // clause, which is reflected separately in the true net saving.
            let factor_score =
                source_indices.len() as isize - (literals.len() + partial_ids.len()) as isize;
            let clause_saving = factor_score - isize::from(literals.len() == 2);

            // A better quotient can occur after a plateau or decline, so extend
            // the full greedy chain while retaining its best prefix.
            if best
                .as_ref()
                .is_none_or(|gate: &Self| factor_score > gate.factor_score)
            {
                best = Some(Self {
                    literals: literals.clone(),
                    partials: partial_ids
                        .iter()
                        .map(|&partial_id| partials[partial_id].literals.clone())
                        .collect(),
                    source_indices,
                    factor_score,
                    clause_saving,
                });
            }
        }

        match best.filter(|gate| gate.factor_score >= FACTOR_BOUND as isize) {
            Some(gate) => FactorSearch::Found(gate),
            None => FactorSearch::NotFound,
        }
    }

    pub(crate) fn factor_score(&self) -> isize {
        self.factor_score
    }

    pub(crate) fn clause_saving(&self) -> isize {
        self.clause_saving
    }

    pub(crate) fn source_clause_count(&self) -> usize {
        self.source_indices.len()
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
        if self.literals.len() == 2 {
            formula.stats.bva_binary_and_factors += 1;
            let first = Literal::new(self.literals[0]);
            let second = Literal::new(self.literals[1]);
            formula
                .extensions
                .add_bva_substitution(&first, &second, &auxiliary);
            formula.add_clause_unchecked(
                definition_clause(vec![auxiliary, first.negated(), second.negated()]),
                logger,
            );
        } else {
            formula.stats.bva_non_binary_and_factors += 1;
            formula.extensions.add_and_definition(
                self.literals.iter().copied().map(Literal::new).collect(),
                &auxiliary,
            );
        }

        for partial in self.partials {
            let mut literals = Vec::with_capacity(partial.len() + 1);
            literals.push(auxiliary.clone());
            literals.extend(partial.into_iter().map(Literal::new));
            formula.add_clause_unchecked(quotient_clause(literals), logger);
        }
        for literal in self.literals {
            formula.add_clause_unchecked(
                definition_clause(vec![auxiliary.negated(), Literal::new(literal)]),
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

/// Pass-local append-only index. Source clauses are immutable during the pass;
/// pending and physical deletions are filtered at lookup, before using a cell.
/// Eligibility bounds clause length to 20, avoiding unbounded quadratic keys.
#[derive(Default)]
pub(crate) struct RemainderIndex {
    buckets: HashMap<u64, Vec<RemainderRow>>,
    next_clause: usize,
    entries: usize,
}

struct RemainderRow {
    literals: Vec<i32>,
    entries: Vec<(usize, i32)>,
}

impl RemainderIndex {
    pub(crate) fn extend(
        &mut self,
        formula: &Formula,
        pending_deleted: &[bool],
        budget: &mut BvaBudget,
    ) -> bool {
        while self.next_clause < formula.clause_slots_len() {
            let clause_idx = self.next_clause;
            if !budget.visit_clause() {
                return false;
            }
            if live_factor_clause(formula, clause_idx, pending_deleted) {
                let literals = formula
                    .get_clause_at_idx(clause_idx)
                    .sorted_literal_indices();
                if !is_tautological(&literals) {
                    // Bound pass-local storage independently of the effort cap.
                    if self.entries.saturating_add(literals.len()) > 250_000 {
                        return false;
                    }
                    // Reserve work before inserting so an interrupted clause
                    // cannot leave duplicate entries if construction is resumed.
                    for _ in &literals {
                        if !budget.visit_clause() {
                            return false;
                        }
                    }
                    for &extra in &literals {
                        let remainder = sorted_without(&literals, extra);
                        self.insert(
                            stable_signature_hash(&remainder),
                            remainder,
                            (clause_idx, extra),
                        );
                    }
                }
            }
            self.next_clause += 1;
        }
        true
    }

    fn insert(&mut self, hash: u64, literals: Vec<i32>, entry: (usize, i32)) {
        self.entries += 1;
        let bucket = self.buckets.entry(hash).or_default();
        if let Some(row) = bucket.iter_mut().find(|row| row.literals == literals) {
            row.entries.push(entry);
        } else {
            bucket.push(RemainderRow {
                literals,
                entries: vec![entry],
            });
        }
    }

    fn lookup(&self, literals: &[i32]) -> &[(usize, i32)] {
        self.lookup_hash(stable_signature_hash(literals), literals)
    }

    fn lookup_hash(&self, hash: u64, literals: &[i32]) -> &[(usize, i32)] {
        self.buckets
            .get(&hash)
            .and_then(|bucket| bucket.iter().find(|row| row.literals == literals))
            .map_or(&[], |row| row.entries.as_slice())
    }
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
    use crate::formula::extension::ExtensionDefinition;

    fn find(formula: &Formula, start: i32, pending_deleted: &[bool]) -> Option<AndGate> {
        let mut budget = BvaBudget::new(usize::MAX);
        let mut index = RemainderIndex::default();
        assert!(index.extend(formula, pending_deleted, &mut budget));
        match AndGate::find(formula, start, pending_deleted, &mut budget, &index) {
            FactorSearch::Found(gate) => Some(gate),
            FactorSearch::NotFound => None,
            FactorSearch::BudgetExhausted => unreachable!("unlimited test budget exhausted"),
        }
    }

    fn sorted_generated_clauses(formula: &Formula, initial_clause_limit: usize) -> Vec<Vec<i32>> {
        let mut clauses = formula
            .get_clauses_and_garbage()
            .filter(|(physical_index, _)| *physical_index >= initial_clause_limit)
            .map(|(_, clause)| clause.sorted_literal_indices())
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
    fn remainder_index_bounds_storage_and_resumes_interrupted_clauses() {
        let formula = Formula::from_vec(vec![vec![1, 2, 3]]);
        let pending = vec![false];
        let mut index = RemainderIndex::default();
        assert!(!index.extend(&formula, &pending, &mut BvaBudget::new(2)));
        assert_eq!(index.entries, 0);
        assert!(index.extend(&formula, &pending, &mut BvaBudget::new(4)));
        assert_eq!(index.lookup(&[2, 3]), &[(0, 1)]);
        let mut capped = RemainderIndex {
            entries: 250_000,
            ..Default::default()
        };
        assert!(!capped.extend(&formula, &pending, &mut BvaBudget::new(100)));
        assert!(capped.buckets.is_empty());
        let long = Formula::from_vec(vec![(1..=21).collect()]);
        let mut index = RemainderIndex::default();
        assert!(index.extend(&long, &pending, &mut BvaBudget::new(1)));
        assert!(index.buckets.is_empty());
    }

    #[test]
    fn remainder_index_resolves_collisions_exactly() {
        let mut index = RemainderIndex::default();
        index.insert(7, vec![2, 10], (0, 1));
        index.insert(7, vec![3, 10], (1, 1));
        index.insert(7, vec![2, 10], (2, 4));
        assert_eq!(index.lookup_hash(7, &[2, 10]), &[(0, 1), (2, 4)]);
        assert_eq!(index.lookup_hash(7, &[3, 10]), &[(1, 1)]);
        assert!(index.lookup_hash(7, &[4, 10]).is_empty());
    }

    #[test]
    fn index_filters_deleted_cells_and_adds_generated_cells_incrementally() {
        let mut formula = Formula::from_vec(
            (1..=2)
                .flat_map(|a| (3..=6).map(move |b| vec![a, b]))
                .collect(),
        );
        let mut pending = vec![false; formula.clause_slots_len()];
        let mut budget = BvaBudget::new(usize::MAX);
        let mut index = RemainderIndex::default();
        assert!(index.extend(&formula, &pending, &mut budget));
        pending[4] = true;
        formula.delete_clause::<std::io::Empty>(5, &mut None);
        assert!(matches!(
            AndGate::find(&formula, 1, &pending, &mut budget, &index),
            FactorSearch::NotFound
        ));
        for b in [3, 4] {
            formula.add_clause_unchecked::<std::io::Empty>(
                definition_clause(vec![Literal::new(2), Literal::new(b)]),
                &mut None,
            );
        }
        pending.resize(formula.clause_slots_len(), false);
        let before = budget.visits();
        assert!(index.extend(&formula, &pending, &mut budget));
        assert_eq!(budget.visits() - before, 6);
        assert!(index.extend(&formula, &pending, &mut budget));
        assert_eq!(budget.visits() - before, 6);
        let FactorSearch::Found(gate) = AndGate::find(&formula, 1, &pending, &mut budget, &index)
        else {
            panic!("generated cells complete the grid")
        };
        assert_eq!(gate.source_indices, vec![0, 1, 2, 3, 6, 7, 8, 9]);
    }

    #[test]
    fn greedy_search_continues_past_a_savings_plateau() {
        let mut formula = Formula::from_vec(vec![
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
        let mut pending_deleted = vec![false; formula.clause_slots_len()];

        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");

        assert_eq!(gate.factor_score(), 2);
        assert_eq!(gate.clause_saving(), 2);
        assert_eq!(gate.literals, vec![1, 2, 3, 4]);
        assert_eq!(gate.partials, vec![vec![10], vec![11]]);
        assert_eq!(gate.source_indices.len(), 8);

        apply(gate, &mut formula, &mut pending_deleted);
        assert_eq!(formula.stats.bva_binary_and_factors, 0);
        assert_eq!(formula.stats.bva_non_binary_and_factors, 1);
        assert_eq!(
            formula
                .extensions
                .substitute(&Literal::new(1), &Literal::new(2)),
            None
        );
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
        let initial_clause_limit = formula.clause_slots_len();
        let mut pending_deleted = vec![false; initial_clause_limit];
        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");

        let deletion_indices = apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(formula.assignment.len(), 8);
        assert_eq!(formula.stats.bva_literals, 1);
        assert_eq!(formula.stats.bva_binary_and_factors, 1);
        assert_eq!(formula.stats.bva_non_binary_and_factors, 0);
        assert_eq!(
            formula.extensions.definition(&Literal::new(7)),
            Some(&ExtensionDefinition::And(vec![
                Literal::new(1),
                Literal::new(2),
            ]))
        );
        assert_eq!(
            formula
                .extensions
                .substitute(&Literal::new(1), &Literal::new(2)),
            Some(Literal::new(7))
        );
        assert_eq!(
            formula.extensions.substitution_inputs(&Literal::new(7)),
            Some((Literal::new(2), Literal::new(1)))
        );
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
                vec![-2, -1, 7],
                vec![3, 7],
                vec![4, 7],
                vec![5, 7],
                vec![6, 7],
            ]
        );
        assert!(
            formula
                .get_clauses_and_garbage()
                .filter(|(physical_index, _)| *physical_index >= initial_clause_limit)
                .all(|(idx, clause)| clause.bva_generated
                    && clause.lbd
                        == if (initial_clause_limit + 1..initial_clause_limit + 5).contains(&idx) {
                            -1
                        } else {
                            0
                        })
        );
    }

    #[test]
    fn binary_grid_that_breaks_even_keeps_legacy_acceptance() {
        let formula = Formula::from_vec(vec![
            vec![1, 3],
            vec![1, 4],
            vec![1, 5],
            vec![2, 3],
            vec![2, 4],
            vec![2, 5],
        ]);
        let pending_deleted = vec![false; formula.clause_slots_len()];

        let gate = find(&formula, 1, &pending_deleted).expect("legacy score is profitable");
        assert_eq!(gate.factor_score(), 1);
        assert_eq!(gate.clause_saving(), 0);
        assert_eq!(formula.assignment.len(), 6);
        assert_eq!(formula.live_clause_count(), 6);
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
        let pending_deleted = vec![false; formula.clause_slots_len()];

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
        let initial_clause_limit = formula.clause_slots_len();
        let mut pending_deleted = vec![false; initial_clause_limit];
        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");
        assert_eq!(gate.clause_saving(), 1);

        apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(
            sorted_generated_clauses(&formula, initial_clause_limit),
            vec![
                vec![-8, 1],
                vec![-8, 2],
                vec![-2, -1, 8],
                vec![3, 4, 8],
                vec![3, 5, 8],
                vec![6, 8],
                vec![7, 8],
            ]
        );

        let quotient_idx = initial_clause_limit + 1;
        assert_eq!(formula.get_clause_at_idx(quotient_idx).lbd, -1);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let z = crate::formula::extension::extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(-3),
            &Literal::new(-4),
        );
        let replacement_idx = formula.clause_slots_len();
        let scope = crate::process::ClauseScope::indices([quotient_idx]);
        crate::process::ges::process(&mut formula, &scope, &mut logger, None, None, None).unwrap();
        assert!(formula.is_clause_garbage(quotient_idx));
        let replacement = formula
            .get_clauses()
            .filter(|(idx, _)| *idx >= replacement_idx)
            .map(|(_, clause)| clause)
            .find(|clause| clause.get_literals() == [Literal::new(8), z.negated()])
            .expect("ordinary GES rewrites the generated AND quotient");
        assert_eq!(replacement.lbd, -1);
        assert!(replacement.bva_generated);
        assert!(!formula.is_clause_garbage(initial_clause_limit));
        assert_eq!(formula.get_clause_at_idx(initial_clause_limit).lbd, 0);
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
        let initial_clause_limit = formula.clause_slots_len();
        let mut pending_deleted = vec![false; initial_clause_limit];

        let gate = find(&formula, 1, &pending_deleted).expect("expected profitable grid");
        assert_eq!(gate.clause_saving(), 3);
        assert_eq!(gate.source_indices.len(), 8);

        let deletion_indices = apply(gate, &mut formula, &mut pending_deleted);

        assert_eq!(deletion_indices.len(), 8);
        assert_eq!(deletion_indices, (0..8).collect::<Vec<_>>());
        assert_eq!(formula.live_clause_count(), 13);
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
        let initial_clause_limit = formula.clause_slots_len();
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
        let pending_deleted = vec![false; formula.clause_slots_len()];

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
