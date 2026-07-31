use crate::circuits::factorization::{
    BudgetResult, FACTOR_BOUND, MAX_FACTOR_CLAUSE_SIZE, claim_clause,
    generated_clause, is_tautological, literal_tie_key, stable_signature_hash,
};
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::literal::Literal;
use crate::process::bva::{ClauseWindow, live_window_factor_clause};
use pyo3::prelude::PyResult;
use std::collections::{BTreeMap, HashMap};
use std::io::Write;

const GATE_DEFINITION_CLAUSES: usize = 4;
const MIN_GATE_MATCHES: usize = GATE_DEFINITION_CLAUSES + FACTOR_BOUND;

pub(crate) struct Gate {
    target: i32,
    second: i32,
    third: i32,
    matches: Vec<GateMatch>,
    clause_saving: isize,
}

impl Gate {
    pub(crate) fn find(
        formula: &Formula,
        window: &ClauseWindow,
        pending_deleted: &[bool],
        target: i32,
    ) -> PyResult<BudgetResult<Option<Self>>> {
        let pairs = match extract_signature_pairs(
            formula,
            window,
            pending_deleted,
            target,
        )? {
            BudgetResult::Complete(pairs) => pairs,
            BudgetResult::Exhausted => return Ok(BudgetResult::Exhausted),
        };

        group_pairs(
            &pairs,
            target,
            pending_deleted.len()
        )
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
        let z = formula.add_literal();
        formula.stats.add_bva_literal();

        // z <-> ITE(target, -third, -second). Every resolvent between a
        // positive-z and a negative-z definition clause is tautological, so
        // these clauses are valid blocked/RAT additions in this order.
        let definitions = [
            vec![
                z.clone(),
                Literal::new(self.target),
                Literal::new(self.second),
            ],
            vec![
                z.clone(),
                Literal::new(-self.target),
                Literal::new(self.third),
            ],
            vec![
                z.negated(),
                Literal::new(self.target),
                Literal::new(-self.second),
            ],
            vec![
                z.negated(),
                Literal::new(-self.target),
                Literal::new(-self.third),
            ],
        ];
        for definition in definitions {
            formula.add_clause_unchecked(generated_clause(definition), logger);
        }

        for gate_match in &self.matches {
            let output = if gate_match.output_positive {
                z.clone()
            } else {
                z.negated()
            };
            let first_branch = if gate_match.output_positive {
                -self.second
            } else {
                self.second
            };
            let first_source = formula.get_clause_at_idx(gate_match.first_clause);
            let mut quotient = Vec::with_capacity(first_source.len() - 1);
            quotient.push(output.clone());
            quotient.extend(first_source.iter().filter_map(|literal| {
                let literal_index = literal.get_index();
                (literal_index != self.target && literal_index != first_branch)
                    .then(|| literal.clone())
            }));

            // These proof-only resolvents make the quotient RUP even after
            // quotients of the opposite output polarity have been added.
            let proof_intermediates = logger.is_some().then(|| {
                let mut first = Vec::with_capacity(quotient.len() + 1);
                let mut second = Vec::with_capacity(quotient.len() + 1);
                first.push(output.clone());
                first.push(Literal::new(self.target));
                second.push(output.clone());
                second.push(Literal::new(-self.target));
                first.extend(quotient.iter().skip(1).cloned());
                second.extend(quotient.iter().skip(1).cloned());
                (first, second)
            });
            if let (Some(log), Some((first, second))) =
                (logger.as_mut(), proof_intermediates.as_ref())
            {
                let _ = log.log_add(first);
                let _ = log.log_add(second);
            }

            formula.add_clause_unchecked(generated_clause(quotient), logger);

            if let (Some(log), Some((first, second))) =
                (logger.as_mut(), proof_intermediates.as_ref())
            {
                let _ = log.log_delete(first);
                let _ = log.log_delete(second);
            }
        }

        // Keep every source physically available until all proof-safe
        // additions are complete, then hide it from later searches in the pass.
        for gate_match in self.matches {
            claim_clause(gate_match.first_clause, pending_deleted, deletion_indices);
            claim_clause(gate_match.second_clause, pending_deleted, deletion_indices);
        }
    }
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

/// Algorithms 1 and 2 from the gate-factorization paper, indexed by exact
/// common remainders. Physical duplicate clauses are paired one-to-one rather
/// than expanded into a Cartesian product.
fn extract_signature_pairs(
    formula: &Formula,
    window: &ClauseWindow,
    pending_deleted: &[bool],
    target: i32,
) -> PyResult<BudgetResult<Vec<ExtractedPair>>> {
    
    let mut first_by_size: [Vec<usize>; MAX_FACTOR_CLAUSE_SIZE + 1] =
        std::array::from_fn(|_| Vec::new());
    let mut second_by_size: [Vec<usize>; MAX_FACTOR_CLAUSE_SIZE + 1] =
        std::array::from_fn(|_| Vec::new());

    for clause_idx in formula.occurrence_of(&Literal::new(target)) {
        if live_gate_clause(formula, clause_idx, window, pending_deleted) {
            let size = formula.get_clause_at_idx(clause_idx).len();
            first_by_size[size].push(clause_idx);
        }
    }
    for clause_idx in formula.occurrence_of(&Literal::new(-target)) {
        if live_gate_clause(formula, clause_idx, window, pending_deleted) {
            let size = formula.get_clause_at_idx(clause_idx).len();
            second_by_size[size].push(clause_idx);
        }
    }

    let mut pairs = Vec::new();
    let mut sorted_clause = Vec::new();
    let mut remainder = Vec::new();
    for size in 3..=MAX_FACTOR_CLAUSE_SIZE {
        if first_by_size[size].is_empty() || second_by_size[size].is_empty() {
            continue;
        }

        let mut signatures = Vec::<GateSignature>::new();
        let mut hash_buckets = HashMap::<u64, Vec<usize>>::new();

        for &clause_idx in &first_by_size[size] {
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

            for &branch in &sorted_clause {
                if branch == target {
                    continue;
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

            for &branch in &sorted_clause {
                if branch == -target {
                    continue;
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
            for (first_branch, first_clauses) in &signature.first_branches {
                for (second_branch, second_clauses) in &signature.second_branches {
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
    window: &ClauseWindow,
    pending_deleted: &[bool],
) -> bool {
    live_window_factor_clause(
        formula,
        clause_idx,
        window,
        pending_deleted,
    ) && formula.get_clause_at_idx(clause_idx).len() >= 3
}

/// Algorithm 3 from the paper: normalize simultaneous polarity flips, select
/// the largest group, and claim each physical clause at most once per group.
fn group_pairs(
    pairs: &[ExtractedPair],
    target: i32,
    initial_clause_limit: usize,
) -> PyResult<BudgetResult<Option<Gate>>> {
    let mut variable_counts = BTreeMap::<u32, usize>::new();
    for pair in pairs {
        *variable_counts
            .entry(pair.second_branch.unsigned_abs())
            .or_default() += 1;
    }

    let mut groups = BTreeMap::<(u32, u32, bool), Vec<ExtractedPair>>::new();
    for &pair in pairs {
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
        let literal = if literal_negative {
            -(literal_variable as i32)
        } else {
            literal_variable as i32
        };
        let mut matches = Vec::new();
        let mut claimed_here = Vec::new();
        for pair in group {
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

    Ok(BudgetResult::Complete(Some(Gate {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::clause::Clause;

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

    fn find_gate(formula: &Formula, target: i32) -> Gate {
        let initial_clause_limit = formula.clause_slots_len();
        let pending_deleted = vec![false; initial_clause_limit];
        let window = ClauseWindow::all_eligible(
            formula,
            initial_clause_limit,
        );

        match Gate::find(
            formula,
            &window,
            &pending_deleted,
            target,
        )
        .unwrap()
        {
            BudgetResult::Complete(Some(gate)) => gate,
            BudgetResult::Complete(None) => panic!("expected gate"),
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        }
    }

    fn extracted_pairs(formula: &Formula, target: i32) -> Vec<ExtractedPair> {
        let initial_clause_limit = formula.clause_slots_len();
        let pending_deleted = vec![false; initial_clause_limit];
        let window = ClauseWindow::all_eligible(
            formula,
            initial_clause_limit,
        );

        match extract_signature_pairs(
            formula,
            &window,
            &pending_deleted,
            target,
        )
        .unwrap()
        {
            BudgetResult::Complete(pairs) => pairs,
            BudgetResult::Exhausted => panic!("test budget exhausted"),
        }
    }

    fn sorted_clauses(formula: &Formula) -> Vec<Vec<i32>> {
        let mut clauses = formula
            .get_clauses()
            .map(|(_, clause)| Clause::sorted_literal_indices(clause))
            .collect::<Vec<_>>();
        clauses.sort();
        clauses
    }

    fn contains_clause(clauses: &[Vec<i32>], mut expected: Vec<i32>) -> bool {
        expected.sort_unstable();
        clauses.contains(&expected)
    }

    #[test]
    fn signature_extraction_and_grouping_follow_the_gate_algorithms() {
        let formula = ite_formula();
        let pairs = extracted_pairs(&formula, 1);

        assert_eq!(pairs.len(), 5);
        assert_eq!(pairs[0].first_branch, 2);
        assert_eq!(pairs[0].second_branch, 3);

        let initial_clause_limit = formula.clause_slots_len();
        let gate = match group_pairs(&pairs, 1, initial_clause_limit).unwrap()
        {
            BudgetResult::Complete(Some(gate)) => gate,
            _ => panic!("expected gate"),
        };

        assert_eq!(gate.second, 2);
        assert_eq!(gate.third, 3);
        assert_ne!(gate.second, -gate.third);
        assert_eq!(gate.matches.len(), 5);
        assert_eq!(gate.clause_saving(), 1);
        assert_eq!(
            gate.matches
                .iter()
                .filter(|gate_match| gate_match.output_positive)
                .count(),
            2
        );
    }

    #[test]
    fn ite_application_adds_definitions_and_quotients_then_claims_sources() {
        let mut formula = ite_formula();
        let gate = find_gate(&formula, 1);
        let initial_clause_limit = formula.clause_slots_len();
        let initial_live_clause_count = formula.live_clause_count();
        let mut pending_deleted = vec![false; initial_clause_limit];
        let mut deletion_indices = Vec::new();
        let mut logger: Option<DratLogger<std::io::Empty>> = None;

        gate.apply(
            &mut formula,
            &mut logger,
            &mut pending_deleted,
            &mut deletion_indices,
        );

        assert_eq!(formula.assignment.len(), 16);
        assert_eq!(formula.live_clause_count(), initial_live_clause_count + 9);
        assert_eq!(formula.stats.bva_literals, 1);
        assert!(pending_deleted.iter().all(|pending| *pending));
        assert_eq!(
            deletion_indices,
            (0..initial_clause_limit).collect::<Vec<_>>()
        );

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
                .get_clauses_and_garbage()
                .filter(|(physical_index, clause)| {
                    *physical_index >= initial_clause_limit
                        && clause.lbd() == 0
                        && clause.is_bva_generated()
                })
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
        let gate = find_gate(&formula, 1);

        assert_eq!(gate.second, -gate.third);
        assert_eq!(gate.second, -3);
        assert_eq!(gate.third, 3);
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

        let gate = match group_pairs(&pairs, 1, 20).unwrap() {
            BudgetResult::Complete(Some(gate)) => gate,
            _ => panic!("expected gate"),
        };

        assert_eq!(gate.matches.len(), 5);
        assert_eq!(gate.second, 2);
        assert_eq!(gate.third, 4);
        assert_ne!(gate.second, -gate.third);
    }

    #[test]
    fn extraction_and_grouping_do_not_reuse_a_physical_clause() {
        let formula = Formula::from_vec(vec![
            vec![1, 2, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
            vec![-1, 3, 10],
        ]);
        let pairs = extracted_pairs(&formula, 1);
        assert_eq!(pairs.len(), 1);

        assert!(matches!(
            group_pairs(&pairs, 1, formula.clause_slots_len()).unwrap(),
            BudgetResult::Complete(None)
        ));
    }

    #[test]
    fn duplicate_inflation_does_not_hide_a_profitable_group() {
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
        let gate = find_gate(&formula, 1);

        assert_eq!(gate.second, 4);
        assert_eq!(gate.third, 5);
        assert_eq!(gate.matches.len(), 5);
    }

    #[test]
    fn definitions_and_proof_intermediates_precede_each_quotient() {
        let mut formula = ite_formula();
        let gate = find_gate(&formula, 1);
        let initial_clause_limit = formula.clause_slots_len();
        let mut pending_deleted = vec![false; initial_clause_limit];
        let mut deletion_indices = Vec::new();
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));

        gate.apply(
            &mut formula,
            &mut logger,
            &mut pending_deleted,
            &mut deletion_indices,
        );
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
    fn size_limit_and_buckets_prevent_invalid_cross_matches() {
        let common = (100..=117).collect::<Vec<_>>();
        let mut oversized = Vec::new();
        for remainder in 10..=14 {
            let mut first = common.clone();
            first.extend([1, 2, remainder]);
            oversized.push(first);
            let mut second = common.clone();
            second.extend([-1, 3, remainder]);
            oversized.push(second);
        }
        assert!(extracted_pairs(&Formula::from_vec(oversized), 1).is_empty());

        let mixed_sizes = Formula::from_vec(vec![
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
        assert!(extracted_pairs(&mixed_sizes, 1).is_empty());
    }

    #[test]
    fn signature_hash_collisions_require_exact_remainder_comparison() {
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
