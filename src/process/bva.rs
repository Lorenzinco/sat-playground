use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::history::History;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::Write;

pub fn process<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    mut history: Option<&mut History>,
) -> PyResult<()> {
    let mut run = BvaRunSummary::default();

    while let Some(step) =
        apply_best_bva_step(formula, logger, &mut signal, history.as_deref_mut())?
    {
        run.record(&step);
    }

    Ok(())
}

fn apply_best_bva_step<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    signal: &mut Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
) -> PyResult<Option<BvaStepSummary>> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let Some(candidate) = find_best_bva_candidate(formula, signal)? else {
        return Ok(None);
    };

    let summary = apply_bva_candidate(formula, logger, history, candidate);

    Ok(Some(summary))
}

fn find_best_bva_candidate(
    formula: &Formula,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Option<BvaCandidate>> {
    let index = BvaIndex::new(formula);
    if index.literal_to_partials.is_empty() {
        return Ok(None);
    }

    let mut starts = index
        .literal_occurrences
        .iter()
        .map(|(&lit, &occurrences)| (lit, occurrences))
        .collect::<Vec<_>>();
    starts.sort_by(|(lit_a, occ_a), (lit_b, occ_b)| {
        occ_b
            .cmp(occ_a)
            .then_with(|| literal_tie_key(*lit_a).cmp(&literal_tie_key(*lit_b)))
    });

    let mut best = None;
    let mut three_hop_cache = HashMap::new();

    for (start, start_occurrences) in starts {
        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }

        let Some(candidate) = build_candidate_for_start(
            formula,
            &index,
            start,
            start_occurrences,
            &mut three_hop_cache,
            signal,
        )?
        else {
            continue;
        };

        if best
            .as_ref()
            .is_none_or(|current| candidate.is_better_than(current))
        {
            best = Some(candidate);
        }
    }

    Ok(best)
}

fn build_candidate_for_start(
    formula: &Formula,
    index: &BvaIndex,
    start: i32,
    start_occurrences: usize,
    three_hop_cache: &mut HashMap<(usize, usize), u64>,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<Option<BvaCandidate>> {
    let Some(start_partials) = index.literal_to_partials.get(&start) else {
        return Ok(None);
    };

    let mut literals = vec![start];
    let mut literal_set = HashSet::from([start]);
    let mut partial_ids = start_partials.iter().copied().collect::<Vec<_>>();
    partial_ids.sort_unstable();

    let mut current_clause_saving = clause_saving(literals.len(), partial_ids.len());

    loop {
        if let Some((py, steps)) = signal.as_mut() {
            signal_checker(*py, *steps)?;
        }

        let mut counts: HashMap<i32, usize> = HashMap::new();
        for &partial_id in &partial_ids {
            for &candidate_lit in &index.partial_to_literals[partial_id] {
                if !literal_set.contains(&candidate_lit) {
                    *counts.entry(candidate_lit).or_default() += 1;
                }
            }
        }

        let Some((next_lit, remaining_partials)) =
            choose_next_literal(index, start, counts, three_hop_cache)
        else {
            break;
        };

        let next_clause_saving = clause_saving(literals.len() + 1, remaining_partials);
        if next_clause_saving <= current_clause_saving {
            break;
        }

        literal_set.insert(next_lit);
        literals.push(next_lit);
        partial_ids.retain(|&partial_id| index.has_clause_for(next_lit, partial_id));
        current_clause_saving = next_clause_saving;
    }

    if literals.len() < 2 || partial_ids.is_empty() || current_clause_saving <= 1 {
        return Ok(None);
    }

    let mut to_delete = Vec::new();
    for &lit in &literals {
        for &partial_id in &partial_ids {
            let Some(indices) = index.clause_indices.get(&(lit, partial_id)) else {
                return Ok(None);
            };
            to_delete.extend(indices.iter().copied());
        }
    }
    to_delete.sort_unstable();
    to_delete.dedup();

    let added_clauses = literals.len() + partial_ids.len();
    let actual_clause_saving = to_delete.len() as isize - added_clauses as isize;
    if actual_clause_saving <= 1 {
        return Ok(None);
    }

    let deleted_literals = to_delete
        .iter()
        .map(|&idx| formula.get_clauses()[idx].len())
        .sum::<usize>();
    let added_literals = partial_ids
        .iter()
        .map(|&partial_id| index.partials[partial_id].len() + 1)
        .sum::<usize>()
        + literals.len() * 2;

    let partials = partial_ids
        .iter()
        .map(|&partial_id| index.partials[partial_id].clone())
        .collect::<Vec<_>>();

    Ok(Some(BvaCandidate {
        start,
        start_occurrences,
        literals,
        partials,
        to_delete,
        added_clauses,
        clause_saving: actual_clause_saving,
        size_saving: actual_clause_saving - 1,
        literal_saving: deleted_literals as isize - added_literals as isize,
    }))
}

fn choose_next_literal(
    index: &BvaIndex,
    start: i32,
    counts: HashMap<i32, usize>,
    three_hop_cache: &mut HashMap<(usize, usize), u64>,
) -> Option<(i32, usize)> {
    let start_var = start.unsigned_abs() as usize;
    let mut best: Option<(i32, usize, u64)> = None;

    for (lit, count) in counts {
        if count == 0 {
            continue;
        }

        let hop_score = three_hop_score(
            index,
            three_hop_cache,
            start_var,
            lit.unsigned_abs() as usize,
        );
        let replace = match best {
            None => true,
            Some((best_lit, best_count, best_hop_score)) => {
                count > best_count
                    || (count == best_count && hop_score > best_hop_score)
                    || (count == best_count
                        && hop_score == best_hop_score
                        && literal_tie_key(lit) < literal_tie_key(best_lit))
            }
        };

        if replace {
            best = Some((lit, count, hop_score));
        }
    }

    best.map(|(lit, count, _)| (lit, count))
}

fn apply_bva_candidate<W: Write>(
    formula: &mut Formula,
    logger: &mut Option<DratLogger<W>>,
    history: Option<&mut History>,
    candidate: BvaCandidate,
) -> BvaStepSummary {
    let z = formula.add_literal();
    formula.stats.add_bva_literal();

    for partial in &candidate.partials {
        let mut literals = Vec::with_capacity(partial.len() + 1);
        literals.push(z.clone());
        literals.extend(partial.iter().map(|&idx| Literal::new(idx)));
        formula.add_clause_unchecked(bva_clause(literals), logger);
    }

    for &lit in &candidate.literals {
        formula.add_clause_unchecked(bva_clause(vec![z.negated(), Literal::new(lit)]), logger);
    }

    for &idx in &candidate.to_delete {
        let deleted = formula.get_clauses()[idx].clone();
        formula.stats.remove_clause(&deleted);
    }
    let old_to_new = formula.delete_clauses(&candidate.to_delete, logger);
    if let Some(history) = history {
        history.remap_clause_indices(&old_to_new);
    }

    BvaStepSummary {
        new_var: z.get_index(),
        literals: candidate.literals.len(),
        partials: candidate.partials.len(),
        deleted_clauses: candidate.to_delete.len(),
        added_clauses: candidate.added_clauses,
        clause_saving: candidate.clause_saving,
        size_saving: candidate.size_saving,
        literal_saving: candidate.literal_saving,
    }
}

fn bva_clause(literals: Vec<Literal>) -> Clause {
    let mut clause = Clause::from_literals(literals, 0);
    clause.bva_generated = true;
    clause
}

fn clause_saving(literals: usize, partials: usize) -> isize {
    (literals * partials) as isize - literals as isize - partials as isize
}

fn literal_tie_key(lit: i32) -> (u32, bool) {
    (lit.unsigned_abs(), lit.is_negative())
}

fn three_hop_score(
    index: &BvaIndex,
    cache: &mut HashMap<(usize, usize), u64>,
    a: usize,
    b: usize,
) -> u64 {
    let key = if a <= b { (a, b) } else { (b, a) };
    if let Some(&score) = cache.get(&key) {
        return score;
    }

    let mut score = 0u64;
    if let Some(a_neighbors) = index.variable_adjacency.get(a) {
        for (&mid_a, &weight_a) in a_neighbors {
            let Some(mid_a_neighbors) = index.variable_adjacency.get(mid_a) else {
                continue;
            };
            for (&mid_b, &weight_mid) in mid_a_neighbors {
                let Some(&weight_b) = index
                    .variable_adjacency
                    .get(mid_b)
                    .and_then(|neighbors| neighbors.get(&b))
                else {
                    continue;
                };
                score = score
                    .saturating_add(weight_a.saturating_mul(weight_mid).saturating_mul(weight_b));
            }
        }
    }

    cache.insert(key, score);
    score
}

fn sorted_without(sorted_clause: &[i32], lit_to_remove: i32) -> Vec<i32> {
    sorted_clause
        .iter()
        .copied()
        .filter(|&lit| lit != lit_to_remove)
        .collect()
}

fn sorted_variables(clause: &Clause) -> Vec<usize> {
    let mut variables = clause
        .get_literals()
        .iter()
        .map(|lit| lit.get_index().unsigned_abs() as usize)
        .collect::<Vec<_>>();
    variables.sort_unstable();
    variables.dedup();
    variables
}

fn is_tautological(sorted_clause: &[i32]) -> bool {
    sorted_clause
        .iter()
        .any(|&lit| sorted_clause.binary_search(&-lit).is_ok())
}

fn bva_eligible_clause(clause: &Clause) -> bool {
    clause.lock_count == 0 && clause.len() >= 2 && (clause.lbd != 0 || clause.bva_generated)
}

#[derive(Default)]
struct BvaRunSummary {
    steps: usize,
    deleted_clauses: usize,
    added_clauses: usize,
    clause_saving: isize,
    size_saving: isize,
    literal_saving: isize,
}

impl BvaRunSummary {
    fn record(&mut self, step: &BvaStepSummary) {
        self.steps += 1;
        self.deleted_clauses += step.deleted_clauses;
        self.added_clauses += step.added_clauses;
        self.clause_saving += step.clause_saving;
        self.size_saving += step.size_saving;
        self.literal_saving += step.literal_saving;
    }
}

struct BvaStepSummary {
    new_var: i32,
    literals: usize,
    partials: usize,
    deleted_clauses: usize,
    added_clauses: usize,
    clause_saving: isize,
    size_saving: isize,
    literal_saving: isize,
}

struct BvaCandidate {
    start: i32,
    start_occurrences: usize,
    literals: Vec<i32>,
    partials: Vec<Vec<i32>>,
    to_delete: Vec<usize>,
    added_clauses: usize,
    clause_saving: isize,
    size_saving: isize,
    literal_saving: isize,
}

impl BvaCandidate {
    fn is_better_than(&self, other: &Self) -> bool {
        self.clause_saving > other.clause_saving
            || (self.clause_saving == other.clause_saving
                && self.literal_saving > other.literal_saving)
            || (self.clause_saving == other.clause_saving
                && self.literal_saving == other.literal_saving
                && self.start_occurrences > other.start_occurrences)
            || (self.clause_saving == other.clause_saving
                && self.literal_saving == other.literal_saving
                && self.start_occurrences == other.start_occurrences
                && literal_tie_key(self.start) < literal_tie_key(other.start))
    }
}

struct BvaIndex {
    partials: Vec<Vec<i32>>,
    partial_to_literals: Vec<Vec<i32>>,
    literal_to_partials: HashMap<i32, HashSet<usize>>,
    clause_indices: HashMap<(i32, usize), Vec<usize>>,
    literal_occurrences: HashMap<i32, usize>,
    variable_adjacency: Vec<HashMap<usize, u64>>,
}

impl BvaIndex {
    fn new(formula: &Formula) -> Self {
        let mut variable_adjacency = vec![HashMap::new(); formula.assignment.len()];
        for clause in formula.get_clauses() {
            let variables = sorted_variables(clause);
            for i in 0..variables.len() {
                for j in (i + 1)..variables.len() {
                    let a = variables[i];
                    let b = variables[j];
                    if a >= variable_adjacency.len() || b >= variable_adjacency.len() {
                        continue;
                    }
                    *variable_adjacency[a].entry(b).or_default() += 1;
                    *variable_adjacency[b].entry(a).or_default() += 1;
                }
            }
        }

        let mut partial_ids: HashMap<Vec<i32>, usize> = HashMap::new();
        let mut partials = Vec::new();
        let mut partial_to_literals: Vec<HashSet<i32>> = Vec::new();
        let mut literal_to_partials: HashMap<i32, HashSet<usize>> = HashMap::new();
        let mut clause_indices: HashMap<(i32, usize), Vec<usize>> = HashMap::new();
        let mut literal_occurrences: HashMap<i32, usize> = HashMap::new();

        for (clause_idx, clause) in formula.get_clauses().iter().enumerate() {
            if !bva_eligible_clause(clause) {
                continue;
            }

            let sorted_clause = clause.sorted_literal_indices();
            if is_tautological(&sorted_clause) {
                continue;
            }

            for &lit in &sorted_clause {
                let partial = sorted_without(&sorted_clause, lit);
                if partial.binary_search(&-lit).is_ok() {
                    continue;
                }

                let partial_id = if let Some(&partial_id) = partial_ids.get(&partial) {
                    partial_id
                } else {
                    let partial_id = partials.len();
                    partial_ids.insert(partial.clone(), partial_id);
                    partials.push(partial);
                    partial_to_literals.push(HashSet::new());
                    partial_id
                };

                partial_to_literals[partial_id].insert(lit);
                literal_to_partials
                    .entry(lit)
                    .or_default()
                    .insert(partial_id);
                clause_indices
                    .entry((lit, partial_id))
                    .or_default()
                    .push(clause_idx);
                *literal_occurrences.entry(lit).or_default() += 1;
            }
        }

        let partial_to_literals = partial_to_literals
            .into_iter()
            .map(|set| {
                let mut literals = set.into_iter().collect::<Vec<_>>();
                literals.sort_unstable_by_key(|lit| literal_tie_key(*lit));
                literals
            })
            .collect::<Vec<_>>();

        Self {
            partials,
            partial_to_literals,
            literal_to_partials,
            clause_indices,
            literal_occurrences,
            variable_adjacency,
        }
    }

    fn has_clause_for(&self, lit: i32, partial_id: usize) -> bool {
        self.clause_indices.contains_key(&(lit, partial_id))
    }
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
        assert!(clauses.contains(&vec![-7, 1]));
        assert!(clauses.contains(&vec![-7, 2]));
        assert!(clauses.contains(&vec![3, 7]));
        assert!(clauses.contains(&vec![4, 7]));
        assert!(clauses.contains(&vec![5, 7]));
        assert!(clauses.contains(&vec![6, 7]));
        assert!(
            formula
                .get_clauses()
                .iter()
                .all(|clause| clause.lbd == 0 && clause.bva_generated)
        );
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
}
