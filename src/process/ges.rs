use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::extension::ExtensionMap;
use crate::formula::literal::Literal;
use crate::heuristics::vsids::Vsids;
use crate::history::History;
use crate::process::ClauseScope;
use crate::python::signal_checker;

use pyo3::Python;
use pyo3::prelude::PyResult;
use std::collections::{HashMap, HashSet};
use std::io::Write;

/// Reformulates live clauses with exact extension substitutions.
///
/// Every compressible `!z` is first expanded through registered
/// `z <-> (a & b)` definitions. The clause is then rerolled using substitutions
/// that minimize its LBD under the current reasoning snapshot. The replacement
/// is added before the source is deleted, so proof logging retains the source
/// clause and extension axioms needed to RUP-check it.
pub(crate) const MAX_CLAUSES_PER_PASS: usize = 250;

#[derive(Clone, Copy)]
pub(crate) enum Policy {
    Cursor,
    Lbd,
    Random,
    Vsids,
    Always,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Objective {
    Lbd,
    Vsids,
    Always,
}

impl Objective {
    fn uses_lbd(self) -> bool {
        !matches!(self, Self::Vsids)
    }
}

pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
    reasoning_levels: Option<&[Option<usize>]>,
) -> PyResult<()> {
    process_with_policy(
        formula,
        scope,
        logger,
        signal,
        history,
        reasoning_levels,
        Policy::Cursor,
    )
}

pub(crate) fn process_with_policy<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    mut signal: Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
    reasoning_levels: Option<&[Option<usize>]>,
    policy: Policy,
) -> PyResult<()> {
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }

    let mut replacements = Vec::new();
    let indices = select_clause_indices(formula, scope, policy);
    let mut workspace = PassWorkspace::new(&formula.extensions);
    workspace.objective = match policy {
        Policy::Vsids => Objective::Vsids,
        Policy::Always => Objective::Always,
        _ => Objective::Lbd,
    };
    let mut reports = Vec::new();
    for clause_idx in indices {
        let evaluation = workspace.evaluate(
            &formula.vsids,
            formula.get_clause_at_idx(clause_idx),
            history.is_some(),
            reasoning_levels,
        );
        reports.push(evaluation.report);
        if let Some(replacement) = evaluation.replacement {
            replacements.push((clause_idx, replacement));
        }
    }

    for report in reports {
        report.merge_into(formula);
    }
    commit_replacements(formula, replacements, logger, history);
    Ok(())
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EvaluationReport {
    pub(crate) inspected: u64,
    pub(crate) noop: u64,
    pub(crate) rejected: u64,
    pub(crate) lbd_improvements: u64,
    pub(crate) vsids_improvements: u64,
    pub(crate) literals_removed: u64,
}

impl EvaluationReport {
    pub(crate) fn merge_into(self, formula: &mut Formula) {
        formula.stats.ges_clauses_inspected += self.inspected;
        formula.stats.ges_noop_rewrites += self.noop;
        formula.stats.ges_rewrites_rejected += self.rejected;
        formula.stats.ges_lbd_improvements += self.lbd_improvements;
        formula.stats.ges_vsids_improvements += self.vsids_improvements;
        formula.stats.ges_literals_removed += self.literals_removed;
    }
}

pub(crate) struct Evaluation {
    pub(crate) replacement: Option<Clause>,
    pub(crate) report: EvaluationReport,
}

impl Evaluation {
    fn without_replacement(noop: bool, rejected: bool) -> Self {
        Self {
            replacement: None,
            report: EvaluationReport {
                inspected: 1,
                noop: u64::from(noop),
                rejected: u64::from(rejected),
                ..EvaluationReport::default()
            },
        }
    }
}

#[cfg(test)]
pub(crate) fn evaluate_clause(
    extensions: &ExtensionMap,
    vsids: &Vsids,
    clause: &Clause,
    has_history: bool,
    reasoning_levels: Option<&[Option<usize>]>,
) -> Evaluation {
    PassWorkspace::new(extensions).evaluate(vsids, clause, has_history, reasoning_levels)
}

/// Borrows one immutable extension snapshot, so cached expansions cannot outlive it.
/// Parallel callers own one workspace per chunk, with no shared mutable cache.
pub(crate) struct PassWorkspace<'a> {
    extensions: &'a ExtensionMap,
    objective: Objective,
    source_activities: Vec<f64>,
    final_activities: Vec<f64>,
    expansions: HashMap<i32, Option<Vec<Literal>>>,
    cached_units: usize,
    expanded: Vec<Literal>,
    expanding: HashSet<i32>,
    literals: Vec<Literal>,
    literal_set: HashSet<Literal>,
    source_set: HashSet<Literal>,
    blocks: Vec<Block>,
    frequencies: BlockCounts,
    positions: HashMap<i32, usize>,
    pairs: Vec<(usize, usize, Literal)>,
}

// Bound both stored literals and entries; large expansions still work uncached.
const MAX_CACHED_EXPANSION_UNITS: usize = 65_536;

impl<'a> PassWorkspace<'a> {
    pub(crate) fn new(extensions: &'a ExtensionMap) -> Self {
        Self {
            extensions,
            objective: Objective::Lbd,
            source_activities: Vec::new(),
            final_activities: Vec::new(),
            expansions: HashMap::new(),
            cached_units: 0,
            expanded: Vec::new(),
            expanding: HashSet::new(),
            literals: Vec::new(),
            literal_set: HashSet::new(),
            source_set: HashSet::new(),
            blocks: Vec::new(),
            frequencies: BlockCounts::default(),
            positions: HashMap::new(),
            pairs: Vec::new(),
        }
    }

    fn unroll(&mut self, source: &[Literal]) -> bool {
        self.literals.clear();
        self.literal_set.clear();
        for &literal in source {
            if self
                .extensions
                .substitution_inputs(&literal.negated())
                .is_none()
            {
                if !append_expansion(&[literal], &mut self.literals, &mut self.literal_set) {
                    return false;
                }
                continue;
            }
            let key = literal.get_index();
            if let Some(cached) = self.expansions.get(&key) {
                let Some(expansion) = cached else {
                    return false;
                };
                if !append_expansion(expansion, &mut self.literals, &mut self.literal_set) {
                    return false;
                }
                continue;
            }
            self.expanded.clear();
            self.expanding.clear();
            // Expand each root with an empty recursion stack. Caching a subtree
            // reached inside a cycle would make the result context-dependent.
            let valid = unroll_literal(
                self.extensions,
                literal,
                &mut self.expanding,
                &mut self.expanded,
            );
            let units = if valid { self.expanded.len() + 1 } else { 1 };
            if units <= MAX_CACHED_EXPANSION_UNITS - self.cached_units {
                self.expansions
                    .insert(key, valid.then(|| self.expanded.clone()));
                self.cached_units += units;
            }
            if !valid
                || !append_expansion(&self.expanded, &mut self.literals, &mut self.literal_set)
            {
                return false;
            }
        }
        true
    }

    pub(crate) fn evaluate(
        &mut self,
        vsids: &Vsids,
        clause: &Clause,
        has_history: bool,
        reasoning_levels: Option<&[Option<usize>]>,
    ) -> Evaluation {
        // Extension axioms remain immutable. Only the isolated `ges_always`
        // experiment may reformulate glue clauses.
        if clause.lbd == 0
            || (clause.lbd == 2 && self.objective != Objective::Always)
            || (clause.lock_count != 0 && !has_history)
        {
            return Evaluation {
                replacement: None,
                report: EvaluationReport::default(),
            };
        }
        substitute_snapshot(self, vsids, clause, reasoning_levels)
    }
}

fn append_expansion(
    expansion: &[Literal],
    literals: &mut Vec<Literal>,
    seen: &mut HashSet<Literal>,
) -> bool {
    for &literal in expansion {
        if seen.contains(&literal.negated()) {
            return false;
        }
        if seen.insert(literal) {
            literals.push(literal);
        }
    }
    true
}

pub(crate) fn commit_replacements<W: Write>(
    formula: &mut Formula,
    replacements: Vec<(usize, Clause)>,
    logger: &mut Option<DratLogger<W>>,
    mut history: Option<&mut History>,
) {
    for (clause_idx, mut replacement) in replacements {
        // Keep proof order: the source clause is needed to RUP-check the
        // replacement, so add the replacement before logging its deletion.
        let source_lock_count = formula.get_clause_at_idx(clause_idx).lock_count;
        replacement.lock_count = source_lock_count;
        replacement.ges_generated = true;
        replacement.ges_used = false;
        for _ in 0..source_lock_count {
            formula.stats.record_ges_reason_use(&mut replacement);
        }
        if replacement.lbd > 0 {
            formula.stats.add_learnt_clause(&replacement);
        }
        let replacement_idx = formula.add_clause_unchecked(replacement, logger);

        if source_lock_count != 0 {
            history
                .as_deref_mut()
                .expect("locked GES source requires history")
                .replace_reason_clause(clause_idx, replacement_idx);
            formula.get_clause_at_idx_mut(clause_idx).lock_count = 0;
        }

        formula.stats.add_global_substitution();
        formula.record_clause_removal(clause_idx);
        formula.delete_clause(clause_idx, logger);
    }
}

fn select_clause_indices(formula: &mut Formula, scope: &ClauseScope, policy: Policy) -> Vec<usize> {
    if matches!(policy, Policy::Cursor | Policy::Vsids | Policy::Always) {
        return select_cursor_clause_indices(formula, scope, MAX_CLAUSES_PER_PASS);
    }
    let slots = formula.clause_slots_len();
    if slots == 0 {
        return Vec::new();
    }
    if matches!(policy, Policy::Lbd) {
        let mut tier3 = Vec::new();
        let mut tier2 = Vec::new();
        for (idx, clause) in formula.get_clauses() {
            if scope.includes(idx, clause) && clause.lbd >= 3 {
                if clause.lbd > 6 {
                    tier3.push((idx, clause.lbd));
                } else {
                    tier2.push((idx, clause.lbd));
                }
            }
        }
        select_lbd_tier(&mut tier3, MAX_CLAUSES_PER_PASS);
        let remaining = MAX_CLAUSES_PER_PASS - tier3.len();
        if remaining != 0 {
            select_lbd_tier(&mut tier2, remaining);
            tier3.extend(tier2);
        }
        return tier3.into_iter().map(|(idx, _)| idx).collect();
    }
    let start = rand::random_range(0..slots);
    sequential_clause_window(formula, scope, start, MAX_CLAUSES_PER_PASS)
        .map(|(idx, _)| idx)
        .collect()
}

/// Count live scoped entries, including clauses protected from evaluation.
/// An empty window leaves the shared cursor unchanged.
pub(crate) fn select_cursor_clause_indices(
    formula: &mut Formula,
    scope: &ClauseScope,
    limit: usize,
) -> Vec<usize> {
    let indices: Vec<_> = sequential_clause_window(formula, scope, formula.ges_cursor, limit)
        .map(|(idx, _)| idx)
        .collect();
    if let Some(&last) = indices.last() {
        formula.ges_cursor = (last + 1) % formula.clause_slots_len();
    }
    indices
}

fn select_lbd_tier(tier: &mut Vec<(usize, i16)>, limit: usize) {
    let order = |(a_idx, a_lbd): &(usize, i16), (b_idx, b_lbd): &(usize, i16)| {
        b_lbd.cmp(a_lbd).then_with(|| a_idx.cmp(b_idx))
    };
    if tier.len() > limit {
        tier.select_nth_unstable_by(limit, order);
        tier.truncate(limit);
    }
    tier.sort_unstable_by(order);
}

fn sequential_clause_window<'a>(
    formula: &'a Formula,
    scope: &'a ClauseScope,
    start: usize,
    limit: usize,
) -> impl Iterator<Item = (usize, &'a Clause)> + 'a {
    let slots = formula.clause_slots_len();
    let start = if slots == 0 { 0 } else { start % slots };
    (start..slots)
        .chain(0..start)
        .filter(move |&idx| !formula.is_clause_garbage(idx))
        .map(move |idx| (idx, formula.get_clause_at_idx(idx)))
        .filter(move |(idx, clause)| scope.includes(*idx, clause))
        .take(limit)
}

#[cfg(test)]
fn substitute_clause(
    formula: &Formula,
    clause: &Clause,
    reasoning_levels: Option<&[Option<usize>]>,
) -> Option<Clause> {
    substitute_snapshot(
        &mut PassWorkspace::new(&formula.extensions),
        &formula.vsids,
        clause,
        reasoning_levels,
    )
    .replacement
}

fn substitute_snapshot(
    workspace: &mut PassWorkspace<'_>,
    vsids: &Vsids,
    clause: &Clause,
    reasoning_levels: Option<&[Option<usize>]>,
) -> Evaluation {
    let objective = workspace.objective;
    if clause.lbd == 2 && objective != Objective::Always {
        return Evaluation::without_replacement(false, false);
    }

    // The acceptance baseline is the source, never the expanded working clause.
    let source = clause.get_literals();
    let source_lbd = objective
        .uses_lbd()
        .then(|| dynamic_lbd_with_scratch(source, reasoning_levels, &mut workspace.frequencies));
    if !workspace.unroll(source) {
        return Evaluation::without_replacement(false, true);
    }
    let PassWorkspace {
        extensions,
        literals,
        blocks,
        frequencies,
        positions,
        pairs,
        source_set,
        source_activities,
        final_activities,
        ..
    } = workspace;
    if objective.uses_lbd() {
        blocks.clear();
        blocks.extend(
            literals
                .iter()
                .map(|&literal| literal_block(literal, reasoning_levels)),
        );
        block_frequencies(blocks, frequencies);
    }
    while literals.len() >= 2 {
        let current_lbd = saturate_lbd(frequencies.len());
        let mut best: Option<(i16, f64, usize, usize, Literal)> = None;

        fill_substitution_pairs(extensions, literals, positions, pairs);
        for &(left_idx, right_idx, replacement) in pairs.iter() {
            // Retaining a tautological clause avoids special proof/deletion
            // handling and cannot accidentally remove a defining axiom.
            if literals.contains(&replacement.negated()) {
                continue;
            }

            let activity = vsids.literal_activity(&replacement);
            let candidate_lbd = match objective {
                Objective::Lbd | Objective::Always => {
                    let lbd = substitution_lbd(
                        frequencies,
                        blocks[left_idx],
                        blocks[right_idx],
                        literal_block(replacement, reasoning_levels),
                    );
                    if objective == Objective::Lbd && lbd > current_lbd {
                        continue;
                    }
                    lbd
                }
                Objective::Vsids => {
                    // Equal activities permit intermediate steps towards a
                    // hotter extension, but never consume a hotter input.
                    if activity < vsids.literal_activity(&literals[left_idx])
                        || activity < vsids.literal_activity(&literals[right_idx])
                    {
                        continue;
                    }
                    // All candidates share this neutral rank: only activity
                    // and then the existing literal-position order decide.
                    0
                }
            };
            let candidate = (candidate_lbd, activity, left_idx, right_idx, replacement);
            if best.as_ref().is_none_or(|(best_lbd, best_activity, ..)| {
                candidate_lbd < *best_lbd
                    || (candidate_lbd == *best_lbd && activity > *best_activity)
            }) {
                best = Some(candidate);
            }
        }

        let Some((_, _, left_idx, right_idx, replacement)) = best else {
            break;
        };
        literals.remove(right_idx);
        literals.remove(left_idx);
        if objective.uses_lbd() {
            frequencies.remove(blocks.remove(right_idx));
            frequencies.remove(blocks.remove(left_idx));
        }
        if !literals.contains(&replacement) {
            literals.push(replacement);
            if objective.uses_lbd() {
                let block = literal_block(replacement, reasoning_levels);
                blocks.push(block);
                frequencies.add(block);
            }
        }
    }

    source_set.clear();
    source_set.extend(source.iter().copied());
    // Working literals are unique after expansion and every substitution.
    if source_set.len() == literals.len() && literals.iter().all(|lit| source_set.contains(lit)) {
        return Evaluation::without_replacement(true, false);
    }
    if literals.len() > source.len() {
        return Evaluation::without_replacement(false, true);
    }
    if objective == Objective::Vsids
        && !activities_improve(vsids, source, literals, source_activities, final_activities)
    {
        return Evaluation::without_replacement(false, true);
    }
    // VSIDS never uses LBD for ranking or acceptance, only for the existing
    // learned-clause metadata update after its activity check succeeds.
    let current_lbd = match objective {
        Objective::Lbd | Objective::Always => saturate_lbd(frequencies.len()),
        Objective::Vsids if clause.lbd > 2 => {
            dynamic_lbd_with_scratch(literals, reasoning_levels, frequencies)
        }
        Objective::Vsids => 0, // Original clauses keep their sentinel; no LBD work needed.
    };
    if objective == Objective::Lbd && source_lbd.is_some_and(|source_lbd| current_lbd >= source_lbd)
    {
        return Evaluation::without_replacement(false, true);
    }
    let literals_removed = (source.len() - literals.len()) as u64;
    let lbd = match (objective, clause.lbd) {
        // Equivalent rewrites of original clauses remain irredundant.
        (_, -1) => -1,
        // `ges_always` deliberately replaces historical learned metadata with
        // the LBD under the current reasoning snapshot, even when it worsens.
        (Objective::Always, _) => current_lbd.max(2),
        (_, stored) if stored > 2 => stored.min(current_lbd.max(2)),
        (_, stored) => stored,
    };
    // Only accepted clauses need owned storage; retain the working capacity.
    let mut replacement = Clause::from_literals(literals.clone(), lbd);
    replacement.activity = clause.activity;
    replacement.bva_generated = clause.bva_generated;
    replacement.ges_generated = true;
    replacement.ges_used = false;
    Evaluation {
        replacement: Some(replacement),
        report: EvaluationReport {
            inspected: 1,
            lbd_improvements: u64::from(match objective {
                Objective::Lbd => true,
                Objective::Always => source_lbd.is_some_and(|source| current_lbd < source),
                Objective::Vsids => false,
            }),
            vsids_improvements: u64::from(objective == Objective::Vsids),
            literals_removed,
            ..EvaluationReport::default()
        },
    }
}

fn activities_improve(
    vsids: &Vsids,
    source: &[Literal],
    candidate: &[Literal],
    source_activities: &mut Vec<f64>,
    final_activities: &mut Vec<f64>,
) -> bool {
    for (literals, activities) in [
        (source, &mut *source_activities),
        (candidate, &mut *final_activities),
    ] {
        activities.clear();
        activities.extend(literals.iter().map(|lit| vsids.literal_activity(lit)));
        activities.sort_unstable_by(|a, b| b.total_cmp(a));
    }
    // A proper prefix only removes activity entries; it is not an improvement.
    source_activities
        .iter()
        .zip(final_activities.iter())
        .find_map(|(source, candidate)| (source != candidate).then_some(candidate > source))
        .unwrap_or(false)
}

#[cfg(test)]
fn substitution_pairs(
    extensions: &ExtensionMap,
    literals: &[Literal],
) -> Vec<(usize, usize, Literal)> {
    let mut pairs = Vec::new();
    fill_substitution_pairs(extensions, literals, &mut HashMap::new(), &mut pairs);
    pairs
}

fn fill_substitution_pairs(
    extensions: &ExtensionMap,
    literals: &[Literal],
    positions: &mut HashMap<i32, usize>,
    pairs: &mut Vec<(usize, usize, Literal)>,
) {
    // Unrolling deduplicates literals. Position ordering, not adjacency-map
    // ordering, must break equal LBD/activity ties exactly as before.
    positions.clear();
    positions.extend(
        literals
            .iter()
            .enumerate()
            .map(|(idx, literal)| (literal.get_index(), idx)),
    );
    pairs.clear();
    for (left_idx, left) in literals.iter().enumerate() {
        for (partner, replacement) in extensions.substitution_partners(&left.negated()) {
            if let Some(&right_idx) = positions.get(&partner.negated().get_index()) {
                if right_idx > left_idx {
                    pairs.push((left_idx, right_idx, replacement.negated()));
                }
            }
        }
    }
    pairs.sort_unstable_by_key(|&(left, right, _)| (left, right));
}

#[cfg(test)]
fn apply_substitution(
    literals: &[Literal],
    left_idx: usize,
    right_idx: usize,
    replacement: Literal,
) -> Vec<Literal> {
    let mut candidate = literals.to_vec();
    candidate.remove(right_idx);
    candidate.remove(left_idx);
    if !candidate.contains(&replacement) {
        candidate.push(replacement);
    }
    candidate
}

#[cfg(test)]
fn unroll_clause(extensions: &ExtensionMap, literals: &[Literal]) -> Option<Vec<Literal>> {
    let mut unrolled = Vec::new();
    let mut expanding = HashSet::new();
    for &literal in literals {
        if !unroll_literal(extensions, literal, &mut expanding, &mut unrolled) {
            return None;
        }
    }
    Some(unrolled)
}

fn unroll_literal(
    extensions: &ExtensionMap,
    literal: Literal,
    expanding: &mut HashSet<i32>,
    unrolled: &mut Vec<Literal>,
) -> bool {
    let substitute = literal.negated();
    if let Some((first, second)) = extensions.substitution_inputs(&substitute)
        && expanding.insert(substitute.get_index())
    {
        let valid = unroll_literal(extensions, first.negated(), expanding, unrolled)
            && unroll_literal(extensions, second.negated(), expanding, unrolled);
        expanding.remove(&substitute.get_index());
        return valid;
    }

    if unrolled.contains(&literal.negated()) {
        return false;
    }
    if !unrolled.contains(&literal) {
        unrolled.push(literal);
    }
    true
}

type Block = (bool, usize);

/// Assigned decision levels and unassigned variables are distinct namespaces.
/// Reset only touched entries, not the full variable-sized arrays each clause.
#[derive(Default)]
struct BlockCounts {
    counts: [Vec<usize>; 2],
    touched: Vec<Block>,
    distinct: usize,
}

impl BlockCounts {
    fn clear(&mut self) {
        for &(variable, index) in &self.touched {
            self.counts[usize::from(variable)][index] = 0;
        }
        self.touched.clear();
        self.distinct = 0;
    }

    fn len(&self) -> usize {
        self.distinct
    }

    fn get(&self, (variable, index): Block) -> usize {
        self.counts[usize::from(variable)]
            .get(index)
            .copied()
            .unwrap_or(0)
    }

    fn add(&mut self, block @ (variable, index): Block) {
        let counts = &mut self.counts[usize::from(variable)];
        if index >= counts.len() {
            counts.resize(index + 1, 0);
        }
        if counts[index] == 0 {
            self.distinct += 1;
            self.touched.push(block);
        }
        counts[index] += 1;
    }

    fn remove(&mut self, (variable, index): Block) {
        let count = &mut self.counts[usize::from(variable)][index];
        debug_assert!(*count > 0);
        *count -= 1;
        self.distinct -= usize::from(*count == 0);
    }

    #[cfg(test)]
    fn capacity(&self) -> usize {
        self.counts[0].capacity() + self.counts[1].capacity() + self.touched.capacity()
    }
}

fn literal_block(literal: Literal, reasoning_levels: Option<&[Option<usize>]>) -> Block {
    let variable = literal.get_index().unsigned_abs() as usize;
    reasoning_levels
        .and_then(|levels| levels.get(variable).copied().flatten())
        .map_or((true, variable), |level| (false, level))
}

fn block_frequencies(blocks: &[Block], frequencies: &mut BlockCounts) {
    frequencies.clear();
    for &block in blocks {
        frequencies.add(block);
    }
}

fn saturate_lbd(blocks: usize) -> i16 {
    i16::try_from(blocks).unwrap_or(i16::MAX)
}

fn substitution_lbd(
    frequencies: &BlockCounts,
    left: Block,
    right: Block,
    replacement: Block,
) -> i16 {
    let remaining =
        |block| frequencies.get(block) - usize::from(block == left) - usize::from(block == right);
    // Keep the distinct count exact until all removals and the insertion are
    // accounted for: subtracting from an already saturated LBD changes ranking.
    let mut blocks = frequencies.len();
    blocks -= usize::from(remaining(left) == 0);
    if right != left {
        blocks -= usize::from(remaining(right) == 0);
    }
    // A surviving replacement literal (or any other literal in its block)
    // already contributes this block, regardless of literal deduplication.
    blocks += usize::from(remaining(replacement) == 0);
    saturate_lbd(blocks)
}

fn dynamic_lbd_with_scratch(
    literals: &[Literal],
    reasoning_levels: Option<&[Option<usize>]>,
    frequencies: &mut BlockCounts,
) -> i16 {
    frequencies.clear();
    for &literal in literals {
        frequencies.add(literal_block(literal, reasoning_levels));
    }
    saturate_lbd(frequencies.len())
}

#[cfg(test)]
fn dynamic_lbd(literals: &[Literal], reasoning_levels: Option<&[Option<usize>]>) -> i16 {
    let blocks = literals
        .iter()
        .map(|literal| {
            let variable = literal.get_index().unsigned_abs() as usize;
            reasoning_levels
                .and_then(|levels| levels.get(variable).copied().flatten())
                .map_or((true, variable), |level| (false, level))
        })
        .collect::<HashSet<_>>()
        .len();
    i16::try_from(blocks).unwrap_or(i16::MAX)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::extension::extension_literal;
    use crate::formula::literal::Literal;

    fn full_scope(formula: &Formula) -> ClauseScope {
        ClauseScope::range(0..formula.clause_slots_len())
    }

    fn evaluate_always(
        formula: &Formula,
        clause: &Clause,
        levels: Option<&[Option<usize>]>,
    ) -> Evaluation {
        let mut workspace = PassWorkspace::new(&formula.extensions);
        workspace.objective = Objective::Always;
        workspace.evaluate(&formula.vsids, clause, false, levels)
    }

    fn evaluate_vsids(
        formula: &Formula,
        clause: &Clause,
        levels: Option<&[Option<usize>]>,
    ) -> Evaluation {
        let mut workspace = PassWorkspace::new(&formula.extensions);
        workspace.objective = Objective::Vsids;
        workspace.evaluate(&formula.vsids, clause, false, levels)
    }

    fn vsids_fixture(definitions: &[(i32, i32, i32)], activities: &[f64]) -> Formula {
        let mut formula = Formula::new(activities.len() - 1);
        for &(a, b, z) in definitions {
            formula.extensions.add_substitution(
                &Literal::new(a),
                &Literal::new(b),
                &Literal::new(z),
            );
        }
        formula.vsids.activity.copy_from_slice(activities);
        formula
    }

    #[test]
    fn vsids_prefers_hottest_replacement_even_when_lbd_worsens() {
        let formula = vsids_fixture(&[(1, 2, 5), (1, 3, 6)], &[0., 1., 2., 3., 4., 9., 10.]);
        let clause = Clause::from_literals([-1, -2, -3, 4].map(Literal::new).to_vec(), 5);
        let levels = [None, Some(1), Some(1), Some(1), Some(1), Some(1), Some(2)];
        let evaluation = evaluate_vsids(&formula, &clause, Some(&levels));
        let replacement = evaluation.replacement.unwrap();
        assert_eq!(replacement.get_literals(), [-2, 4, -6].map(Literal::new));
        assert_eq!(dynamic_lbd(clause.get_literals(), Some(&levels)), 1);
        assert_eq!(dynamic_lbd(replacement.get_literals(), Some(&levels)), 2);
        assert_eq!(evaluation.report.vsids_improvements, 1);
        assert_eq!(evaluation.report.lbd_improvements, 0);
        assert_eq!(replacement.lbd, 2);
        assert!(
            evaluate_clause(
                &formula.extensions,
                &formula.vsids,
                &clause,
                false,
                Some(&levels)
            )
            .replacement
            .is_none()
        );
    }

    #[test]
    fn vsids_preserves_hot_inputs_but_allows_equal_activity_intermediates() {
        let mut formula = vsids_fixture(&[(1, 2, 5), (5, 3, 6)], &[0., 1., 2., 1., 0., 10., 9.]);
        let clause = Clause::from_literals([-1, -2, -3, 4].map(Literal::new).to_vec(), -1);
        let replacement = evaluate_vsids(&formula, &clause, None).replacement.unwrap();
        assert_eq!(replacement.get_literals(), [-3, 4, -5].map(Literal::new));
        assert_eq!(replacement.lbd, -1);
        formula.vsids.activity[5] = 2.;
        let replacement = evaluate_vsids(&formula, &clause, None).replacement.unwrap();
        assert_eq!(replacement.get_literals(), [4, -6].map(Literal::new));
        formula.vsids.activity[5] = 0.;
        assert!(
            evaluate_vsids(&formula, &clause, None)
                .replacement
                .is_none()
        );
    }

    #[test]
    fn vsids_equal_replacement_scores_use_literal_positions() {
        let formula = vsids_fixture(&[(1, 3, 5), (1, 2, 6)], &[0., 1., 1., 1., 0., 10., 10.]);
        for (source, expected) in [
            ([-1, -2, -3, 4], [-3, 4, -6]),
            ([-1, -3, -2, 4], [-2, 4, -5]),
        ] {
            let clause = Clause::from_literals(source.map(Literal::new).to_vec(), -1);
            assert_eq!(
                evaluate_vsids(&formula, &clause, None)
                    .replacement
                    .unwrap()
                    .get_literals(),
                expected.map(Literal::new)
            );
        }
    }

    #[test]
    fn vsids_final_activity_comparison_is_lexicographic_not_average_or_length() {
        let formula = vsids_fixture(&[], &[0., 100., 20., 10., 80., 110., 5.]);
        let source = [1, 2, 3].map(Literal::new);
        let mut before = Vec::new();
        let mut after = Vec::new();
        for (candidate, expected) in [
            (vec![1, 4], true),
            (vec![1, 2], false),
            (vec![5, 6], true),
            (vec![1, 4, 6], true),
            (vec![1, 3], false),
            (vec![3, 2, 1], false),
            (vec![-1, -2, -3], false),
        ] {
            let candidate: Vec<_> = candidate.into_iter().map(Literal::new).collect();
            assert_eq!(
                activities_improve(&formula.vsids, &source, &candidate, &mut before, &mut after),
                expected
            );
        }
        let formula = vsids_fixture(&[(1, 2, 4)], &[0., 0., 0., 0., 0.]);
        let clause = Clause::from_literals([-1, -2, 3].map(Literal::new).to_vec(), -1);
        let evaluation = evaluate_vsids(&formula, &clause, None);
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.rejected, 1);
    }

    #[test]
    fn vsids_compares_against_source_before_expansion_and_rejects_growth() {
        let formula = vsids_fixture(&[(1, 2, 5), (1, 3, 6)], &[0., 1., 1., 1., 0., 100., 10.]);
        let clause = Clause::from_literals([-5, -3, 4].map(Literal::new).to_vec(), -1);
        // Recovering the original hot extension is a no-op, not an improvement.
        let evaluation = evaluate_vsids(&formula, &clause, None);
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.noop, 1);
        let formula = vsids_fixture(&[(1, 2, 5), (1, 3, 6)], &[0., 1., 110., 1., 0., 100., 10.]);
        let evaluation = evaluate_vsids(&formula, &clause, None);
        let replacement = evaluation.replacement.unwrap();
        assert_eq!(replacement.get_literals().len(), clause.len());
        assert_eq!(replacement.get_literals(), [-2, 4, -6].map(Literal::new));
        // An activity gain solely from expanding to a larger clause is rejected.
        let clause = Clause::from_literals([-5, 4].map(Literal::new).to_vec(), -1);
        let evaluation = evaluate_vsids(&formula, &clause, None);
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.rejected, 1);
    }

    #[test]
    fn vsids_rejects_greedy_result_colder_than_original_extension() {
        let formula = vsids_fixture(
            &[(1, 2, 5), (5, 3, 7), (1, 4, 6)],
            &[0., 1., 1., 1., 1., 10., 90., 100., 0.],
        );
        let clause = Clause::from_literals([-7, -4, -2, -3, 8].map(Literal::new).to_vec(), -1);
        // Choosing -6 first blocks reconstructing the original -7. This
        // improves the expanded clause, but loses the source's hottest literal.
        let mut workspace = PassWorkspace::new(&formula.extensions);
        workspace.objective = Objective::Vsids;
        let evaluation = workspace.evaluate(&formula.vsids, &clause, false, None);
        assert!(workspace.literals.contains(&Literal::new(-6)));
        assert!(!workspace.literals.contains(&Literal::new(-7)));
        assert!(workspace.literals.len() < clause.len());

        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.rejected, 1);
    }

    #[test]
    fn vsids_cursor_budget_and_proof_stats_match_shared_infrastructure() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 4]; MAX_CLAUSES_PER_PASS + 2]);
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));
        let z = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        formula.vsids.activity[z.get_index() as usize] = 100.;
        formula.ges_cursor = 1;
        let scope = full_scope(&formula);
        crate::process::ges_vsids::process(&mut formula, &scope, &mut logger, None, None, None)
            .unwrap();
        drop(logger);
        assert!(!formula.is_clause_garbage(0));
        assert!(!formula.is_clause_garbage(MAX_CLAUSES_PER_PASS + 1));
        assert_eq!(formula.ges_cursor, MAX_CLAUSES_PER_PASS + 1);
        assert_eq!(
            formula.stats.ges_vsids_improvements,
            MAX_CLAUSES_PER_PASS as u64
        );
        assert_eq!(formula.stats.ges_lbd_improvements, 0);
        assert_eq!(
            formula.stats.ges_literals_removed,
            MAX_CLAUSES_PER_PASS as u64
        );
        let proof = String::from_utf8(proof).unwrap();
        assert!(proof.ends_with("4 -5 0\nd -1 -2 4 0\n"));
    }

    #[test]
    fn always_accepts_lbd_worsening_glue_rewrite_but_regular_ges_does_not() {
        let mut formula = Formula::new(5);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(5));
        let glue = Clause::from_literals([-1, -2, 3, 4].map(Literal::new).to_vec(), 2);
        let levels = [None, Some(1), Some(1), Some(1), Some(2), Some(3)];
        assert_eq!(dynamic_lbd(glue.get_literals(), Some(&levels)), 2);

        let regular = evaluate_clause(
            &formula.extensions,
            &formula.vsids,
            &glue,
            false,
            Some(&levels),
        );
        assert!(regular.replacement.is_none());
        assert_eq!(regular.report, EvaluationReport::default());

        let always = evaluate_always(&formula, &glue, Some(&levels));
        let replacement = always.replacement.unwrap();
        assert_eq!(replacement.get_literals(), [3, 4, -5].map(Literal::new));
        assert_eq!(dynamic_lbd(replacement.get_literals(), Some(&levels)), 3);
        assert_eq!(replacement.lbd, 3);
        assert_eq!(always.report.inspected, 1);
        assert_eq!(always.report.lbd_improvements, 0);
        assert_eq!(always.report.literals_removed, 1);
    }

    #[test]
    fn always_preserves_original_sentinel_and_protects_extension_axioms() {
        let mut formula = Formula::new(5);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(5));
        let original = Clause::from_literals([-1, -2, 3].map(Literal::new).to_vec(), -1);
        let replacement = evaluate_always(&formula, &original, None)
            .replacement
            .unwrap();
        assert_eq!(replacement.get_literals(), [3, -5].map(Literal::new));
        assert_eq!(replacement.lbd, -1);

        let axiom = Clause::from_literals([-1, -2, 5].map(Literal::new).to_vec(), 0);
        let evaluation = evaluate_always(&formula, &axiom, None);
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report, EvaluationReport::default());
    }

    #[test]
    fn always_wrapper_uses_cursor_budget_shared_commit_and_current_lbd() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 3, 4]]);
        formula.get_clause_at_idx_mut(0).lbd = 2;
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));
        let extension = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        assert_eq!(extension, Literal::new(5));
        let levels = [None, Some(1), Some(1), Some(1), Some(2), Some(3)];
        let scope = full_scope(&formula);
        crate::process::ges_always::process(
            &mut formula,
            &scope,
            &mut logger,
            None,
            None,
            Some(&levels),
        )
        .unwrap();
        drop(logger);

        assert!(formula.is_clause_garbage(0));
        assert_eq!(formula.ges_cursor, 0);
        let replacement = formula.get_clause_at_idx(4);
        assert_eq!(replacement.get_literals(), [3, 4, -5].map(Literal::new));
        assert_eq!(replacement.lbd, 3);
        assert_eq!(formula.stats.ges_clauses_inspected, 1);
        assert_eq!(formula.stats.ges_lbd_improvements, 0);
        assert_eq!(formula.stats.ges_literals_removed, 1);
        assert_eq!(formula.stats.global_extension_substitution, 1);
        let proof = String::from_utf8(proof).unwrap();
        assert!(proof.ends_with("3 4 -5 0\nd -1 -2 3 4 0\n"));
    }

    #[test]
    fn cached_expansions_match_uncached_order_for_signed_clauses_and_cycles() {
        let mut formula = Formula::new(8);
        for (a, b, z) in [(1, 2, 5), (5, 3, 6), (6, 5, 7), (-2, 4, 8)] {
            formula.extensions.add_substitution(
                &Literal::new(a),
                &Literal::new(b),
                &Literal::new(z),
            );
        }
        // Also exercise context-sensitive cycle guards: only complete root
        // expansions may be reused, never partial recursive expansions.
        for cyclic in [false, true] {
            if cyclic {
                formula.extensions.add_substitution(
                    &Literal::new(7),
                    &Literal::new(4),
                    &Literal::new(1),
                );
            }
            let mut workspace = PassWorkspace::new(&formula.extensions);
            for a in -8..=8 {
                for b in -8..=8 {
                    for c in -8..=8 {
                        if a == 0 || b == 0 || c == 0 {
                            continue;
                        }
                        let source = [a, b, c].map(Literal::new);
                        let expected = unroll_clause(&formula.extensions, &source);
                        assert_eq!(workspace.unroll(&source), expected.is_some(), "{source:?}");
                        if let Some(expected) = expected {
                            assert_eq!(workspace.literals, expected, "{source:?}");
                        }
                    }
                }
            }
            assert!(!workspace.expansions.is_empty());
            assert!(workspace.cached_units <= MAX_CACHED_EXPANSION_UNITS);
        }
    }

    #[test]
    fn expansion_cache_reuses_storage_and_full_cache_falls_back() {
        let mut formula = Formula::new(6);
        for (a, b, z) in [(1, 2, 5), (5, 3, 6)] {
            formula.extensions.add_substitution(
                &Literal::new(a),
                &Literal::new(b),
                &Literal::new(z),
            );
        }
        let mut workspace = PassWorkspace::new(&formula.extensions);
        let source = [-6, -5, 4].map(Literal::new);
        assert!(workspace.unroll(&source));
        let cached_ptr = workspace.expansions[&-6].as_ref().unwrap().as_ptr();
        let units = workspace.cached_units;
        let capacity = workspace.literals.capacity();
        for _ in 0..3 {
            assert!(workspace.unroll(&source));
            assert_eq!(
                workspace.expansions[&-6].as_ref().unwrap().as_ptr(),
                cached_ptr
            );
            assert_eq!(workspace.cached_units, units);
            assert_eq!(workspace.literals.capacity(), capacity);
        }
        let mut uncached = PassWorkspace::new(&formula.extensions);
        uncached.cached_units = MAX_CACHED_EXPANSION_UNITS;
        assert!(uncached.unroll(&source));
        assert_eq!(uncached.literals, workspace.literals);
        assert!(uncached.expansions.is_empty());
        // A conflicting prefix must not poison an otherwise valid root entry.
        assert!(!workspace.unroll(&[Literal::new(1), Literal::new(-6)]));
        assert!(workspace.unroll(&source));
    }

    #[test]
    fn reused_workspace_matches_fresh_evaluations_and_retains_scratch_capacity() {
        let mut formula = Formula::new(7);
        for (a, b, z) in [(1, 2, 5), (5, 3, 6), (2, 4, 7)] {
            formula.extensions.add_substitution(
                &Literal::new(a),
                &Literal::new(b),
                &Literal::new(z),
            );
        }
        let mut workspace = PassWorkspace::new(&formula.extensions);
        let levels = [
            None,
            Some(1),
            Some(2),
            Some(3),
            Some(4),
            Some(3),
            Some(3),
            Some(1),
        ];
        for snapshot in [None, Some(levels.as_slice())] {
            for source in [
                vec![-1, -2, 3, 4],
                vec![-6, 4],
                vec![-6, 1],
                vec![5, -3],
                vec![-5, -2, 4],
            ] {
                for lbd in [-1, 0, 2, 4] {
                    let clause = Clause::from_literals(
                        source.iter().copied().map(Literal::new).collect(),
                        lbd,
                    );
                    let expected = evaluate_clause(
                        &formula.extensions,
                        &formula.vsids,
                        &clause,
                        false,
                        snapshot,
                    );
                    let actual = workspace.evaluate(&formula.vsids, &clause, false, snapshot);
                    assert_eq!(actual.report, expected.report);
                    assert_eq!(
                        actual
                            .replacement
                            .as_ref()
                            .map(|c| (c.get_literals(), c.lbd)),
                        expected
                            .replacement
                            .as_ref()
                            .map(|c| (c.get_literals(), c.lbd))
                    );
                }
            }
        }
        let clause = Clause::from_literals([-1, -2, 3, 4].map(Literal::new).to_vec(), 4);
        assert!(
            workspace
                .evaluate(&formula.vsids, &clause, false, None)
                .replacement
                .is_some()
        );
        let capacities = |w: &PassWorkspace<'_>| {
            (
                w.literals.capacity(),
                w.blocks.capacity(),
                w.frequencies.capacity(),
                w.positions.capacity(),
                w.pairs.capacity(),
                w.source_set.capacity(),
            )
        };
        let before = capacities(&workspace);
        assert!(
            workspace
                .evaluate(&formula.vsids, &clause, false, None)
                .replacement
                .is_some()
        );
        assert_eq!(capacities(&workspace), before);
    }

    #[test]
    fn new_pass_observes_changed_extension_definitions() {
        let mut formula = Formula::new(5);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(5));
        {
            let mut workspace = PassWorkspace::new(&formula.extensions);
            assert!(workspace.unroll(&[Literal::new(-5)]));
            assert_eq!(
                workspace.literals,
                unroll_clause(&formula.extensions, &[Literal::new(-5)]).unwrap()
            );
            assert!(workspace.literals.contains(&Literal::new(-1)));
        }
        formula
            .extensions
            .add_substitution(&Literal::new(3), &Literal::new(4), &Literal::new(5));
        let mut workspace = PassWorkspace::new(&formula.extensions);
        assert!(workspace.unroll(&[Literal::new(-5)]));
        assert_eq!(
            workspace.literals,
            unroll_clause(&formula.extensions, &[Literal::new(-5)]).unwrap()
        );
        assert!(workspace.literals.contains(&Literal::new(-3)));
        assert!(!workspace.literals.contains(&Literal::new(-1)));
    }

    #[test]
    fn policies_limit_order_and_preserve_independent_cursor() {
        let mut formula = Formula::from_vec(vec![vec![1]; MAX_CLAUSES_PER_PASS + 4]);
        for idx in 0..formula.clause_slots_len() {
            formula.get_clause_at_idx_mut(idx).lbd = 4;
        }
        let last = formula.clause_slots_len() - 1;
        formula.get_clause_at_idx_mut(last).lbd = 9;
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.delete_clause(1, &mut logger);
        let scope = ClauseScope::indices((0..=last).filter(|&idx| idx != 2));
        formula.ges_cursor = 3;
        let lbd = select_clause_indices(&mut formula, &scope, Policy::Lbd);
        assert_eq!(lbd.len(), MAX_CLAUSES_PER_PASS);
        assert_eq!(&lbd[..4], &[last, 0, 3, 4]);
        assert_eq!(formula.ges_cursor, 3);
        for _ in 0..20 {
            let random = select_clause_indices(&mut formula, &scope, Policy::Random);
            assert_eq!(random.len(), MAX_CLAUSES_PER_PASS);
            let expected: Vec<_> =
                sequential_clause_window(&formula, &scope, random[0], MAX_CLAUSES_PER_PASS)
                    .map(|(idx, _)| idx)
                    .collect();
            assert_eq!(random, expected);
            assert_eq!(formula.ges_cursor, 3);
        }
        let cursor = select_clause_indices(&mut formula, &scope, Policy::Cursor);
        assert_eq!(cursor, (3..last).collect::<Vec<_>>());
        assert_eq!(formula.ges_cursor, last);
        let next = select_clause_indices(&mut formula, &scope, Policy::Cursor);
        assert_eq!(&next[..3], &[last, 0, 3]);
    }

    #[test]
    fn lbd_tiers_exclude_permanent_and_glue_clauses() {
        let mut formula = Formula::from_vec(vec![vec![1]; 9]);
        for (idx, lbd) in [-1, 0, 1, 2, 3, 6, 7, 9, 6].into_iter().enumerate() {
            formula.get_clause_at_idx_mut(idx).lbd = lbd;
        }
        let scope = full_scope(&formula);
        assert_eq!(
            select_clause_indices(&mut formula, &scope, Policy::Lbd),
            vec![7, 6, 5, 8, 4]
        );
        let mut original = Formula::from_vec(vec![vec![1, 2]]);
        let scope = full_scope(&original);
        assert!(select_clause_indices(&mut original, &scope, Policy::Lbd).is_empty());
    }

    #[test]
    fn full_tier_three_window_matches_full_sort() {
        let mut formula = Formula::from_vec(vec![vec![1]; MAX_CLAUSES_PER_PASS + 20]);
        for idx in 0..formula.clause_slots_len() {
            formula.get_clause_at_idx_mut(idx).lbd = 7 + (idx % 5) as i16;
        }
        formula.get_clause_at_idx_mut(0).lbd = 6;
        let mut expected: Vec<_> = formula.get_clauses().map(|(idx, c)| (idx, c.lbd)).collect();
        expected.sort_unstable_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        expected.truncate(MAX_CLAUSES_PER_PASS);
        let scope = full_scope(&formula);
        assert_eq!(
            select_clause_indices(&mut formula, &scope, Policy::Lbd),
            expected.into_iter().map(|(idx, _)| idx).collect::<Vec<_>>()
        );
    }

    #[test]
    fn empty_policies_are_safe() {
        let mut formula = Formula::new(0);
        for policy in [
            Policy::Cursor,
            Policy::Lbd,
            Policy::Random,
            Policy::Vsids,
            Policy::Always,
        ] {
            assert!(
                select_clause_indices(&mut formula, &ClauseScope::range(0..0), policy).is_empty()
            );
        }
    }

    #[test]
    fn adjacency_matches_quadratic_pair_order_for_signed_permutations() {
        use itertools::Itertools;
        let mut extensions = ExtensionMap::new();
        for (left, right, replacement) in [
            (1, 2, 10),
            (1, -3, -11),
            (2, -3, 12),
            (2, 4, 13),
            (1, 1, 14),
        ] {
            extensions.add_substitution(
                &Literal::new(left),
                &Literal::new(right),
                &Literal::new(replacement),
            );
        }
        for literals in [-1, -2, 3, -4, 5]
            .into_iter()
            .map(Literal::new)
            .permutations(5)
        {
            let mut expected = Vec::new();
            for left in 0..literals.len() {
                for right in left + 1..literals.len() {
                    if let Some(replacement) =
                        extensions.substitute(&literals[left].negated(), &literals[right].negated())
                    {
                        expected.push((left, right, replacement.negated()));
                    }
                }
            }
            assert_eq!(substitution_pairs(&extensions, &literals), expected);
        }
    }

    #[test]
    fn indexed_counts_keep_namespaces_separate_and_reset_reintroduced_blocks() {
        let mut counts = BlockCounts::default();
        counts.add((false, 0));
        counts.add((false, 7));
        counts.add((true, 7));
        counts.add((true, 7));
        assert_eq!(counts.len(), 3);
        counts.remove((false, 7));
        counts.add((false, 7));
        counts.remove((true, 7));
        assert_eq!(counts.get((true, 7)), 1);
        assert_eq!(counts.len(), 3);
        counts.clear();
        assert_eq!(counts.len(), 0);
        for block in [(false, 0), (false, 7), (true, 7)] {
            assert_eq!(counts.get(block), 0);
        }
        let capacity = counts.capacity();
        counts.add((false, 7));
        counts.add((true, 7));
        assert_eq!(counts.len(), 2);
        assert_eq!(counts.capacity(), capacity);
    }

    #[test]
    fn vsids_original_rewrite_never_populates_lbd_scratch() {
        let formula = vsids_fixture(&[(1, 2, 4)], &[0., 1., 2., 3., 10.]);
        let mut workspace = PassWorkspace::new(&formula.extensions);
        workspace.objective = Objective::Vsids;
        let levels = [None, Some(0), Some(1), None, Some(2)];
        let clause = Clause::from_literals([-1, -2, 3].map(Literal::new).to_vec(), -1);
        let evaluation = workspace.evaluate(&formula.vsids, &clause, false, Some(&levels));
        assert_eq!(evaluation.replacement.unwrap().lbd, -1);
        assert_eq!(workspace.frequencies.capacity(), 0);
        assert_eq!(workspace.blocks.capacity(), 0);
        let learned = Clause::from_literals(clause.get_literals().to_vec(), 5);
        let evaluation = workspace.evaluate(&formula.vsids, &learned, false, Some(&levels));
        assert_eq!(evaluation.replacement.unwrap().lbd, 2);
        assert!(workspace.frequencies.capacity() > 0);
    }

    #[test]
    fn greedy_updates_leave_exact_counts_across_reused_clauses() {
        let formula = vsids_fixture(&[(1, 2, 5), (5, 3, 6), (6, 4, 7)], &[0.; 8]);
        let mut workspace = PassWorkspace::new(&formula.extensions);
        for levels in [
            None,
            Some([
                None,
                Some(0),
                Some(0),
                None,
                Some(1),
                Some(0),
                Some(1),
                Some(0),
            ]),
        ] {
            for raw in [vec![-1, -2, -3, -4], vec![-7, -1], vec![-1, -2, 4], vec![1]] {
                let clause = Clause::from_literals(raw.into_iter().map(Literal::new).collect(), -1);
                workspace.evaluate(
                    &formula.vsids,
                    &clause,
                    false,
                    levels.as_ref().map(|v| v.as_slice()),
                );
                let mut expected = HashMap::new();
                for &lit in &workspace.literals {
                    *expected
                        .entry(literal_block(lit, levels.as_ref().map(|v| v.as_slice())))
                        .or_insert(0) += 1;
                }
                assert_eq!(workspace.frequencies.len(), expected.len());
                assert_eq!(workspace.blocks.len(), workspace.literals.len());
                for (block, count) in expected {
                    assert_eq!(workspace.frequencies.get(block), count);
                }
            }
        }
    }

    fn assert_incremental_scores(
        literals: &[Literal],
        levels: Option<&[Option<usize>]>,
        replacements: &[Literal],
    ) {
        let blocks: Vec<_> = literals
            .iter()
            .map(|&lit| literal_block(lit, levels))
            .collect();
        let mut frequencies = BlockCounts::default();
        block_frequencies(&blocks, &mut frequencies);
        let current_lbd = dynamic_lbd(literals, levels);
        assert_eq!(saturate_lbd(frequencies.len()), current_lbd);
        let mut incremental_best = None;
        let mut reference_best = None;
        for left in 0..literals.len() {
            for right in left + 1..literals.len() {
                for (idx, &replacement) in replacements.iter().enumerate() {
                    let actual = substitution_lbd(
                        &frequencies,
                        blocks[left],
                        blocks[right],
                        literal_block(replacement, levels),
                    );
                    let candidate_literals = apply_substitution(literals, left, right, replacement);
                    let expected = dynamic_lbd(&candidate_literals, levels);
                    let mut updated = BlockCounts::default();
                    block_frequencies(&blocks, &mut updated);
                    updated.remove(blocks[right]);
                    updated.remove(blocks[left]);
                    let replacement_survives = literals
                        .iter()
                        .enumerate()
                        .any(|(idx, &lit)| idx != left && idx != right && lit == replacement);
                    if !replacement_survives {
                        updated.add(literal_block(replacement, levels));
                    }
                    assert_eq!(saturate_lbd(updated.len()), expected);
                    let mut reference = HashMap::new();
                    for &lit in &candidate_literals {
                        *reference.entry(literal_block(lit, levels)).or_insert(0) += 1;
                    }
                    for block in blocks
                        .iter()
                        .copied()
                        .chain(std::iter::once(literal_block(replacement, levels)))
                    {
                        assert_eq!(
                            updated.get(block),
                            reference.get(&block).copied().unwrap_or(0)
                        );
                    }
                    assert_eq!(
                        actual, expected,
                        "pair ({left}, {right}), replacement {replacement:?}, levels {levels:?}"
                    );
                    if literals.contains(&replacement.negated()) {
                        continue;
                    }
                    // Repeated activities exercise ties; tuple ordering retains
                    // the first original position after LBD and descending activity.
                    let activity = ((left + 2 * right + idx) % 3) as i32;
                    let candidate = (actual, -activity, left, right, idx);
                    if actual <= current_lbd && incremental_best.is_none_or(|best| candidate < best)
                    {
                        incremental_best = Some(candidate);
                    }
                    let reference = (expected, -activity, left, right, idx);
                    if expected <= current_lbd && reference_best.is_none_or(|best| reference < best)
                    {
                        reference_best = Some(reference);
                    }
                }
            }
        }
        assert_eq!(incremental_best, reference_best);
    }

    #[test]
    fn incremental_scores_match_full_reference_for_small_reasoning_snapshots() {
        // Exhaust all unknown/level-zero/level-one assignments, including a
        // replacement outside the clause, both polarities, and shortened tables.
        let replacements: Vec<_> = (-5..=5).filter(|&v| v != 0).map(Literal::new).collect();
        for encoded in 0..3usize.pow(5) {
            let mut digits = encoded;
            let mut levels = vec![None];
            for _ in 0..5 {
                levels.push(match digits % 3 {
                    0 => None,
                    value => Some(value - 1),
                });
                digits /= 3;
            }
            for signs in 0..16 {
                let literals: Vec<_> = (1..=4)
                    .map(|v| Literal::new(if signs & (1 << (v - 1)) == 0 { v } else { -v }))
                    .collect();
                assert_incremental_scores(&literals, Some(&levels), &replacements);
            }
        }
        let literals: Vec<_> = [1, -2, 3, -4].into_iter().map(Literal::new).collect();
        assert_incremental_scores(&literals, None, &replacements);
        assert_incremental_scores(&literals, Some(&[None, Some(2), None]), &replacements);
    }

    #[test]
    fn incremental_scores_handle_shared_removed_and_replacement_blocks() {
        let literals: Vec<_> = [1, 2, 3, 4].into_iter().map(Literal::new).collect();
        let replacements: Vec<_> = (1..=6).map(Literal::new).collect();
        // The first pair removes its entire shared block. Replacements either
        // restore it, already survive, share a surviving block, or add a new one.
        let levels = [None, Some(0), Some(0), Some(1), Some(1), Some(0), None];
        assert_incremental_scores(&literals, Some(&levels), &replacements);
        // Unknown variables must not collide with known levels of the same ID.
        let levels = [None, None, Some(1), None, Some(3), None, None];
        assert_incremental_scores(&literals, Some(&levels), &replacements);
        // Reusing a buffer must discard all counts from its previous contents.
        let mut frequencies = BlockCounts::default();
        block_frequencies(&[(true, 1), (true, 1)], &mut frequencies);
        block_frequencies(&[(false, 0)], &mut frequencies);
        assert_eq!(frequencies.len(), 1);
        assert_eq!(frequencies.get((false, 0)), 1);
        assert_eq!(frequencies.get((true, 1)), 0);
    }

    #[test]
    fn incremental_scores_saturate_only_after_exact_block_updates() {
        for count in [
            i16::MAX as usize - 1,
            i16::MAX as usize,
            i16::MAX as usize + 1,
            i16::MAX as usize + 2,
        ] {
            let literals: Vec<_> = (1..=count as i32).map(Literal::new).collect();
            let blocks: Vec<_> = literals
                .iter()
                .map(|&lit| literal_block(lit, None))
                .collect();
            let mut frequencies = BlockCounts::default();
            block_frequencies(&blocks, &mut frequencies);
            for replacement in [
                Literal::new(1),
                Literal::new(3),
                Literal::new(count as i32 + 1),
            ] {
                assert_eq!(
                    substitution_lbd(
                        &frequencies,
                        blocks[0],
                        blocks[1],
                        literal_block(replacement, None)
                    ),
                    dynamic_lbd(&apply_substitution(&literals, 0, 1, replacement), None),
                    "distinct blocks {count}, replacement {replacement:?}",
                );
            }
        }
    }

    #[test]
    fn equal_pair_scores_choose_literal_position_not_partner_order() {
        let mut formula = Formula::from_vec(vec![vec![-1, -3, -2]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let first = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(3),
        );
        extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0), None).unwrap();
        assert_eq!(
            replacement.get_literals(),
            &[Literal::new(-2), first.negated()]
        );
    }

    #[test]
    fn sequential_clause_window_wraps_and_skips_garbage() {
        let mut formula =
            Formula::from_vec(vec![vec![1], vec![2], vec![3], vec![4], vec![5], vec![6]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        formula.delete_clause(1, &mut logger);
        formula.delete_clause(4, &mut logger);

        let scope = full_scope(&formula);
        let indices = sequential_clause_window(&formula, &scope, 2, 4)
            .map(|(clause_idx, _)| clause_idx)
            .collect::<Vec<_>>();

        assert_eq!(indices, vec![2, 3, 5, 0]);
    }

    #[test]
    fn substitutes_the_negated_inputs_and_logs_add_before_delete() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 4]]);
        let mut proof = Vec::new();
        let mut logger = Some(DratLogger::new(&mut proof));
        let z = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );

        let scope = full_scope(&formula);
        process(&mut formula, &scope, &mut logger, None, None, None).unwrap();
        drop(logger);

        assert!(formula.is_clause_garbage(0));
        assert_eq!(
            formula.get_clause_at_idx(4).get_literals(),
            &[Literal::new(4), z.negated()]
        );
        assert_eq!(formula.get_clause_at_idx(4).lbd, -1);
        assert_eq!(formula.live_clause_count(), 4);
        assert_eq!(formula.stats.clauses_deleted, 1);
        assert_eq!(formula.stats.global_extension_substitution, 1);

        let proof = String::from_utf8(proof).unwrap();
        assert!(proof.ends_with("4 -5 0\nd -1 -2 4 0\n"));
    }

    #[test]
    fn repeatedly_applies_chained_substitutions() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, -3, 4]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let first = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let second = extension_literal(&mut formula, &mut logger, &first, &Literal::new(3));

        let scope = full_scope(&formula);
        process(&mut formula, &scope, &mut logger, None, None, None).unwrap();

        assert_eq!(
            formula.get_clause_at_idx(7).get_literals(),
            &[Literal::new(4), second.negated()]
        );
    }

    #[test]
    fn substitutes_all_five_disjoint_pairs() {
        let mut formula =
            Formula::from_vec(vec![vec![-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, 11]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let first = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let second = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(3),
            &Literal::new(4),
        );
        let third = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(5),
            &Literal::new(6),
        );
        let fourth = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(7),
            &Literal::new(8),
        );
        let fifth = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(9),
            &Literal::new(10),
        );

        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0), None).unwrap();

        assert_eq!(replacement.len(), 6);
        assert!(replacement.get_literals().contains(&Literal::new(11)));
        for extension in [first, second, third, fourth, fifth] {
            assert!(replacement.get_literals().contains(&extension.negated()));
        }
    }

    #[test]
    fn selects_the_highest_replacement_vsids_without_collecting_pairs() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, -3, 4]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let lower = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let higher = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(3),
        );
        // Operand activity favors the first pair, while replacement activity
        // favors the second. GES must rank what it introduces into the clause.
        formula.vsids.activity[1] = 100.0;
        formula.vsids.activity[2] = 100.0;
        formula.vsids.activity[3] = 1.0;
        formula.vsids.activity[lower.get_index().unsigned_abs() as usize] = 2.0;
        formula.vsids.activity[higher.get_index().unsigned_abs() as usize] = 8.0;

        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0), None).unwrap();

        assert_eq!(
            replacement.get_literals(),
            &[Literal::new(-2), Literal::new(4), higher.negated()]
        );
        assert!(!replacement.get_literals().contains(&lower.negated()));
    }

    #[test]
    fn keeps_disjoint_substitutions_when_overlapping_pairs_compete() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, -3, -4, -5, 6]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let lower_overlap = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let higher_overlap = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(3),
        );
        let disjoint = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(4),
            &Literal::new(5),
        );
        formula.vsids.activity[lower_overlap.get_index().unsigned_abs() as usize] = 2.0;
        formula.vsids.activity[higher_overlap.get_index().unsigned_abs() as usize] = 8.0;
        formula.vsids.activity[disjoint.get_index().unsigned_abs() as usize] = 4.0;

        let replacement = substitute_clause(&formula, formula.get_clause_at_idx(0), None).unwrap();

        assert_eq!(replacement.len(), 4);
        assert!(replacement.get_literals().contains(&Literal::new(-2)));
        assert!(replacement.get_literals().contains(&Literal::new(6)));
        assert!(
            replacement
                .get_literals()
                .contains(&higher_overlap.negated())
        );
        assert!(replacement.get_literals().contains(&disjoint.negated()));
        assert!(
            !replacement
                .get_literals()
                .contains(&lower_overlap.negated())
        );
    }

    #[test]
    fn only_rewrites_learned_clauses_selected_by_index_scope() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 4], vec![-1, -2, 5]]);
        formula.get_clause_at_idx_mut(0).lbd = 3;
        formula.get_clause_at_idx_mut(1).lbd = 3;
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let z = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let scope = ClauseScope::indices([1]);

        process(&mut formula, &scope, &mut logger, None, None, None).unwrap();

        assert!(!formula.is_clause_garbage(0));
        assert!(formula.is_clause_garbage(1));
        assert_eq!(
            formula
                .get_clauses()
                .find(|(_, clause)| clause.get_literals().contains(&Literal::new(5)))
                .unwrap()
                .1
                .get_literals(),
            &[Literal::new(5), z.negated()]
        );
    }

    #[test]
    fn rejects_count_growth_even_when_unrolling_decreases_dynamic_lbd() {
        let mut formula = Formula::new(6);
        let first = Literal::new(4);
        let second = Literal::new(5);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &first);
        formula
            .extensions
            .add_substitution(&first, &Literal::new(3), &second);
        let clause = Clause::from_literals(vec![second.negated(), Literal::new(6)], -1);
        let mut levels = vec![None; 7];
        levels[1] = Some(1);
        levels[2] = Some(1);
        levels[3] = Some(1);
        levels[4] = Some(3);
        levels[5] = Some(4);
        levels[6] = Some(1);

        let unrolled = unroll_clause(&formula.extensions, clause.get_literals()).unwrap();
        assert_eq!(dynamic_lbd(&unrolled, Some(&levels)), 1);
        assert_eq!(dynamic_lbd(clause.get_literals(), Some(&levels)), 2);
        let evaluation = evaluate_clause(
            &formula.extensions,
            &formula.vsids,
            &clause,
            false,
            Some(&levels),
        );
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.rejected, 1);
    }

    #[test]
    fn rerolls_with_the_substitution_that_minimizes_current_lbd() {
        let mut formula = Formula::new(6);
        let old = Literal::new(5);
        let better_now = Literal::new(6);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &old);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(3), &better_now);
        let clause =
            Clause::from_literals(vec![old.negated(), Literal::new(-3), Literal::new(4)], 4);
        let mut levels = vec![None; 7];
        levels[1] = Some(1);
        levels[2] = Some(1);
        levels[3] = Some(2);
        levels[4] = Some(3);
        levels[5] = Some(4);
        levels[6] = Some(1);

        let replacement = substitute_clause(&formula, &clause, Some(&levels)).unwrap();

        assert_eq!(
            replacement.get_literals(),
            &[Literal::new(-2), Literal::new(4), better_now.negated()]
        );
        assert_eq!(replacement.lbd, 2);
    }

    #[test]
    fn final_lbd_is_compared_to_source_not_unrolled_working_clause() {
        let mut formula = Formula::new(6);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(5));
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(3), &Literal::new(6));
        let clause = Clause::from_literals([-5, -3, 4].map(Literal::new).to_vec(), 4);
        let levels = [None, Some(1), Some(1), Some(2), Some(3), Some(3), Some(1)];
        let unrolled = unroll_clause(&formula.extensions, clause.get_literals()).unwrap();
        assert_eq!(dynamic_lbd(&unrolled, Some(&levels)), 3);
        assert_eq!(dynamic_lbd(clause.get_literals(), Some(&levels)), 2);
        formula.vsids.activity[6] = 1.0;
        // Rerolling to [-2, 4, -6] improves the working LBD, but ties the source.
        let evaluation = evaluate_clause(
            &formula.extensions,
            &formula.vsids,
            &clause,
            false,
            Some(&levels),
        );
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.rejected, 1);
    }

    #[test]
    fn shortening_requires_strict_dynamic_lbd_improvement() {
        let mut formula = Formula::new(4);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(4));
        let clause = Clause::from_literals([-1, -2, 3].map(Literal::new).to_vec(), 3);
        let levels = [None, Some(1), Some(1), Some(1), Some(1)];
        let evaluation = evaluate_clause(
            &formula.extensions,
            &formula.vsids,
            &clause,
            false,
            Some(&levels),
        );
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.rejected, 1);
        assert_eq!(evaluation.report.literals_removed, 0);
        let evaluation = evaluate_clause(&formula.extensions, &formula.vsids, &clause, false, None);
        assert!(evaluation.replacement.is_some());
        assert_eq!(
            evaluation.report,
            EvaluationReport {
                inspected: 1,
                lbd_improvements: 1,
                literals_removed: 1,
                ..EvaluationReport::default()
            }
        );
    }

    #[test]
    fn accepts_dynamic_improvement_above_stored_lbd() {
        let mut formula = Formula::new(6);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(6));
        let clause = Clause::from_literals([-1, -2, 3, 4, 5].map(Literal::new).to_vec(), 3);
        assert_eq!(dynamic_lbd(clause.get_literals(), None), 5);
        let candidate = apply_substitution(clause.get_literals(), 0, 1, Literal::new(-6));
        assert_eq!(dynamic_lbd(&candidate, None), 4);
        let replacement = substitute_clause(&formula, &clause, None).unwrap();
        assert_eq!(replacement.get_literals(), candidate);
        assert_eq!(replacement.lbd, 3);
        assert!(replacement.ges_generated);
        assert!(!replacement.ges_used);
    }

    #[test]
    fn rejects_dynamic_worsening_even_within_stored_lbd() {
        let mut formula = Formula::new(4);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(4));
        let mut clause = Clause::from_literals([-1, -2, 3].map(Literal::new).to_vec(), 3);
        let levels = [None, Some(1), Some(1), Some(1), Some(2)];
        assert_eq!(dynamic_lbd(clause.get_literals(), Some(&levels)), 1);
        assert!(substitute_clause(&formula, &clause, Some(&levels)).is_none());

        clause.lbd = -1;
        assert!(substitute_clause(&formula, &clause, Some(&levels)).is_none());
        let replacement = substitute_clause(&formula, &clause, None).unwrap();
        assert_eq!(replacement.lbd, -1);
    }

    #[test]
    fn intermediate_threshold_tracks_working_dynamic_lbd() {
        let mut formula = Formula::new(7);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(6));
        formula
            .extensions
            .add_substitution(&Literal::new(3), &Literal::new(4), &Literal::new(7));
        let clause = Clause::from_literals([-1, -2, -3, -4, 5].map(Literal::new).to_vec(), 3);
        let levels = [
            None,
            Some(1),
            Some(2),
            Some(3),
            Some(3),
            Some(3),
            Some(4),
            Some(5),
        ];
        assert_eq!(dynamic_lbd(clause.get_literals(), Some(&levels)), 3);
        let first = apply_substitution(clause.get_literals(), 0, 1, Literal::new(-6));
        assert_eq!(dynamic_lbd(&first, Some(&levels)), 2);
        let replacement = substitute_clause(&formula, &clause, Some(&levels)).unwrap();
        assert_eq!(
            replacement.get_literals(),
            &[
                Literal::new(-3),
                Literal::new(-4),
                Literal::new(5),
                Literal::new(-6)
            ]
        );
        assert_eq!(dynamic_lbd(replacement.get_literals(), Some(&levels)), 2);
        assert_eq!(replacement.lbd, 2);
    }

    #[test]
    fn rejects_same_literal_set_after_unroll_and_reroll_in_different_order() {
        let mut formula = Formula::new(6);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &Literal::new(6));
        let clause = Clause::from_literals([-6, 3, 4, 5].map(Literal::new).to_vec(), 3);
        let unrolled = unroll_clause(&formula.extensions, clause.get_literals()).unwrap();
        assert_ne!(unrolled, clause.get_literals());
        assert_eq!(dynamic_lbd(&unrolled, None), 5);
        // Rerolling moves -6 to the end, but that is not a new clause.
        let evaluation = evaluate_clause(&formula.extensions, &formula.vsids, &clause, false, None);
        assert!(evaluation.replacement.is_none());
        assert_eq!(evaluation.report.noop, 1);
        assert_eq!(evaluation.report.rejected, 0);
    }

    #[test]
    fn original_and_lbd_two_clauses_keep_their_lbd_policy() {
        let mut formula = Formula::new(4);
        let extension = Literal::new(4);
        formula
            .extensions
            .add_substitution(&Literal::new(1), &Literal::new(2), &extension);
        let original = Clause::from_literals(
            vec![Literal::new(-1), Literal::new(-2), Literal::new(3)],
            -1,
        );
        let glue =
            Clause::from_literals(vec![Literal::new(-1), Literal::new(-2), Literal::new(3)], 2);

        let replacement = substitute_clause(&formula, &original, None).unwrap();

        assert_eq!(replacement.lbd, -1);
        assert!(substitute_clause(&formula, &glue, None).is_none());
    }

    #[test]
    fn transfers_a_locked_reason_to_the_equivalent_reformulation() {
        let mut formula = Formula::from_vec(vec![vec![-1, -2, 3]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        let extension = extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        let mut history = History::new();
        formula.assign_implication(Literal::new(1), &mut history, None);
        formula.assign_implication(Literal::new(2), &mut history, None);
        formula.assign_implication(extension, &mut history, Some(1));
        formula.assign_implication(Literal::new(3), &mut history, Some(0));
        // A snapshot with a strict improvement keeps reason-transfer coverage.
        let levels = [None, Some(1), Some(2), Some(3), Some(1)];

        let scope = full_scope(&formula);
        process(
            &mut formula,
            &scope,
            &mut logger,
            None,
            Some(&mut history),
            Some(&levels),
        )
        .unwrap();

        assert!(formula.is_clause_garbage(0));
        assert_eq!(
            formula.get_clause_at_idx(4).get_literals(),
            &[Literal::new(3), extension.negated()]
        );
        assert_eq!(formula.get_clause_at_idx(4).lock_count, 1);
        assert_eq!(
            history.decision_levels[0].get_reason(&Literal::new(3)),
            Some(4)
        );
    }

    #[test]
    fn does_not_substitute_positive_inputs_or_locked_clauses() {
        let mut formula = Formula::from_vec(vec![vec![1, 2, 4], vec![-1, -2, 5]]);
        let mut logger: Option<DratLogger<std::io::Empty>> = None;
        extension_literal(
            &mut formula,
            &mut logger,
            &Literal::new(1),
            &Literal::new(2),
        );
        formula.get_clause_at_idx_mut(1).increment_lock_count();

        let scope = full_scope(&formula);
        process(&mut formula, &scope, &mut logger, None, None, None).unwrap();

        assert!(!formula.is_clause_garbage(0));
        assert!(!formula.is_clause_garbage(1));
        assert_eq!(formula.clause_slots_len(), 5);
    }
}
