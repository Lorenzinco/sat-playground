use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet};

use super::{ObservedPair, Pair, StrategyUpdate};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Coord {
    row: usize,
    col: usize,
}

type PivotKey = (usize, Coord);
type MergeContext = (usize, Coord, Coord);

#[derive(Clone, Debug)]
struct Stage {
    matrix: Vec<Vec<i32>>,
    literal_coords: HashMap<i32, Vec<Coord>>,
    depth: usize,
}

impl Stage {
    fn new(matrix: Vec<Vec<i32>>, depth: usize) -> Self {
        let mut literal_coords: HashMap<i32, Vec<Coord>> = HashMap::new();
        for (row, values) in matrix.iter().enumerate() {
            for (col, literal) in values.iter().copied().enumerate() {
                literal_coords
                    .entry(literal)
                    .or_default()
                    .push(Coord { row, col });
            }
        }
        Self {
            matrix,
            literal_coords,
            depth,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct TargetState {
    merge_pairs: BTreeSet<Pair>,
    child_literal: Option<i32>,
}

#[derive(Clone, Debug)]
struct PivotContext {
    stage: usize,
    pivot: Coord,
    targets: HashMap<Coord, TargetState>,
    spawned: bool,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum MatchContext {
    Collision {
        stage: usize,
        pivot: Coord,
        target: Coord,
    },
    Merge {
        stage: usize,
        pivot: Coord,
        target: Coord,
    },
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CollisionEvent {
    stage: usize,
    pivot: Coord,
    target: Coord,
    pair: Pair,
    result: i32,
}

#[derive(Debug)]
pub(crate) struct PigeonholeTracker {
    stages: Vec<Stage>,
    literal_locations: HashMap<i32, HashMap<usize, Vec<Coord>>>,
    pivots: HashMap<PivotKey, PivotContext>,
    ready_merges: HashMap<Pair, HashSet<MergeContext>>,
    completion_frontier: BTreeSet<PivotKey>,
    valid_contexts: HashMap<Pair, HashSet<MatchContext>>,
    completed_stages: usize,
    deepest_level: usize,
    best_progress: usize,
    #[cfg(test)]
    collision_coordinate_checks: usize,
}

impl PigeonholeTracker {
    pub(crate) fn new(holes: usize) -> Self {
        let rows = holes + 1;
        let matrix = (0..rows)
            .map(|row| {
                (0..holes)
                    .map(|col| (row * holes + col + 1) as i32)
                    .collect()
            })
            .collect();

        let mut tracker = Self {
            stages: Vec::new(),
            literal_locations: HashMap::new(),
            pivots: HashMap::new(),
            ready_merges: HashMap::new(),
            completion_frontier: BTreeSet::new(),
            valid_contexts: HashMap::new(),
            completed_stages: 0,
            deepest_level: 0,
            best_progress: 0,
            #[cfg(test)]
            collision_coordinate_checks: 0,
        };
        tracker.add_stage(matrix, 0);
        tracker
    }

    fn add_stage(&mut self, matrix: Vec<Vec<i32>>, depth: usize) -> usize {
        let stage_id = self.stages.len();
        let stage = Stage::new(matrix, depth);
        for (literal, coords) in &stage.literal_coords {
            self.literal_locations
                .entry(*literal)
                .or_default()
                .insert(stage_id, coords.clone());
        }
        self.stages.push(stage);
        stage_id
    }

    fn contexts_from_coords(
        stage: usize,
        first: &[Coord],
        second: &[Coord],
    ) -> BTreeSet<(usize, Coord, Coord)> {
        let mut contexts = BTreeSet::new();
        for a in first {
            for b in second {
                if a.row == b.row || a.col == b.col {
                    continue;
                }
                contexts.insert((
                    stage,
                    Coord {
                        row: b.row,
                        col: a.col,
                    },
                    Coord {
                        row: a.row,
                        col: b.col,
                    },
                ));
                contexts.insert((
                    stage,
                    Coord {
                        row: a.row,
                        col: b.col,
                    },
                    Coord {
                        row: b.row,
                        col: a.col,
                    },
                ));
            }
        }
        contexts
    }

    fn collision_events_for_observation(&mut self, pair: Pair, result: i32) -> Vec<CollisionEvent> {
        let first = self
            .literal_locations
            .get(&pair.first)
            .cloned()
            .unwrap_or_default();
        let second = self
            .literal_locations
            .get(&pair.second)
            .cloned()
            .unwrap_or_default();
        let mut contexts = BTreeSet::new();
        for (stage, first_coords) in first {
            let Some(second_coords) = second.get(&stage) else {
                continue;
            };
            #[cfg(test)]
            {
                self.collision_coordinate_checks += first_coords.len() * second_coords.len();
            }
            contexts.extend(Self::contexts_from_coords(
                stage,
                &first_coords,
                second_coords,
            ));
        }
        contexts
            .into_iter()
            .map(|(stage, pivot, target)| CollisionEvent {
                stage,
                pivot,
                target,
                pair,
                result,
            })
            .collect()
    }

    fn collision_events_for_stage(
        &mut self,
        stage_id: usize,
        pair: Pair,
        result: i32,
    ) -> Vec<CollisionEvent> {
        let first = self.stages[stage_id]
            .literal_coords
            .get(&pair.first)
            .cloned()
            .unwrap_or_default();
        let second = self.stages[stage_id]
            .literal_coords
            .get(&pair.second)
            .cloned()
            .unwrap_or_default();
        #[cfg(test)]
        {
            self.collision_coordinate_checks += first.len() * second.len();
        }
        Self::contexts_from_coords(stage_id, &first, &second)
            .into_iter()
            .map(|(stage, pivot, target)| CollisionEvent {
                stage,
                pivot,
                target,
                pair,
                result,
            })
            .collect()
    }

    fn target_literal(&self, stage: usize, target: Coord) -> i32 {
        self.stages[stage].matrix[target.row][target.col]
    }

    fn apply_collision(&mut self, event: CollisionEvent, observed: &HashMap<Pair, ObservedPair>) {
        let key = (event.stage, event.pivot);
        let merge_context = (event.stage, event.pivot, event.target);
        let target_literal = self.target_literal(event.stage, event.target);
        let merge_pair = Pair::new(-target_literal, -event.result);

        self.valid_contexts
            .entry(event.pair)
            .or_default()
            .insert(MatchContext::Collision {
                stage: event.stage,
                pivot: event.pivot,
                target: event.target,
            });
        self.valid_contexts
            .entry(merge_pair)
            .or_default()
            .insert(MatchContext::Merge {
                stage: event.stage,
                pivot: event.pivot,
                target: event.target,
            });

        let target = self
            .pivots
            .entry(key)
            .or_insert_with(|| PivotContext {
                stage: event.stage,
                pivot: event.pivot,
                targets: HashMap::new(),
                spawned: false,
            })
            .targets
            .entry(event.target)
            .or_default();
        let new_merge_pair = target.merge_pairs.insert(merge_pair);
        let incomplete = target.child_literal.is_none();

        if new_merge_pair && incomplete {
            if let Some(result) = observed.get(&merge_pair).map(|record| record.actual_result) {
                self.complete_target(key, event.target, -result);
            } else {
                self.ready_merges
                    .entry(merge_pair)
                    .or_default()
                    .insert(merge_context);
            }
        }
    }

    fn complete_target(&mut self, key: PivotKey, target_coord: Coord, child_literal: i32) {
        let (merge_pairs, progress) = {
            let context = self
                .pivots
                .get_mut(&key)
                .expect("completion references an existing pivot");
            let target = context
                .targets
                .get_mut(&target_coord)
                .expect("completion references an existing target");
            if target.child_literal.is_some() {
                return;
            }
            target.child_literal = Some(child_literal);
            let merge_pairs: Vec<Pair> = target.merge_pairs.iter().copied().collect();
            let progress = Self::completed_targets(context);
            (merge_pairs, progress)
        };

        let merge_context = (key.0, key.1, target_coord);
        for pair in merge_pairs {
            let remove_pair = if let Some(contexts) = self.ready_merges.get_mut(&pair) {
                contexts.remove(&merge_context);
                contexts.is_empty()
            } else {
                false
            };
            if remove_pair {
                self.ready_merges.remove(&pair);
            }
        }
        self.best_progress = self.best_progress.max(progress);
        self.completion_frontier.insert(key);
    }

    fn consume_ready_merge(&mut self, pair: Pair, observed: &HashMap<Pair, ObservedPair>) {
        let Some(result) = observed.get(&pair).map(|record| record.actual_result) else {
            return;
        };
        let contexts = self.ready_merges.remove(&pair).unwrap_or_default();
        for (stage, pivot, target) in contexts {
            self.complete_target((stage, pivot), target, -result);
        }
    }

    fn expected_targets(&self, context: &PivotContext) -> usize {
        let stage = &self.stages[context.stage];
        (stage.matrix.len() - 1) * (stage.matrix[0].len() - 1)
    }

    fn completed_targets(context: &PivotContext) -> usize {
        context
            .targets
            .values()
            .filter(|target| target.child_literal.is_some())
            .count()
    }

    fn child_matrix(&self, context: &PivotContext) -> Vec<Vec<i32>> {
        let stage = &self.stages[context.stage];
        let mut child = Vec::with_capacity(stage.matrix.len() - 1);
        for row in 0..stage.matrix.len() {
            if row == context.pivot.row {
                continue;
            }
            let mut child_row = Vec::with_capacity(stage.matrix[0].len() - 1);
            for col in 0..stage.matrix[0].len() {
                if col == context.pivot.col {
                    continue;
                }
                child_row.push(
                    context.targets[&Coord { row, col }]
                        .child_literal
                        .expect("a completed pivot has every child literal"),
                );
            }
            child.push(child_row);
        }
        child
    }

    fn replay_stage(&mut self, stage_id: usize, observed: &HashMap<Pair, ObservedPair>) {
        let mut pairs: Vec<Pair> = observed.keys().copied().collect();
        pairs.sort_unstable();
        for pair in pairs {
            let result = observed[&pair].actual_result;
            let events = self.collision_events_for_stage(stage_id, pair, result);
            for event in events {
                self.apply_collision(event, observed);
            }
        }
    }

    fn spawn_completed_pivots(&mut self, observed: &HashMap<Pair, ObservedPair>) -> usize {
        let mut newly_completed = 0;
        while let Some(key) = self.completion_frontier.pop_first() {
            let complete = {
                let context = &self.pivots[&key];
                !context.spawned
                    && context.targets.len() == self.expected_targets(context)
                    && context
                        .targets
                        .values()
                        .all(|target| target.child_literal.is_some())
            };
            if !complete {
                continue;
            }

            let child = self.child_matrix(&self.pivots[&key]);
            let depth = self.stages[self.pivots[&key].stage].depth + 1;
            self.pivots
                .get_mut(&key)
                .expect("spawn references an existing pivot")
                .spawned = true;
            let child_stage = self.add_stage(child, depth);
            self.completed_stages += 1;
            newly_completed += 1;
            self.deepest_level = self.deepest_level.max(depth);
            self.replay_stage(child_stage, observed);
        }
        newly_completed
    }

    pub(crate) fn process(
        &mut self,
        observed: &HashMap<Pair, ObservedPair>,
        new_observation: Option<(Pair, i32)>,
    ) -> StrategyUpdate {
        if let Some((pair, result)) = new_observation {
            let events = self.collision_events_for_observation(pair, result);
            for event in events {
                self.apply_collision(event, observed);
            }
            self.consume_ready_merge(pair, observed);
        }

        StrategyUpdate {
            stages_completed: self.spawn_completed_pivots(observed),
        }
    }

    fn compare_contexts(&self, left: &PivotContext, right: &PivotContext) -> Ordering {
        self.stages[right.stage]
            .depth
            .cmp(&self.stages[left.stage].depth)
            .then_with(|| Self::completed_targets(right).cmp(&Self::completed_targets(left)))
            .then_with(|| left.stage.cmp(&right.stage))
            .then_with(|| left.pivot.cmp(&right.pivot))
    }

    pub(crate) fn suggest(&self, _observed: &HashMap<Pair, ObservedPair>) -> Option<Pair> {
        let mut merges: Vec<(Pair, MergeContext)> = self
            .ready_merges
            .iter()
            .flat_map(|(pair, contexts)| contexts.iter().map(|context| (*pair, *context)))
            .filter(|(_, (stage, pivot, target))| {
                self.pivots
                    .get(&(*stage, *pivot))
                    .and_then(|context| context.targets.get(target))
                    .is_some_and(|target| target.child_literal.is_none())
            })
            .collect();
        merges.sort_by(|(left_pair, left), (right_pair, right)| {
            self.compare_contexts(
                &self.pivots[&(left.0, left.1)],
                &self.pivots[&(right.0, right.1)],
            )
            .then_with(|| left.2.cmp(&right.2))
            .then_with(|| left_pair.cmp(right_pair))
        });
        if let Some((pair, _)) = merges.first() {
            return Some(*pair);
        }

        let mut contexts: Vec<&PivotContext> = self
            .pivots
            .values()
            .filter(|context| !context.spawned)
            .collect();
        contexts.sort_by(|left, right| self.compare_contexts(left, right));

        // Continue the deepest, most advanced coherent pivot.
        for context in &contexts {
            let stage = &self.stages[context.stage];
            for row in 0..stage.matrix.len() {
                if row == context.pivot.row {
                    continue;
                }
                for col in 0..stage.matrix[0].len() {
                    if col == context.pivot.col {
                        continue;
                    }
                    let target = Coord { row, col };
                    if context.targets.contains_key(&target) {
                        continue;
                    }
                    return Some(Pair::new(
                        stage.matrix[row][context.pivot.col],
                        stage.matrix[context.pivot.row][col],
                    ));
                }
            }
        }

        // No pivot has been materialized yet: choose the first collision in the
        // deepest available non-base stage.
        let mut stage_ids: Vec<usize> = (0..self.stages.len()).collect();
        stage_ids.sort_by(|left, right| {
            self.stages[*right]
                .depth
                .cmp(&self.stages[*left].depth)
                .then_with(|| left.cmp(right))
        });
        for stage_id in stage_ids {
            let stage = &self.stages[stage_id];
            if stage.matrix.len() >= 2 && stage.matrix[0].len() >= 2 {
                return Some(Pair::new(stage.matrix[1][0], stage.matrix[0][1]));
            }
        }
        None
    }

    pub(crate) fn contexts_for(&self, pair: Pair) -> usize {
        self.valid_contexts.get(&pair).map_or(0, HashSet::len)
    }

    pub(crate) fn stages_completed(&self) -> usize {
        self.completed_stages
    }

    pub(crate) fn deepest_level(&self) -> usize {
        self.deepest_level
    }

    pub(crate) fn current_progress(&self) -> usize {
        self.pivots
            .values()
            .filter(|context| !context.spawned)
            .map(Self::completed_targets)
            .max()
            .unwrap_or(0)
    }

    pub(crate) fn best_progress(&self) -> usize {
        self.best_progress
    }

    #[cfg(test)]
    pub(crate) fn collision_coordinate_checks(&self) -> usize {
        self.collision_coordinate_checks
    }
}
