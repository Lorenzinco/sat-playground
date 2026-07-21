use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

use super::{ObservedPair, Pair, StrategyUpdate};

#[derive(Clone, Debug)]
struct Node {
    planned: Pair,
    actual_pair: Option<Pair>,
    actual_result: Option<i32>,
    level: usize,
}

#[derive(Debug)]
pub(crate) struct StaticDagTracker {
    original_variables: usize,
    nodes: Vec<Node>,
    dependents: Vec<Vec<usize>>,
    unresolved_dependencies: Vec<usize>,
    activation_frontier: VecDeque<usize>,
    ready_by_pair: HashMap<Pair, Vec<usize>>,
    suggestions: BTreeSet<(usize, Pair)>,
    valid_contexts: HashMap<Pair, HashSet<usize>>,
    completed: usize,
    deepest_level: usize,
    #[cfg(test)]
    activation_visits: usize,
}

impl StaticDagTracker {
    pub(crate) fn new(original_variables: usize, operands: Vec<[i32; 2]>) -> Self {
        let mut levels = Vec::with_capacity(operands.len());
        let mut nodes = Vec::with_capacity(operands.len());
        let mut dependents = vec![Vec::new(); operands.len()];
        let mut unresolved_dependencies = vec![0; operands.len()];

        for (index, pair) in operands.into_iter().enumerate() {
            let planned = Pair::new(pair[0], pair[1]);
            let dependency_level = |literal: i32| {
                let variable = literal.unsigned_abs() as usize;
                if variable <= original_variables {
                    0
                } else {
                    levels[variable - original_variables - 1]
                }
            };
            let level = 1 + dependency_level(pair[0]).max(dependency_level(pair[1]));

            for literal in pair {
                let variable = literal.unsigned_abs() as usize;
                if variable > original_variables {
                    let dependency = variable - original_variables - 1;
                    dependents[dependency].push(index);
                    unresolved_dependencies[index] += 1;
                }
            }

            levels.push(level);
            nodes.push(Node {
                planned,
                actual_pair: None,
                actual_result: None,
                level,
            });
        }

        let activation_frontier = unresolved_dependencies
            .iter()
            .enumerate()
            .filter_map(|(index, remaining)| (*remaining == 0).then_some(index))
            .collect();
        let mut tracker = Self {
            original_variables,
            nodes,
            dependents,
            unresolved_dependencies,
            activation_frontier,
            ready_by_pair: HashMap::new(),
            suggestions: BTreeSet::new(),
            valid_contexts: HashMap::new(),
            completed: 0,
            deepest_level: 0,
            #[cfg(test)]
            activation_visits: 0,
        };
        tracker.process(&HashMap::new(), None);
        tracker
    }

    fn translate_literal(&self, literal: i32) -> Option<i32> {
        let variable = literal.unsigned_abs() as usize;
        if variable <= self.original_variables {
            return Some(literal);
        }

        let node = self.nodes.get(variable - self.original_variables - 1)?;
        let actual = node.actual_result?;
        Some(if literal < 0 { -actual } else { actual })
    }

    fn complete_node(&mut self, index: usize, result: i32) -> bool {
        if self.nodes[index].actual_result.is_some() {
            return false;
        }

        if let Some(pair) = self.nodes[index].actual_pair {
            self.suggestions.remove(&(index, pair));
        }
        self.nodes[index].actual_result = Some(result);
        self.completed += 1;
        self.deepest_level = self.deepest_level.max(self.nodes[index].level);

        for dependent in self.dependents[index].iter().copied() {
            self.unresolved_dependencies[dependent] -= 1;
            if self.unresolved_dependencies[dependent] == 0 {
                self.activation_frontier.push_back(dependent);
            }
        }
        true
    }

    fn complete_ready_pair(&mut self, pair: Pair, result: i32) -> usize {
        let ready = self.ready_by_pair.remove(&pair).unwrap_or_default();
        ready
            .into_iter()
            .map(|index| usize::from(self.complete_node(index, result)))
            .sum()
    }

    fn activate_frontier(&mut self, observed: &HashMap<Pair, ObservedPair>) -> usize {
        let mut newly_completed = 0;
        while let Some(index) = self.activation_frontier.pop_front() {
            if self.nodes[index].actual_pair.is_some() {
                continue;
            }
            #[cfg(test)]
            {
                self.activation_visits += 1;
            }

            let planned = self.nodes[index].planned;
            let left = self
                .translate_literal(planned.first)
                .expect("frontier nodes have resolved dependencies");
            let right = self
                .translate_literal(planned.second)
                .expect("frontier nodes have resolved dependencies");
            let actual_pair = Pair::new(left, right);
            self.nodes[index].actual_pair = Some(actual_pair);
            self.valid_contexts
                .entry(actual_pair)
                .or_default()
                .insert(index);

            if let Some(result) = observed
                .get(&actual_pair)
                .map(|record| record.actual_result)
            {
                newly_completed += usize::from(self.complete_node(index, result));
            } else {
                self.ready_by_pair
                    .entry(actual_pair)
                    .or_default()
                    .push(index);
                self.suggestions.insert((index, actual_pair));
            }
        }
        newly_completed
    }

    pub(crate) fn process(
        &mut self,
        observed: &HashMap<Pair, ObservedPair>,
        new_pair: Option<Pair>,
    ) -> StrategyUpdate {
        let mut newly_completed = 0;
        if let Some(pair) = new_pair {
            if let Some(result) = observed.get(&pair).map(|record| record.actual_result) {
                newly_completed += self.complete_ready_pair(pair, result);
            }
        }
        newly_completed += self.activate_frontier(observed);

        StrategyUpdate {
            stages_completed: newly_completed,
        }
    }

    pub(crate) fn suggest(&self) -> Option<Pair> {
        self.suggestions.first().map(|(_, pair)| *pair)
    }

    pub(crate) fn contexts_for(&self, pair: Pair) -> usize {
        self.valid_contexts.get(&pair).map_or(0, HashSet::len)
    }

    pub(crate) fn stages_completed(&self) -> usize {
        self.completed
    }

    pub(crate) fn deepest_level(&self) -> usize {
        self.deepest_level
    }

    pub(crate) fn current_progress(&self) -> usize {
        self.completed
    }

    #[cfg(test)]
    pub(crate) fn activation_visits(&self) -> usize {
        self.activation_visits
    }
}
