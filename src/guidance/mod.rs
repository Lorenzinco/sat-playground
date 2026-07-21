mod pair;
mod pigeonhole;
mod static_dag;

use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufWriter, Write};

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::{PyBool, PyDict};

use pair::Pair;
use pigeonhole::PigeonholeTracker;
use static_dag::StaticDagTracker;

const SCHEMA_VERSION: i64 = 2;

/// Owned configuration for one guidance strategy.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GuidanceSpec {
    PigeonholeCook {
        holes: usize,
    },
    StaticAndDag {
        original_variables: usize,
        operands: Vec<[i32; 2]>,
    },
}

impl GuidanceSpec {
    fn validate(&self) -> Result<(), String> {
        match self {
            Self::PigeonholeCook { holes } => {
                if *holes == 0 {
                    return Err("holes must be positive".to_owned());
                }
                let rows = holes
                    .checked_add(1)
                    .ok_or_else(|| "pigeonhole matrix is too large".to_owned())?;
                let variables = holes
                    .checked_mul(rows)
                    .ok_or_else(|| "pigeonhole matrix is too large".to_owned())?;
                if variables > i32::MAX as usize {
                    return Err("pigeonhole matrix literals exceed signed DIMACS range".to_owned());
                }
                Ok(())
            }
            Self::StaticAndDag {
                original_variables,
                operands,
            } => {
                if *original_variables == 0 {
                    return Err("original_variables must be positive".to_owned());
                }
                if original_variables
                    .checked_add(operands.len())
                    .is_none_or(|last| last > i32::MAX as usize)
                {
                    return Err("static DAG variables exceed signed DIMACS range".to_owned());
                }

                for (index, pair) in operands.iter().enumerate() {
                    let largest_available = original_variables + index;
                    for literal in pair {
                        if *literal == 0 {
                            return Err(format!("operands[{index}] contains literal 0"));
                        }
                        if literal.unsigned_abs() as usize > largest_available {
                            return Err(format!(
                                "operands[{index}] references a forward or unknown variable {}",
                                literal.unsigned_abs()
                            ));
                        }
                    }
                }
                Ok(())
            }
        }
    }
}

fn value_error(message: impl Into<String>) -> PyErr {
    PyValueError::new_err(message.into())
}

struct StrictI64(i64);

impl FromPyObject<'_, '_> for StrictI64 {
    type Error = PyErr;

    fn extract(object: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        if object.cast::<PyBool>().is_ok() {
            return Err(value_error("booleans are not integers in guidance specs"));
        }
        object.extract::<i64>().map(Self)
    }
}

impl FromPyObject<'_, '_> for GuidanceSpec {
    type Error = PyErr;

    fn extract(object: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let dictionary = object
            .cast::<PyDict>()
            .map_err(|_| value_error("guidance spec must be a dict"))?;

        let version = dictionary
            .get_item("schema_version")
            .map_err(|error| value_error(format!("invalid schema_version: {error}")))?
            .ok_or_else(|| value_error("missing schema_version"))?
            .extract::<StrictI64>()
            .map_err(|_| value_error("schema_version must be an integer"))?
            .0;
        if version != SCHEMA_VERSION {
            return Err(value_error(format!(
                "unsupported guidance schema_version {version}; expected {SCHEMA_VERSION}"
            )));
        }

        let kind = dictionary
            .get_item("kind")
            .map_err(|error| value_error(format!("invalid kind: {error}")))?
            .ok_or_else(|| value_error("missing kind"))?
            .extract::<String>()
            .map_err(|_| value_error("kind must be a string"))?;

        let spec = match kind.as_str() {
            "pigeonhole_cook" => {
                let holes = dictionary
                    .get_item("holes")
                    .map_err(|error| value_error(format!("invalid holes: {error}")))?
                    .ok_or_else(|| value_error("missing holes"))?
                    .extract::<StrictI64>()
                    .map_err(|_| value_error("holes must be an integer"))?
                    .0;
                let holes =
                    usize::try_from(holes).map_err(|_| value_error("holes must be positive"))?;
                Self::PigeonholeCook { holes }
            }
            "static_and_dag" => {
                let original_variables = dictionary
                    .get_item("original_variables")
                    .map_err(|error| value_error(format!("invalid original_variables: {error}")))?
                    .ok_or_else(|| value_error("missing original_variables"))?
                    .extract::<StrictI64>()
                    .map_err(|_| value_error("original_variables must be an integer"))?
                    .0;
                let original_variables = usize::try_from(original_variables)
                    .map_err(|_| value_error("original_variables must be positive"))?;

                let raw_operands = dictionary
                    .get_item("operands")
                    .map_err(|error| value_error(format!("invalid operands: {error}")))?
                    .ok_or_else(|| value_error("missing operands"))?
                    .extract::<Vec<Vec<StrictI64>>>()
                    .map_err(|_| value_error("operands must be a list of two-integer lists"))?;
                let mut operands = Vec::with_capacity(raw_operands.len());
                for (index, raw_pair) in raw_operands.into_iter().enumerate() {
                    if raw_pair.len() != 2 {
                        return Err(value_error(format!(
                            "operands[{index}] must contain exactly two literals"
                        )));
                    }
                    let left = i32::try_from(raw_pair[0].0).map_err(|_| {
                        value_error(format!("operands[{index}][0] is outside i32 range"))
                    })?;
                    let right = i32::try_from(raw_pair[1].0).map_err(|_| {
                        value_error(format!("operands[{index}][1] is outside i32 range"))
                    })?;
                    operands.push([left, right]);
                }
                Self::StaticAndDag {
                    original_variables,
                    operands,
                }
            }
            _ => {
                return Err(value_error(format!(
                    "unknown guidance kind {kind:?}; expected pigeonhole_cook or static_and_dag"
                )));
            }
        };

        spec.validate().map_err(value_error)?;
        Ok(spec)
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GuidanceObservation {
    pub matched: bool,
    pub unique_match: bool,
    pub contexts: usize,
    /// Number of DAG nodes or coherent PHP pivots completed by this observation,
    /// including completions unlocked by replay.
    pub stages_completed: usize,
    /// The deterministic suggestion computed immediately before this DIP.
    pub suggestion: Option<(i32, i32)>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct GuidanceSummary {
    pub checks: usize,
    pub matches: usize,
    pub unique_matches: usize,
    pub stages_completed: usize,
    pub deepest_level: usize,
    /// Largest coherent pivot progress (or completed static-node count) observed.
    pub best_progress: usize,
}

#[derive(Clone, Debug)]
struct ObservedPair {
    actual_result: i32,
    occurrence_count: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct StrategyUpdate {
    stages_completed: usize,
}

#[derive(Debug)]
enum Strategy {
    Pigeonhole(PigeonholeTracker),
    Static(StaticDagTracker),
}

impl Strategy {
    fn process(
        &mut self,
        observed: &HashMap<Pair, ObservedPair>,
        pair: Pair,
        result: i32,
    ) -> StrategyUpdate {
        match self {
            Self::Pigeonhole(tracker) => tracker.process(observed, Some((pair, result))),
            Self::Static(tracker) => tracker.process(observed, Some(pair)),
        }
    }

    fn suggest(&self, observed: &HashMap<Pair, ObservedPair>) -> Option<Pair> {
        match self {
            Self::Pigeonhole(tracker) => tracker.suggest(observed),
            Self::Static(tracker) => tracker.suggest(),
        }
    }

    fn contexts_for(&self, pair: Pair) -> usize {
        match self {
            Self::Pigeonhole(tracker) => tracker.contexts_for(pair),
            Self::Static(tracker) => tracker.contexts_for(pair),
        }
    }

    fn stages_completed(&self) -> usize {
        match self {
            Self::Pigeonhole(tracker) => tracker.stages_completed(),
            Self::Static(tracker) => tracker.stages_completed(),
        }
    }

    fn deepest_level(&self) -> usize {
        match self {
            Self::Pigeonhole(tracker) => tracker.deepest_level(),
            Self::Static(tracker) => tracker.deepest_level(),
        }
    }

    fn current_progress(&self) -> usize {
        match self {
            Self::Pigeonhole(tracker) => tracker.current_progress(),
            Self::Static(tracker) => tracker.current_progress(),
        }
    }

    fn best_progress(&self) -> usize {
        match self {
            Self::Pigeonhole(tracker) => tracker.best_progress(),
            Self::Static(tracker) => tracker.current_progress(),
        }
    }
}

/// Stateful guidance for observed `z <-> (left AND right)` extension primitives.
#[derive(Debug)]
pub struct GuidanceTracker {
    strategy: Strategy,
    observed: HashMap<Pair, ObservedPair>,
    summary: GuidanceSummary,
    log: Option<BufWriter<File>>,
    finished: bool,
}

impl GuidanceTracker {
    pub fn new(spec: GuidanceSpec, log_path: Option<String>) -> io::Result<Self> {
        spec.validate()
            .map_err(|message| io::Error::new(io::ErrorKind::InvalidInput, message))?;

        let (strategy, description) = match spec {
            GuidanceSpec::PigeonholeCook { holes } => (
                Strategy::Pigeonhole(PigeonholeTracker::new(holes)),
                format!("pigeonhole_cook holes={holes}"),
            ),
            GuidanceSpec::StaticAndDag {
                original_variables,
                operands,
            } => {
                let nodes = operands.len();
                (
                    Strategy::Static(StaticDagTracker::new(original_variables, operands)),
                    format!("static_and_dag original_variables={original_variables} nodes={nodes}"),
                )
            }
        };

        let log = if let Some(path) = log_path {
            let mut writer = BufWriter::new(File::create(path)?);
            writeln!(writer, "guidance strategy: {description}")?;
            Some(writer)
        } else {
            None
        };

        Ok(Self {
            strategy,
            observed: HashMap::new(),
            summary: GuidanceSummary::default(),
            log,
            finished: false,
        })
    }

    /// Return a deterministic proof-consistent pair for diagnostics and logs.
    /// This does not influence which DIP conflict analysis selects.
    pub fn suggest(&self) -> Option<(i32, i32)> {
        self.strategy.suggest(&self.observed).map(Pair::tuple)
    }

    pub fn observe(
        &mut self,
        left: i32,
        right: i32,
        result: i32,
    ) -> io::Result<GuidanceObservation> {
        for (name, literal) in [("left", left), ("right", right)] {
            if literal == 0 || literal == i32::MIN {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!("{name} must be a nonzero signed DIMACS literal in i32 range"),
                ));
            }
        }
        if result <= 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "result must be a positive DIMACS extension variable",
            ));
        }

        let suggestion = self.suggest();
        let pair = Pair::new(left, right);
        let (update, first_observation) = if let Some(record) = self.observed.get_mut(&pair) {
            if record.actual_result != result {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!(
                        "canonical pair {pair} was previously observed with result {}, not {result}",
                        record.actual_result
                    ),
                ));
            }
            record.occurrence_count += 1;
            (StrategyUpdate::default(), false)
        } else {
            self.observed.insert(
                pair,
                ObservedPair {
                    actual_result: result,
                    occurrence_count: 1,
                },
            );
            (self.strategy.process(&self.observed, pair, result), true)
        };

        let contexts = self.strategy.contexts_for(pair);
        let matched = contexts != 0;
        let unique_match = matched && first_observation;

        self.summary.checks += 1;
        self.summary.matches += usize::from(matched);
        self.summary.unique_matches += usize::from(unique_match);
        self.summary.stages_completed = self.strategy.stages_completed();
        self.summary.deepest_level = self.strategy.deepest_level();
        self.summary.best_progress = self
            .summary
            .best_progress
            .max(self.strategy.best_progress());

        let observation = GuidanceObservation {
            matched,
            unique_match,
            contexts,
            stages_completed: update.stages_completed,
            suggestion,
        };

        if let Some(log) = &mut self.log {
            writeln!(
                log,
                "dip actual=({left}, {right})->{result} canonical={pair} matched={matched} unique={unique_match} contexts={contexts} stages_completed_now={} active_progress={} best_progress={} stages_completed_total={} deepest_level={} suggestion_before={suggestion:?}",
                observation.stages_completed,
                self.strategy.current_progress(),
                self.summary.best_progress,
                self.summary.stages_completed,
                self.summary.deepest_level,
            )?;
        }

        Ok(observation)
    }

    pub fn summary(&self) -> GuidanceSummary {
        self.summary.clone()
    }

    pub fn finish(&mut self) -> io::Result<()> {
        if let Some(log) = &mut self.log {
            if !self.finished {
                writeln!(
                    log,
                    "summary checks={} matches={} unique_matches={} stages_completed={} deepest_level={} best_progress={}",
                    self.summary.checks,
                    self.summary.matches,
                    self.summary.unique_matches,
                    self.summary.stages_completed,
                    self.summary.deepest_level,
                    self.summary.best_progress,
                )?;
                self.finished = true;
            }
            log.flush()?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    use pyo3::prelude::*;
    use pyo3::types::{PyAnyMethods, PyDict, PyDictMethods};

    use super::{GuidanceSpec, GuidanceTracker, Pair, Strategy};

    fn static_tracker(original_variables: usize, operands: &[[i32; 2]]) -> GuidanceTracker {
        GuidanceTracker::new(
            GuidanceSpec::StaticAndDag {
                original_variables,
                operands: operands.to_vec(),
            },
            None,
        )
        .unwrap()
    }

    fn php_tracker(holes: usize) -> GuidanceTracker {
        GuidanceTracker::new(GuidanceSpec::PigeonholeCook { holes }, None).unwrap()
    }

    fn static_activation_visits(tracker: &GuidanceTracker) -> usize {
        match &tracker.strategy {
            Strategy::Static(static_tracker) => static_tracker.activation_visits(),
            Strategy::Pigeonhole(_) => panic!("expected a static tracker"),
        }
    }

    fn php_coordinate_checks(tracker: &GuidanceTracker) -> usize {
        match &tracker.strategy {
            Strategy::Pigeonhole(php_tracker) => php_tracker.collision_coordinate_checks(),
            Strategy::Static(_) => panic!("expected a pigeonhole tracker"),
        }
    }

    #[test]
    fn static_empty_dag_is_supported() {
        let tracker = static_tracker(3, &[]);
        assert_eq!(tracker.suggest(), None);
        assert_eq!(tracker.summary().stages_completed, 0);
    }

    #[test]
    fn static_dependency_uses_actual_result_variable() {
        let mut tracker = static_tracker(3, &[[1, -2], [4, 3]]);
        assert_eq!(tracker.suggest(), Some((-2, 1)));
        let first = tracker.observe(-2, 1, 10).unwrap();
        assert!(first.matched);
        assert_eq!(first.stages_completed, 1);
        assert_eq!(tracker.suggest(), Some((3, 10)));
        let second = tracker.observe(10, 3, 11).unwrap();
        assert!(second.matched);
        assert_eq!(tracker.summary().stages_completed, 2);
        assert_eq!(tracker.summary().deepest_level, 2);
    }

    #[test]
    fn static_replays_an_early_observation() {
        let mut tracker = static_tracker(3, &[[1, 2], [3, 4]]);
        assert!(!tracker.observe(3, 9, 12).unwrap().matched);
        let observation = tracker.observe(2, 1, 9).unwrap();
        assert!(observation.matched);
        assert_eq!(observation.stages_completed, 2);
        assert_eq!(tracker.summary().stages_completed, 2);
    }

    #[test]
    fn static_duplicate_is_matched_but_not_unique() {
        let mut tracker = static_tracker(2, &[[1, -2]]);
        assert!(tracker.observe(1, -2, 7).unwrap().unique_match);
        let duplicate = tracker.observe(-2, 1, 7).unwrap();
        assert!(duplicate.matched);
        assert!(!duplicate.unique_match);
        assert_eq!(duplicate.contexts, 1);
    }

    #[test]
    fn static_ignores_irrelevant_extensions() {
        let mut tracker = static_tracker(2, &[[1, 2]]);
        let observation = tracker.observe(1, -2, 99).unwrap();
        assert!(!observation.matched);
        assert_eq!(tracker.suggest(), Some((1, 2)));
    }

    #[test]
    fn static_irrelevant_observations_do_not_rescan_activated_nodes() {
        let operands = vec![[1, 2]; 2_000];
        let mut tracker = static_tracker(2, &operands);
        assert_eq!(static_activation_visits(&tracker), operands.len());

        for offset in 0..500 {
            assert!(
                !tracker
                    .observe(10_000 + offset, 20_000 + offset, 30_000 + offset)
                    .unwrap()
                    .matched
            );
        }
        assert_eq!(static_activation_visits(&tracker), operands.len());
        assert_eq!(tracker.summary().stages_completed, 0);
    }

    #[test]
    fn same_php_row_or_column_is_rejected() {
        let mut tracker = php_tracker(2);
        assert!(!tracker.observe(1, 2, 7).unwrap().matched);
        assert!(!tracker.observe(1, 3, 8).unwrap().matched);
    }

    #[test]
    fn php_diagonal_collision_creates_both_contexts() {
        let mut tracker = php_tracker(2);
        let observation = tracker.observe(2, 3, 7).unwrap();
        assert!(observation.matched);
        assert!(observation.unique_match);
        assert_eq!(observation.contexts, 2);
    }

    #[test]
    fn php_wrong_merge_is_rejected_and_right_merge_is_accepted() {
        let mut tracker = php_tracker(2);
        tracker.observe(2, 3, 7).unwrap();
        assert!(!tracker.observe(-3, -7, 8).unwrap().matched);
        let merge = tracker.observe(-4, -7, 8).unwrap();
        assert!(merge.matched);
        assert_eq!(tracker.summary().best_progress, 1);
    }

    #[test]
    fn php_replays_merge_observed_before_collision() {
        let mut tracker = php_tracker(2);
        assert!(!tracker.observe(-4, -7, 8).unwrap().matched);
        let collision = tracker.observe(3, 2, 7).unwrap();
        assert!(collision.matched);
        assert_eq!(tracker.summary().best_progress, 1);
    }

    #[test]
    fn php_duplicate_collision_is_not_unique() {
        let mut tracker = php_tracker(2);
        assert!(tracker.observe(2, 3, 7).unwrap().unique_match);
        let duplicate = tracker.observe(3, 2, 7).unwrap();
        assert!(duplicate.matched);
        assert!(!duplicate.unique_match);
        assert_eq!(duplicate.contexts, 2);
    }

    #[test]
    fn duplicate_pair_with_different_result_is_invalid_input() {
        let mut tracker = php_tracker(2);
        tracker.observe(2, 3, 7).unwrap();

        let error = tracker.observe(3, 2, 8).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
        assert_eq!(tracker.summary().checks, 1);
        assert_eq!(tracker.observed[&Pair::new(2, 3)].occurrence_count, 1);
    }

    #[test]
    fn php_unrelated_observations_do_not_revisit_existing_contexts() {
        let mut tracker = php_tracker(2);
        assert_eq!(tracker.observe(2, 3, 7).unwrap().contexts, 2);
        let checks_after_collision = php_coordinate_checks(&tracker);

        for offset in 0..500 {
            let observation = tracker
                .observe(10_000 + offset, 20_000 + offset, 30_000 + offset)
                .unwrap();
            assert!(!observation.matched);
        }
        assert_eq!(php_coordinate_checks(&tracker), checks_after_collision);

        let duplicate = tracker.observe(3, 2, 7).unwrap();
        assert_eq!(duplicate.contexts, 2);
        assert_eq!(tracker.summary().stages_completed, 0);
    }

    #[test]
    fn php_duplicate_stress_does_not_amplify_child_replay() {
        const DUPLICATES: usize = 10_000;

        let mut baseline = php_tracker(3);
        let mut stressed = php_tracker(3);
        let first_pair = baseline.suggest().unwrap();
        assert_eq!(stressed.suggest(), Some(first_pair));
        let first_result = 1_000;
        baseline
            .observe(first_pair.0, first_pair.1, first_result)
            .unwrap();
        stressed
            .observe(first_pair.0, first_pair.1, first_result)
            .unwrap();

        let checks_after_unique_collision = php_coordinate_checks(&stressed);
        let contexts_after_unique_collision = stressed
            .strategy
            .contexts_for(Pair::new(first_pair.0, first_pair.1));
        for _ in 0..DUPLICATES {
            let duplicate = stressed
                .observe(first_pair.1, first_pair.0, first_result)
                .unwrap();
            assert!(duplicate.matched);
            assert!(!duplicate.unique_match);
            assert_eq!(duplicate.contexts, contexts_after_unique_collision);
            assert_eq!(duplicate.stages_completed, 0);
        }
        assert_eq!(
            php_coordinate_checks(&stressed),
            checks_after_unique_collision
        );
        assert_eq!(stressed.observed.len(), 1);
        assert_eq!(
            stressed.observed[&Pair::new(first_pair.0, first_pair.1)].occurrence_count,
            DUPLICATES + 1
        );
        let duplicate_summary = stressed.summary();
        assert_eq!(duplicate_summary.checks, DUPLICATES + 1);
        assert_eq!(duplicate_summary.matches, DUPLICATES + 1);
        assert_eq!(duplicate_summary.unique_matches, 1);

        let mut history = vec![first_pair];
        let mut next_result = first_result + 1;
        while baseline.summary().deepest_level == 0 {
            let pair = baseline.suggest().expect("root PHP stage has work");
            assert_eq!(stressed.suggest(), Some(pair));
            baseline.observe(pair.0, pair.1, next_result).unwrap();
            stressed.observe(pair.0, pair.1, next_result).unwrap();
            history.push(pair);
            next_result += 1;
            assert!(history.len() < 100, "root PHP stage should complete");
        }

        assert_eq!(baseline.summary().deepest_level, 1);
        assert_eq!(stressed.summary().deepest_level, 1);
        assert_eq!(stressed.observed.len(), baseline.observed.len());
        assert_eq!(
            php_coordinate_checks(&stressed),
            php_coordinate_checks(&baseline)
        );
        for pair in history {
            let pair = Pair::new(pair.0, pair.1);
            assert_eq!(
                stressed.strategy.contexts_for(pair),
                baseline.strategy.contexts_for(pair)
            );
        }
    }

    #[test]
    fn php_completes_one_coherent_pivot_and_spawns_child() {
        let mut tracker = php_tracker(2);
        tracker.observe(2, 3, 7).unwrap();
        tracker.observe(-4, -7, 8).unwrap();
        tracker.observe(2, 5, 9).unwrap();
        let completion = tracker.observe(-6, -9, 10).unwrap();
        assert!(completion.matched);
        assert_eq!(completion.stages_completed, 1);
        let summary = tracker.summary();
        assert_eq!(summary.stages_completed, 1);
        assert_eq!(summary.deepest_level, 1);
        assert_eq!(summary.best_progress, 2);
    }

    #[test]
    fn php_multiple_stages_and_duplicate_history_remain_stable() {
        let mut tracker = php_tracker(3);
        let mut history = Vec::new();
        while tracker.summary().deepest_level < 2 {
            let pair = tracker.suggest().expect("a non-base stage has work");
            let result = 1_000 + history.len() as i32;
            let observation = tracker.observe(pair.0, pair.1, result).unwrap();
            assert!(observation.matched);
            history.push((pair, result));
            assert!(
                history.len() < 500,
                "suggestions should eventually finish a depth-two coherent path"
            );
        }

        let completed_stages = tracker.summary().stages_completed;
        assert!(completed_stages >= 2);

        let mut contexts = BTreeMap::new();
        for (pair, _) in &history {
            contexts
                .entry(Pair::new(pair.0, pair.1))
                .or_insert_with(|| tracker.strategy.contexts_for(Pair::new(pair.0, pair.1)));
        }
        for (pair, result) in &history {
            let observation = tracker.observe(pair.0, pair.1, *result).unwrap();
            assert!(observation.matched);
            assert!(!observation.unique_match);
            assert_eq!(observation.contexts, contexts[&Pair::new(pair.0, pair.1)]);
            assert_eq!(observation.stages_completed, 0);
        }
        assert_eq!(tracker.summary().stages_completed, completed_stages);
        assert_eq!(tracker.summary().deepest_level, 2);
    }

    #[test]
    fn php_one_hole_is_a_base_case() {
        let mut tracker = php_tracker(1);
        assert_eq!(tracker.suggest(), None);
        assert!(!tracker.observe(1, 2, 3).unwrap().matched);
        assert_eq!(tracker.summary().stages_completed, 0);
    }

    #[test]
    fn php_suggestion_prioritizes_ready_merge_and_is_valid() {
        let mut tracker = php_tracker(2);
        assert_eq!(tracker.suggest(), Some((2, 3)));
        let collision = tracker.observe(2, 3, 7).unwrap();
        assert_eq!(collision.suggestion, Some((2, 3)));
        assert_eq!(tracker.suggest(), Some((-7, -4)));
        let suggested = tracker.suggest().unwrap();
        assert!(
            tracker
                .observe(suggested.0, suggested.1, 8)
                .unwrap()
                .matched
        );
    }

    #[test]
    fn invalid_observation_literals_return_invalid_input() {
        let mut tracker = static_tracker(1, &[[1, 1]]);
        assert_eq!(
            tracker.observe(0, 1, 2).unwrap_err().kind(),
            std::io::ErrorKind::InvalidInput
        );
        assert_eq!(
            tracker.observe(1, 1, -2).unwrap_err().kind(),
            std::io::ErrorKind::InvalidInput
        );
    }

    #[test]
    fn logging_contains_header_dips_suggestion_and_summary() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "sat-playground-guidance-{}-{nonce}.log",
            std::process::id()
        ));
        let mut tracker = GuidanceTracker::new(
            GuidanceSpec::StaticAndDag {
                original_variables: 2,
                operands: vec![[1, 2]],
            },
            Some(path.to_string_lossy().into_owned()),
        )
        .unwrap();
        tracker.observe(2, 1, 5).unwrap();
        tracker.finish().unwrap();

        let contents = fs::read_to_string(&path).unwrap();
        fs::remove_file(path).unwrap();
        assert!(contents.contains("guidance strategy: static_and_dag"));
        assert!(contents.contains("actual=(2, 1)->5"));
        assert!(contents.contains("suggestion_before=Some((1, 2))"));
        assert!(contents.contains("matched=true unique=true contexts=1"));
        assert!(contents.contains(
            "stages_completed_now=1 active_progress=1 best_progress=1 stages_completed_total=1 deepest_level=1"
        ));
        assert!(contents.contains("summary checks=1 matches=1 unique_matches=1"));
    }

    #[test]
    fn parser_accepts_owned_compact_specs() {
        Python::initialize();
        Python::attach(|py| {
            let dictionary = PyDict::new(py);
            dictionary.set_item("schema_version", 2).unwrap();
            dictionary.set_item("kind", "static_and_dag").unwrap();
            dictionary.set_item("original_variables", 3).unwrap();
            dictionary
                .set_item("operands", vec![vec![1, -2], vec![4, 3]])
                .unwrap();
            let spec: GuidanceSpec = dictionary.extract().unwrap();
            assert_eq!(
                spec,
                GuidanceSpec::StaticAndDag {
                    original_variables: 3,
                    operands: vec![[1, -2], [4, 3]],
                }
            );
        });
    }

    #[test]
    fn parser_rejects_bad_version_kind_and_sizes() {
        Python::initialize();
        Python::attach(|py| {
            for (version, kind, holes) in [
                (1, "pigeonhole_cook", 2),
                (2, "unknown", 2),
                (2, "pigeonhole_cook", 0),
            ] {
                let dictionary = PyDict::new(py);
                dictionary.set_item("schema_version", version).unwrap();
                dictionary.set_item("kind", kind).unwrap();
                dictionary.set_item("holes", holes).unwrap();
                let error = dictionary.extract::<GuidanceSpec>().unwrap_err();
                assert!(error.is_instance_of::<pyo3::exceptions::PyValueError>(py));
            }
        });
    }

    #[test]
    fn parser_rejects_booleans_for_integer_fields_and_literals() {
        Python::initialize();
        Python::attach(|py| {
            let boolean_version = PyDict::new(py);
            boolean_version.set_item("schema_version", true).unwrap();
            boolean_version.set_item("kind", "pigeonhole_cook").unwrap();
            boolean_version.set_item("holes", 2).unwrap();

            let boolean_holes = PyDict::new(py);
            boolean_holes.set_item("schema_version", 2).unwrap();
            boolean_holes.set_item("kind", "pigeonhole_cook").unwrap();
            boolean_holes.set_item("holes", true).unwrap();

            let boolean_original_variables = PyDict::new(py);
            boolean_original_variables
                .set_item("schema_version", 2)
                .unwrap();
            boolean_original_variables
                .set_item("kind", "static_and_dag")
                .unwrap();
            boolean_original_variables
                .set_item("original_variables", true)
                .unwrap();
            boolean_original_variables
                .set_item("operands", vec![vec![1, 1]])
                .unwrap();

            let boolean_operand = PyDict::new(py);
            boolean_operand.set_item("schema_version", 2).unwrap();
            boolean_operand.set_item("kind", "static_and_dag").unwrap();
            boolean_operand.set_item("original_variables", 3).unwrap();
            boolean_operand
                .set_item("operands", vec![vec![true, false]])
                .unwrap();

            for dictionary in [
                boolean_version,
                boolean_holes,
                boolean_original_variables,
                boolean_operand,
            ] {
                let error = dictionary.extract::<GuidanceSpec>().unwrap_err();
                assert!(error.is_instance_of::<pyo3::exceptions::PyValueError>(py));
            }
        });
    }

    #[test]
    fn parser_rejects_bad_operands_and_forward_references() {
        Python::initialize();
        Python::attach(|py| {
            for operands in [
                vec![vec![1]],
                vec![vec![1, 0]],
                vec![vec![1, 4]],
                vec![vec![1, 2, 3]],
            ] {
                let dictionary = PyDict::new(py);
                dictionary.set_item("schema_version", 2).unwrap();
                dictionary.set_item("kind", "static_and_dag").unwrap();
                dictionary.set_item("original_variables", 3).unwrap();
                dictionary.set_item("operands", operands).unwrap();
                let error = dictionary.extract::<GuidanceSpec>().unwrap_err();
                assert!(error.is_instance_of::<pyo3::exceptions::PyValueError>(py));
            }
        });
    }
}
