use crate::formula::clause::Clause;
use crate::formula::extension::{ExtensionMap, ExtensionOrigin};
use crate::guidance::GuidanceSummary;
use pyo3::prelude::*;
use std::collections::{BTreeMap, HashSet};
use std::time::Duration;
use std::time::Instant;

#[pyclass(from_py_object)]
#[derive(Clone)]
pub struct Stats {
    #[pyo3(get)]
    pub conflicts: u64,
    #[pyo3(get)]
    pub restarts: u64,
    #[pyo3(get)]
    pub clauses_learnt: u64,
    #[pyo3(get)]
    pub clauses_deleted: u64,
    #[pyo3(get)]
    pub clauses_subsumed: u64,
    #[pyo3(get)]
    pub subsumption_checks: u64,
    #[pyo3(get)]
    pub vivification_passes: u64,
    #[pyo3(get)]
    pub vivification_clauses_tried: u64,
    #[pyo3(get)]
    pub vivification_clauses_strengthened: u64,
    #[pyo3(get)]
    pub vivification_literals_removed: u64,
    #[pyo3(get)]
    pub vivification_propagation_ticks: u64,
    #[pyo3(get)]
    pub vivification_budget_exhaustions: u64,
    #[pyo3(get)]
    pub vivification_units: u64,
    #[pyo3(get)]
    pub minimized_literals: u64,
    #[pyo3(get)]
    pub clauses_kept: u64,
    #[pyo3(get)]
    pub literals_learnt: u64,
    #[pyo3(get)]
    pub extension_literals: u64,
    #[pyo3(get)]
    pub dip_candidates_found: u64,
    #[pyo3(get)]
    pub dip_unit_post_clauses: u64,
    #[pyo3(get)]
    pub dip_glue_post_clauses: u64,
    #[pyo3(get)]
    pub dip_lbd_rejections: u64,
    #[pyo3(get)]
    pub dip_assigned_extension_rejections: u64,
    #[pyo3(get)]
    pub dip_uip_fallbacks: u64,
    #[pyo3(get)]
    pub guidance_checks: u64,
    #[pyo3(get)]
    pub guidance_matches: u64,
    #[pyo3(get)]
    pub guidance_unique_matches: u64,
    #[pyo3(get)]
    pub guidance_stages_completed: u64,
    #[pyo3(get)]
    pub guidance_deepest_level: u64,
    #[pyo3(get)]
    pub guidance_best_progress: u64,
    #[pyo3(get)]
    pub bva_literals: u64,
    #[pyo3(get)]
    pub bva_candidates_attempted: u64,
    #[pyo3(get)]
    pub bva_clause_visits: u64,
    #[pyo3(get)]
    pub bva_clauses_saved: u64,
    #[pyo3(get)]
    pub bva_source_clauses_replaced: u64,
    #[pyo3(get)]
    pub bva_budget_exhaustions: u64,
    #[pyo3(get)]
    pub bva_budget_increases: u64,
    #[pyo3(get)]
    pub bva_budget_decreases: u64,
    #[pyo3(get)]
    pub bva_current_budget: u64,
    #[pyo3(get)]
    pub bva_peak_budget: u64,
    #[pyo3(get)]
    pub bva_binary_and_factors: u64,
    #[pyo3(get)]
    pub bva_non_binary_and_factors: u64,
    #[pyo3(get)]
    pub bva_ite_factors: u64,
    #[pyo3(get)]
    pub bva_xor_factors: u64,
    #[pyo3(get)]
    pub bve_eliminated_variables: u64,
    #[pyo3(get)]
    pub bve_resolvents: u64,
    #[pyo3(get)]
    pub avg_clause_length: f64,
    #[pyo3(get)]
    pub global_extension_substitution: u64,
    #[pyo3(get)]
    pub ges_clauses_inspected: u64,
    #[pyo3(get)]
    pub ges_noop_rewrites: u64,
    #[pyo3(get)]
    pub ges_rewrites_rejected: u64,
    #[pyo3(get)]
    pub ges_lbd_improvements: u64,
    #[pyo3(get)]
    pub ges_vsids_improvements: u64,
    #[pyo3(get)]
    pub ges_utility_improvements: u64,
    #[pyo3(get)]
    pub ges_literals_removed: u64,
    #[pyo3(get)]
    pub ges_literals_added: u64,
    #[pyo3(get)]
    pub ges_binary_clauses_compressed: u64,
    #[pyo3(get)]
    pub ges_clauses_unrolled: u64,
    #[pyo3(get)]
    pub ges_dip_extensions_unrolled: u64,
    #[pyo3(get)]
    pub ges_bva_extensions_unrolled: u64,
    #[pyo3(get)]
    pub ges_other_extensions_unrolled: u64,
    #[pyo3(get)]
    pub ges_unrolled_source_literals: u64,
    #[pyo3(get)]
    pub ges_unrolled_working_literals: u64,
    #[pyo3(get)]
    pub ges_substitutions_after_unrolling: u64,
    #[pyo3(get)]
    pub ges_substitutions_to_dip: u64,
    #[pyo3(get)]
    pub ges_substitutions_to_bva: u64,
    #[pyo3(get)]
    pub ges_substitutions_to_other: u64,
    #[pyo3(get)]
    pub ges_rewrites_after_unrolling: u64,
    #[pyo3(get)]
    pub ges_rerolled_rewrites_after_unrolling: u64,
    #[pyo3(get)]
    pub ges_unrolled_rewrites_rejected: u64,
    #[pyo3(get)]
    pub ges_unrolled_rewrites_restored: u64,
    #[pyo3(get)]
    pub ges_replacements_used: u64,
    #[pyo3(get)]
    pub ges_replacement_reason_uses: u64,
    #[pyo3(get)]
    pub ges_replacement_analysis_uses: u64,
    #[pyo3(get)]
    pub ges_replacements_deleted_unused: u64,
    #[pyo3(get)]
    pub ges_budget_increases: u64,
    #[pyo3(get)]
    pub ges_budget_decreases: u64,
    #[pyo3(get)]
    pub ges_current_budget: u64,
    #[pyo3(get)]
    pub ges_peak_budget: u64,
    #[pyo3(get)]
    pub ges_trail_unique_touches: u64,
    #[pyo3(get)]
    pub ges_trail_clauses_selected: u64,
    #[pyo3(get)]
    pub ges_trail_cursor_selected: u64,
    #[pyo3(get)]
    pub ges_trail_duplicate_skips: u64,
    /// Signed clause literal -> (extension origin, recursive unrolls, greedy choices).
    #[pyo3(get)]
    pub ges_extension_preference: BTreeMap<i32, (String, u64, u64)>,
    #[pyo3(get)]
    pub preference_passes: u64,
    #[pyo3(get)]
    pub preference_candidates: u64,
    #[pyo3(get)]
    pub preference_skipped_dependents: u64,
    #[pyo3(get)]
    pub preference_skipped_assigned: u64,
    #[pyo3(get)]
    pub preference_root_assigned_true: u64,
    #[pyo3(get)]
    pub preference_root_assigned_false: u64,
    #[pyo3(get)]
    pub preference_root_assigned_unique: u64,
    #[pyo3(get)]
    pub preference_root_rebuilds: u64,
    preference_root_seen: HashSet<usize>,
    #[pyo3(get)]
    pub preference_skipped_unsafe: u64,
    #[pyo3(get)]
    pub preference_extensions_retired: u64,
    #[pyo3(get)]
    pub preference_clauses_added: u64,
    #[pyo3(get)]
    pub preference_clauses_removed: u64,
    #[pyo3(get)]
    pub preference_learned_positive_dropped: u64,
    pub learnt_clause_literals_kept: u64,
    pub preprocess_nanos: u128,
    pub solve_nanos: u128,
    pub propagation_nanos: u128,
    pub conflict_analysis_nanos: u128,
    pub minimization_nanos: u128,
    pub learning_nanos: u128,
    pub db_reduction_nanos: u128,
    pub subsumption_nanos: u128,
    pub restart_nanos: u128,
    pub inprocessing_nanos: u128,
    pub time_start: Option<Instant>,
    pub time_stop: Option<Instant>,
}

impl Stats {
    pub fn new() -> Self {
        Self {
            conflicts: 0,
            restarts: 0,
            clauses_learnt: 0,
            clauses_deleted: 0,
            clauses_subsumed: 0,
            subsumption_checks: 0,
            vivification_passes: 0,
            vivification_clauses_tried: 0,
            vivification_clauses_strengthened: 0,
            vivification_literals_removed: 0,
            vivification_propagation_ticks: 0,
            vivification_budget_exhaustions: 0,
            vivification_units: 0,
            minimized_literals: 0,
            clauses_kept: 0,
            literals_learnt: 0,
            extension_literals: 0,
            dip_candidates_found: 0,
            dip_unit_post_clauses: 0,
            dip_glue_post_clauses: 0,
            dip_lbd_rejections: 0,
            dip_assigned_extension_rejections: 0,
            dip_uip_fallbacks: 0,
            guidance_checks: 0,
            guidance_matches: 0,
            guidance_unique_matches: 0,
            guidance_stages_completed: 0,
            guidance_deepest_level: 0,
            guidance_best_progress: 0,
            bva_literals: 0,
            bva_candidates_attempted: 0,
            bva_clause_visits: 0,
            bva_clauses_saved: 0,
            bva_source_clauses_replaced: 0,
            bva_budget_exhaustions: 0,
            bva_budget_increases: 0,
            bva_budget_decreases: 0,
            bva_current_budget: 0,
            bva_peak_budget: 0,
            bva_binary_and_factors: 0,
            bva_non_binary_and_factors: 0,
            bva_ite_factors: 0,
            bva_xor_factors: 0,
            bve_eliminated_variables: 0,
            bve_resolvents: 0,
            avg_clause_length: 0.0,
            global_extension_substitution: 0,
            ges_clauses_inspected: 0,
            ges_noop_rewrites: 0,
            ges_rewrites_rejected: 0,
            ges_lbd_improvements: 0,
            ges_vsids_improvements: 0,
            ges_utility_improvements: 0,
            ges_literals_removed: 0,
            ges_literals_added: 0,
            ges_binary_clauses_compressed: 0,
            ges_clauses_unrolled: 0,
            ges_dip_extensions_unrolled: 0,
            ges_bva_extensions_unrolled: 0,
            ges_other_extensions_unrolled: 0,
            ges_unrolled_source_literals: 0,
            ges_unrolled_working_literals: 0,
            ges_substitutions_after_unrolling: 0,
            ges_substitutions_to_dip: 0,
            ges_substitutions_to_bva: 0,
            ges_substitutions_to_other: 0,
            ges_rewrites_after_unrolling: 0,
            ges_rerolled_rewrites_after_unrolling: 0,
            ges_unrolled_rewrites_rejected: 0,
            ges_unrolled_rewrites_restored: 0,
            ges_replacements_used: 0,
            ges_replacement_reason_uses: 0,
            ges_replacement_analysis_uses: 0,
            ges_replacements_deleted_unused: 0,
            ges_budget_increases: 0,
            ges_budget_decreases: 0,
            ges_current_budget: 0,
            ges_peak_budget: 0,
            ges_trail_unique_touches: 0,
            ges_trail_clauses_selected: 0,
            ges_trail_cursor_selected: 0,
            ges_trail_duplicate_skips: 0,
            ges_extension_preference: BTreeMap::new(),
            preference_passes: 0,
            preference_candidates: 0,
            preference_skipped_dependents: 0,
            preference_skipped_assigned: 0,
            preference_root_assigned_true: 0,
            preference_root_assigned_false: 0,
            preference_root_assigned_unique: 0,
            preference_root_rebuilds: 0,
            preference_root_seen: HashSet::new(),
            preference_skipped_unsafe: 0,
            preference_extensions_retired: 0,
            preference_clauses_added: 0,
            preference_clauses_removed: 0,
            preference_learned_positive_dropped: 0,
            learnt_clause_literals_kept: 0,
            preprocess_nanos: 0,
            solve_nanos: 0,
            propagation_nanos: 0,
            conflict_analysis_nanos: 0,
            minimization_nanos: 0,
            learning_nanos: 0,
            db_reduction_nanos: 0,
            subsumption_nanos: 0,
            restart_nanos: 0,
            inprocessing_nanos: 0,
            time_start: None,
            time_stop: None,
        }
    }

    pub(crate) fn record_preference_root_assignment(&mut self, variable: usize, value: bool) {
        if value {
            self.preference_root_assigned_true += 1;
        } else {
            self.preference_root_assigned_false += 1;
        }
        if self.preference_root_seen.insert(variable) {
            self.preference_root_assigned_unique += 1;
        }
    }

    fn preference_entry(
        &mut self,
        literal: i32,
        extensions: &ExtensionMap,
    ) -> &mut (String, u64, u64) {
        self.ges_extension_preference
            .entry(literal)
            .or_insert_with(|| {
                let origin = match extensions
                    .substitution_origin(&crate::formula::literal::Literal::new(literal))
                {
                    Some(ExtensionOrigin::Dip) => "dip",
                    Some(ExtensionOrigin::Bva) => "bva",
                    _ => "other",
                };
                (origin.to_owned(), 0, 0)
            })
    }

    pub(crate) fn record_ges_extension_unroll(&mut self, literal: i32, extensions: &ExtensionMap) {
        self.preference_entry(literal, extensions).1 += 1;
    }

    pub(crate) fn record_ges_extension_choice(&mut self, literal: i32, extensions: &ExtensionMap) {
        self.preference_entry(literal, extensions).2 += 1;
    }

    /// Count each successful implication, including each active reason transferred
    /// to a GES replacement. Repeated uses count even after `ges_used` is set.
    pub fn record_ges_reason_use(&mut self, clause: &mut Clause) {
        if clause.ges_generated {
            if !clause.ges_used {
                self.ges_replacements_used += 1;
                clause.ges_used = true;
            }
            self.ges_replacement_reason_uses += 1;
        }
    }

    /// Count each source-clause occurrence in the shared conflict-analysis walk
    /// (including the conflict clause), not subsequent minimization/DIP rereads.
    pub fn record_ges_analysis_use(&mut self, clause: &mut Clause) {
        if clause.ges_generated {
            if !clause.ges_used {
                self.ges_replacements_used += 1;
                clause.ges_used = true;
            }
            self.ges_replacement_analysis_uses += 1;
        }
    }

    pub fn add_literal(&mut self) {
        self.add_extension_literal();
    }

    pub fn add_extension_literal(&mut self) {
        self.literals_learnt += 1;
        self.extension_literals += 1;
    }

    pub fn add_bva_literal(&mut self) {
        self.literals_learnt += 1;
        self.bva_literals += 1;
    }

    pub fn record_guidance(&mut self, summary: &GuidanceSummary) {
        self.guidance_checks = summary.checks as u64;
        self.guidance_matches = summary.matches as u64;
        self.guidance_unique_matches = summary.unique_matches as u64;
        self.guidance_stages_completed = summary.stages_completed as u64;
        self.guidance_deepest_level = summary.deepest_level as u64;
        self.guidance_best_progress = summary.best_progress as u64;
    }

    pub fn add_bve_eliminated_variable(&mut self) {
        self.bve_eliminated_variables += 1;
    }

    pub fn add_bve_resolvent(&mut self) {
        self.bve_resolvents += 1;
    }

    pub fn add_conflict(&mut self) {
        self.conflicts += 1
    }

    pub fn add_restart(&mut self) {
        self.restarts += 1;
    }

    pub fn remove_clause(&mut self, clause: &Clause) {
        self.clauses_deleted += 1;

        if clause.lbd > 0 {
            self.clauses_kept = self.clauses_kept.saturating_sub(1);
            self.learnt_clause_literals_kept = self
                .learnt_clause_literals_kept
                .saturating_sub(clause.len() as u64);

            if self.clauses_kept == 0 {
                self.avg_clause_length = 0.0;
            } else {
                self.avg_clause_length =
                    self.learnt_clause_literals_kept as f64 / self.clauses_kept as f64;
            }
        }
    }

    pub fn add_subsumed_clauses(&mut self, count: u64) {
        self.clauses_subsumed += count;
    }

    pub fn add_subsumption_checks(&mut self, count: u64) {
        self.subsumption_checks += count;
    }

    pub fn add_minimized_literals(&mut self, count: u64) {
        self.minimized_literals += count;
    }

    pub fn add_learnt_clause(&mut self, clause: &Clause) {
        self.clauses_learnt += 1;
        self.clauses_kept += 1;

        self.learnt_clause_literals_kept += clause.len() as u64;

        self.avg_clause_length = self.learnt_clause_literals_kept as f64 / self.clauses_kept as f64;
    }

    pub fn record_preprocess_time(&mut self, duration: Duration) {
        self.preprocess_nanos += duration.as_nanos();
    }

    pub fn record_solve_time(&mut self, duration: Duration) {
        self.solve_nanos += duration.as_nanos();
    }

    pub fn record_propagation_time(&mut self, duration: Duration) {
        self.propagation_nanos += duration.as_nanos();
    }

    pub fn record_conflict_analysis_time(&mut self, duration: Duration) {
        self.conflict_analysis_nanos += duration.as_nanos();
    }

    pub fn record_minimization_time(&mut self, duration: Duration) {
        self.minimization_nanos += duration.as_nanos();
    }

    pub fn record_learning_time(&mut self, duration: Duration) {
        self.learning_nanos += duration.as_nanos();
    }

    pub fn record_db_reduction_time(&mut self, duration: Duration) {
        self.db_reduction_nanos += duration.as_nanos();
    }

    pub fn record_subsumption_time(&mut self, duration: Duration) {
        self.subsumption_nanos += duration.as_nanos();
    }

    pub fn record_restart_time(&mut self, duration: Duration) {
        self.restart_nanos += duration.as_nanos();
    }

    pub fn record_inprocessing_time(&mut self, duration: Duration) {
        self.inprocessing_nanos += duration.as_nanos();
    }

    pub fn start(&mut self) {
        self.time_start = Some(Instant::now());
        self.time_stop = None;
    }

    pub fn add_global_substitution(&mut self) {
        self.global_extension_substitution += 1;
    }

    pub fn stop(&mut self) {
        self.time_stop = Some(Instant::now());
    }

    fn format_duration(nanos: u128) -> String {
        if nanos >= 1_000_000_000 {
            format!("{:.3}s", nanos as f64 / 1_000_000_000.0)
        } else if nanos >= 1_000_000 {
            format!("{:.3}ms", nanos as f64 / 1_000_000.0)
        } else if nanos >= 1_000 {
            format!("{:.3}µs", nanos as f64 / 1_000.0)
        } else {
            format!("{}ns", nanos)
        }
    }

    fn format_duration_with_percent(nanos: u128, total_nanos: u128) -> String {
        let percent = if total_nanos == 0 {
            0.0
        } else {
            nanos as f64 * 100.0 / total_nanos as f64
        };

        format!("{} ({:.2}%)", Self::format_duration(nanos), percent)
    }
}

#[pymethods]
impl Stats {
    #[new]
    pub fn py_new() -> Self {
        Self::new()
    }

    #[getter]
    pub fn preference(&self) -> BTreeMap<i32, (String, u64, u64)> {
        self.ges_extension_preference.clone()
    }

    pub fn __str__(&self) -> String {
        let red = "\x1b[31m";
        let blue = "\x1b[34m";
        let reset = "\x1b[0m";

        let mut elapsed: f64 = self.elapsed_nanos().unwrap_or(0) as f64;
        let unit = if elapsed > 1000.0 * 1000.0 {
            "s"
        } else if elapsed > 1000.0 {
            "ms"
        } else {
            "ns"
        };
        match unit {
            "ms" => elapsed = self.elapsed_millis().unwrap_or(0) as f64,
            "ns" => {}
            "s" => elapsed = self.elapsed_secs().unwrap_or(0.0),
            _ => unreachable!(),
        };

        let total_nanos = self.elapsed_nanos().unwrap_or(0);

        let elapsed_s = format!("{:>40.2}", elapsed);
        let learnt_s = format!("{:>40}", self.clauses_learnt);
        let deleted_s = format!("{:>40}", self.clauses_deleted);
        let subsumed_s = format!("{:>40}", self.clauses_subsumed);
        let subsumption_checks_s = format!("{:>40}", self.subsumption_checks);
        let minimized_s = format!("{:>40}", self.minimized_literals);
        let kept_s = format!("{:>40}", self.clauses_kept);
        let avg_len_s = format!("{:>40.2}", self.avg_clause_length);
        let conflicts_s = format!("{:>40}", self.conflicts);
        let restarts_s = format!("{:>40}", self.restarts);
        let lits_s = format!("{:>40}", self.literals_learnt);
        let ext_lits_s = format!("{:>40}", self.extension_literals);
        let guidance_hits_s = format!(
            "{:>40}",
            format!(
                "{}/{} ({} unique)",
                self.guidance_matches, self.guidance_checks, self.guidance_unique_matches
            )
        );
        let guidance_stages_s = format!(
            "{:>40}",
            format!(
                "{} (depth {})",
                self.guidance_stages_completed, self.guidance_deepest_level
            )
        );
        let guidance_progress_s = format!("{:>40}", self.guidance_best_progress);
        let dip_rows = [
            ("DIP candidates found", self.dip_candidates_found),
            ("DIP unit post clauses", self.dip_unit_post_clauses),
            ("DIP glue post clauses", self.dip_glue_post_clauses),
            ("DIP LBD rejections", self.dip_lbd_rejections),
            (
                "DIP assigned ext rejects",
                self.dip_assigned_extension_rejections,
            ),
            ("DIP UIP fallbacks", self.dip_uip_fallbacks),
        ]
        .into_iter()
        .map(|(label, value)| format!("c | {label:<27} | {value:>40} |\n"))
        .collect::<String>();
        let vivification_rows = [
            ("Vivification passes", self.vivification_passes),
            (
                "Vivification clauses tried",
                self.vivification_clauses_tried,
            ),
            (
                "Vivification strengthened",
                self.vivification_clauses_strengthened,
            ),
            (
                "Vivification lits removed",
                self.vivification_literals_removed,
            ),
            (
                "Vivification prop ticks",
                self.vivification_propagation_ticks,
            ),
            (
                "Vivification budget exhaust",
                self.vivification_budget_exhaustions,
            ),
            ("Vivification units", self.vivification_units),
        ]
        .into_iter()
        .map(|(label, value)| format!("c | {label:<27} | {value:>40} |\n"))
        .collect::<String>();
        let bva_lits_s = format!("{:>40}", self.bva_literals);
        let bva_rows = [
            ("BVA candidates attempted", self.bva_candidates_attempted),
            ("BVA clause visits", self.bva_clause_visits),
            ("BVA clauses saved", self.bva_clauses_saved),
            ("BVA sources replaced", self.bva_source_clauses_replaced),
            ("BVA budget exhaustions", self.bva_budget_exhaustions),
            ("BVA budget increases", self.bva_budget_increases),
            ("BVA budget decreases", self.bva_budget_decreases),
            ("BVA current budget", self.bva_current_budget),
            ("BVA peak budget", self.bva_peak_budget),
            ("BVA binary AND factors", self.bva_binary_and_factors),
            (
                "BVA non-binary AND factors",
                self.bva_non_binary_and_factors,
            ),
            ("BVA ITE factors", self.bva_ite_factors),
            ("BVA XOR factors", self.bva_xor_factors),
        ]
        .into_iter()
        .map(|(label, value)| format!("c | {label:<27} | {value:>40} |\n"))
        .collect::<String>();
        let bve_vars_s = format!("{:>40}", self.bve_eliminated_variables);
        let bve_resolvents_s = format!("{:>40}", self.bve_resolvents);
        let preprocess_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.preprocess_nanos, total_nanos)
        );
        let solve_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.solve_nanos, total_nanos)
        );
        let propagation_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.propagation_nanos, total_nanos)
        );
        let analysis_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.conflict_analysis_nanos, total_nanos)
        );
        let minimization_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.minimization_nanos, total_nanos)
        );
        let learning_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.learning_nanos, total_nanos)
        );
        let db_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.db_reduction_nanos, total_nanos)
        );
        let subsumption_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.subsumption_nanos, total_nanos)
        );
        let restart_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.restart_nanos, total_nanos)
        );
        let inprocessing_s = format!(
            "{:>40}",
            Self::format_duration_with_percent(self.inprocessing_nanos, total_nanos)
        );

        let global_extension_substitution_s = format!("{:>40}", self.global_extension_substitution);
        let ges_rows = [
            ("GES clauses inspected", self.ges_clauses_inspected),
            ("GES noop rewrites", self.ges_noop_rewrites),
            ("GES rewrites rejected", self.ges_rewrites_rejected),
            ("GES LBD improvements", self.ges_lbd_improvements),
            ("GES VSIDS improvements", self.ges_vsids_improvements),
            ("GES utility improvements", self.ges_utility_improvements),
            ("GES literals removed", self.ges_literals_removed),
            ("GES literals added", self.ges_literals_added),
            ("GES binary compressed", self.ges_binary_clauses_compressed),
            ("GES clauses unrolled", self.ges_clauses_unrolled),
            (
                "GES DIP extensions unrolled",
                self.ges_dip_extensions_unrolled,
            ),
            (
                "GES BVA extensions unrolled",
                self.ges_bva_extensions_unrolled,
            ),
            ("GES other ext unrolled", self.ges_other_extensions_unrolled),
            (
                "GES unrolled source lits",
                self.ges_unrolled_source_literals,
            ),
            (
                "GES unrolled working lits",
                self.ges_unrolled_working_literals,
            ),
            (
                "GES post-unroll subs",
                self.ges_substitutions_after_unrolling,
            ),
            ("GES substitutions to DIP", self.ges_substitutions_to_dip),
            ("GES substitutions to BVA", self.ges_substitutions_to_bva),
            (
                "GES substitutions to other",
                self.ges_substitutions_to_other,
            ),
            (
                "GES rewrites after unroll",
                self.ges_rewrites_after_unrolling,
            ),
            (
                "GES rerolled rewrites",
                self.ges_rerolled_rewrites_after_unrolling,
            ),
            ("GES unrolled rejected", self.ges_unrolled_rewrites_rejected),
            ("GES unrolled restored", self.ges_unrolled_rewrites_restored),
            ("GES replacements used", self.ges_replacements_used),
            ("GES reason uses", self.ges_replacement_reason_uses),
            ("GES analysis uses", self.ges_replacement_analysis_uses),
            ("GES deleted unused", self.ges_replacements_deleted_unused),
            ("GES budget increases", self.ges_budget_increases),
            ("GES budget decreases", self.ges_budget_decreases),
            ("GES current budget", self.ges_current_budget),
            ("GES peak budget", self.ges_peak_budget),
            ("GES trail unique touches", self.ges_trail_unique_touches),
            (
                "GES trail clauses selected",
                self.ges_trail_clauses_selected,
            ),
            ("GES trail cursor selected", self.ges_trail_cursor_selected),
            ("GES trail duplicate skips", self.ges_trail_duplicate_skips),
        ]
        .into_iter()
        .map(|(label, value)| format!("c | {label:<27} | {value:>40} |\n"))
        .collect::<String>();
        let preference_rows = [
            ("Preference passes", self.preference_passes),
            ("Preference candidates", self.preference_candidates),
            (
                "Preference skipped dependent",
                self.preference_skipped_dependents,
            ),
            (
                "Preference skipped assigned",
                self.preference_skipped_assigned,
            ),
            (
                "Preference skipped assigned",
                self.preference_skipped_assigned,
            ),
            (
                "Preference root true checks",
                self.preference_root_assigned_true,
            ),
            (
                "Preference root false checks",
                self.preference_root_assigned_false,
            ),
            (
                "Preference root unique",
                self.preference_root_assigned_unique,
            ),
            ("Preference root rebuilds", self.preference_root_rebuilds),
            (
                "Preference extensions retired",
                self.preference_extensions_retired,
            ),
            ("Preference clauses added", self.preference_clauses_added),
            (
                "Preference clauses removed",
                self.preference_clauses_removed,
            ),
            (
                "Preference learned + dropped",
                self.preference_learned_positive_dropped,
            ),
        ]
        .into_iter()
        .map(|(label, value)| format!("c | {label:<27} | {value:>40} |\n"))
        .collect::<String>();

        format!(
            "c +------------------------------------------------------------------------+\n\
                 c | {:^70} |\n\
                 c +------------------------------------------------------------------------+\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 {dip_rows}\
                 {vivification_rows}\
                 {bva_rows}\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 {ges_rows}\
                 {preference_rows}\
                 c +------------------------------------------------------------------------+\n\
                 c | {:^70} |\n\
                 c +------------------------------------------------------------------------+\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 c +------------------------------------------------------------------------+",
            "Stats",
            format!("Elapsed ({unit})"),
            format!("{red}{elapsed_s}{reset}"),
            "Clauses learnt",
            format!("{blue}{learnt_s}{reset}"),
            "Clauses deleted",
            format!("{red}{deleted_s}{reset}"),
            "Clauses subsumed",
            format!("{red}{subsumed_s}{reset}"),
            "Subsumption checks",
            subsumption_checks_s,
            "Minimized literals",
            format!("{blue}{minimized_s}{reset}"),
            "Clauses kept",
            kept_s,
            "Avg clause length",
            avg_len_s,
            "Conflicts",
            format!("{red}{conflicts_s}{reset}"),
            "Restarts",
            format!("{red}{restarts_s}{reset}"),
            "Added literals total",
            format!("{blue}{lits_s}{reset}"),
            "Extension literals",
            format!("{blue}{ext_lits_s}{reset}"),
            "Global extension substitutions",
            format!("{blue}{global_extension_substitution_s}{reset}"),
            "Guidance matches/checks",
            guidance_hits_s,
            "Guidance stages/depth",
            guidance_stages_s,
            "Guidance best progress",
            guidance_progress_s,
            "BVA literals",
            format!("{blue}{bva_lits_s}{reset}"),
            "BVE eliminated vars",
            format!("{blue}{bve_vars_s}{reset}"),
            "BVE resolvents",
            bve_resolvents_s,
            "Runtime breakdown",
            "Preprocessing",
            preprocess_s,
            "Solving",
            format!("{red}{solve_s}{reset}"),
            "Propagation",
            propagation_s,
            "Conflict analysis",
            analysis_s,
            "Clause minimization",
            minimization_s,
            "Clause learning",
            learning_s,
            "DB reduction",
            db_s,
            "Subsumption",
            subsumption_s,
            "Restarts",
            restart_s,
            "Inprocessing",
            inprocessing_s,
        )
    }

    pub fn elapsed_secs(&self) -> Option<f64> {
        match (self.time_start, self.time_stop) {
            (Some(start), Some(stop)) => Some((stop - start).as_secs_f64()),
            (Some(start), None) => Some(start.elapsed().as_secs_f64()),
            _ => None,
        }
    }

    pub fn elapsed_millis(&self) -> Option<u128> {
        match (self.time_start, self.time_stop) {
            (Some(start), Some(stop)) => Some((stop - start).as_millis()),
            (Some(start), None) => Some(start.elapsed().as_millis()),
            _ => None,
        }
    }

    pub fn elapsed_nanos(&self) -> Option<u128> {
        match (self.time_start, self.time_stop) {
            (Some(start), Some(stop)) => Some((stop - start).as_nanos()),
            (Some(start), None) => Some(start.elapsed().as_nanos()),
            _ => None,
        }
    }

    pub fn preprocessing_millis(&self) -> f64 {
        self.preprocess_nanos as f64 / 1_000_000.0
    }

    pub fn solving_millis(&self) -> f64 {
        self.solve_nanos as f64 / 1_000_000.0
    }

    pub fn propagation_millis(&self) -> f64 {
        self.propagation_nanos as f64 / 1_000_000.0
    }

    pub fn conflict_analysis_millis(&self) -> f64 {
        self.conflict_analysis_nanos as f64 / 1_000_000.0
    }

    pub fn clause_minimization_millis(&self) -> f64 {
        self.minimization_nanos as f64 / 1_000_000.0
    }

    pub fn clause_learning_millis(&self) -> f64 {
        self.learning_nanos as f64 / 1_000_000.0
    }

    pub fn db_reduction_millis(&self) -> f64 {
        self.db_reduction_nanos as f64 / 1_000_000.0
    }

    pub fn subsumption_millis(&self) -> f64 {
        self.subsumption_nanos as f64 / 1_000_000.0
    }

    pub fn restart_millis(&self) -> f64 {
        self.restart_nanos as f64 / 1_000_000.0
    }

    pub fn inprocessing_millis(&self) -> f64 {
        self.inprocessing_nanos as f64 / 1_000_000.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::literal::Literal;

    #[test]
    fn dip_counters_have_zero_readonly_python_getters_and_display_rows() {
        let fields = [
            ("dip_candidates_found", "DIP candidates found"),
            ("dip_unit_post_clauses", "DIP unit post clauses"),
            ("dip_glue_post_clauses", "DIP glue post clauses"),
            ("dip_lbd_rejections", "DIP LBD rejections"),
            (
                "dip_assigned_extension_rejections",
                "DIP assigned ext rejects",
            ),
            ("dip_uip_fallbacks", "DIP UIP fallbacks"),
        ];
        Python::initialize();
        Python::attach(|py| {
            let stats = Py::new(py, Stats::new()).unwrap();
            let bound = stats.bind(py);
            let display = stats.borrow(py).__str__();
            for (field, label) in fields {
                assert_eq!(bound.getattr(field).unwrap().extract::<u64>().unwrap(), 0);
                assert!(bound.setattr(field, 1).is_err());
                assert!(display.contains(label));
                assert!(include_str!("../../tests/run.py").contains(field));
                assert!(include_str!("../../clsat/clsat.pyi").contains(field));
            }
        });
    }

    #[test]
    fn bva_counters_have_zero_readonly_python_getters_and_display_rows() {
        let fields = [
            ("bva_candidates_attempted", "BVA candidates attempted"),
            ("bva_clause_visits", "BVA clause visits"),
            ("bva_clauses_saved", "BVA clauses saved"),
            ("bva_source_clauses_replaced", "BVA sources replaced"),
            ("bva_budget_exhaustions", "BVA budget exhaustions"),
            ("bva_budget_increases", "BVA budget increases"),
            ("bva_budget_decreases", "BVA budget decreases"),
            ("bva_current_budget", "BVA current budget"),
            ("bva_peak_budget", "BVA peak budget"),
            ("bva_binary_and_factors", "BVA binary AND factors"),
            ("bva_non_binary_and_factors", "BVA non-binary AND factors"),
            ("bva_ite_factors", "BVA ITE factors"),
            ("bva_xor_factors", "BVA XOR factors"),
        ];
        Python::initialize();
        Python::attach(|py| {
            let stats = Py::new(py, Stats::new()).unwrap();
            let bound = stats.bind(py);
            let display = stats.borrow(py).__str__();
            for (field, label) in fields {
                assert_eq!(bound.getattr(field).unwrap().extract::<u64>().unwrap(), 0);
                assert!(bound.setattr(field, 1).is_err());
                assert!(display.contains(label));
                assert!(include_str!("../../tests/run.py").contains(field));
                assert!(include_str!("../../clsat/clsat.pyi").contains(field));
            }
        });
    }

    #[test]
    fn ges_counters_have_zero_readonly_python_getters_and_display_rows() {
        let fields = [
            ("ges_clauses_inspected", "GES clauses inspected"),
            ("ges_noop_rewrites", "GES noop rewrites"),
            ("ges_rewrites_rejected", "GES rewrites rejected"),
            ("ges_lbd_improvements", "GES LBD improvements"),
            ("ges_vsids_improvements", "GES VSIDS improvements"),
            ("ges_utility_improvements", "GES utility improvements"),
            ("ges_literals_removed", "GES literals removed"),
            ("ges_literals_added", "GES literals added"),
            ("ges_binary_clauses_compressed", "GES binary compressed"),
            ("ges_clauses_unrolled", "GES clauses unrolled"),
            ("ges_dip_extensions_unrolled", "GES DIP extensions unrolled"),
            ("ges_bva_extensions_unrolled", "GES BVA extensions unrolled"),
            ("ges_other_extensions_unrolled", "GES other ext unrolled"),
            ("ges_unrolled_source_literals", "GES unrolled source lits"),
            ("ges_unrolled_working_literals", "GES unrolled working lits"),
            ("ges_substitutions_after_unrolling", "GES post-unroll subs"),
            ("ges_substitutions_to_dip", "GES substitutions to DIP"),
            ("ges_substitutions_to_bva", "GES substitutions to BVA"),
            ("ges_substitutions_to_other", "GES substitutions to other"),
            ("ges_rewrites_after_unrolling", "GES rewrites after unroll"),
            (
                "ges_rerolled_rewrites_after_unrolling",
                "GES rerolled rewrites",
            ),
            ("ges_unrolled_rewrites_rejected", "GES unrolled rejected"),
            ("ges_unrolled_rewrites_restored", "GES unrolled restored"),
            ("ges_replacements_used", "GES replacements used"),
            ("ges_replacement_reason_uses", "GES reason uses"),
            ("ges_replacement_analysis_uses", "GES analysis uses"),
            ("ges_replacements_deleted_unused", "GES deleted unused"),
            ("ges_budget_increases", "GES budget increases"),
            ("ges_budget_decreases", "GES budget decreases"),
            ("ges_current_budget", "GES current budget"),
            ("ges_peak_budget", "GES peak budget"),
            ("ges_trail_unique_touches", "GES trail unique touches"),
            ("ges_trail_clauses_selected", "GES trail clauses selected"),
            ("ges_trail_cursor_selected", "GES trail cursor selected"),
            ("ges_trail_duplicate_skips", "GES trail duplicate skips"),
        ];
        Python::initialize();
        Python::attach(|py| {
            let stats = Py::new(py, Stats::new()).unwrap();
            let bound = stats.bind(py);
            let display = stats.borrow(py).__str__();
            for (field, label) in fields {
                assert_eq!(bound.getattr(field).unwrap().extract::<u64>().unwrap(), 0);
                assert!(bound.setattr(field, 1).is_err());
                assert!(display.contains(label));
                assert!(include_str!("../../tests/run.py").contains(field));
                assert!(include_str!("../../clsat/clsat.pyi").contains(field));
            }
            stats.borrow_mut(py).ges_replacement_reason_uses = u64::MAX;
            assert_eq!(
                bound
                    .getattr("ges_replacement_reason_uses")
                    .unwrap()
                    .extract::<u64>()
                    .unwrap(),
                u64::MAX
            );
        });
    }

    #[test]
    fn extension_preference_is_available_to_python_but_not_in_default_display() {
        Python::initialize();
        Python::attach(|py| {
            let mut stats = Stats::new();
            let mut extensions = ExtensionMap::new();
            extensions.add_substitution_with_origin(
                &crate::formula::literal::Literal::new(1),
                &crate::formula::literal::Literal::new(2),
                &crate::formula::literal::Literal::new(3),
                ExtensionOrigin::Bva,
            );
            stats.record_ges_extension_unroll(-3, &extensions);
            stats.record_ges_extension_choice(-3, &extensions);
            stats.record_ges_extension_choice(-3, &extensions);
            let display = stats.__str__();
            let bound = Py::new(py, stats).unwrap();
            let counts: BTreeMap<i32, (String, u64, u64)> = bound
                .bind(py)
                .getattr("ges_extension_preference")
                .unwrap()
                .extract()
                .unwrap();
            assert_eq!(counts.get(&-3), Some(&("bva".to_owned(), 1, 2)));
            let preference: BTreeMap<i32, (String, u64, u64)> = bound
                .bind(py)
                .getattr("preference")
                .unwrap()
                .extract()
                .unwrap();
            assert_eq!(preference, counts);
            assert!(!display.contains("GES ext -3 (bva)"));
        });
    }

    #[test]
    fn ges_use_helpers_ignore_original_clauses_and_count_each_transfer() {
        let mut stats = Stats::new();
        let mut clause = Clause::from_literals(vec![Literal::new(1)], 1);
        stats.record_ges_reason_use(&mut clause);
        stats.record_ges_analysis_use(&mut clause);
        assert!(!clause.ges_used);
        assert_eq!(stats.ges_replacements_used, 0);
        assert_eq!(stats.ges_replacement_reason_uses, 0);
        assert_eq!(stats.ges_replacement_analysis_uses, 0);
        clause.ges_generated = true;
        for _ in 0..2 {
            clause.increment_lock_count();
            stats.record_ges_reason_use(&mut clause);
        }
        assert!(clause.ges_used);
        assert_eq!(stats.ges_replacements_used, 1);
        assert_eq!(stats.ges_replacement_reason_uses, 2);
        stats.record_ges_analysis_use(&mut clause);
        assert_eq!(stats.ges_replacements_used, 1);
        assert_eq!(stats.ges_replacement_analysis_uses, 1);
    }
}
