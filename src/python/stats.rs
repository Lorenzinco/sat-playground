use crate::formula::clause::Clause;
use crate::guidance::GuidanceSummary;
use pyo3::prelude::*;
use std::time::Duration;
use std::time::Instant;

#[pyclass(from_py_object)]
#[derive(Clone, Copy)]
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
    pub minimized_literals: u64,
    #[pyo3(get)]
    pub clauses_kept: u64,
    #[pyo3(get)]
    pub literals_learnt: u64,
    #[pyo3(get)]
    pub extension_literals: u64,
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
    pub ges_literals_removed: u64,
    #[pyo3(get)]
    pub ges_replacement_reason_uses: u64,
    #[pyo3(get)]
    pub ges_replacement_analysis_uses: u64,
    #[pyo3(get)]
    pub ges_replacements_deleted_unused: u64,
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
            minimized_literals: 0,
            clauses_kept: 0,
            literals_learnt: 0,
            extension_literals: 0,
            guidance_checks: 0,
            guidance_matches: 0,
            guidance_unique_matches: 0,
            guidance_stages_completed: 0,
            guidance_deepest_level: 0,
            guidance_best_progress: 0,
            bva_literals: 0,
            bve_eliminated_variables: 0,
            bve_resolvents: 0,
            avg_clause_length: 0.0,
            global_extension_substitution: 0,
            ges_clauses_inspected: 0,
            ges_noop_rewrites: 0,
            ges_rewrites_rejected: 0,
            ges_lbd_improvements: 0,
            ges_vsids_improvements: 0,
            ges_literals_removed: 0,
            ges_replacement_reason_uses: 0,
            ges_replacement_analysis_uses: 0,
            ges_replacements_deleted_unused: 0,
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

    /// Count each successful implication, including each active reason transferred
    /// to a GES replacement. Repeated uses count even after `ges_used` is set.
    pub fn record_ges_reason_use(&mut self, clause: &mut Clause) {
        if clause.ges_generated {
            clause.ges_used = true;
            self.ges_replacement_reason_uses += 1;
        }
    }

    /// Count each source-clause occurrence in the shared conflict-analysis walk
    /// (including the conflict clause), not subsequent minimization/DIP rereads.
    pub fn record_ges_analysis_use(&mut self, clause: &mut Clause) {
        if clause.ges_generated {
            clause.ges_used = true;
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
        let bva_lits_s = format!("{:>40}", self.bva_literals);
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
            ("GES literals removed", self.ges_literals_removed),
            ("GES reason uses", self.ges_replacement_reason_uses),
            ("GES analysis uses", self.ges_replacement_analysis_uses),
            ("GES deleted unused", self.ges_replacements_deleted_unused),
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
                 c | {:<27} | {} |\n\
                 c | {:<27} | {} |\n\
                 {ges_rows}\
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
    fn ges_counters_have_zero_readonly_python_getters_and_display_rows() {
        let fields = [
            ("ges_clauses_inspected", "GES clauses inspected"),
            ("ges_noop_rewrites", "GES noop rewrites"),
            ("ges_rewrites_rejected", "GES rewrites rejected"),
            ("ges_lbd_improvements", "GES LBD improvements"),
            ("ges_vsids_improvements", "GES VSIDS improvements"),
            ("ges_literals_removed", "GES literals removed"),
            ("ges_replacement_reason_uses", "GES reason uses"),
            ("ges_replacement_analysis_uses", "GES analysis uses"),
            ("ges_replacements_deleted_unused", "GES deleted unused"),
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
    fn ges_use_helpers_ignore_original_clauses_and_count_each_transfer() {
        let mut stats = Stats::new();
        let mut clause = Clause::from_literals(vec![Literal::new(1)], 1);
        stats.record_ges_reason_use(&mut clause);
        stats.record_ges_analysis_use(&mut clause);
        assert!(!clause.ges_used);
        assert_eq!(stats.ges_replacement_reason_uses, 0);
        assert_eq!(stats.ges_replacement_analysis_uses, 0);
        clause.ges_generated = true;
        for _ in 0..2 {
            clause.increment_lock_count();
            stats.record_ges_reason_use(&mut clause);
        }
        assert!(clause.ges_used);
        assert_eq!(stats.ges_replacement_reason_uses, 2);
        stats.record_ges_analysis_use(&mut clause);
        assert_eq!(stats.ges_replacement_analysis_uses, 1);
    }
}
