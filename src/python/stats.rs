use crate::formula::clause::Clause;
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
    pub bva_literals: u64,
    #[pyo3(get)]
    pub bve_eliminated_variables: u64,
    #[pyo3(get)]
    pub bve_resolvents: u64,
    #[pyo3(get)]
    pub avg_clause_length: f64,
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
            bva_literals: 0,
            bve_eliminated_variables: 0,
            bve_resolvents: 0,
            avg_clause_length: 0.0,
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
