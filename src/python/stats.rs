use pyo3::prelude::*;
use std::time::Instant;
use crate::formula::clause::Clause;

#[pyclass(from_py_object)]
#[derive(Clone,Copy)]
pub struct Stats {
    #[pyo3(get)]
    pub conflicts: u64,
    #[pyo3(get)]
    pub clauses_learnt: u64,
    #[pyo3(get)]
    pub literals_learnt: u64,
    #[pyo3(get)]
    pub avg_clause_length: f64,
    pub time_start: Option<Instant>,
    pub time_stop: Option<Instant>,
}

impl Stats {
    pub fn new() -> Self {
        Self {
            conflicts: 0,
            clauses_learnt: 0,
            literals_learnt: 0,
            avg_clause_length: 0.0,
            time_start: None,
            time_stop: None,
        }
    }
    
    pub fn add_literal(&mut self){
        self.literals_learnt += 1
    }
    
    pub fn add_conflict(&mut self){
        self.conflicts += 1
    }
    
    pub fn add_learnt_clause(&mut self, clause: &Clause){
        self.avg_clause_length = (self.avg_clause_length * self.clauses_learnt as f64 + clause.len() as f64) / (self.clauses_learnt as f64 + 1.0);
        self.clauses_learnt += 1;
    }

    pub fn start(&mut self) {
        self.time_start = Some(Instant::now());
        self.time_stop = None;
    }

    pub fn stop(&mut self) {
        self.time_stop = Some(Instant::now());
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
            let unit = if elapsed > 1000.0*1000.0 {"s"} else if elapsed > 1000.0 {"ms"} else {"ns"};
            match unit {
                "ms" => {elapsed = self.elapsed_millis().unwrap_or(0) as f64},
                "ns" => {},
                "s" => {elapsed = self.elapsed_secs().unwrap_or(0 as f64)},
                _=>{unreachable!()}
            };
            let learnt = self.clauses_learnt;
            let avg_len = self.avg_clause_length;
            let conflicts = self.conflicts;
            let lits = self.literals_learnt;
    
            let elapsed_s = format!("{:>40.2}", elapsed);
            let learnt_s = format!("{:>40}", learnt);
            let avg_len_s = format!("{:>40.2}", avg_len);
            let conflicts_s = format!("{:>40}", conflicts);
            let lits_s = format!("{:>40}",lits);
    
            format!(
                "c +------------------------------------------------------------------------+\n\
                 c | {:^70} |\n\
                 c +------------------------------------------------------------------------+\n\
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
                "Avg clause length",
                avg_len_s,
                "Conflicts",
                format!("{red}{conflicts_s}{reset}"),
                "Learnet lits",
                format!("{blue}{lits_s}{reset}")
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
}