pub mod dpll;
pub mod cdcl;

use std::io::Write;
use std::io;
use std::thread;
use std::time::Duration;
use std::time::Instant;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::heuristics::Heuristics;
use crate::heuristics::vsids::Vsids;
use crate::history::ImplicationPoint;
use crate::preprocess::Preprocess;

use pyo3::prelude::*;
use pyo3::FromPyObject;

pub enum Algorithm {
    DPLL,
    CDCL
}

impl FromPyObject<'_,'_> for Algorithm {
    type Error = PyErr;
    
    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let algo = obj.extract::<String>()?;
        match algo.as_str() {
            "dpll" => Ok(Algorithm::DPLL),
            "cdcl" => Ok(Algorithm::CDCL),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!("Unknown algorithm: {}, allowed values are: dpll, cdcl", algo))),
        }
}
    
}

pub fn solve<'py,W: Write>(formula: &mut Formula, py: Python<'_>, algorithm: Algorithm,implication_point: ImplicationPoint, preprocess: Vec<Preprocess>, heuristics: Heuristics, logger: &mut Option<DratLogger<W>>) -> PyResult<Option<Vec<bool>>> {

    let stop = Arc::new(AtomicBool::new(false));
    let stop_for_thread = Arc::clone(&stop);
    let stats_ptr = &formula.stats as *const _ as usize;

    //override default empty
    let mut heuristics = match heuristics {
        Heuristics::VSIDS(_) => {
            Heuristics::VSIDS(Vsids::new(formula.assignment.len()))
        }
        _ => Heuristics::None,
    };

    formula.preprocess(preprocess);

    let timer = thread::spawn(move || {
        let start = Instant::now();

        while !stop_for_thread.load(Ordering::Relaxed) {
            let elapsed = start.elapsed().as_secs();
            let time_str = if elapsed >= 60 {
                let minutes = elapsed / 60;
                let seconds = elapsed % 60;
                format!(" {}m {}s", minutes, seconds)
            } else {
                format!(" {}s", elapsed)
            };

            // We cast the pointer back to read the struct properties.
            // Technically a data race for printing purposes, but entirely benign.
            let stats = unsafe { &*(stats_ptr as *const crate::python::stats::Stats) };

            print!(
                "\r\x1b[2Kc \x1b[31mTime: {}\x1b[0m | \x1b[31mConflicts: {}\x1b[0m | \x1b[34mLearnt: {}\x1b[0m | Lits: {} | AvgLen: {:.2}",
                time_str,
                stats.conflicts,
                stats.clauses_learnt,
                stats.literals_learnt,
                stats.avg_clause_length
            );
            io::stdout().flush().ok();

            thread::sleep(Duration::from_millis(100));
        }

        print!("\r\x1b[2K");
        io::stdout().flush().ok();
    });


    formula.stats.start();
    let result = match algorithm {
        Algorithm::DPLL => dpll::solve_dpll(py,formula),
        Algorithm::CDCL => cdcl::solve_cdcl(py,formula,implication_point, &mut heuristics, logger)
    };
    
    stop.store(true, Ordering::Relaxed);
    let _ = timer.join();
    
    formula.stats.stop();
    
    result
}