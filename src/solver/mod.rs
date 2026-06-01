pub mod cdcl;
pub mod dpll;

use std::io;
use std::io::Write;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::thread;
use std::time::Duration;
use std::time::Instant;

use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::heuristics::Heuristics;
use crate::heuristics::vsids::Vsids;
use crate::history::ImplicationPoint;
use crate::process::Process;

use pyo3::FromPyObject;
use pyo3::prelude::*;

pub enum Algorithm {
    DPLL,
    CDCL,
}

impl FromPyObject<'_, '_> for Algorithm {
    type Error = PyErr;

    fn extract(obj: Borrowed<'_, '_, PyAny>) -> Result<Self, Self::Error> {
        let algo = obj.extract::<String>()?;
        match algo.as_str() {
            "dpll" => Ok(Algorithm::DPLL),
            "cdcl" => Ok(Algorithm::CDCL),
            _ => Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(format!(
                "Unknown algorithm: {}, allowed values are: dpll, cdcl",
                algo
            ))),
        }
    }
}

pub fn solve<'py, W: Write>(
    formula: &mut Formula,
    py: Python<'_>,
    algorithm: Algorithm,
    implication_point: ImplicationPoint,
    preprocess: Vec<Process>,
    inprocessing: Vec<Process>,
    heuristics: Heuristics,
    logger: &mut Option<DratLogger<W>>,
) -> PyResult<Option<Vec<bool>>> {
    let stop = Arc::new(AtomicBool::new(false));
    let stop_for_thread = Arc::clone(&stop);
    let stats_ptr = &formula.stats as *const _ as usize;

    let requested_heuristics = heuristics;

    formula.stats.start();

    let preprocess_start = Instant::now();
    let mut preprocessing_steps = 0;
    formula.process(
        preprocess.clone(),
        logger,
        Some((py, &mut preprocessing_steps)),
        true,
        None,
    )?;
    formula
        .stats
        .record_preprocess_time(preprocess_start.elapsed());

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
                "\r\x1b[2Kc \x1b[31mTime: {}\x1b[0m | \x1b[31mConflicts: {}\x1b[0m | Restarts: {} | \x1b[34mLearnt: {}\x1b[0m | Min: {} | Deleted: {} | Subsumed: {} | Kept: {} | Lits: {} (ext {}, bva {}) | BVE: {}/{} | AvgLen: {:.2}",
                time_str,
                stats.conflicts,
                stats.restarts,
                stats.clauses_learnt,
                stats.minimized_literals,
                stats.clauses_deleted,
                stats.clauses_subsumed,
                stats.clauses_kept,
                stats.literals_learnt,
                stats.extension_literals,
                stats.bva_literals,
                stats.bve_eliminated_variables,
                stats.bve_resolvents,
                stats.avg_clause_length
            );
            io::stdout().flush().ok();

            thread::sleep(Duration::from_millis(100));
        }

        print!("\r\x1b[2K");
        io::stdout().flush().ok();
    });

    // Build branching heuristics after preprocessing so BVA/BVE auxiliary variables
    // receive meaningful initial activity instead of being appended with score 0.
    let mut heuristics = match requested_heuristics {
        Heuristics::VSIDS(_) => Heuristics::VSIDS(Vsids::from_formula(formula)),
        _ => Heuristics::None,
    };

    let solve_start = Instant::now();
    let result = match algorithm {
        Algorithm::DPLL => dpll::solve_dpll(py, formula),
        Algorithm::CDCL => cdcl::solve_cdcl(
            py,
            formula,
            implication_point,
            &mut heuristics,
            logger,
            inprocessing,
        ),
    };

    stop.store(true, Ordering::Relaxed);
    let _ = timer.join();

    formula.stats.record_solve_time(solve_start.elapsed());
    formula.stats.stop();

    result
}
