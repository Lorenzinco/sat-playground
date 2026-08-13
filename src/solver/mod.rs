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
use crate::guidance::GuidanceTracker;
use crate::heuristics::Heuristics;
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
    guidance: &mut Option<GuidanceTracker>,
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
                "\r\x1b[2Kc \x1b[31mTime: {}\x1b[0m | \x1b[31mConflicts: {}\x1b[0m | Restarts: {} | \x1b[34mLearnt: {}\x1b[0m | Deleted: {} | Lits: (ext {}, bva {}) | GES: {}",
                time_str,
                stats.conflicts,
                stats.restarts,
                stats.clauses_learnt,
                stats.clauses_deleted,
                stats.extension_literals,
                stats.bva_literals,
                stats.global_extension_substitution,
            );
            io::stdout().flush().ok();

            thread::sleep(Duration::from_millis(1000));
        }

        print!("\r\x1b[2K");
        io::stdout().flush().ok();
    });

    // Refresh the formula-owned activity after preprocessing so auxiliary
    // variables receive meaningful initial scores.
    formula.rebuild_vsids();
    let mut heuristics = match requested_heuristics {
        Heuristics::VSIDS => Heuristics::VSIDS,
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
            guidance,
        ),
    };

    stop.store(true, Ordering::Relaxed);
    let _ = timer.join();

    formula.stats.record_solve_time(solve_start.elapsed());
    formula.stats.stop();

    result
}
