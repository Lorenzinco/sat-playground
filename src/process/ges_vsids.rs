//! Cursor GES maximizing replacement activity, independently of LBD.
//!
//! Each greedy replacement must be at least as active as both inputs. Final
//! descending activity sequences must improve at their first differing entry;
//! merely dropping a suffix is not an improvement. The source before expansion
//! remains the baseline, and replacements may not grow the clause.
use std::io::Write;

use pyo3::{Python, prelude::PyResult};

use super::{
    ClauseScope,
    ges::{GesOptions, Policy, process_with_policy},
};
use crate::{drat::DratLogger, formula::Formula, history::History};

#[cfg(test)]
pub(crate) fn process<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
    reasoning_levels: Option<&[Option<usize>]>,
) -> PyResult<()> {
    process_with_options(
        formula,
        scope,
        logger,
        signal,
        history,
        reasoning_levels,
        GesOptions::default(),
    )
}

pub(crate) fn process_with_options<W: Write>(
    formula: &mut Formula,
    scope: &ClauseScope,
    logger: &mut Option<DratLogger<W>>,
    signal: Option<(Python<'_>, &mut u64)>,
    history: Option<&mut History>,
    reasoning_levels: Option<&[Option<usize>]>,
    options: GesOptions,
) -> PyResult<()> {
    process_with_policy(
        formula,
        scope,
        logger,
        signal,
        history,
        reasoning_levels,
        Policy::Vsids,
        options,
    )
}
