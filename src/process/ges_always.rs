//! Cursor GES that always installs a changed, non-growing LBD reformulation.
//!
//! Unlike the regular LBD objective, this experiment does not require either
//! an intermediate or final LBD improvement. Original clauses stay irredundant,
//! learned clauses (including glue) receive their current dynamic LBD, and
//! extension axioms remain protected by the shared evaluator.
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
        Policy::Always,
        options,
    )
}
