//! Cursor GES maximizing signed literal utility from propagation and conflict use.
//!
//! Each greedy replacement must be at least as useful as both inputs. Final
//! descending utility sequences must improve at their first differing entry;
//! merely dropping a suffix is not an improvement. Branching VSIDS is unchanged.
use std::io::Write;

use pyo3::{Python, prelude::PyResult};

use super::{
    ClauseScope,
    ges::{GesOptions, Policy, process_with_policy},
};
use crate::{drat::DratLogger, formula::Formula, history::History};

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
        Policy::Utility,
        options,
    )
}
