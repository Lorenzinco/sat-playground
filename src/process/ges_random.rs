//! GES over a sequential window starting at a random physical clause slot.
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
        Policy::Random,
        options,
    )
}
