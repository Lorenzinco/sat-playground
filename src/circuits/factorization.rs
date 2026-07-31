use crate::circuits::and_gate::AndGate;
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::literal::Literal;
use crate::process::ProcessBudget;
use crate::python::signal_checker;
use pyo3::Python;
use pyo3::prelude::PyResult;
use std::io::Write;

// CaDiCaL-FX's default factor bound requires a reduction of at least one clause.
pub(crate) const FACTOR_BOUND: usize = 1;
pub(crate) const MAX_FACTOR_CLAUSE_SIZE: usize = 20;

pub(crate) enum BudgetResult<T> {
    Complete(T),
    Exhausted,
}

pub(crate) enum Factorization {
    And(AndGate),
    Gate(Gate),
}

impl Factorization {
    pub(crate) fn select(and_gate: Option<AndGate>, gate: Option<Gate>) -> Option<Self> {
        match (and_gate, gate) {
            (Some(and_gate), Some(gate)) => {
                if gate.clause_saving() >= and_gate.clause_saving() {
                    Some(Self::Gate(gate))
                } else {
                    Some(Self::And(and_gate))
                }
            }
            (Some(and_gate), None) => Some(Self::And(and_gate)),
            (None, Some(gate)) => Some(Self::Gate(gate)),
            (None, None) => None,
        }
    }

    pub(crate) fn apply<W: Write>(
        self,
        formula: &mut Formula,
        logger: &mut Option<DratLogger<W>>,
        pending_deleted: &mut [bool],
        deletion_indices: &mut Vec<usize>,
    ) {
        match self {
            Self::And(and_gate) => {
                and_gate.apply(formula, logger, pending_deleted, deletion_indices)
            }
            Self::Gate(gate) => gate.apply(formula, logger, pending_deleted, deletion_indices),
        }
    }
}

pub(crate) fn continue_search(
    budget: &ProcessBudget,
    signal: &mut Option<(Python<'_>, &mut u64)>,
) -> PyResult<bool> {
    if budget.exhausted() {
        return Ok(false);
    }
    if let Some((py, steps)) = signal.as_mut() {
        signal_checker(*py, *steps)?;
    }
    Ok(true)
}

/*pub(crate) fn live_factor_clause(
    formula: &Formula,
    clause_idx: usize,
    initial_clause_limit: usize,
    pending_deleted: &[bool],
) -> bool {
    clause_idx < initial_clause_limit
        && !formula.is_clause_garbage(clause_idx)
        && !pending_deleted[clause_idx]
        && factor_eligible_clause(formula.get_clause_at_idx(clause_idx))
}*/

pub(crate) fn factor_eligible_clause(clause: &Clause) -> bool {
    clause.lock_count() == 0
        && (2..=MAX_FACTOR_CLAUSE_SIZE).contains(&clause.len())
        && (clause.lbd() != 0 || clause.is_bva_generated())
}

pub(crate) fn generated_clause(literals: Vec<Literal>) -> Clause {
    let mut clause = Clause::from_literals(literals, 0);
    clause.mark_bva_generated();
    clause
}

pub(crate) fn claim_clause(
    clause_idx: usize,
    pending_deleted: &mut [bool],
    deletion_indices: &mut Vec<usize>,
) {
    if !pending_deleted[clause_idx] {
        pending_deleted[clause_idx] = true;
        deletion_indices.push(clause_idx);
    }
}

pub(crate) fn literal_tie_key(literal: i32) -> (u32, bool) {
    (literal.unsigned_abs(), literal.is_negative())
}

pub(crate) fn is_tautological(sorted_clause: &[i32]) -> bool {
    sorted_clause
        .iter()
        .any(|&literal| sorted_clause.binary_search(&-literal).is_ok())
}

// Explicit FNV-1a-style hashing keeps scheduling and grouping deterministic.
// Hash equality is only a lookup hint; callers also compare complete vectors.
pub(crate) fn stable_signature_hash(literals: &[i32]) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    hash ^= literals.len() as u64;
    hash = hash.wrapping_mul(0x100000001b3);
    for &literal in literals {
        hash ^= literal as u32 as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signature_hash_is_deterministic_and_order_sensitive() {
        assert_eq!(
            stable_signature_hash(&[1, -2, 3]),
            stable_signature_hash(&[1, -2, 3])
        );
        assert_ne!(
            stable_signature_hash(&[1, -2, 3]),
            stable_signature_hash(&[3, -2, 1])
        );
    }

    #[test]
    fn generated_clauses_are_marked_as_permanent_bva_clauses() {
        let clause = generated_clause(vec![Literal::new(1), Literal::new(-2)]);
        assert_eq!(clause.lbd(), 0);
        assert!(clause.is_bva_generated());
    }

    #[test]
    fn claiming_a_clause_is_idempotent() {
        let mut pending = vec![false; 3];
        let mut deletion_indices = Vec::new();
        claim_clause(1, &mut pending, &mut deletion_indices);
        claim_clause(1, &mut pending, &mut deletion_indices);
        assert_eq!(deletion_indices, vec![1]);
    }
}
