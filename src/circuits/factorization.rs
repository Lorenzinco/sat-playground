use crate::circuits::and_gate::AndGate;
use crate::circuits::gate::Gate;
use crate::drat::DratLogger;
use crate::formula::Formula;
use crate::formula::clause::Clause;
use crate::formula::clause::CreationType;
use crate::formula::literal::Literal;
use std::io::Write;

// CaDiCaL-FX's default factor bound requires a reduction of at least one clause.
// Gate factoring makes the paper's targeted exception for clause-neutral XORs.
pub(crate) const FACTOR_BOUND: usize = 1;
pub(crate) const MAX_FACTOR_CLAUSE_SIZE: usize = 20;

pub(crate) struct BvaBudget {
    limit: usize,
    visits: usize,
}

impl BvaBudget {
    pub(crate) fn new(limit: usize) -> Self {
        Self { limit, visits: 0 }
    }

    pub(crate) fn visit_clause(&mut self) -> bool {
        if self.visits >= self.limit {
            return false;
        }
        self.visits += 1;
        true
    }

    pub(crate) fn visits(&self) -> usize {
        self.visits
    }
}

pub(crate) enum FactorSearch<T> {
    Found(T),
    NotFound,
    BudgetExhausted,
}

pub(crate) enum Factorization {
    And(AndGate),
    Gate(Gate),
}

impl Factorization {
    pub(crate) fn select(and_gate: Option<AndGate>, gate: Option<Gate>) -> Option<Self> {
        match (and_gate, gate) {
            (Some(and_gate), Some(gate)) => {
                if gate.factor_score() >= and_gate.factor_score() {
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

    pub(crate) fn clause_saving(&self) -> isize {
        match self {
            Self::And(gate) => gate.clause_saving(),
            Self::Gate(gate) => gate.clause_saving(),
        }
    }

    pub(crate) fn source_clause_count(&self) -> usize {
        match self {
            Self::And(gate) => gate.source_clause_count(),
            Self::Gate(gate) => gate.source_clause_count(),
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

pub(crate) fn live_factor_clause(
    formula: &Formula,
    clause_idx: usize,
    pending_deleted: &[bool],
) -> bool {
    clause_idx < pending_deleted.len()
        && !pending_deleted[clause_idx]
        && !formula.is_clause_garbage(clause_idx)
        && factor_eligible_clause(formula.get_clause_at_idx(clause_idx))
}

pub(crate) fn factor_eligible_clause(clause: &Clause) -> bool {
    clause.lock_count == 0
        && (2..=MAX_FACTOR_CLAUSE_SIZE).contains(&clause.len())
        && (clause.lbd != 0 || clause.bva_generated)
}

/// Registered definitions stay on GES's protected extension path.
pub(crate) fn definition_clause(literals: Vec<Literal>) -> Clause {
    Clause::new(literals, 0, CreationType::BvaGenerated)
}

/// Quotients replace essential source clauses: permanent in the database, but
/// eligible for ordinary GES rather than extension-definition compression.
pub(crate) fn quotient_clause(literals: Vec<Literal>) -> Clause {
    Clause::new(literals, -1, CreationType::BvaGenerated)
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
    fn definitions_are_marked_as_protected_bva_clauses() {
        let clause = definition_clause(vec![Literal::new(1), Literal::new(-2)]);
        assert_eq!(clause.lbd, 0);
        assert!(clause.bva_generated);
    }

    #[test]
    fn quotients_are_essential_bva_clauses_not_extension_axioms() {
        let clause = quotient_clause(vec![Literal::new(1), Literal::new(-2)]);
        assert_eq!(clause.lbd, -1);
        assert!(clause.bva_generated);
    }

    #[test]
    fn budget_never_exceeds_its_limit() {
        let mut budget = BvaBudget::new(2);
        assert!(budget.visit_clause());
        assert!(budget.visit_clause());
        assert!(!budget.visit_clause());
        assert_eq!(budget.visits(), 2);
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
