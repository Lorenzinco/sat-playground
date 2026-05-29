use crate::formula::literal::Literal;

pub struct DecisionLevel {
    decision_literal: Option<Literal>,
    implied_literals: Vec<(Literal, Option<usize>)>,
    reason_by_unsigned: Vec<Option<usize>>,
}

impl DecisionLevel {
    pub fn new(decision_literal: &Literal) -> Self {
        Self {
            decision_literal: Some(decision_literal.clone()),
            implied_literals: Vec::new(),
            reason_by_unsigned: Vec::new(),
        }
    }

    pub fn empty() -> Self {
        Self {
            decision_literal: None,
            implied_literals: Vec::new(),
            reason_by_unsigned: Vec::new(),
        }
    }

    pub fn add_implied_literal(&mut self, lit: &Literal, clause_index: Option<usize>) {
        let key = lit.get_unsigned_index() as usize;
        if key >= self.reason_by_unsigned.len() {
            self.reason_by_unsigned.resize(key + 1, None);
        }
        self.reason_by_unsigned[key] = clause_index;
        self.implied_literals.push((lit.clone(), clause_index));
    }

    pub fn get_decision_literal(&self) -> Option<&Literal> {
        self.decision_literal.as_ref()
    }

    pub fn get_implied_literals_rev(&self) -> impl Iterator<Item = &Literal> {
        self.implied_literals.iter().rev().map(|(lit, _)| lit)
    }

    pub fn get_reason(&self, lit: &Literal) -> Option<usize> {
        self.reason_by_unsigned
            .get(lit.get_unsigned_index() as usize)
            .copied()
            .flatten()
    }

    pub fn implied_literals_iter(&self) -> impl Iterator<Item = &Literal> + '_ {
        self.implied_literals.iter().map(|(lit, _)| lit)
    }
}
