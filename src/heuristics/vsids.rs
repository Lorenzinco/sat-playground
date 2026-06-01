use crate::formula::Formula;
use crate::formula::literal::Literal;

#[derive(Clone)]
pub struct Vsids {
    scores: Vec<f64>,
    decay: f64,
    saved_phases: Vec<bool>,
}

impl Vsids {
    pub fn new(num_vars: usize) -> Self {
        Self {
            scores: vec![0.0; num_vars],
            decay: 0.95,
            saved_phases: vec![false; num_vars],
        }
    }

    pub fn bump(&mut self, lit: &Literal) {
        let var = lit.get_index().abs() as usize;
        if var >= self.scores.len() {
            self.scores.resize(var + 1, 0.0);
            self.saved_phases.resize(var + 1, false);
        }
        self.scores[var] += 1.0;
        self.saved_phases[var] = !lit.is_negated()
    }

    pub fn decay_all(&mut self) {
        for score in &mut self.scores {
            *score *= self.decay;
        }
    }

    pub fn empty() -> Self {
        Vsids::new(0)
    }

    pub fn from_formula(formula: &Formula) -> Self {
        let mut vsids = Vsids::new(formula.assignment.len());
        let mut positive_occurrences = vec![0usize; formula.assignment.len()];
        let mut negative_occurrences = vec![0usize; formula.assignment.len()];

        for clause in formula.get_clauses() {
            let weight = if clause.len() == 0 {
                1.0
            } else {
                2f64.powi(-(clause.len() as i32))
            };

            for lit in clause.get_literals() {
                let var = lit.get_index().unsigned_abs() as usize;
                if var >= vsids.scores.len() {
                    vsids.scores.resize(var + 1, 0.0);
                    vsids.saved_phases.resize(var + 1, false);
                    positive_occurrences.resize(var + 1, 0);
                    negative_occurrences.resize(var + 1, 0);
                }

                vsids.scores[var] += weight;
                if lit.is_negated() {
                    negative_occurrences[var] += 1;
                } else {
                    positive_occurrences[var] += 1;
                }
            }
        }

        for var in 1..vsids.saved_phases.len() {
            vsids.saved_phases[var] = positive_occurrences[var] >= negative_occurrences[var];
        }

        vsids
    }

    pub fn get_best_unassigned(&mut self, formula: &Formula) -> Option<Literal> {
        // Automatically enlarge the scores array if new extension variables were added
        if self.scores.len() < formula.assignment.len() {
            self.scores.resize(formula.assignment.len(), 0.0);
            self.saved_phases.resize(formula.assignment.len(), false);
        }

        let mut best_var = None;
        let mut best_score = -1.0;

        for i in 1..formula.assignment.len() {
            if formula.assignment.get_value(i).is_none() {
                let score = self.scores[i];
                if score > best_score {
                    best_score = score;
                    best_var = Some(i);
                }
            }
        }

        best_var.map(|var| {
            if self.saved_phases[var] {
                Literal::new(var as i32)
            } else {
                Literal::new(-(var as i32))
            }
        })
    }
}
