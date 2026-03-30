use crate::formula::Formula;
use crate::formula::Literal;

pub struct Vsids {
    scores: Vec<f64>,
    decay: f64,
}

impl Vsids {
    pub fn new(num_vars: usize) -> Self {
        Self {
            scores: vec![0.0; num_vars],
            decay: 0.95,
        }
    }

    pub fn bump(&mut self, var: usize) {
        if var >= self.scores.len() {
            self.scores.resize(var + 1, 0.0);
        }
        self.scores[var] += 1.0;
    }

    pub fn decay_all(&mut self) {
        for score in &mut self.scores {
            *score *= self.decay;
        }
    }

    pub fn get_best_unassigned(&mut self, formula: &Formula) -> Option<Literal> {
        // Automatically enlarge the scores array if new extension variables were added
        if self.scores.len() < formula.assignment.len() {
            self.scores.resize(formula.assignment.len(), 0.0);
        }

        let mut best_var = None;
        let mut best_score = -1.0;

        for i in 0..formula.assignment.len() {
            if formula.assignment.get_value(i as u64).is_none() {
                let score = self.scores[i];
                if score > best_score {
                    best_score = score;
                    best_var = Some(i as u64);
                }
            }
        }

        best_var.map(|var| Literal::new(var, false))
    }
}