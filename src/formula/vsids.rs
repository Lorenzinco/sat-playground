use crate::formula::Formula;
use crate::formula::Literal;

pub struct Vsids {
    scores: Vec<f64>,
    decay: f64,
    saved_phases: Vec<bool>
}

impl Vsids {
    pub fn new(num_vars: usize) -> Self {
        Self {
            scores: vec![0.0; num_vars],
            decay: 0.95,
            saved_phases: vec![false; num_vars]
        }
    }

    pub fn bump(&mut self, lit: &Literal) {
        let var = lit.get_index() as usize;
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

        best_var.map(|var| Literal::new(var, !self.saved_phases[var as usize]))
    }
}