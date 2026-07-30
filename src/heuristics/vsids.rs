use crate::formula::Formula;
use crate::formula::literal::Literal;

#[derive(Clone)]
pub struct Vsids {
    activity: Vec<f32>,
    var_increment: f32,
    decay: f32,
    saved_phases: Vec<bool>,
}

impl Vsids {
    pub fn new(num_vars: usize) -> Self {
        Self {
            activity: vec![0.0; num_vars],
            var_increment: 1.0,
            decay: 0.95,
            saved_phases: vec![false; num_vars],
        }
    }

    pub fn bump(&mut self, lit: &Literal) {
        let var = lit.get_index().unsigned_abs() as usize;
        if var >= self.activity.len() {
            self.activity.resize(var + 1, 0.0);
            self.saved_phases.resize(var + 1, false);
        }
        self.activity[var] += self.var_increment;
        self.saved_phases[var] = !lit.is_negated();

        // Rescale since now everything bumps up to the ceiling, 1e30 is just a random high number
        if self.activity[var] > 1e30 {
            for score in &mut self.activity {
                *score *= 1e-100;
            }
            self.var_increment *= 1e-100;
        }
    }

    pub fn decay_all(&mut self) {
        self.var_increment /= self.decay
    }

    pub fn empty() -> Self {
        Vsids::new(0)
    }

    pub fn from_formula(formula: &Formula) -> Self {
        let mut vsids = Vsids::new(formula.assignment.len());
        let mut positive_occurrences = vec![0usize; formula.assignment.len()];
        let mut negative_occurrences = vec![0usize; formula.assignment.len()];

        for (_, clause) in formula.get_clauses() {
            let weight = if clause.len() == 0 {
                1.0
            } else {
                2f32.powi(-(clause.len() as i32))
            };

            for lit in clause.get_literals() {
                let var = lit.get_index().unsigned_abs() as usize;
                if var >= vsids.activity.len() {
                    vsids.activity.resize(var + 1, 0.0);
                    vsids.saved_phases.resize(var + 1, false);
                    positive_occurrences.resize(var + 1, 0);
                    negative_occurrences.resize(var + 1, 0);
                }

                vsids.activity[var] += weight;
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
        // Automatically enlarge the activity array if new extension variables were added
        if self.activity.len() < formula.assignment.len() {
            self.activity.resize(formula.assignment.len(), 0.0);
            self.saved_phases.resize(formula.assignment.len(), false);
        }

        let mut best_var = None;
        let mut best_score = -1.0;

        for i in 1..formula.assignment.len() {
            if formula.assignment.get_value(i).is_none() {
                let score = self.activity[i];
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
