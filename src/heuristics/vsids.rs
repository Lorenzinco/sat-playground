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

    pub(crate) fn add_variable(&mut self) {
        self.activity.push(0.0);
        self.saved_phases.push(false);
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

    pub(crate) fn sample_literal(&self, formula: &Formula) -> Option<Literal> {
        let (variable, positive_occurs, negative_occurs) =
            self.sample_variable(formula, rand::random::<f64>())?;
        let positive = match (positive_occurs, negative_occurs) {
            (true, true) => rand::random::<bool>(),
            (true, false) => true,
            (false, true) => false,
            (false, false) => unreachable!("sampled variables have a live occurrence"),
        };
        Some(Literal::new(if positive {
            variable as i32
        } else {
            -(variable as i32)
        }))
    }

    fn sample_variable(&self, formula: &Formula, unit_sample: f64) -> Option<(usize, bool, bool)> {
        let candidates = (1..formula.assignment.len())
            .filter_map(|variable| {
                let positive = Literal::new(variable as i32);
                let negative = positive.negated();
                let positive_occurs = formula.live_occurrence_len(&positive) != 0;
                let negative_occurs = formula.live_occurrence_len(&negative) != 0;
                (positive_occurs || negative_occurs).then_some((
                    variable,
                    positive_occurs,
                    negative_occurs,
                    self.activity.get(variable).copied().unwrap_or(0.0).max(0.0) as f64,
                ))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return None;
        }

        let total_activity = candidates
            .iter()
            .map(|(_, _, _, activity)| activity)
            .sum::<f64>();
        if total_activity.is_finite() && total_activity > 0.0 {
            let mut target = unit_sample.clamp(0.0, 1.0 - f64::EPSILON) * total_activity;
            for &(variable, positive, negative, activity) in &candidates {
                if target < activity {
                    return Some((variable, positive, negative));
                }
                target -= activity;
            }
            let &(variable, positive, negative, _) = candidates.last().unwrap();
            return Some((variable, positive, negative));
        }

        // Before VSIDS has any activity, retain uniform sampling over live variables.
        let index = ((unit_sample.clamp(0.0, 1.0 - f64::EPSILON) * candidates.len() as f64)
            as usize)
            .min(candidates.len() - 1);
        let (variable, positive, negative, _) = candidates[index];
        Some((variable, positive, negative))
    }

    pub(crate) fn sample_low_activity_variable(&self, formula: &Formula) -> Option<usize> {
        self.sample_low_activity_variable_at(formula, rand::random::<f64>())
    }

    fn sample_low_activity_variable_at(
        &self,
        formula: &Formula,
        unit_sample: f64,
    ) -> Option<usize> {
        let candidates = (1..formula.assignment.len())
            .filter_map(|variable| {
                let positive = Literal::new(variable as i32);
                let negative = positive.negated();
                (formula.live_occurrence_len(&positive) != 0
                    && formula.live_occurrence_len(&negative) != 0)
                    .then_some(variable)
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return None;
        }

        let weights = candidates
            .iter()
            .map(|&variable| {
                let activity = self.activity.get(variable).copied().unwrap_or(0.0).max(0.0) as f64;
                1.0 / (1.0 + activity)
            })
            .collect::<Vec<_>>();
        let total_weight = weights.iter().sum::<f64>();
        if total_weight.is_finite() && total_weight > 0.0 {
            let mut target = unit_sample.clamp(0.0, 1.0 - f64::EPSILON) * total_weight;
            for (&variable, &weight) in candidates.iter().zip(&weights) {
                if target < weight {
                    return Some(variable);
                }
                target -= weight;
            }
        }

        candidates.last().copied()
    }

    pub fn get_best_unassigned(&self, formula: &Formula) -> Option<Literal> {
        let mut best_var = None;
        let mut best_score = -1.0;

        for i in 1..formula.assignment.len() {
            if formula.assignment.get_value(i).is_none() {
                let score = self.activity.get(i).copied().unwrap_or(0.0);
                if score > best_score {
                    best_score = score;
                    best_var = Some(i);
                }
            }
        }

        best_var.map(|var| {
            if self.saved_phases.get(var).copied().unwrap_or(false) {
                Literal::new(var as i32)
            } else {
                Literal::new(-(var as i32))
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Vsids;
    use crate::formula::Formula;

    #[test]
    fn weighted_sampling_uses_activity_and_ignores_absent_variables() {
        let formula = Formula::from_vec(vec![vec![1, -2], vec![-1, 2], vec![4]]);
        let mut vsids = Vsids::new(formula.assignment.len());
        vsids.activity[1] = 1.0;
        vsids.activity[2] = 3.0;
        vsids.activity[3] = 100.0;
        vsids.activity[4] = 6.0;

        assert_eq!(
            vsids.sample_variable(&formula, 0.0).map(|sample| sample.0),
            Some(1)
        );
        assert_eq!(
            vsids.sample_variable(&formula, 0.2).map(|sample| sample.0),
            Some(2)
        );
        assert_eq!(
            vsids.sample_variable(&formula, 0.99).map(|sample| sample.0),
            Some(4)
        );
    }

    #[test]
    fn zero_activity_sampling_falls_back_to_uniform_live_variables() {
        let formula = Formula::from_vec(vec![vec![1], vec![-3]]);
        let vsids = Vsids::new(formula.assignment.len());

        assert_eq!(
            vsids.sample_variable(&formula, 0.0).map(|sample| sample.0),
            Some(1)
        );
        assert_eq!(
            vsids.sample_variable(&formula, 0.99).map(|sample| sample.0),
            Some(3)
        );
    }

    #[test]
    fn bve_sampling_prefers_lower_activity_variables() {
        let formula = Formula::from_vec(vec![vec![1, 2], vec![-1, -2]]);
        let mut vsids = Vsids::new(formula.assignment.len());
        vsids.activity[1] = 1.0;
        vsids.activity[2] = 3.0;

        // The inverse weights are 1/2 and 1/4, so variable 1 owns the
        // first two thirds of the sampling interval.
        assert_eq!(
            vsids.sample_low_activity_variable_at(&formula, 0.65),
            Some(1)
        );
        assert_eq!(
            vsids.sample_low_activity_variable_at(&formula, 0.67),
            Some(2)
        );
    }
}
