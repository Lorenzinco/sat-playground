use crate::formula::Formula;
use crate::formula::literal::Literal;

use rand::RngExt;
use rand::prelude::IndexedRandom;
use rand::rng;


pub fn get_random_unassigned_literal(formula: &Formula) -> Option<Literal> {
    let unassigned: Vec<u64> = (0..formula.assignment.len())
        .map(|i| i as u64)
        .filter(|&i| formula.assignment.get_value(i).is_none())
        .collect();

    if unassigned.is_empty() {
        return None;
    }

    let mut rng = rng();

    let var = *unassigned.choose(&mut rng).unwrap();
    let negated = rng.random_bool(0.5);

    Some(Literal::new(var, negated))
}