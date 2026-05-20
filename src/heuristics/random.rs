use crate::formula::Formula;
use crate::formula::literal::Literal;

use rand::RngExt;
use rand::prelude::IndexedRandom;
use rand::rng;


pub fn get_random_unassigned_literal(formula: &Formula) -> Option<Literal> {
    let unassigned: Vec<usize> = (0..formula.assignment.len())
        .filter(|&i| formula.assignment.get_value(i).is_none())
        .collect();

    if unassigned.is_empty() {
        return None;
    }

    let mut rng = rng();

    let var = *unassigned.choose(&mut rng).unwrap();
    let negated = rng.random_bool(0.5);
    let literal = if negated { var as i32 } else { -(var as i32)};

    Some(Literal::new(literal))
}