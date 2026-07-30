use super::literal::Literal;
use crate::formula::Assignment;

use std::collections::HashSet;
use std::fmt;

#[derive(Clone)]
pub struct Clause {
    // The first two literals are the watched literals, avoiding per-clause watch indices.
    literals: Box<[Literal]>,
    lock_count: u32,
    lbd: i16,
    bva_generated: bool,
}

impl<'a> IntoIterator for &'a Clause {
    type Item = &'a Literal;
    type IntoIter = std::slice::Iter<'a, Literal>;

    fn into_iter(self) -> Self::IntoIter {
        self.literals.iter()
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let len = self.literals.len();
        write!(f, "(")?;
        for (i, lit) in self.literals.iter().enumerate() {
            let trailing = if i < len - 1 { "∨" } else { "" };
            write!(f, "{}{}", lit, trailing)?;
        }
        write!(f, ")")
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let len = self.literals.len();
        write!(f, "(")?;
        for (i, lit) in self.literals.iter().enumerate() {
            let trailing = if i < len - 1 { "," } else { "" };
            write!(f, "{:?}{}", lit, trailing)?;
        }
        write!(f, ")")
    }
}

impl Clause {
    pub fn new() -> Self {
        Self {
            literals: Box::new([]),
            lock_count: 0,
            lbd: -1,
            bva_generated: false,
        }
    }

    pub fn from_literals(literals: Vec<Literal>, lbd: i16) -> Self {
        assert!(lbd >= -1, "LBD must be -1 (unknown) or non-negative");
        Self {
            literals: literals.into_boxed_slice(),
            lock_count: 0,
            lbd,
            bva_generated: false,
        }
    }

    pub fn calculate_lbd(levels: impl IntoIterator<Item = usize>) -> i16 {
        let distinct_levels = levels.into_iter().collect::<HashSet<_>>().len();
        i16::try_from(distinct_levels).unwrap_or(i16::MAX)
    }

    pub fn lbd(&self) -> i16 {
        self.lbd
    }

    pub fn lock_count(&self) -> usize {
        self.lock_count as usize
    }

    pub fn increment_lock_count(&mut self) {
        self.lock_count = self
            .lock_count
            .checked_add(1)
            .expect("clause lock count overflow");
    }

    pub fn decrement_lock_count(&mut self) {
        self.lock_count = self.lock_count.saturating_sub(1);
    }

    pub fn is_bva_generated(&self) -> bool {
        self.bva_generated
    }

    pub fn mark_bva_generated(&mut self) {
        self.bva_generated = true;
    }

    pub fn len(&self) -> usize {
        self.into_iter().len()
    }

    // 	/// Assigns <value> to x_<index> if present and not already assigned, otherwhise returns an error
    // 	/// To set the value regardless of already assigned values please use pub fn set_value(index: u64, value: bool).
    // pub fn assign(&mut self, index: u64, value: bool)->Result<(),&str>{
    // 	match self.literals.entry(index) {
    // 		Entry::Occupied (mut entry) => {
    // 			let lit = entry.get_mut();
    // 			if lit.already_assigned(){
    // 				return Err("Already assigned")
    // 			}
    // 			lit.assign(value);
    // 			return Ok(());
    // 		}
    // 		Entry::Vacant(_)=>{
    // 			return Err("Literal not found")
    // 		}
    // 	}
    // }

    // /// Sets the value <value> to literal x_<index> if present, otherwhise returns an error.
    // pub fn set_value(&mut self, index: u64, value: bool)->Result<(),&str>{
    // 	match self.literals.entry(index) {
    // 		Entry::Occupied (mut entry) => {
    // 			entry.get_mut().assign(value);
    // 			return Ok(())
    // 		}
    // 		Entry::Vacant(_)=>{
    // 			return Err("Literal not found")
    // 		}
    // 	}
    // }

    pub fn iter(&self) -> std::slice::Iter<'_, Literal> {
        self.literals.iter()
    }

    /// Adds a literal to the clause, returns an Error if the literal is already present inside the clause
    pub fn add_literal(&mut self, literal: &Literal) -> Result<(), &str> {
        self.add_literals(std::slice::from_ref(literal))
    }

    /// Adds many literals in batch, returns an error if any literal is duplicated.
    pub fn add_literals(&mut self, literals: &[Literal]) -> Result<(), &str> {
        for (index, literal) in literals.iter().enumerate() {
            if self.literals.contains(literal) || literals[..index].contains(literal) {
                return Err("Literal already inside clause");
            }
        }

        if literals.is_empty() {
            return Ok(());
        }

        let mut combined = std::mem::take(&mut self.literals).into_vec();
        combined.reserve_exact(literals.len());
        combined.extend_from_slice(literals);
        self.literals = combined.into_boxed_slice();

        Ok(())
    }

    pub fn get_literals(&self) -> &[Literal] {
        &self.literals
    }

    pub fn sorted_literal_indices(&self) -> Vec<i32> {
        let mut literals = self
            .literals
            .iter()
            .map(|lit| lit.get_index())
            .collect::<Vec<_>>();
        literals.sort_unstable();
        literals
    }

    pub fn watched_literals(&self) -> Option<(&Literal, Option<&Literal>)> {
        match self.literals.as_ref() {
            [] => None,
            [first] => Some((first, None)),
            [first, second, ..] => Some((first, Some(second))),
        }
    }

    pub(crate) fn replace_watched_literal(
        &mut self,
        watched_index: usize,
        replacement_index: usize,
    ) {
        debug_assert!(watched_index < 2);
        debug_assert!(replacement_index >= 2);
        self.literals.swap(watched_index, replacement_index);
    }

    pub fn is_subset_of(&self, other: &Clause) -> bool {
        let subsumer = self.sorted_literal_indices();
        let candidate = other.sorted_literal_indices();
        let mut i = 0;
        let mut j = 0;

        while i < subsumer.len() && j < candidate.len() {
            match subsumer[i].cmp(&candidate[j]) {
                std::cmp::Ordering::Equal => {
                    i += 1;
                    j += 1;
                }
                std::cmp::Ordering::Greater => j += 1,
                std::cmp::Ordering::Less => return false,
            }
        }

        i == subsumer.len()
    }

    pub fn resolve_on(&self, other: &Clause, var: i32) -> Option<Clause> {
        let mut literals = Vec::new();
        let mut seen = HashSet::new();

        for lit in &self.literals {
            let idx = lit.get_index();
            if idx == var {
                continue;
            }
            if seen.contains(&-idx) {
                return None;
            }
            if seen.insert(idx) {
                literals.push(Literal::new(idx));
            }
        }

        for lit in &other.literals {
            let idx = lit.get_index();
            if idx == -var {
                continue;
            }
            if seen.contains(&-idx) {
                return None;
            }
            if seen.insert(idx) {
                literals.push(Literal::new(idx));
            }
        }

        literals.sort_unstable_by_key(|lit| lit.get_index());
        Some(Clause::from_literals(literals, -1))
    }

    /// Returns a vector of the unassigned literals of this clause, if there are no unassigned literals returns an empty vector.
    pub fn get_unassigned_literals(&self, assignment: &Assignment) -> Vec<&Literal> {
        self.literals
            .iter()
            .filter(|lit| lit.eval(assignment).is_none())
            .collect()
    }

    // ///  Removes from this clause all of the literals which value has already been assigned, this method in-place modifies this clause.
    // pub fn simplify(&mut self){
    // 	self.literals.retain(|_,lit|!lit.already_assigned());
    // }
    //

    /// Returns true if this clause contains a literal with index <index>, false otherwise.
    pub fn contains_literal(&self, index: i32) -> bool {
        self.literals.contains(&Literal::new(index))
            || self.literals.contains(&Literal::new(-index))
    }

    /// Returns true if this clause is satisfied, false otherwise. A clause is satisfied if at least one of its literals resolves to true.
    pub fn is_satisfied(&self, assignment: &Assignment) -> bool {
        self.literals
            .iter()
            .any(|lit| lit.eval(assignment) == Some(true))
    }

    /// Returns true if this clause is a unit clause, false otherwise. A unit clause is a clause that contains exactly one unassigned literal.
    pub fn is_unit(&self, assignment: &Assignment) -> bool {
        self.get_unit_literal(assignment).is_some()
    }

    pub fn negate(&self) -> Self {
        let negated_literals = self.literals.iter().map(|lit| lit.negated()).collect();
        Self::from_literals(negated_literals, self.lbd())
    }

    pub fn get_unit_literal(&self, assignment: &Assignment) -> Option<&Literal> {
        let mut unit = None;

        for lit in &self.literals {
            match lit.eval(assignment) {
                Some(true) => return None,
                Some(false) => {}
                None => {
                    if unit.is_some() {
                        return None;
                    }
                    unit = Some(lit);
                }
            }
        }

        unit
    }

    /// Returns true is this clause is empty, the clause is empty where it is not satisfied and contains no unassigned literals, false otherwise.
    pub fn is_empty(&self, assignment: &Assignment) -> bool {
        self.literals
            .iter()
            .all(|lit| lit.eval(assignment) == Some(false))
    }

    /// Unit propagates this clause, this method in-place modifies this clause and returns the literal that was propagated, if this clause is not a unit clause this method panics.
    pub fn unit_propagate(&mut self, assignment: &mut Assignment) -> Option<&Literal> {
        if let Some(lit) = self.get_unit_literal(assignment) {
            assignment.assign(lit.get_index().abs() as usize, !lit.is_negated());
            return Some(lit);
        }

        None
    }

    // /// Resolve the clauses giving back another Clause which is the resolvant
    // pub fn resolve(c1: &Clause, c2: &Clause, lit: &Literal)-> Option<Clause>{
    //     let index = lit.get_index();
    //     if !c1.contains_literal(index) && !c2.contains_literal(index){
    //         return None
    //     }

    //     let mut lits: Vec<Literal> = c1.get_literals()
    //         .into_iter()
    //         .filter(|l| l.get_index() != index);

    //     None
    // }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn clause_occupies_three_machine_words() {
        assert_eq!(size_of::<Clause>(), 24);
        assert_eq!(size_of::<Clause>(), 3 * size_of::<usize>());
    }

    #[test]
    fn lbd_values_larger_than_i8_are_preserved() {
        let clause = Clause::from_literals(Vec::new(), 200);

        assert_eq!(clause.lbd(), 200);
        assert_eq!(Clause::calculate_lbd(0..200), 200);
        assert_eq!(size_of::<Clause>(), 24);
    }

    #[test]
    fn lock_count_round_trips_without_changing_lbd() {
        let mut clause = Clause::from_literals(vec![Literal::new(1)], 7);

        clause.increment_lock_count();
        clause.increment_lock_count();
        assert_eq!(clause.lbd(), 7);
        assert_eq!(clause.lock_count(), 2);
        assert!(!clause.is_bva_generated());

        clause.decrement_lock_count();
        clause.decrement_lock_count();
        clause.decrement_lock_count();
        assert_eq!(clause.lbd(), 7);
        assert_eq!(clause.lock_count(), 0);
    }

    #[test]
    fn bva_and_lock_metadata_coexist_with_zero_lbd() {
        let mut clause = Clause::from_literals(vec![Literal::new(1), Literal::new(2)], 0);

        clause.mark_bva_generated();
        clause.increment_lock_count();
        assert_eq!(clause.lbd(), 0);
        assert_eq!(clause.lock_count(), 1);
        assert!(clause.is_bva_generated());

        clause.decrement_lock_count();
        assert_eq!(clause.lbd(), 0);
        assert_eq!(clause.lock_count(), 0);
        assert!(clause.is_bva_generated());
    }

    #[test]
    fn unknown_lbd_survives_locking_and_returns_to_minus_one() {
        let mut clause = Clause::new();

        clause.increment_lock_count();
        assert_eq!(clause.lbd(), -1);
        assert_eq!(clause.lock_count(), 1);

        clause.decrement_lock_count();
        assert_eq!(clause.lbd(), -1);
        assert_eq!(clause.lock_count(), 0);
    }

    #[test]
    fn add_literals_appends_a_batch_in_order() {
        let mut clause = Clause::from_literals(vec![Literal::new(1)], -1);

        clause
            .add_literals(&[Literal::new(2), Literal::new(-3)])
            .unwrap();

        assert_eq!(
            clause.get_literals(),
            &[Literal::new(1), Literal::new(2), Literal::new(-3)]
        );
    }

    #[test]
    fn add_literals_rejects_duplicates_atomically() {
        let original = vec![Literal::new(1)];
        let mut clause = Clause::from_literals(original.clone(), -1);

        assert!(
            clause
                .add_literals(&[Literal::new(2), Literal::new(1)])
                .is_err()
        );
        assert_eq!(clause.get_literals(), original);

        assert!(
            clause
                .add_literals(&[Literal::new(2), Literal::new(2)])
                .is_err()
        );
        assert_eq!(clause.get_literals(), original);
    }

    #[test]
    fn add_literal_uses_batch_duplicate_semantics() {
        let mut clause = Clause::new();

        clause.add_literal(&Literal::new(1)).unwrap();
        assert!(clause.add_literal(&Literal::new(1)).is_err());
        assert_eq!(clause.get_literals(), &[Literal::new(1)]);
    }

    #[test]
    fn replacing_a_watch_swaps_it_into_the_watched_prefix() {
        let mut clause =
            Clause::from_literals(vec![Literal::new(1), Literal::new(2), Literal::new(3)], -1);

        clause.replace_watched_literal(0, 2);

        assert_eq!(
            clause.get_literals(),
            &[Literal::new(3), Literal::new(2), Literal::new(1)]
        );
        let (first, second) = clause.watched_literals().unwrap();
        assert_eq!(first, &Literal::new(3));
        assert_eq!(second, Some(&Literal::new(2)));
    }
}
