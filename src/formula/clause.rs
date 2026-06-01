use super::literal::Literal;
use crate::formula::Assignment;
use crate::two_watched::Watched;
use std::collections::HashSet;
use std::fmt;

#[derive(Clone)]
pub struct Clause {
    literals: Vec<Literal>,
    pub watched: Watched,
    pub lbd: i64,
    pub lock_count: usize,
    pub bva_generated: bool,
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
            literals: vec![],
            watched: Watched::None,
            lbd: -1,
            lock_count: 0,
            bva_generated: false,
        }
    }

    fn watched_for_len(len: usize) -> Watched {
        match len {
            0 => Watched::None,
            1 => Watched::One(0),
            _ => Watched::Two(0, 1),
        }
    }

    pub fn from_literals(literals: Vec<Literal>, lbd: i64) -> Self {
        let watched = Self::watched_for_len(literals.len());
        Self {
            literals,
            watched,
            lbd,
            lock_count: 0,
            bva_generated: false,
        }
    }

    pub fn calculate_lbd(levels: impl IntoIterator<Item = usize>) -> i64 {
        levels.into_iter().collect::<HashSet<_>>().len() as i64
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
        if self.literals.contains(literal) {
            return Err("Literal already inside clause");
        }

        match self.watched {
            Watched::None => self.watched = Watched::One(0),
            Watched::One(_) => self.watched = Watched::Two(0, 1),
            Watched::Two(_, _) => { /* Already ok */ }
        }
        self.literals.push(literal.clone());

        Ok(())
    }

    pub fn get_literals(&self) -> &Vec<Literal> {
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
        match self.watched {
            Watched::None => None,
            Watched::One(i) => Some((&self.literals[i], None)),
            Watched::Two(i, j) => Some((&self.literals[i], Some(&self.literals[j]))),
        }
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
        Self::from_literals(negated_literals, self.lbd)
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
