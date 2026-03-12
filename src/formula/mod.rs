pub mod clause;
pub mod literal;
pub mod variable;

use crate::implication_graph::ImplicationGraph;
use crate::solver::{self, Algorithm};
use std::cell::RefCell;
use std::rc::Rc;
use clause::Clause;
use literal::Literal;
use variable::Variable;
use pyo3::prelude::*;
use std::fmt;


pub struct Formula{
	clauses: Vec<Clause>,
	variables: Vec<Rc<RefCell<Variable>>>
}

impl Clone for Formula {
    fn clone(&self) -> Self {
        let new_variables: Vec<Rc<RefCell<Variable>>> = self.variables
            .iter()
            .map(|var_ref| {
                let var = var_ref.borrow().clone();
                Rc::new(RefCell::new(var))
            })
            .collect();
        
        let mut new_clauses = Vec::new();
        for clause in &self.clauses {
            let mut new_clause = Clause::new();
            if let Some(literals) = clause.get_literals() {
                for lit in literals {
                    let index = lit.get_index();
                    let negated = lit.is_negated();
                    let new_var_ref = new_variables[index as usize].clone();
                    let new_lit = Literal::new(new_var_ref, negated);
                    new_clause.add_literal(new_lit).ok();
                }
            }
            new_clauses.push(new_clause);
        }
        
        Formula {
            clauses: new_clauses,
            variables: new_variables,
        }
    }
}

impl fmt::Debug for Formula {
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let len = self.clauses.len();
		for (i,clause) in self.clauses.iter().enumerate() {
			let trailing = if i < len-1 {"∧"} else {""};
			write!(f,"{:?}{}",clause,trailing)?;
		}
		write!(f,"")
	}
}


impl fmt::Display for Formula{
	fn fmt(&self, f: &mut fmt::Formatter<'_>)->fmt::Result{
		let len = self.clauses.len();
		for (i,clause) in self.clauses.iter().enumerate() {
			let trailing = if i < len-1 {"∧"} else {""};
			write!(f,"{}{}",clause,trailing)?;
		}
		write!(f,"")
	}
}

impl Formula {

 	/// Creates a new empty formula, to create one starting from a dimacs file see from_dimacs(dimacs: &str).
	/// 
	/// ```
	/// use sat_playground::formula::Formula;
	/// 
	/// let phi = Formula::new();
	/// ```
	pub fn new()->Self{

		Formula{
			clauses: vec!(),
			variables: vec!()
		}
	}
	
	pub fn from_clauses(clauses: Vec<Clause>, variables: Vec<Rc<RefCell<Variable>>>)->Self{
		Self {
			clauses: clauses.to_owned(),
			variables: variables.to_owned()
		}
	}
	
	pub fn get_variables(&self)->&Vec<Rc<RefCell<Variable>>>{
		&self.variables
	}
	
	/// Returns a mutable reference to the clauses of the formula, this is used to modify the clauses during the solving process.
	pub fn get_clauses(&mut self)->&mut Vec<Clause>{
	    &mut self.clauses
	}
	
	/// Returns a vector of mutable references to the unsatisfied clauses of the formula, this is used to modify the clauses during the solving process.
	pub fn get_unsatisfied_clauses(&mut self)->Vec<&mut Clause>{
        self.get_clauses().iter_mut().filter(|clause| !clause.is_satisfied()).collect()
    }
	
	pub fn add_clause(&mut self, clause: Clause) {
		self.clauses.push(clause);
	}
	
	pub fn set_variable(&mut self, index: u64, value: bool)->Result<(),&str>{
		let rc = self.variables.get(index as usize).ok_or("Variable index out of bounds")?;
		let mut variable = rc.borrow_mut();
		Ok(variable.assign(value))
	}
	
	pub fn unset_variable(&mut self, index: u64)->Result<(),&str>{
        let rc = self.variables.get(index as usize).ok_or("Variable index out of bounds")?;
        let mut variable = rc.borrow_mut();
        Ok(variable.unset())
    }
	
	pub fn solve<'py>(&mut self, algorithm: Algorithm) -> PyResult<Option<Vec<bool>>> {
	
        solver::solve(self, algorithm)
    }
    
    pub fn contains_unit_clause(&mut self) -> bool {
        self.get_unsatisfied_clauses().iter().any(|clause| clause.is_unit())
    }
    
    pub fn get_pure_literals(&mut self) -> Vec<(Rc<RefCell<Variable>>, bool)> {
        let clauses = self.get_unsatisfied_clauses();
        let mut seen: std::collections::HashMap<u64,(bool,bool)> = std::collections::HashMap::new();
        
        for clause in clauses {
            let literals = clause.get_unassigned_literals();
                for literal in literals {
                    let index = literal.get_index();
                    let negated = literal.is_negated();
                    match seen.entry(index) {
                        std::collections::hash_map::Entry::Occupied(mut entry) => {
                            let (neg,pure) = entry.get();
                            if !pure{
                                continue;
                            }
                            if negated & *neg {
                                continue;
                            }
                            if !negated & !*neg {
                                continue;
                            }
                            entry.insert((negated,false));
                        }
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            let sign = literal.is_negated();
                            entry.insert((sign,true));
                        }
                    }
                }
        }
        
        
        let mut pure_literals: Vec<(Rc<RefCell<Variable>>,bool)> = Vec::new();
        for (index,(neg,pure)) in seen {
            if pure {
                let var_ref = self.variables.get(index as usize).unwrap().clone();
                pure_literals.push((var_ref.clone(), !neg));
            }
        }
        
        pure_literals
    }
    
    pub fn is_satisfied(&self) -> bool {
        self.clauses.iter().all(|clause| clause.is_satisfied())
    }
    
    /// Performs unit propagation on the formula, to also update an implication graph use unit_propagate_with_graph(ig: &mut ImplicationGraph) instead, this is used in the DPLL algorithm.
    pub fn unit_propagate(&mut self) {
        let clauses = self.get_unsatisfied_clauses();
        for clause in clauses {
            if clause.is_unit() {
                clause.unit_propagate();
            }
        }
    }
    
    pub fn unit_propagate_with_graph(&mut self, ig: &mut ImplicationGraph) {
        let clauses = self.get_unsatisfied_clauses();
        for clause in clauses {
            if clause.is_unit() {
                println!("Unit propagating clause: {:?}, is unit: {}", clause, clause.is_unit());
                let implied_literal = clause.unit_propagate_with_graph(ig);
                if let Some(lit) = implied_literal {
                    println!("Implied literal: {:?}", lit);
                    continue;
                }
                else {
                    panic!("Unit propagation failed, clause is not a unit clause.");
                }
            }
        }
    }
    
    pub fn contains_empty_clause(&self) -> bool {
        self.clauses.iter().any(|clause| clause.is_empty())
    }
    
    pub fn get_unassigned_literal(&self) -> Option<Literal> {
        for clause in self.clauses.iter() {
            let literals = clause.get_unassigned_literals();
            if literals.len() > 0 {
                return Some(literals[0].clone());
            }
        }
        None
    }
    
    pub fn get_model(&self) -> Vec<bool> {
        self.variables.iter().map(|var| var.borrow().get_value().unwrap_or(false)).collect()
    }
    
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::implication_graph::ImplicationGraph;
    use crate::formula::clause::Clause;
    use crate::formula::literal::Literal;
    use crate::formula::variable::Variable;
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_vars(n: u64) -> Vec<Rc<RefCell<Variable>>> {
        (0..n)
            .map(|i| Rc::new(RefCell::new(Variable::new(i, None))))
            .collect()
    }

    fn lit(vars: &[Rc<RefCell<Variable>>], idx: u64, neg: bool) -> Literal {
        Literal::new(vars[idx as usize].clone(), neg)
    }

    fn clause_from_literals(lits: Vec<Literal>) -> Clause {
        let mut c = Clause::new();
        for lit in lits {
            c.add_literal(lit).unwrap();
        }
        c
    }

    fn formula_from_literal_matrix(nvars: u64, clauses: Vec<Vec<(u64, bool)>>) -> Formula {
        let vars = make_vars(nvars);
        let built_clauses = clauses
            .into_iter()
            .map(|cl| {
                let lits = cl.into_iter().map(|(idx, neg)| lit(&vars, idx, neg)).collect();
                clause_from_literals(lits)
            })
            .collect();
        Formula::from_clauses(built_clauses, vars)
    }

    fn clause_literals(clause: &Clause) -> Vec<Literal> {
        clause.get_literals().unwrap_or_default()
    }

    fn assert_same_literals(mut got: Vec<Literal>, mut expected: Vec<Literal>) {
        got.sort_by_key(|l| (l.get_index(), l.is_negated()));
        expected.sort_by_key(|l| (l.get_index(), l.is_negated()));
        assert_eq!(got, expected);
    }

    #[test]
    fn unit_propagation_with_graph_creates_real_graph_conflict_when_formula_has_empty_clause() {
        // Formula:
        // (¬a ∨ b)
        // (a ∨ b)
        // (a ∨ ¬b)
        //
        // If we decide ¬a, then:
        // - (a ∨ b)  -> b
        // - (a ∨ ¬b) -> ¬b
        // hence conflict on b / ¬b and an empty clause should appear.
        let mut formula = formula_from_literal_matrix(
            2,
            vec![
                vec![(0, true), (1, false)],  // ¬a ∨ b
                vec![(0, false), (1, false)], // a ∨ b
                vec![(0, false), (1, true)],  // a ∨ ¬b
            ],
        );

        let vars = formula.get_variables().clone();
        let not_a = Literal::new(vars[0].clone(), true);
        let b = Literal::new(vars[1].clone(), false);
        let not_b = Literal::new(vars[1].clone(), true);

        let mut ig = ImplicationGraph::new();

        // decision: ¬a
        formula.set_variable(0, false).unwrap();
        ig.add_neighbour(not_a.clone(), not_a.clone(), true);

        while formula.contains_unit_clause() {
            formula.unit_propagate_with_graph(&mut ig);
        }

        assert!(formula.contains_empty_clause(), "formula should contain an empty clause after b and ¬b are both implied");

        let conflict = ig.there_is_conflict();
        assert!(conflict.is_some(), "if formula has an empty clause from contradictory propagation, implication graph must contain a conflict");

        let conflict_lit = conflict.unwrap();
        assert!(
            conflict_lit == b || conflict_lit == not_b,
            "conflict should be on b or ¬b"
        );

        let closest = ig.closest_arbitrary_implication(&conflict_lit);
        assert_eq!(
            closest,
            Some(not_a.clone()),
            "the closest arbitrary implication should be the decision ¬a"
        );
    }

    #[test]
    fn conflict_clause_matches_current_graph_cut_for_formula_driven_conflict() {
        // Same setup as above:
        // decide ¬a, propagate b and ¬b
        //
        // With your current implementation, the conflict clause is just the union
        // of the immediate predecessors of b and ¬b, which should be {¬a}.
        let mut formula = formula_from_literal_matrix(
            2,
            vec![
                vec![(0, true), (1, false)],  // ¬a ∨ b
                vec![(0, false), (1, false)], // a ∨ b
                vec![(0, false), (1, true)],  // a ∨ ¬b
            ],
        );

        let vars = formula.get_variables().clone();
        let not_a = Literal::new(vars[0].clone(), true);

        let mut ig = ImplicationGraph::new();

        formula.set_variable(0, false).unwrap();
        ig.add_neighbour(not_a.clone(), not_a.clone(), true);

        while formula.contains_unit_clause() {
            formula.unit_propagate_with_graph(&mut ig);
        }

        assert!(formula.contains_empty_clause());

        let conflict_lit = ig.there_is_conflict().expect("graph should contain a conflict");
        let learned_clause = ig
            .get_conflict_clause(&conflict_lit)
            .expect("current implementation should produce a conflict clause");

        assert_same_literals(clause_literals(&learned_clause), vec![not_a]);
    }

    #[test]
    fn manual_formula_backtrack_and_graph_remove_restore_consistency() {
        // Same branching formula again. We decide ¬a, get b and ¬b, then backtrack manually.
        let mut formula = formula_from_literal_matrix(
            2,
            vec![
                vec![(0, true), (1, false)],  // ¬a ∨ b
                vec![(0, false), (1, false)], // a ∨ b
                vec![(0, false), (1, true)],  // a ∨ ¬b
            ],
        );

        let vars = formula.get_variables().clone();
        let not_a = Literal::new(vars[0].clone(), true);

        let mut ig = ImplicationGraph::new();

        formula.set_variable(0, false).unwrap();
        ig.add_neighbour(not_a.clone(), not_a.clone(), true);

        while formula.contains_unit_clause() {
            formula.unit_propagate_with_graph(&mut ig);
        }

        assert!(formula.contains_empty_clause());

        let conflict_lit = ig.there_is_conflict().unwrap();
        let decision = ig.closest_arbitrary_implication(&conflict_lit).unwrap();
        assert_eq!(decision, not_a);

        let mut to_unset = ig.backtrack(&decision);
        to_unset.push(decision.clone());

        for lit in &to_unset {
            formula.unset_variable(lit.get_index()).unwrap();
        }

        for lit in &to_unset {
            ig.remove_literal(lit);
        }

        assert_eq!(ig.there_is_conflict(), None, "after removing the decision cone, the graph must no longer contain the conflict");

        for var in formula.get_variables() {
            assert_eq!(var.borrow().get_value(), None, "all assignments in the decision cone should be unset");
        }
    }

    #[test]
    fn backtrack_and_remove_on_graph_matches_formula_unset_for_entire_decision_cone() {
        // decision d = a
        // a -> b
        // b -> c
        //
        // After backtrack_and_remove(a, true), formula variables for a,b,c should be unset
        // and graph should contain none of them.
        let mut formula = formula_from_literal_matrix(
            3,
            vec![
                vec![(0, false)],              // a
                vec![(0, true), (1, false)],   // ¬a ∨ b
                vec![(1, true), (2, false)],   // ¬b ∨ c
            ],
        );

        let vars = formula.get_variables().clone();
        let a = Literal::new(vars[0].clone(), false);

        let mut ig = ImplicationGraph::new();

        formula.set_variable(0, true).unwrap();
        ig.add_neighbour(a.clone(), a.clone(), true);

        while formula.contains_unit_clause() {
            formula.unit_propagate_with_graph(&mut ig);
        }

        // a is arbitrary
        assert!(ig.is_arbitrary(&a));

        let classified = ig.classify_literals(vec![
            Literal::new(vars[0].clone(), false),
            Literal::new(vars[1].clone(), false),
            Literal::new(vars[2].clone(), false),
        ]);

        assert_eq!(classified[0].1, true);
        assert_eq!(classified[1].1, false);
        assert_eq!(classified[2].1, false);

        let removed = ig.backtrack_and_remove(&a, true);
        assert_eq!(removed.len(), 2, "should remove b and c transitively, excluding the decision itself from the returned vector");

        formula.unset_variable(0).unwrap();
        formula.unset_variable(1).unwrap();
        formula.unset_variable(2).unwrap();

        for var in formula.get_variables() {
            assert_eq!(var.borrow().get_value(), None);
        }

        assert_eq!(ig.get_predecessors(&a), None);
        assert_eq!(ig.get_implied(&a), None);
        assert_eq!(ig.there_is_conflict(), None);
    }

    #[test]
    fn no_arbitrary_choice_exists_in_pure_unit_unsat_chain() {
        // Formula:
        // (a)
        // (¬a ∨ b)
        // (¬a ∨ ¬b)
        //
        // Here conflict is produced entirely by unit propagation from a unit clause.
        // No arbitrary decision should exist.
        let mut formula = formula_from_literal_matrix(
            2,
            vec![
                vec![(0, false)],             // a
                vec![(0, true), (1, false)],  // ¬a ∨ b
                vec![(0, true), (1, true)],   // ¬a ∨ ¬b
            ],
        );

        let mut ig = ImplicationGraph::new();

        while formula.contains_unit_clause() {
            formula.unit_propagate_with_graph(&mut ig);
        }

        assert!(formula.contains_empty_clause(), "pure unit propagation should lead to contradiction");
        let conflict_lit = ig.there_is_conflict().expect("graph must contain the same contradiction");
        assert_eq!(
            ig.closest_arbitrary_implication(&conflict_lit),
            None,
            "there must be no arbitrary decision to backtrack to"
        );
    }
}