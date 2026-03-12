use crate::formula::Formula;
use crate::implication_graph::ImplicationGraph;
use pyo3::prelude::PyResult;


pub fn solve_cdcl<'py>(formula: &mut Formula) -> PyResult<Option<Vec<bool>>> {
    let mut ig = ImplicationGraph::new();
    
    loop {
        while formula.contains_unit_clause() {
            formula.unit_propagate_with_graph(&mut ig);
            println!("Formula: {:?}",formula);
        }
        
        println!("Formula after unit propagation: {:?}", formula);
        
        if formula.is_satisfied() {
            return Ok(Some(formula.get_model()));
        }
        
        if formula.contains_empty_clause() {
            let conflict_lit = match ig.there_is_conflict() {
                Some(lit) => {
                    println!("Conflict detected at literal: {}", lit);
                    lit
                },
                None => {
                    println!("Conflict detected but no conflict literal found, this should not happen.");
                    return Ok(None);
                }
            };
            
            let learned_clause = match ig.get_conflict_clause(&conflict_lit) {
                Some(clause) => clause.negate(),
                None => {
                    println!("Conflict detected but no conflict clause found, this should not happen.");
                    return Ok(None)
                },
            };
            
            let decision = match ig.closest_arbitrary_implication(&conflict_lit) {
                Some(lit) => lit,
                None => {
                    return Ok(None);
                }
            };
    
    
            let mut to_unset = ig.backtrack(&decision);
            to_unset.push(decision.clone());
    
            for lit in &to_unset {
                let index = lit.get_index();
                formula.unset_variable(index).unwrap();
            }
    
            for lit in &to_unset {
                ig.remove_literal(lit);
            }
    
            println!("Learned clause: {}", learned_clause);
            formula.add_clause(learned_clause);
    
            continue;
        }
        
        let lit = match formula.get_unassigned_literal() {
            Some(l) => l,
            None => return Ok(Some(formula.get_model())),
        };
    
        println!("Deciding literal: {}", lit);
        formula.set_variable(lit.get_index(), !lit.is_negated()).unwrap();
    
        ig.add_neighbour(lit.clone(), lit.clone(), true);
    }
}

#[cfg(test)]
mod tests {
    use super::solve_cdcl;
    use crate::formula::Formula;
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

    fn satisfies_formula(formula: &Formula, model: &[bool]) -> bool {
        let mut f = formula.clone();
        for (i, value) in model.iter().enumerate() {
            f.set_variable(i as u64, *value).unwrap();
        }
        f.is_satisfied()
    }

    #[test]
    fn cdcl_returns_none_only_when_conflict_has_no_arbitrary_decision() {
        // (a)
        // (¬a ∨ b)
        // (¬a ∨ ¬b)
        //
        // Unit propagation alone causes contradiction. There is no arbitrary decision,
        // so returning None is correct here.
        let mut formula = formula_from_literal_matrix(
            2,
            vec![
                vec![(0, false)],             // a
                vec![(0, true), (1, false)],  // ¬a ∨ b
                vec![(0, true), (1, true)],   // ¬a ∨ ¬b
            ],
        );

        let result = solve_cdcl(&mut formula).unwrap();
        assert_eq!(
            result, None,
            "CDCL should fail only when contradiction occurs with no arbitrary choice to backtrack to"
        );
    }

    #[test]
    fn cdcl_does_not_fail_prematurely_when_a_conflict_has_an_arbitrary_ancestor() {
        // (¬a ∨ b)
        // (a ∨ b)
        // (a ∨ ¬b)
        //
        // If CDCL picks ¬a first (which is plausible if the first literal returned by
        // get_unassigned_literal is the first literal of the first clause), then:
        //   a = false
        //   b and ¬b are both implied
        // This conflict DOES have an arbitrary ancestor (¬a), so CDCL must not return None
        // just because a conflict happened.
        //
        // A correct backtracking behavior should recover and find a model.
        let original = formula_from_literal_matrix(
            2,
            vec![
                vec![(0, true), (1, false)],  // ¬a ∨ b
                vec![(0, false), (1, false)], // a ∨ b
                vec![(0, false), (1, true)],  // a ∨ ¬b
            ],
        );

        let mut formula = original.clone();
        let result = solve_cdcl(&mut formula).unwrap();

        assert!(
            result.is_some(),
            "if a conflict has an arbitrary ancestor, CDCL should backtrack instead of failing immediately"
        );

        let model = result.unwrap();
        assert!(
            satisfies_formula(&original, &model),
            "returned model must satisfy the original formula"
        );
    }
}