use fastbit::BitVec;
use fastbit::BitRead;
use fastbit::BitWrite;

use crate::formula::literal::Literal;
use crate::formula::clause::Clause;
use crate::formula::Formula;
use crate::history::History;

pub fn find_1uip(history: &History, formula: &Formula, conflict_clause_index: usize) -> (Clause, usize) {
    let current_level = history.get_decision_level();
    if current_level == 0 { return (Clause::new(), 0); } // Unsat

    let mut seen = BitVec::<u64>::new(formula.assignment.len());
    let mut learned_lits: Vec<Literal> = Vec::new();
    let mut path_count = 0;
    
    let mut current_clause_idx = Some(conflict_clause_index);
    let mut resolved_lit: Option<Literal> = None;

    let level_data = &history.decision_levels[current_level];
    let mut trail_iter = level_data.get_implied_literals_rev()
        .chain(level_data.get_decision_literal().into_iter());

    loop {
        if let Some(clause_idx) = current_clause_idx {
            let clause = &formula.get_clauses()[clause_idx];
            for lit in clause.iter() {
                if Some(lit) == resolved_lit.as_ref() { continue; }
                
                let var = lit.get_index() as usize;
                if !seen.test(var) {
                    seen.set(var);
                    if history.get_literal_level(lit) == Some(current_level) {
                        path_count += 1;
                    } else {
                        learned_lits.push(lit.clone());
                    }
                }
            }
        }

        loop {
            if let Some(lit) = trail_iter.next() {
                let var = lit.get_index() as usize;
                if seen.test(var) {
                    resolved_lit = Some(lit.clone());
                    path_count -= 1;
                    current_clause_idx = level_data.get_reason(lit);
                    break;
                }
            } else {
                unreachable!("Trail is empty but path_count is > 0");
            }
        }

        if path_count == 0 {
            learned_lits.push(resolved_lit.unwrap().negated());
            break;
        }
    }
    
    let last_idx = learned_lits.len() - 1;
    learned_lits.swap(0, last_idx);

    let mut min_seen = BitVec::<u64>::new(formula.assignment.len());
    for lit in &learned_lits {
        min_seen.set(lit.get_index() as usize);
    }
    
    let mut poisoned = BitVec::<u64>::new(formula.assignment.len());
    
    let mut minimized_lits = Vec::new();
    minimized_lits.push(learned_lits[0].clone());
    
    for lit in learned_lits.iter().skip(1) {
        let var = lit.get_index() as usize;
        let level = history.get_literal_level(lit).unwrap_or(0);
        
        if level == 0 { continue; }
        
        let mut stack = vec![lit.clone()];
        let mut local_seen = Vec::new();
        let mut failed = false;
        
        while let Some(current) = stack.pop() {
            let c_var = current.get_index() as usize;
            
            if c_var != var && min_seen.test(c_var) { continue; }
            
            if poisoned.test(c_var) { 
                failed = true; 
                break; 
            }
            
            let c_level = history.get_literal_level(&current).unwrap_or(0);
            if c_level == 0 { continue; }
            
            let reason_idx = history.decision_levels[c_level].get_reason(&current);
            
            match reason_idx {
                None => {
                    failed = true;
                    break;
                }
                Some(idx) => {
                    let clause = &formula.get_clauses()[idx];
                    
                    if c_var != var {
                        min_seen.set(c_var);
                        local_seen.push(c_var);
                    }
                    
                    for child in clause.get_literals() {
                        let child_var = child.get_index() as usize;
                        if child_var != c_var {
                            stack.push(child.clone());
                        }
                    }
                }
            }
        }
        
        if failed {
            for &c_var in &local_seen {
                min_seen.reset(c_var);
                poisoned.set(c_var);
            }
            poisoned.set(var);
            minimized_lits.push(lit.clone());
        } else {
        }
    }
    
    let mut backtrack_level = 0;
    for lit in minimized_lits.iter().skip(1) {
        let level = history.get_literal_level(lit).unwrap_or(0);
        if level > backtrack_level {
            backtrack_level = level;
        }
    }
    
    //(Clause::from_literals(&minimized_lits), backtrack_level)
    (Clause::from_literals(&learned_lits), backtrack_level)
}
