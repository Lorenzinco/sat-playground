use fastbit::{BitVec, BitRead, BitWrite};
use crate::formula::literal::Literal;
use crate::formula::clause::Clause;
use crate::formula::Formula;
use crate::history::History;

pub fn find_dip(
    history: &History, 
    formula: &Formula, 
    conflict_clause_index: usize
) -> (Clause, usize, Option<(Literal, Literal)>) {
    let current_level = history.get_decision_level();
    if current_level == 0 { return (Clause::new(), 0, None); } // Unsat

    let mut seen = BitVec::<u64>::new(formula.assignment.len());
    let mut learned_lits: Vec<Literal> = Vec::new();
    let mut path_count = 0;
    
    let mut current_clause_idx = Some(conflict_clause_index);
    let mut resolved_lit: Option<Literal> = None;

    let level_data = &history.decision_levels[current_level];
    let mut trail_iter = level_data.get_implied_literals_rev()
        .chain(level_data.get_decision_literal().into_iter());

    let mut dip_pair = None;

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

        // ---> DIP STOP CONDITION <---
        if path_count == 2 {
            // create new iterator to scan the trail without consuming the unwinding 'trail_iter'
            let scan_iter = level_data.get_implied_literals_rev().chain(level_data.get_decision_literal().into_iter());
            let mut lits = Vec::new();
            for lit in scan_iter {
                if seen.test(lit.get_index() as usize) {
                    lits.push(lit.clone());
                    if lits.len() == 2 {
                        break;
                    }
                }
            }
            if lits.len() == 2 {
                dip_pair = Some((lits[0].negated(), lits[1].negated()));
                learned_lits.push(lits[0].negated());
                learned_lits.push(lits[1].negated());
            } else {
                unreachable!("path_count == 2 but couldn't find 2 literals on trail");
            }
            break; 
        }

        // Standard UIP trail unwinding
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
                unreachable!("Trail is empty but path_count > 0");
            }
        }

        // ---> 1-UIP FALLBACK <---
        if path_count == 0 {
            learned_lits.push(resolved_lit.unwrap().negated());
            break;
        }
    }
    
    let last_idx = learned_lits.len().saturating_sub(1);
       if dip_pair.is_some() {
        if learned_lits.len() > 1 {
            learned_lits.swap(0, last_idx - 1);
            learned_lits.swap(1, last_idx);
        }
    } else {
        if learned_lits.len() > 0 {
            learned_lits.swap(0, last_idx);
        }
    }

    let mut backtrack_level = 0;
    
    // If we stopped at DIP, skip the first 2 literals (the DIP pair)
    // If we stopped at 1-UIP, skip the first 1 literal
    let skip_count = if dip_pair.is_some() { 2 } else { 1 };
    
    for lit in learned_lits.iter().skip(skip_count) {
        let level = history.get_literal_level(lit).unwrap_or(0);
        if level > backtrack_level {
            backtrack_level = level;
        }
    }
    
    (Clause::from_literals(&learned_lits), backtrack_level, dip_pair)
}
