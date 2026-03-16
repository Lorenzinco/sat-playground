use crate::formula::Formula;
use pyo3::prelude::PyResult;


pub fn solve_cdcl<'py>(_formula: &mut Formula) -> PyResult<Option<Vec<bool>>> {
    todo!()
    // let mut ig = ImplicationGraph::new();
    
    // loop {
    //     while formula.contains_unit_clause() {
    //         formula.unit_propagate_with_graph(&mut ig);
    //     }
        
        
    //     if formula.is_satisfied() {
    //         return Ok(Some(formula.get_model()));
    //     }
        
    //     if formula.contains_empty_clause() {
    //         let conflict_lit = match ig.there_is_conflict() {
    //             Some(lit) => {
    //                 lit
    //             },
    //             None => {
    //                 return Ok(None);
    //             }
    //         };
            
    //         let learned_clause = match ig.get_conflict_clause(&conflict_lit) {
    //             Some(clause) => clause.negate(),
    //             None => {
    //                 return Ok(None)
    //             },
    //         };
            
    //         let decision = match ig.closest_arbitrary_implication(&conflict_lit) {
    //             Some(lit) => lit,
    //             None => {
    //                 return Ok(None);
    //             }
    //         };
    
    
    //         let mut to_unset = ig.backtrack(&decision);
    //         to_unset.push(decision.clone());
    
    //         for lit in &to_unset {
    //             let index = lit.get_index();
    //             formula.unset_variable(index).unwrap();
    //         }
    
    //         for lit in &to_unset {
    //             ig.remove_literal(lit);
    //         }
    
    //         formula.add_clause(learned_clause);
    
    //         continue;
    //     }
        
    //     let lit = match formula.get_unassigned_literal() {
    //         Some(l) => l,
    //         None => return Ok(Some(formula.get_model())),
    //     };
    
    //     formula.set_variable(lit.get_index(), !lit.is_negated()).unwrap();
    
    //     ig.add_neighbour(lit.clone(), lit.clone(), true);
    // }
}

#[cfg(test)]
mod tests {

}