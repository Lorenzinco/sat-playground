use crate::formula::clause::Clause;
use crate::formula::variable::Variable;
use crate::formula::literal::Literal;
use crate::formula::Formula;
use std::rc::Rc;
use std::cell::RefCell;


pub fn parse_dimacs(dimacs: &str)-> Result<Formula,String>{
	let mut num_vars: u64 = 0;
	let mut num_clauses: u64;
	
	let mut clause_lines: Vec<&str> = Vec::new();
	
	for (line_no,raw_line) in dimacs.lines().enumerate() {
		let line = raw_line.trim();
		
		if line.is_empty() || line.starts_with('c') {
      continue;
    }
    
	 	if line.starts_with("p") {
			let parts: Vec<&str> = line.split_whitespace().collect();
			if parts.len() != 4 {
				return Err(format!("Invalid dimacs format, expected 3 arguments after p at line {}",line_no))
			}
			
			if parts[1] != "cnf" {
				return Err(format!("Expected \"cnf\" as problem type at line {}: {}",line_no,line))
			}
			
			if num_vars != 0 {
				return Err(format!("Multiple problem lines {}: {}",line_no,line))
			}
			
			num_vars = u64::from_str_radix(parts[2],10).map_err(|_| format!("Invalid variable count {} {}:{}",parts[2],line_no,line))?;
			
			if num_vars == 0 {
				return Err(format!("Invalid variable count {} {}:{}",num_vars,line_no,line))
			}
			
			num_clauses = u64::from_str_radix(parts[3], 10).map_err(|_| format!("Invalid clauses count {} {}:{}",parts[3],line_no,line))?;
			
			if num_clauses == 0 {
				return Err(format!("Invalid clauses count {} {}:{}",num_clauses,line_no,line))
			}
			
			continue;
		}
		
		clause_lines.push(line);
	}
	
	let mut variables: Vec<Rc<RefCell<Variable>>> = Vec::new();
	
	for i in 0..num_vars{
		println!("Creating variable: {}",i);
		let variable = Rc::new(RefCell::new(Variable::new(i as u64,false,false)));
		variables.push(variable);
		println!("{:?}",variables);
	}
	
	let mut clauses: Vec<Clause> = Vec::new();
	
	for clause_line in clause_lines{
		let tokens: Vec<&str> = clause_line.split_whitespace().collect();
		let tokens_len = tokens.len();
		if tokens_len < 2 {
			return Err(format!("Invalid clause, clause should have at least one literal: {}",clause_line))
		}
		let mut clause = Clause::new();
		for i in 0..tokens_len-1 {
			let mut var_index = i64::from_str_radix(tokens[i], 10).map_err(|_| format!("Invalid literal: {}",clause_line))?;
			if var_index == 0 {
				break
			}
			
			let negative = if var_index < 0 {true} else {false};
			var_index = (var_index).abs();
			var_index-= 1;
			let variable = variables.get(var_index as usize).unwrap();
			let literal = Literal::new(variable.clone(),negative);
			clause.add_literal(literal).expect(format!("Same literal more than once: {}",clause_line).as_str());
		}
		clauses.push(clause);
	}
	
	Ok(Formula::from_clauses(clauses, variables))
}

#[cfg(test)]
mod tests{
	use super::*;
	
	#[test]
    fn parses_valid_dimacs() {
        let input = r#"
c comment
p cnf 3 2
1 -2 0
2 3 0
"#;

        let formula = parse_dimacs(input).unwrap();

        assert_eq!(formula.get_variables().len(), 3);
        assert_eq!(formula.get_clauses().len(), 2);
    }

    #[test]
    fn rejects_missing_cnf_header_type() {
        let input = r#"
p sat 3 2
1 -2 0
2 3 0
"#;

        let err = parse_dimacs(input).unwrap_err();
        assert!(err.contains("Expected \"cnf\""));
    }

    #[test]
    fn rejects_multiple_problem_lines() {
        let input = r#"
p cnf 3 2
p cnf 3 2
1 -2 0
2 3 0
"#;

        let err = parse_dimacs(input).unwrap_err();
        assert!(err.contains("Multiple problem lines"));
    }

    #[test]
    fn rejects_zero_variable_count() {
        let input = r#"
p cnf 0 2
1 -2 0
2 3 0
"#;

        let err = parse_dimacs(input).unwrap_err();
        assert!(err.contains("Invalid variable count"));
    }

    #[test]
    fn rejects_short_clause() {
        let input = r#"
p cnf 3 1
0
"#;

        let err = parse_dimacs(input).unwrap_err();
        assert!(err.contains("Invalid clause"));
    }
}
