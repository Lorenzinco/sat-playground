use crate::encodings::csp::*;
use crate::formula::Formula;
use crate::problems::Problem;
use std::cell::RefCell;
use std::rc::Rc;

/// A variable of a CSP.
///
/// Each variable has:
/// - an `index` identifying it inside the CSP
/// - a `domain` representing the finite set of values it may take.
#[derive(Clone, Debug)]
pub struct CspVariable {
	/// Index of the variable in the CSP variable vector.
	pub index: usize,

	/// Finite domain of values the variable may take.
	pub domain: Vec<i64>,
}

impl CspVariable {
	/// Creates a new CSP variable with the given index and domain.
	///
	/// # Arguments
	///
	/// * `index` - Position of the variable in the CSP.
	/// * `domain` - Finite set of allowed values.
	pub fn new(index: usize, domain: Vec<i64>) -> Self {
		Self { index, domain }
	}
}

/// Symbolic relation describing the semantics of a CSP constraint.
///
/// The relation defines how the variables in the constraint scope interact.
/// This representation is **intensional**, meaning it describes the relation
/// symbolically instead of enumerating all allowed/forbidden tuples.
#[derive(Clone, Debug)]
pub enum CspRelation {
	/// Equality constraint: `x = y`
	Equal,

	/// Inequality constraint: `x ≠ y`
	NotEqual,

	/// Strict ordering: `x < y`
	LessThan,

	/// Non-strict ordering: `x ≤ y`
	LessEqual,

	/// Strict ordering: `x > y`
	GreaterThan,

	/// Non-strict ordering: `x ≥ y`
	GreaterEqual,

	/// Linear equality constraint:
	///
	/// `a₁x₁ + a₂x₂ + ... + aₙxₙ = rhs`
	LinearEq {
			coeffs: Vec<i64>,
			rhs: i64,
	},

	/// Linear inequality constraint:
	///
	/// `a₁x₁ + a₂x₂ + ... + aₙxₙ ≤ rhs`
	LinearLeq {
			coeffs: Vec<i64>,
			rhs: i64,
	},

	/// Linear inequality constraint:
	///
	/// `a₁x₁ + a₂x₂ + ... + aₙxₙ ≥ rhs`
	LinearGeq {
			coeffs: Vec<i64>,
			rhs: i64,
	},

	/// Sum equality constraint:
	///
	/// `x₁ + x₂ + ... + xₙ = rhs`
	SumEq {
			rhs: i64,
	},

	/// Sum inequality constraint:
	///
	/// `x₁ + x₂ + ... + xₙ ≤ rhs`
	SumLeq {
			rhs: i64,
	},

	/// Sum inequality constraint:
	///
	/// `x₁ + x₂ + ... + xₙ ≥ rhs`
	SumGeq {
			rhs: i64,
	},

	/// Global constraint requiring all variables in the scope
	/// to take pairwise distinct values.
	AllDifferent,

	/// Generic relation defined by a symbolic name and parameters.
	///
	/// Useful when parsing external CSP formats that contain
	/// domain-specific constraints.
	Custom {
			name: String,
			params: Vec<i64>,
	},
}

/// A CSP constraint.
///
/// A constraint is defined by:
///
/// - a **scope**: the variables involved
/// - a **relation**: how those variables interact
///
/// This is the canonical `(scope, relation)` representation of CSP constraints.
#[derive(Clone, Debug)]
pub struct CspConstraint {
		/// Variables participating in the constraint.
		pub scope: Vec<Rc<RefCell<CspVariable>>>,

		/// Relation describing the allowed combinations.
		pub relation: CspRelation,
}

impl CspConstraint {
	/// Creates a new constraint with validation.
	///
	/// The function verifies that the relation is compatible with
	/// the scope size (e.g. binary relations require two variables).
	pub fn new(
		scope: Vec<Rc<RefCell<CspVariable>>>,
		relation: CspRelation,
	) -> Result<Self, String> {
		if scope.is_empty() {
				return Err("constraint scope cannot be empty".to_string());
		}

		match &relation {
			CspRelation::Equal
			| CspRelation::NotEqual
			| CspRelation::LessThan
			| CspRelation::LessEqual
			| CspRelation::GreaterThan
			| CspRelation::GreaterEqual => {
				if scope.len() != 2 {
					return Err("binary relation requires exactly 2 variables".to_string());
				}
			}

			CspRelation::LinearEq { coeffs, .. }
			| CspRelation::LinearLeq { coeffs, .. }
			| CspRelation::LinearGeq { coeffs, .. } => {
				if coeffs.len() != scope.len() {
					return Err(format!(
						"number of coefficients ({}) must match scope length ({})",
						coeffs.len(),
						scope.len()
					));
				}
			}

			CspRelation::AllDifferent => {
				if scope.len() < 2 {
					return Err("AllDifferent requires at least 2 variables".to_string());
				}
			}

			CspRelation::SumEq { .. }
			| CspRelation::SumLeq { .. }
			| CspRelation::SumGeq { .. }
			| CspRelation::Custom { .. } => {}
		}

			Ok(Self { scope, relation })
	}

	/// Returns the number of variables participating in the constraint.
	pub fn arity(&self) -> usize {
		self.scope.len()
	}

	/// Returns `true` if the constraint is binary.
	pub fn is_binary(&self) -> bool {
		self.scope.len() == 2
	}

	/// Returns the indices of all variables in the constraint scope.
	pub fn variable_indices(&self) -> Vec<usize> {
		self.scope.iter().map(|v| v.borrow().index).collect()
	}
}

/// A full Constraint Satisfaction Problem instance.
///
/// A CSP consists of:
///
/// - a set of variables
/// - a set of constraints
/// - a chosen SAT reduction method
#[derive(Clone, Debug)]
pub struct Csp {
	/// All variables in the CSP.
	variables: Vec<Rc<RefCell<CspVariable>>>,

	/// List of constraints.
	clauses: Vec<CspConstraint>,

	/// Selected encoding used when converting the CSP to SAT.
	reduction_kind: CspReductions,
}

impl Problem for Csp {
	/// Reduces the CSP instance into a SAT formula
	/// using the selected encoding.
	fn reduction(&self) -> Formula {
		match self.reduction_kind {
			CspReductions::Log => <Csp as LogEncoding>::encode(self),
			CspReductions::Direct => <Csp as DirectEncoding>::encode(self),
			CspReductions::Support => <Csp as SupportEncoding>::encode(self),
		}
	}
}

impl Csp {
	/// Creates an empty CSP instance.
	pub fn new() -> Self {
		Self {
			variables: vec![],
			clauses: vec![],
			reduction_kind: CspReductions::Direct,
	}
	}

	/// Sets which SAT reduction should be used.
	pub fn set_reduction_type(&mut self, reduction: CspReductions) {
		self.reduction_kind = reduction
	}

	/// Adds a new variable with the specified domain.
	///
	/// Returns a reference-counted pointer to the created variable.
	pub fn add_variable(&mut self, domain: Vec<i64>) -> Rc<RefCell<CspVariable>> {
		let index = self.variables.len();
		let var = Rc::new(RefCell::new(CspVariable::new(index, domain)));
		self.variables.push(var.clone());
		
		var
	}

	/// Returns the variable with the given index if it exists.
	pub fn get_variable(&self, index: usize) -> Option<Rc<RefCell<CspVariable>>> {
		self.variables.get(index).cloned()
	}

	/// Returns all variables in the CSP.
	pub fn variables(&self) -> &[Rc<RefCell<CspVariable>>] {
		&self.variables
	}

	/// Returns all constraints of the CSP.
	pub fn constraints(&self) -> &[CspConstraint] {
		&self.clauses
	}

	/// Adds an already constructed constraint to the CSP.
	pub fn add_constraint(&mut self, constraint: CspConstraint) {
		self.clauses.push(constraint);
	}

	/// Creates and adds a constraint directly from scope and relation.
	pub fn add_constraint_from_parts(
		&mut self,
		scope: Vec<Rc<RefCell<CspVariable>>>,
		relation: CspRelation,
	) -> Result<(), String> {
		let constraint = CspConstraint::new(scope, relation)?;
		self.clauses.push(constraint);
		Ok(())
	}

	/// Returns the number of variables in the CSP.
	pub fn num_variables(&self) -> usize {
		self.variables.len()
	}

	/// Returns the number of constraints in the CSP.
	pub fn num_constraints(&self) -> usize {
		self.clauses.len()
	}
}