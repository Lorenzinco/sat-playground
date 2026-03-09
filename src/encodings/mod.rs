pub mod csp;

use crate::formula::Formula;
use crate::problems::csp::Csp;

pub trait CspEncoding {
	fn encode(&self, csp: &Csp) -> Formula;
}