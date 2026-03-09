use crate::problems::csp::Csp;
use crate::formula::Formula;

#[derive(Clone, Debug)]
pub enum CspReductions{
	Log,
	Direct,
	Support,
}

pub trait LogEncoding {
	fn encode(&self)->Formula;
}

pub trait DirectEncoding {
	fn encode(&self)->Formula;
}

pub trait SupportEncoding {
	fn encode(&self)->Formula;
}

impl LogEncoding for Csp {
	fn encode(&self)->Formula {
		return Formula::new()
	}
}

impl DirectEncoding for Csp {
	fn encode(&self)->Formula {
		return Formula::new()
	}
}

impl SupportEncoding for Csp {
	fn encode(&self)->Formula {
		return Formula::new()
	}
}