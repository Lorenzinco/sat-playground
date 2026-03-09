pub mod csp;

use crate::formula::Formula;



pub trait Problem: Clone {
	fn reduction(&self)->Formula;
}