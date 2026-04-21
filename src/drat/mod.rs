use std::io::Write;
use std::io;
use crate::formula::literal::Literal;

pub struct DratLogger<W:Write> {
    writer: W
}

impl <W: Write> DratLogger<W> {
    pub fn new(writer:W) -> Self {
        Self{ writer: writer }
    }
    
    // DIMACS variables are 1-indexed. Adjust the `+ 1` if your variable_index is already 1-based.
    fn lit_to_dimacs(lit: &Literal) -> i64 {
        let var = (lit.get_index() + 1) as i64;
        if lit.is_negated() { -var } else { var }
    }

    /// Logs a learned clause or a preprocessed clause.
    pub fn log_add(&mut self, clause: &[Literal]) -> io::Result<()> {
        for lit in clause {
            write!(self.writer, "{} ", Self::lit_to_dimacs(lit))?;
        }
        writeln!(self.writer, "0")
    }

    /// Logs the deletion of a clause (e.g., during database reduction).
    pub fn log_delete(&mut self, clause: &[Literal]) -> io::Result<()> {
        write!(self.writer, "d ")?;
        for lit in clause {
            write!(self.writer, "{} ", Self::lit_to_dimacs(lit))?;
        }
        writeln!(self.writer, "0")
    }

    /// Logs the final empty clause to signify UNSAT.
    pub fn log_empty_clause(&mut self) -> io::Result<()> {
        writeln!(self.writer, "0")
    }
}