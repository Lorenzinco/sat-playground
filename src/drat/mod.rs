use crate::formula::literal::Literal;
use std::io;
use std::io::Write;

pub struct DratLogger<W: Write> {
    writer: W,
}

impl<W: Write> DratLogger<W> {
    pub fn new(writer: W) -> Self {
        Self { writer: writer }
    }

    // Literals already carry their DIMACS index/sign (e.g., -3 for ¬x3).
    fn lit_to_dimacs(lit: &Literal) -> i64 {
        lit.get_index() as i64
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::literal::Literal;

    #[test]
    fn log_add_delete_empty_formats_dimacs() {
        let mut buf = Vec::new();
        let mut logger = DratLogger::new(&mut buf);

        let clause = vec![Literal::new(1), Literal::new(-3)];
        logger.log_add(&clause).unwrap();

        let del = vec![Literal::new(2)];
        logger.log_delete(&del).unwrap();

        logger.log_empty_clause().unwrap();

        let out = String::from_utf8(buf).unwrap();
        assert_eq!(out, "1 -3 0\nd 2 0\n0\n");
    }
}
