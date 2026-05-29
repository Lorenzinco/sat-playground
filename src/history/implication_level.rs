use crate::formula::literal::Literal;

pub struct ImplicationLevels {
    levels_by_var: Vec<Option<usize>>,
}

impl ImplicationLevels {
    pub fn new() -> Self {
        Self {
            levels_by_var: Vec::new(),
        }
    }

    pub fn set_level(&mut self, lit: &Literal, level: usize) {
        let var = lit.get_index().unsigned_abs() as usize;
        if var >= self.levels_by_var.len() {
            self.levels_by_var.resize(var + 1, None);
        }
        self.levels_by_var[var] = Some(level);
    }

    pub fn get_level(&self, lit: &Literal) -> Option<usize> {
        self.levels_by_var
            .get(lit.get_index().unsigned_abs() as usize)
            .copied()
            .flatten()
    }

    pub fn unset_level(&mut self, lit: &Literal) {
        if let Some(level) = self
            .levels_by_var
            .get_mut(lit.get_index().unsigned_abs() as usize)
        {
            *level = None;
        }
    }
}
