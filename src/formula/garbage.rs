use fastbit::{BitRead, BitVec, BitWrite};

pub struct Garbage {
    bitvec: BitVec<u8>,
    count: usize,
}

impl Clone for Garbage {
    fn clone(&self) -> Self {
        let mut clone = Self::new(self.len());
        for index in self.to_delete() {
            clone.delete(index);
        }
        clone
    }
}

impl Garbage {
    pub fn new(size: usize) -> Self {
        Self {
            bitvec: BitVec::new(size),
            count: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.bitvec.len()
    }

    pub fn count(&self) -> usize {
        self.count
    }

    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    pub fn push_live(&mut self) {
        self.bitvec.resize(self.len() + 1);
    }

    /// Marks an index as garbage and returns whether it was newly marked.
    pub fn delete(&mut self, clause_index: usize) -> bool {
        assert!(clause_index < self.len(), "clause index out of bounds");
        if self.bitvec.test(clause_index) {
            return false;
        }

        self.bitvec.set(clause_index);
        self.count += 1;
        true
    }

    /// Marks a batch and returns the number of newly marked indexes.
    pub fn delete_batch(&mut self, clause_indexes: &[usize]) -> usize {
        clause_indexes
            .iter()
            .filter(|&&index| self.delete(index))
            .count()
    }

    #[inline]
    pub fn is_garbage(&self, clause_index: usize) -> bool {
        self.count != 0 && clause_index < self.len() && self.bitvec.test(clause_index)
    }

    pub fn reset(&mut self, size: usize) {
        self.bitvec = BitVec::new(size);
        self.count = 0;
    }

    pub fn to_delete(&self) -> Vec<usize> {
        (0..self.len())
            .filter(|&index| self.bitvec.test(index))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deletion_is_idempotent_and_counted_once() {
        let mut garbage = Garbage::new(4);

        assert!(garbage.delete(2));
        assert!(!garbage.delete(2));
        assert_eq!(garbage.count(), 1);
        assert_eq!(garbage.to_delete(), vec![2]);
    }

    #[test]
    fn batch_delete_and_push_live_preserve_slot_indexes() {
        let mut garbage = Garbage::new(2);
        garbage.push_live();

        assert_eq!(garbage.len(), 3);
        assert_eq!(garbage.delete_batch(&[0, 2, 2]), 2);
        assert!(garbage.is_garbage(0));
        assert!(!garbage.is_garbage(1));
        assert!(garbage.is_garbage(2));
        assert!(!garbage.is_garbage(3));
    }

    #[test]
    fn reset_clears_marks_and_sets_the_compacted_size() {
        let mut garbage = Garbage::new(5);
        garbage.delete_batch(&[1, 4]);

        garbage.reset(3);

        assert_eq!(garbage.len(), 3);
        assert!(garbage.is_empty());
        assert_eq!(garbage.to_delete(), Vec::<usize>::new());
    }
}
