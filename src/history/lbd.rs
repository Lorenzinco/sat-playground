use super::History;
use crate::formula::literal::Literal;

#[derive(Default)]
pub(super) struct LevelCounter {
    stamps: Vec<u32>,
    epoch: u32,
    distinct: i16,
}

impl LevelCounter {
    pub(super) fn begin(&mut self) {
        if self.epoch == u32::MAX {
            self.stamps.fill(0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
        self.distinct = 0;
    }

    pub(super) fn insert(&mut self, level: usize) {
        if level >= self.stamps.len() {
            self.stamps.resize(level + 1, 0);
        }
        if self.stamps[level] != self.epoch {
            self.stamps[level] = self.epoch;
            self.distinct = self.distinct.saturating_add(1);
        }
    }

    pub(super) fn lbd(&self) -> i16 {
        self.distinct
    }

    fn count_bounded(&mut self, levels: impl IntoIterator<Item = usize>, limit: i16) -> i16 {
        debug_assert!(limit > 0);
        self.begin();
        for level in levels {
            self.insert(level);
            if self.distinct >= limit {
                break;
            }
        }
        self.lbd()
    }
}

impl History {
    /// Exact below `limit`; otherwise returns `limit` as soon as no improvement is possible.
    pub(super) fn clause_lbd_bounded(&self, literals: &[Literal], limit: i16) -> i16 {
        self.lbd_scratch.borrow_mut().count_bounded(
            literals
                .iter()
                .filter_map(|literal| self.get_literal_level(literal)),
            limit,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::clause::Clause;

    #[test]
    fn counter_matches_hashset_with_duplicates_growth_and_saturation() {
        let mut counter = LevelCounter::default();
        for levels in [
            vec![],
            vec![0, 0, 7, 7, 2, 0],
            (0..i16::MAX as usize + 10).collect(),
            vec![7, 0, 7],
        ] {
            counter.begin();
            for &level in &levels {
                counter.insert(level);
            }
            assert_eq!(counter.lbd(), Clause::calculate_lbd(levels.iter().copied()));
            for limit in [1, 2, 7, i16::MAX] {
                assert_eq!(
                    counter.count_bounded(levels.iter().copied(), limit),
                    Clause::calculate_lbd(levels.iter().copied()).min(limit),
                );
            }
        }
    }

    #[test]
    fn bounded_count_stops_at_threshold_and_resets_after_early_exit() {
        let mut counter = LevelCounter::default();
        let levels = [0, 0, 3, 3, 5].into_iter().chain(std::iter::once_with(|| {
            panic!("counting continued beyond the third distinct level")
        }));
        assert_eq!(counter.count_bounded(levels, 3), 3);
        assert_eq!(counter.count_bounded([5, 3, 0, 5], 10), 3);
        assert_eq!(counter.count_bounded([], 10), 0);
        assert_eq!(counter.count_bounded([0], 1), 1);
    }

    #[test]
    fn epoch_wrap_clears_old_stamps_and_reuses_storage() {
        let mut counter = LevelCounter::default();
        assert_eq!(counter.count_bounded([0, 10], 3), 2);
        let capacity = counter.stamps.capacity();
        counter.epoch = u32::MAX - 1;
        assert_eq!(counter.count_bounded([5], 1), 1);
        assert_eq!(counter.count_bounded([0, 5, 10, 0], 4), 3);
        assert_eq!(counter.epoch, 1);
        assert_eq!(counter.stamps.capacity(), capacity);
        assert_eq!(counter.count_bounded([10, 5], 4), 2);
    }
}
