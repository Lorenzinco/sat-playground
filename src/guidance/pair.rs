use std::fmt;

/// A canonical pair of signed DIMACS literals. AND operands are commutative.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct Pair {
    pub(crate) first: i32,
    pub(crate) second: i32,
}

impl Pair {
    pub(crate) fn new(left: i32, right: i32) -> Self {
        if left <= right {
            Self {
                first: left,
                second: right,
            }
        } else {
            Self {
                first: right,
                second: left,
            }
        }
    }

    pub(crate) fn tuple(self) -> (i32, i32) {
        (self.first, self.second)
    }
}

impl fmt::Display for Pair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.first, self.second)
    }
}

#[cfg(test)]
mod tests {
    use super::Pair;

    #[test]
    fn pair_is_commutative() {
        assert_eq!(Pair::new(7, -3), Pair::new(-3, 7));
    }

    #[test]
    fn signs_are_part_of_the_pair() {
        assert_ne!(Pair::new(2, 5), Pair::new(-2, 5));
        assert_eq!(Pair::new(-2, -2).tuple(), (-2, -2));
    }
}
