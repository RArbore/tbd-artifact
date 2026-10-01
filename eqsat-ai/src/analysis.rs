use core::fmt::{Display, Formatter, Result};
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

use crate::trie::TupleValue;

// Per bit, the mapping is:
// - low_high: 0, concrete: 0 -> bot
// - low_high: 0, concrete: 1 -> 0
// - low_high: 1, concrete: 1 -> 1
// - low_high: 1, concrete: 0 -> top
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KnownBits {
    pub low_high: i64,
    pub concrete: i64,
}

impl KnownBits {
    pub fn bot() -> Self {
        Self {
            low_high: 0,
            concrete: 0,
        }
    }

    pub fn top() -> Self {
        Self {
            low_high: !0,
            concrete: 0,
        }
    }

    pub fn from_constant(cons: i64) -> Self {
        Self {
            low_high: cons,
            concrete: !0,
        }
    }

    pub fn try_constant(&self) -> Option<i64> {
        if (self.low_high & !self.concrete) != 0 {
            // If any bit is top, then this isn't a constant.
            None
        } else {
            // Arbitrarily view bot bits as 0.
            Some(self.low_high)
        }
    }

    pub fn is_constant(&self, cons: i64) -> bool {
        self.leq(&KnownBits::from_constant(cons))
    }

    pub fn contains_constant(&self, cons: i64) -> bool {
        KnownBits::from_constant(cons).leq(self)
    }

    pub fn flip(&self) -> Self {
        // Flip the not concrete bits.
        Self {
            low_high: self.low_high ^ !self.concrete,
            concrete: self.concrete,
        }
    }

    pub fn meet(&self, other: &Self) -> Self {
        // This implements the following table:
        // |  s.lh |  s.ic |  o.lh |  o.ic |  r.lh |  r.ic |
        // -------------------------------------------------
        // |   0   |   0   |   _   |   _   |   0   |   0   |
        // |   _   |   _   |   0   |   0   |   0   |   0   |
        // |   1   |   0   |   a   |   b   |   a   |   b   |
        // |   a   |   b   |   1   |   0   |   a   |   b   |
        // |   a   |   1   |   a   |   1   |   a   |   1   |
        // |   a   |   1   |   b   |   1   |   0   |   0   |   if a != b
        let lh3 = self.low_high & !self.concrete & other.low_high;
        let ic3 = self.low_high & !self.concrete & other.concrete;
        let lh4 = other.low_high & !other.concrete & self.low_high;
        let ic4 = other.low_high & !other.concrete & self.concrete;
        let lh5 = self.low_high & other.low_high & self.concrete & other.concrete;
        let ic5 = !(self.low_high ^ other.low_high) & self.concrete & other.concrete;
        Self {
            low_high: lh3 | lh4 | lh5,
            concrete: ic3 | ic4 | ic5,
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        self.flip().meet(&other.flip()).flip()
    }

    pub fn leq(&self, other: &Self) -> bool {
        // In a lattice, we know that...
        // a <= b iff b = join(a, b) iff a = meet(a, b)
        let first = *other == self.join(other);
        let second = *self == self.meet(other);
        assert_eq!(first, second);
        first
    }

    pub fn neg(&self) -> Self {
        // TODO: make non-trivial.
        Self::top()
    }

    pub fn bitwise_not(&self) -> Self {
        // Flip the concrete bits.
        Self {
            low_high: self.low_high ^ self.concrete,
            concrete: self.concrete,
        }
    }

    pub fn add(&self, _other: &Self) -> Self {
        // TODO: make non-trivial.
        Self::top()
    }

    pub fn sub(&self, _other: &Self) -> Self {
        // TODO: make non-trivial.
        Self::top()
    }

    pub fn mul(&self, _other: &Self) -> Self {
        // TODO: make non-trivial.
        Self::top()
    }

    pub fn bitwise_and(&self, other: &Self) -> Self {
        // This implements the following table:
        // |  s.lh |  s.ic |  o.lh |  o.ic |  r.lh |  r.ic |
        // -------------------------------------------------
        // |   a   |   1   |   b   |   1   | a & b |   1   |
        // |   a   |   0   |   b   |   0   | a & b |   0   |
        // |   0   |   0   |   _   |   1   |   0   |   0   |
        // |   1   |   0   |   0   |   1   |   0   |   1   |
        // |   1   |   0   |   1   |   1   |   1   |   0   |
        // |   _   |   1   |   0   |   0   |   0   |   0   |
        // |   0   |   1   |   1   |   0   |   0   |   1   |
        // |   1   |   1   |   1   |   0   |   1   |   0   |
        let lh1 = self.concrete & other.concrete & self.low_high & other.low_high;
        let ic1 = self.concrete & other.concrete;
        let lh2 = !self.concrete & !other.concrete & self.low_high & other.low_high;
        let ic4 = self.low_high & !self.concrete & !other.low_high & other.concrete;
        let lh5 = self.low_high & !self.concrete & other.low_high & other.concrete;
        let ic7 = !self.low_high & self.concrete & other.low_high & !other.concrete;
        let lh8 = self.low_high & self.concrete & other.low_high & !other.concrete;
        Self {
            low_high: lh1 | lh2 | lh5 | lh8,
            concrete: ic1 | ic4 | ic7,
        }
    }

    pub fn bitwise_or(&self, other: &Self) -> Self {
        self.bitwise_not()
            .bitwise_and(&other.bitwise_not())
            .bitwise_not()
    }

    pub fn bitwise_xor(&self, other: &Self) -> Self {
        self.bitwise_and(&other.bitwise_not())
            .bitwise_or(&self.bitwise_not().bitwise_and(&other))
    }
}

impl Default for KnownBits {
    fn default() -> Self {
        Self::top()
    }
}

impl Display for KnownBits {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for i in (0..64).rev() {
            match ((self.low_high >> i) & 1, (self.concrete >> i) & 1) {
                (0, 0) => write!(f, "⊥")?,
                (_, 0) => write!(f, "⊤")?,
                (0, _) => write!(f, "0")?,
                (_, _) => write!(f, "1")?,
            }
        }
        Ok(())
    }
}

pub trait CommutativeMonoid: Clone + PartialEq + Eq {
    fn identity() -> Self;
    fn plus(&self, other: &Self) -> Self;
}

impl CommutativeMonoid for () {
    fn identity() -> Self {
        ()
    }

    fn plus(&self, _: &Self) -> Self {
        ()
    }
}

impl CommutativeMonoid for usize {
    fn identity() -> Self {
        0
    }

    fn plus(&self, other: &Self) -> Self {
        *self + *other
    }
}

impl CommutativeMonoid for KnownBits {
    fn identity() -> Self {
        Self::top()
    }

    fn plus(&self, other: &Self) -> Self {
        self.meet(other)
    }
}

impl<A: CommutativeMonoid, B: CommutativeMonoid> CommutativeMonoid for (A, B) {
    fn identity() -> Self {
        (A::identity(), B::identity())
    }

    fn plus(&self, other: &Self) -> Self {
        (self.0.plus(&other.0), self.1.plus(&other.1))
    }
}

// Global intern tables for analysis values.
type Interner<T> = (HashMap<T, TupleValue>, Vec<T>);
static KB_INTERN: LazyLock<Mutex<Interner<KnownBits>>> =
    LazyLock::new(|| Mutex::new(Default::default()));

pub fn intern_kb(kb: KnownBits) -> TupleValue {
    let mut interner = KB_INTERN.lock().unwrap();
    let interner: &mut Interner<KnownBits> = &mut interner;
    let entry = interner.0.entry(kb);
    *entry.or_insert_with(|| {
        let id = interner.1.len();
        interner.1.push(kb);
        id as TupleValue
    })
}

pub fn get_kb(id: TupleValue) -> KnownBits {
    KB_INTERN.lock().unwrap().1[id as usize]
}
