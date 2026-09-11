use std::collections::{HashMap, HashSet};

use crate::ssa::{SSA, SSAId};

// The relational tuple representation is separate from the hashcons, so this doesn't have to be the
// same type as SSAId.
pub type TupleValue = u32;

pub fn tuple_field(id: SSAId, ssa: SSA, column: usize) -> TupleValue {
    if column == 0 {
        return id as TupleValue;
    }
    use SSA::*;
    match ssa {
        Constant(cons) => {
            assert_eq!(column, 1);
            cons as TupleValue
        }
        Param(idx) => {
            assert_eq!(column, 1);
            idx as TupleValue
        }
        Unary(_, input) => {
            assert_eq!(column, 1);
            input as TupleValue
        }
        Binary(_, lhs, rhs) => {
            if column == 1 {
                lhs as TupleValue
            } else {
                assert_eq!(column, 2);
                rhs as TupleValue
            }
        }
        Knot(id) => {
            assert_eq!(column, 1);
            id as TupleValue
        }
    }
}

// For now, we use the dumbest possible implementation of a trie - each internal node stores a
// separately allocated hash map mapping tuple values to other trie nodes. We store the *non-
// canonical* SSAIds of inserted nodes into the leaf nodes of the trie.
#[derive(Debug, PartialEq, Eq)]
pub enum Trie {
    Internal(HashMap<TupleValue, Trie>),
    Leaf(HashSet<SSAId>),
}

impl Trie {
    pub fn try_internal(&self) -> Option<&HashMap<TupleValue, Trie>> {
        use Trie::*;
        match self {
            Internal(map) => Some(map),
            Leaf(_) => None,
        }
    }

    pub fn try_leaf(&self) -> Option<&HashSet<SSAId>> {
        use Trie::*;
        match self {
            Internal(_) => None,
            Leaf(set) => Some(set),
        }
    }
    
    pub fn insert_tuple<I>(&mut self, mut iter: I, id: SSAId)
    where
        I: Iterator<Item = TupleValue>,
    {
        use Trie::*;
        let mut it = self;
        while let Some(value) = iter.next() {
            let Internal(node) = it else { panic!() };
            it = node.entry(value).or_insert(Trie::default());
        }
        match it {
            Internal(map) => {
                assert!(map.is_empty());
                *it = Leaf(HashSet::from_iter([id]));
            }
            Leaf(ids) => {
                ids.insert(id);
            }
        }
    }
}

impl Default for Trie {
    fn default() -> Self {
        Self::Internal(Default::default())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use super::Trie;

    #[test]
    fn trie1() {
        let mut trie1 = Trie::default();
        trie1.insert_tuple([0, 1].into_iter(), 7);
        trie1.insert_tuple([0, 2].into_iter(), 42);
        trie1.insert_tuple([0, 2].into_iter(), 43);
        assert_eq!(
            trie1,
            Trie::Internal(HashMap::from_iter([(
                0,
                Trie::Internal(HashMap::from_iter([
                    (1, Trie::Leaf(HashSet::from_iter([7]))),
                    (2, Trie::Leaf(HashSet::from_iter([42, 43])))
                ]))
            )]))
        );

        let mut trie2 = Trie::default();
        trie2.insert_tuple([0, 2].into_iter(), 43);
        trie2.insert_tuple([0, 2].into_iter(), 42);
        trie2.insert_tuple([0, 1].into_iter(), 7);
        assert_eq!(trie1, trie2);
    }

    #[test]
    #[should_panic]
    fn trie2() {
        let mut trie = Trie::default();
        trie.insert_tuple([0, 2].into_iter(), 9);
        trie.insert_tuple([0, 2, 3].into_iter(), 42);
    }
}
