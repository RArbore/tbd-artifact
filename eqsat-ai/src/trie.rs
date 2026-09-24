use std::collections::{HashMap, HashSet};

use crate::nonssa::Constant;
use crate::ssa::{SSA, SSAId};

// The relational tuple representation is separate from the hash-cons, so this doesn't have to be the
// same type as SSAId.
pub type TupleValue = u32;

impl Into<TupleValue> for Constant {
    fn into(self) -> TupleValue {
        match self {
            Constant::Bool(val) => val as TupleValue,
            Constant::I64(val) => val as TupleValue,
        }
    }
}

pub fn tuple_field(id: SSAId, ssa: SSA, column: usize) -> TupleValue {
    if column == 0 {
        return id as TupleValue;
    }
    use SSA::*;
    match ssa {
        Constant(cons) => {
            assert_eq!(column, 1);
            cons.into()
        }
        Param(idx, _) => {
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
        Knot(id, _) => {
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

    pub fn remove_tuple<I>(&mut self, mut iter: I, id: SSAId) -> bool
    where
        I: Iterator<Item = TupleValue>,
    {
        use Trie::*;
        if let Some(value) = iter.next() {
            let Internal(node) = self else { panic!() };
            if node.get_mut(&value).unwrap().remove_tuple(iter, id) {
                node.remove(&value);
                node.is_empty()
            } else {
                false
            }
        } else {
            let Leaf(ids) = self else { panic!() };
            assert!(ids.remove(&id));
            ids.is_empty()
        }
    }

    pub fn clear(&mut self) {
        *self = Trie::default();
    }
}

impl Default for Trie {
    fn default() -> Self {
        Self::Internal(Default::default())
    }
}
