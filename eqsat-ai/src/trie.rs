use hashbrown::HashMap;

use crate::ssa::SSAId;

// The relational tuple representation is separate from the hashcons, so this doesn't have to be the
// same type as SSAId.
pub type TupleValue = u32;

// For now, we use the dumbest possible implementation of a trie - each internal node stores a
// separately allocated hash map mapping tuple values to other trie nodes.
#[derive(Debug, PartialEq, Eq)]
pub enum Trie {
    Internal(HashMap<TupleValue, Trie>),
    Leaf(SSAId),
}

impl Trie {
    pub fn new() -> Self {
        Self::Internal(Default::default())
    }

    pub fn insert_tuple<I>(&mut self, mut iter: I, id: SSAId)
    where
        I: Iterator<Item = TupleValue>,
    {
        use Trie::*;
        let mut it = self;
        while let Some(value) = iter.next() {
            let Internal(node) = it else { panic!() };
            it = node.entry(value).or_insert(Trie::new());
        }
        match it {
            Internal(map) => assert!(map.is_empty()),
            Leaf(old_id) => assert_eq!(id, *old_id),
        }
        *it = Leaf(id);
    }
}

#[cfg(test)]
mod tests {
    use hashbrown::HashMap;

    use super::Trie;

    #[test]
    fn trie1() {
        let mut trie1 = Trie::new();
        trie1.insert_tuple([0, 1].into_iter(), 7);
        trie1.insert_tuple([0, 2].into_iter(), 42);
        assert_eq!(
            trie1,
            Trie::Internal(HashMap::from_iter([(
                0,
                Trie::Internal(HashMap::from_iter([
                    (1, Trie::Leaf(7)),
                    (2, Trie::Leaf(42))
                ]))
            )]))
        );

        let mut trie2 = Trie::new();
        trie2.insert_tuple([0, 2].into_iter(), 42);
        trie2.insert_tuple([0, 1].into_iter(), 7);
        assert_eq!(trie1, trie2);
    }

    #[test]
    #[should_panic]
    fn trie2() {
        let mut trie = Trie::new();
        trie.insert_tuple([0, 2].into_iter(), 9);
        trie.insert_tuple([0, 2, 3].into_iter(), 42);
    }
}
