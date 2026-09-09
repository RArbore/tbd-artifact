use hashbrown::HashMap;

use crate::ssa::SSAId;

// A version is a layer of a layered union find. Each layer of the layered union find is "just" a
// union find over the canonical IDs of the parent union find. Versions form a hierarchy.
#[derive(Debug, Default)]
pub struct Version {
    uf: SparseUnionFind,
}

// We use a sparse representation for union finds, because in the majority of versions there are
// relatively few unions compared to the number of SSAIds. We use Rem's algorithm for unions and
// store sibling pointers for set traversal (each set corresponds to a circular linked list).
#[derive(Debug, Default)]
struct SparseUnionFind {
    parents: HashMap<SSAId, SSAId>,
    siblings: HashMap<SSAId, SSAId>,
}

#[derive(Debug)]
struct SparseUnionFindSet<'a> {
    start: SSAId,
    curr: Option<SSAId>,
    uf: &'a SparseUnionFind,
}

impl SparseUnionFind {
    fn parent(&self, id: SSAId) -> SSAId {
        self.parents.get(&id).cloned().unwrap_or(id)
    }

    fn set_parent(&mut self, id: SSAId, parent: SSAId) {
        if id != parent {
            self.parents.insert(id, parent);
        }
    }

    fn sibling(&self, id: SSAId) -> SSAId {
        self.siblings.get(&id).cloned().unwrap_or(id)
    }

    fn set_sibling(&mut self, id: SSAId, sibling: SSAId) {
        if id != sibling {
            self.siblings.insert(id, sibling);
        }
    }

    fn exchange_siblings(&mut self, x: SSAId, y: SSAId) {
        let sx = self.sibling(x);
        let sy = self.sibling(y);
        self.set_sibling(x, sy);
        self.set_sibling(y, sx);
    }

    fn find(&mut self, mut id: SSAId) -> SSAId {
        let mut p = self.parent(id);
        while p != id {
            let gp = self.parent(p);
            self.set_parent(id, gp);
            id = p;
            p = gp;
        }
        id
    }

    fn union(&mut self, mut x: SSAId, mut y: SSAId) -> SSAId {
        loop {
            let px = self.parent(x);
            let py = self.parent(y);
            if px == py {
                // Union was already represented, so don't exchange siblings.
                break px;
            }

            if px > py {
                if x == px {
                    self.set_parent(x, py);
                    self.exchange_siblings(x, y);
                    break self.find(py);
                }
                self.set_parent(x, py);
                x = px;
            } else {
                if y == py {
                    self.set_parent(y, px);
                    self.exchange_siblings(x, y);
                    break self.find(px);
                }
                self.set_parent(y, px);
                y = py;
            }
        }
    }

    fn set(&self, id: SSAId) -> impl Iterator<Item = SSAId> + '_ {
        SparseUnionFindSet {
            start: id,
            curr: Some(id),
            uf: self,
        }
    }
}

impl Iterator for SparseUnionFindSet<'_> {
    type Item = SSAId;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(curr) = self.curr {
            let sibling = self.uf.sibling(curr);
            if sibling == self.start {
                self.curr = None;
            } else {
                self.curr = Some(sibling);
            }
            Some(curr)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use hashbrown::HashSet;

    use super::SparseUnionFind;

    #[test]
    fn uf1() {
        let mut uf = SparseUnionFind::default();
        assert_eq!(uf.union(0, 4), 0);
        assert_eq!(uf.union(1, 3), 1);
        assert_eq!(uf.union(2, 5), 2);
        assert_eq!(uf.union(5, 9), 2);
        assert_eq!(uf.find(0), 0);
        assert_eq!(uf.find(4), 0);
        assert_eq!(uf.find(1), 1);
        assert_eq!(uf.find(3), 1);
        assert_eq!(uf.find(2), 2);
        assert_eq!(uf.find(5), 2);
        assert_eq!(uf.find(9), 2);
        assert_eq!(
            HashSet::from_iter([0, 4]),
            uf.set(4).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([1, 3]),
            uf.set(1).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([2, 5, 9]),
            uf.set(5).collect::<HashSet<_>>()
        );

        assert_eq!(uf.union(4, 5), 0);
        assert_eq!(uf.find(2), 0);
        assert_eq!(uf.find(5), 0);
        assert_eq!(uf.find(9), 0);
        assert_eq!(
            HashSet::from_iter([0, 2, 4, 5, 9]),
            uf.set(9).collect::<HashSet<_>>()
        );
    }

    #[test]
    fn uf2() {
        let mut uf = SparseUnionFind::default();
        for i in 0..100 {
            assert_ne!(uf.find(i), uf.find(i + 1));
            assert_eq!(uf.find(i), i);
        }
        for i in 0..100 {
            assert_eq!(uf.union(i, i + 1), 0);
        }
        for i in 0..100 {
            assert_eq!(uf.find(i), uf.find(i + 1));
        }
        for i in 100..200 {
            assert_ne!(uf.find(i), uf.find(i + 1));
        }
    }
}
