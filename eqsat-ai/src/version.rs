use hashbrown::HashMap;

use crate::ssa::SSAId;

// A version is a layer of a layered union find. Each layer of the layered union find is "just" a
// union find over the canonical IDs of the parent union find. Versions form a hierarchy.
#[derive(Debug, Default)]
pub struct Version {
    uf: SparseUnionFind,
}

// We use a sparse representation for union finds, because in the majority of versions there are
// relatively few unions compared to the number of SSAIds.
#[derive(Debug, Default)]
struct SparseUnionFind {
    parents: HashMap<SSAId, SSAId>,
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
                break px;
            }

            if px > py {
                if x == px {
                    self.set_parent(x, py);
                    break self.find(py);
                }
                self.set_parent(x, py);
                x = px;
            } else {
                if y == py {
                    self.set_parent(y, px);
                    break self.find(px);
                }
                self.set_parent(y, px);
                y = py;
            }
        }
    }
}

#[cfg(test)]
mod tests {
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
        assert_eq!(uf.union(4, 5), 0);
        assert_eq!(uf.find(2), 0);
        assert_eq!(uf.find(5), 0);
        assert_eq!(uf.find(9), 0);
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
