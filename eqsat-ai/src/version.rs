use std::rc::Rc;

use hashbrown::HashMap;

use crate::ssa::SSAId;

// We use a sparse representation for union finds, because in the majority of versions there are
// relatively few unions compared to the number of SSAIds. We use Rem's algorithm for unions and
// store sibling pointers for set traversal (each set corresponds to a circular linked list).
#[derive(Debug, Default)]
struct SparseUnionFind {
    parents: HashMap<SSAId, SSAId>,
    siblings: HashMap<SSAId, SSAId>,
}

// A version is a layer of a layered union find. Each layer of the layered union find is "just" a
// union find over the canonical IDs of the parent union find. Versions form a hierarchy. We get away
// with using a layered union find, rather than the more complicated versioned union find, because we
// only ever modify (at-the-moment) leaf versions.
#[derive(Debug, Default)]
pub struct Version {
    uf: SparseUnionFind,
    // Store a pointer to the parent version. This is ref-counted to simplify the code in the
    // abstract interpreter w.r.t. ownership of versions.
    parent: Option<Rc<Version>>,
}

#[derive(Debug)]
struct SparseUnionFindSet<'a> {
    start: SSAId,
    curr: Option<SSAId>,
    uf: &'a SparseUnionFind,
}

#[derive(Debug)]
struct VersionSet<'a> {
    set_stack: Vec<SparseUnionFindSet<'a>>,
    version_stack: Vec<&'a Version>,
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

    fn find(&self, mut id: SSAId) -> SSAId {
        loop {
            let p = self.parent(id);
            if p == id {
                break id;
            }
            id = p;
        }
    }

    fn find_mut(&mut self, mut id: SSAId) -> SSAId {
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
                    break self.find_mut(py);
                }
                self.set_parent(x, py);
                x = px;
            } else {
                if y == py {
                    self.set_parent(y, px);
                    self.exchange_siblings(x, y);
                    break self.find_mut(px);
                }
                self.set_parent(y, px);
                y = py;
            }
        }
    }

    fn set(&self, id: SSAId) -> SparseUnionFindSet<'_> {
        SparseUnionFindSet {
            start: id,
            curr: Some(id),
            uf: self,
        }
    }
}

impl Iterator for SparseUnionFindSet<'_> {
    type Item = SSAId;

    fn next(&mut self) -> Option<SSAId> {
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

impl Version {
    pub fn child(parent: Rc<Version>) -> Self {
        Self {
            uf: Default::default(),
            parent: Some(parent),
        }
    }

    pub fn find(&self, id: SSAId) -> SSAId {
        self.uf.find(
            self.parent
                .as_ref()
                .map(|parent| parent.find(id))
                .unwrap_or(id),
        )
    }

    pub fn find_mut(&mut self, id: SSAId) -> SSAId {
        self.uf.find_mut(
            self.parent
                .as_ref()
                .map(|parent| parent.find(id))
                .unwrap_or(id),
        )
    }

    pub fn union(&mut self, mut x: SSAId, mut y: SSAId) -> SSAId {
        if let Some(parent) = self.parent.as_ref() {
            x = parent.find(x);
            y = parent.find(y);
        }
        self.uf.union(x, y)
    }

    pub fn set(&self, id: SSAId) -> impl Iterator<Item = SSAId> + '_ {
        VersionSet {
            set_stack: vec![self.uf.set(self.find(id))],
            version_stack: vec![self],
        }
    }
}

impl Iterator for VersionSet<'_> {
    type Item = SSAId;

    fn next(&mut self) -> Option<SSAId> {
        loop {
            // Once all sets in the stack have been visited, this `?` will return `None`, breaking
            // out of the loop.
            let last_set = self.set_stack.last_mut()?;
            let last_version = *self.version_stack.last().unwrap();
            if let Some(id) = last_set.next() {
                if let Some(parent_version) = last_version.parent.as_ref() {
                    self.set_stack.push(parent_version.uf.set(id));
                    self.version_stack.push(parent_version);
                } else {
                    break Some(id);
                }
            } else {
                self.set_stack.pop();
                self.version_stack.pop();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use hashbrown::HashSet;

    use super::{SparseUnionFind, Version};

    #[test]
    fn uf1() {
        let mut uf = SparseUnionFind::default();
        assert_eq!(uf.union(0, 4), 0);
        assert_eq!(uf.union(1, 3), 1);
        assert_eq!(uf.union(2, 5), 2);
        assert_eq!(uf.union(5, 9), 2);
        assert_eq!(uf.union(2, 9), 2);
        assert_eq!(uf.find(0), 0);
        assert_eq!(uf.find(4), 0);
        assert_eq!(uf.find_mut(1), 1);
        assert_eq!(uf.find_mut(3), 1);
        assert_eq!(uf.find(2), 2);
        assert_eq!(uf.find_mut(5), 2);
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
        assert_eq!(uf.find_mut(2), 0);
        assert_eq!(uf.find(5), 0);
        assert_eq!(uf.find_mut(9), 0);
        assert_eq!(
            HashSet::from_iter([0, 2, 4, 5, 9]),
            uf.set(9).collect::<HashSet<_>>()
        );
    }

    #[test]
    fn uf2() {
        let mut uf = SparseUnionFind::default();
        for i in 0..100 {
            assert_ne!(uf.find(i), uf.find_mut(i + 1));
            assert_eq!(uf.find_mut(i), i);
        }
        for i in 0..100 {
            assert_eq!(uf.union(i, i + 1), 0);
        }
        for i in 0..100 {
            assert_eq!(uf.find_mut(i), uf.find(i + 1));
        }
        for i in 100..200 {
            assert_ne!(uf.find_mut(i), uf.find_mut(i + 1));
        }
    }

    #[test]
    fn luf1() {
        let mut parent = Version::default();
        parent.union(0, 1);
        parent.union(2, 3);
        assert_eq!(parent.find_mut(0), parent.find_mut(1));
        assert_eq!(parent.find_mut(2), parent.find_mut(3));
        assert_ne!(parent.find_mut(0), parent.find_mut(2));
        assert_eq!(
            HashSet::from_iter([0, 1]),
            parent.set(1).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([2, 3]),
            parent.set(2).collect::<HashSet<_>>()
        );

        let parent = Rc::new(parent);
        let mut child = Version::child(parent.clone());
        child.union(0, 3);
        assert_eq!(child.find_mut(0), child.find_mut(1));
        assert_eq!(child.find_mut(2), child.find_mut(3));
        assert_eq!(child.find(0), child.find(2));
        assert_eq!(child.find(0), child.find(3));
        assert_ne!(parent.find(0), parent.find(3));
        assert_eq!(
            HashSet::from_iter([0, 1, 2, 3]),
            child.set(0).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([0, 1, 2, 3]),
            child.set(3).collect::<HashSet<_>>()
        );
    }
}
