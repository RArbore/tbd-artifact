use core::ptr::eq;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ssa::{SSA, SSABlockId, SSAId};

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
#[derive(Debug)]
pub struct Version {
    uf: SparseUnionFind,
    // Track the size of the multi-layer set for every canonical SSAId. Store an Option<usize>, since
    // the count when a SSAId is not mapped is actually 1, not 0.
    count: HashMap<SSAId, Option<usize>>,
    // Store a pointer to the parent version. This is ref-counted to simplify the code in the
    // saturator w.r.t. ownership of versions.
    parent: Option<Rc<Version>>,
    // Track which level in the version hierarchy this version corresponds to.
    level: usize,
    // Track which SSA block this version corresponds to.
    block: SSABlockId,
}

#[derive(Debug)]
struct SparseUnionFindSet<'a> {
    start: SSAId,
    curr: Option<SSAId>,
    uf: &'a SparseUnionFind,
}

#[derive(Debug)]
enum VersionSet<'a> {
    Trivial(Option<SSAId>),
    NonTrivial {
        set_stack: Vec<SparseUnionFindSet<'a>>,
        version_stack: Vec<&'a Version>,
        up_to: Option<SSABlockId>,
    },
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

    // To properly maintain delta sets, we need to be able to, on a union, add all of the IDs whose
    // canonical IDs changed to the delta set. In effect, this means running a function on the
    // disjoint set that "lost" the comparison on a union (that is, when unioning two sets, right
    // before joining the two sets with `exchange_siblings`, we call `fn_for_changed_set` on all of
    // the IDs in the set that's about to be entirely non-canonical).
    fn union_with<F>(&mut self, mut x: SSAId, mut y: SSAId, mut fn_for_changed_set: F) -> SSAId
    where
        F: FnMut(SSAId, SSAId, SSAId),
    {
        loop {
            let px = self.parent(x);
            let py = self.parent(y);
            if px == py {
                break px;
            }

            if px > py {
                if x == px {
                    let canon_id = self.find_mut(py);
                    self.set_parent(x, canon_id);
                    // The only difference with `union`.
                    for id in self.set(x) {
                        fn_for_changed_set(id, x, canon_id);
                    }
                    self.exchange_siblings(x, y);
                    break canon_id;
                }
                self.set_parent(x, py);
                x = px;
            } else {
                if y == py {
                    let canon_id = self.find_mut(px);
                    self.set_parent(y, canon_id);
                    // And here.
                    for id in self.set(y) {
                        fn_for_changed_set(id, y, canon_id);
                    }
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

    fn non_canon_ids(&self) -> impl Iterator<Item = SSAId> + '_ {
        self.parents.keys().cloned()
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
    pub fn root(block: SSABlockId) -> Self {
        Self {
            uf: Default::default(),
            count: HashMap::new(),
            parent: None,
            level: 0,
            block,
        }
    }

    pub fn child(parent: Rc<Version>, block: SSABlockId) -> Self {
        let level = parent.level + 1;
        Self {
            uf: Default::default(),
            count: parent.count.clone(),
            parent: Some(parent),
            level,
            block,
        }
    }

    pub fn parent(&self) -> Option<&Version> {
        self.parent.as_ref().map(|v| &**v)
    }

    pub fn lca<'a, F1, F2>(
        mut a: &'a Version,
        mut b: &'a Version,
        mut f1: F1,
        mut f2: F2,
    ) -> &'a Version
    where
        F1: FnMut(&Version),
        F2: FnMut(&Version),
    {
        loop {
            if a.level < b.level {
                f2(b);
                b = b.parent.as_ref().unwrap();
            } else if a.level > b.level {
                f1(a);
                a = a.parent.as_ref().unwrap();
            } else if !eq(a, b) {
                f1(a);
                f2(b);
                a = a.parent.as_ref().unwrap();
                b = b.parent.as_ref().unwrap();
            } else {
                break a;
            }
        }
    }

    pub fn block(&self) -> SSABlockId {
        self.block
    }

    pub fn find_in_parent(&self, id: SSAId) -> SSAId {
        self.parent
            .as_ref()
            .map(|parent| parent.find(id))
            .unwrap_or(id)
    }

    pub fn find(&self, id: SSAId) -> SSAId {
        self.uf.find(self.find_in_parent(id))
    }

    pub fn find_mut(&mut self, id: SSAId) -> SSAId {
        self.uf.find_mut(
            self.parent
                .as_ref()
                .map(|parent| parent.find(id))
                .unwrap_or(id),
        )
    }

    pub fn count(&self, id: SSAId) -> usize {
        self.count.get(&id).unwrap_or(&Some(1)).unwrap()
    }

    fn update_counts(&mut self, x: SSAId, y: SSAId, canon: SSAId) {
        if canon == x {
            *self.count.entry(x).or_insert(Some(1)).as_mut().unwrap() +=
                self.count.get(&y).unwrap_or(&Some(1)).unwrap();
            self.count.insert(y, None);
        } else {
            *self.count.entry(y).or_insert(Some(1)).as_mut().unwrap() +=
                self.count.get(&x).unwrap_or(&Some(1)).unwrap();
            self.count.insert(x, None);
        }
    }

    pub fn union(&mut self, mut x: SSAId, mut y: SSAId) -> SSAId {
        x = self.find_mut(x);
        y = self.find_mut(y);
        if x == y {
            x
        } else {
            let canon = self.uf.union(x, y);
            self.update_counts(x, y, canon);
            canon
        }
    }

    // See `SparseUnionFind::union_with` for an explanation of `fn_for_changed_set`.
    pub fn union_with<F>(&mut self, mut x: SSAId, mut y: SSAId, mut fn_for_changed_set: F) -> SSAId
    where
        F: FnMut(SSAId, SSAId, SSAId),
    {
        x = self.find_mut(x);
        y = self.find_mut(y);
        if x == y {
            x
        } else {
            let canon = self.uf.union_with(x, y, |id, old_canon_id, new_canon_id| {
                // `SparseUnionFind::union` will call `fn_for_changed_set` on all IDs in the set *at the
                // current layer*, but we want to call it on all IDs in the *multi-layer* set of the
                // losing ID.
                if let Some(parent) = self.parent.as_ref() {
                    for set_id in parent.set(id, None) {
                        fn_for_changed_set(set_id, old_canon_id, new_canon_id);
                    }
                } else {
                    fn_for_changed_set(id, old_canon_id, new_canon_id);
                }
            });
            self.update_counts(x, y, canon);
            canon
        }
    }

    pub fn set(&self, id: SSAId, up_to: Option<SSABlockId>) -> impl Iterator<Item = SSAId> + '_ {
        let canon_id = self.find(id);
        if let Some(up_to) = up_to
            && self.block == up_to
        {
            VersionSet::Trivial(Some(canon_id))
        } else {
            VersionSet::NonTrivial {
                set_stack: vec![self.uf.set(canon_id)],
                version_stack: vec![self],
                up_to,
            }
        }
    }

    pub fn is_canonical(&self, ssa: SSA) -> bool {
        use SSA::*;
        match ssa {
            Unary(_, input) => input == self.find(input),
            Binary(_, lhs, rhs) => lhs == self.find(lhs) && rhs == self.find(rhs),
            _ => true,
        }
    }

    pub fn canonicalize(&self, ssa: SSA) -> SSA {
        use SSA::*;
        match ssa {
            Unary(op, input) => Unary(op, self.find(input)),
            Binary(op, lhs, rhs) => Binary(op, self.find(lhs), self.find(rhs)),
            _ => ssa,
        }
    }

    pub fn non_canon_ids_at_level(&self) -> impl Iterator<Item = SSAId> + '_ {
        self.uf.non_canon_ids()
    }
}

impl Iterator for VersionSet<'_> {
    type Item = SSAId;

    fn next(&mut self) -> Option<SSAId> {
        use VersionSet::*;
        match self {
            Trivial(id) => {
                let old_id = *id;
                *id = None;
                old_id
            }
            NonTrivial {
                set_stack,
                version_stack,
                up_to,
            } => {
                loop {
                    // Once all sets in the stack have been visited, this `?` will return `None`,
                    // breaking out of the loop.
                    let last_set = set_stack.last_mut()?;
                    let last_version = *version_stack.last().unwrap();
                    if let Some(id) = last_set.next() {
                        // If `up_to` is some version, then only enumerate IDs that are canonical in
                        // that version (version must be an ancestor of the original version).
                        if let Some(parent_version) = last_version.parent.as_ref()
                            && up_to
                                .map(|up_to| up_to != parent_version.block)
                                .unwrap_or(true)
                        {
                            set_stack.push(parent_version.uf.set(id));
                            version_stack.push(parent_version);
                        } else {
                            // Yield the ID if we've traversed all the way to the root (or `up_to`).
                            break Some(id);
                        }
                    } else {
                        set_stack.pop();
                        version_stack.pop();
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::rc::Rc;

    use super::*;

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
        assert_eq!(
            HashSet::from_iter([3, 4, 5, 9]),
            uf.non_canon_ids().collect::<HashSet<_>>()
        );

        assert_eq!(uf.union(4, 5), 0);
        assert_eq!(uf.find_mut(2), 0);
        assert_eq!(uf.find(5), 0);
        assert_eq!(uf.find_mut(9), 0);
        assert_eq!(
            HashSet::from_iter([0, 2, 4, 5, 9]),
            uf.set(9).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([2, 3, 4, 5, 9]),
            uf.non_canon_ids().collect::<HashSet<_>>()
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
        assert_eq!(
            HashSet::from_iter(1..=100),
            uf.non_canon_ids().collect::<HashSet<_>>()
        );
    }

    #[test]
    fn uf3() {
        let mut uf = SparseUnionFind::default();
        let mut set = HashSet::new();
        uf.union_with(1, 2, |id, old_canon_id, new_canon_id| {
            set.insert(id);
            assert_eq!(old_canon_id, 2);
            assert_eq!(new_canon_id, 1);
        });
        assert_eq!(set, HashSet::from([2]));
        let mut set = HashSet::new();
        uf.union_with(2, 0, |id, old_canon_id, new_canon_id| {
            set.insert(id);
            assert_eq!(old_canon_id, 1);
            assert_eq!(new_canon_id, 0);
        });
        assert_eq!(set, HashSet::from([1, 2]));
        let mut set = HashSet::new();
        uf.union_with(3, 0, |id, old_canon_id, new_canon_id| {
            set.insert(id);
            assert_eq!(old_canon_id, 3);
            assert_eq!(new_canon_id, 0);
        });
        assert_eq!(set, HashSet::from([3]));
    }

    #[test]
    fn luf1() {
        let mut parent = Version::root(0);
        parent.union(0, 1);
        parent.union(2, 3);
        assert_eq!(parent.find_mut(0), parent.find_mut(1));
        assert_eq!(parent.find_mut(2), parent.find_mut(3));
        assert_ne!(parent.find_mut(0), parent.find_mut(2));
        assert_eq!(
            HashSet::from_iter([0, 1]),
            parent.set(1, None).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([2, 3]),
            parent.set(2, None).collect::<HashSet<_>>()
        );
        assert_eq!(parent.count(0), 2);
        assert_eq!(parent.count(2), 2);

        let parent = Rc::new(parent);
        let mut child = Version::child(Rc::clone(&parent), 1);
        child.union(0, 3);
        assert_eq!(child.find_mut(0), child.find_mut(1));
        assert_eq!(child.find_mut(2), child.find_mut(3));
        assert_eq!(child.find(0), child.find(2));
        assert_eq!(child.find(0), child.find(3));
        assert_ne!(parent.find(0), parent.find(3));
        for i in [0, 1, 2, 3] {
            assert_eq!(
                HashSet::from_iter([0, 1, 2, 3]),
                child.set(i, None).collect::<HashSet<_>>()
            );
        }
        assert_eq!(
            HashSet::from_iter([0, 1]),
            parent.set(1, None).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([2, 3]),
            parent.set(2, None).collect::<HashSet<_>>()
        );
        for i in [0, 1, 2, 3] {
            assert_eq!(
                HashSet::from_iter([0, 2]),
                child.set(i, Some(0)).collect::<HashSet<_>>()
            );
        }
        assert_eq!(
            HashSet::from_iter([5]),
            child.set(5, Some(0)).collect::<HashSet<_>>()
        );
        for i in [0, 1, 2, 3] {
            assert_eq!(
                HashSet::from_iter([child.find(i)]),
                child.set(i, Some(1)).collect::<HashSet<_>>()
            );
            assert_eq!(
                HashSet::from_iter([parent.find(i)]),
                parent.set(i, Some(0)).collect::<HashSet<_>>()
            );
        }
        assert_eq!(parent.count(0), 2);
        assert_eq!(parent.count(2), 2);
        assert_eq!(child.count(0), 4);
        assert!(eq(Version::lca(&child, &parent, |_| {}, |_| {}), &*parent));
    }

    #[test]
    fn luf2() {
        let mut parent = Version::root(0);
        parent.union(0, 1);
        parent.union(2, 3);
        assert_eq!(parent.count(0), 2);
        assert_eq!(parent.count(2), 2);

        let parent = Rc::new(parent);
        let mut child = Version::child(Rc::clone(&parent), 1);
        let mut set = HashSet::new();
        child.union_with(0, 3, |id, old_canon_id, new_canon_id| {
            set.insert(id);
            assert_eq!(old_canon_id, 2);
            assert_eq!(new_canon_id, 0);
        });
        assert_eq!(set, HashSet::from([2, 3]));
        assert_eq!(parent.count(0), 2);
        assert_eq!(parent.count(2), 2);
        assert_eq!(child.count(0), 4);
        assert!(eq(Version::lca(&child, &parent, |_| {}, |_| {}), &*parent));
    }
}
