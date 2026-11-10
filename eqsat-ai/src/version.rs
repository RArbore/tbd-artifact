use core::cell::RefCell;
use core::cmp::max;
use core::ptr::eq;
use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::Domain;
use crate::ssa::{SSA, SSAId};

// We use a sparse representation for union finds, because in the majority of versions there are
// relatively few unions compared to the number of SSAIds. We use Rem's algorithm for unions and
// store sibling pointers for set traversal (each set corresponds to a circular linked list).
#[derive(Debug, Default)]
pub struct SparseUnionFind {
    parents: RefCell<FxHashMap<SSAId, SSAId>>,
    siblings: FxHashMap<SSAId, SSAId>,
}

// A version is a layer of a layered union find. Each layer of the layered union find is "just" a
// union find over the canonical IDs of the parent union find. Versions form a hierarchy. We get away
// with using a layered union find, rather than the more complicated versioned union find, because we
// only ever modify (at-the-moment) leaf versions.
#[derive(Debug, Default)]
pub struct Version<A: Domain> {
    uf: SparseUnionFind,
    // Track an "analysis" value per e-class. If the map at this version doesn't contain an entry,
    // then the analysis value for the e-class is given by the parent version (recursively).
    analysis: FxHashMap<SSAId, A>,
    // Track whether we have found a contradiction in this version.
    contradiction: bool,
    // Store a pointer to the parent version. This is ref-counted to simplify the code in the
    // saturator w.r.t. ownership of versions.
    parent: Option<Rc<Version<A>>>,
    // Cache calls to `Version::find_in_parent`.
    find_cache: RefCell<FxHashMap<SSAId, SSAId>>,
    // Track the maximum SSAId that was ever given a non-trivial parent in this version.
    max_find_id: SSAId,
    // Track the maximum SSAId that was ever given a non-trivial sibling in this version.
    max_sibling_id: SSAId,
    // Cache calls to `Version::analysis_in_parent`.
    analysis_cache: RefCell<FxHashMap<SSAId, A>>,
    // Track the maximum SSAId that was ever given a non-trivial analysis in this version.
    max_analysis_id: SSAId,
    // Track which level in the version hierarchy this version corresponds to.
    level: usize,
    // Track which SSAIds have been "examined" in this version. A SSAId is considered "examined" in a
    // version if it was ever 1. added as a new node in the hash-cons while this is the current
    // version or 2. was ever interned when the SSAId was in `IDManager::previously_examined` (see
    // `saturator.rs`) while this is the current version.
    examined_ids: FxHashSet<SSAId>,
}

#[derive(Debug)]
pub struct SparseUnionFindSet<'a> {
    start: SSAId,
    curr: Option<SSAId>,
    uf: &'a SparseUnionFind,
}

#[derive(Debug)]
pub enum VersionSet<'a, A: Domain> {
    Trivial(Option<SSAId>),
    NonTrivial {
        set_stack: Vec<SparseUnionFindSet<'a>>,
        version_stack: Vec<&'a Version<A>>,
        up_to: Option<&'a Version<A>>,
    },
}

impl SparseUnionFind {
    fn parent(&self, id: SSAId) -> SSAId {
        self.parents.borrow().get(&id).cloned().unwrap_or(id)
    }

    fn set_parent(&self, id: SSAId, parent: SSAId) {
        if id != parent {
            self.parents.borrow_mut().insert(id, parent);
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

    pub fn find(&self, mut id: SSAId) -> SSAId {
        let mut p = self.parent(id);
        while p != id {
            let gp = self.parent(p);
            self.set_parent(id, gp);
            id = p;
            p = gp;
        }
        id
    }

    pub fn union(&mut self, mut x: SSAId, mut y: SSAId) -> SSAId {
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

    // To properly maintain delta sets, we need to be able to, on a union, add all of the IDs whose
    // canonical IDs changed to the delta set. In effect, this means running a function on the
    // disjoint set that "lost" the comparison on a union (that is, when unioning two sets, right
    // before joining the two sets with `exchange_siblings`, we call `fn_for_changed_set` on all of
    // the IDs in the set that's about to be entirely non-canonical).
    pub fn union_with<F>(&mut self, mut x: SSAId, mut y: SSAId, mut fn_for_changed_set: F) -> SSAId
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
                    let canon_id = self.find(py);
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
                    let canon_id = self.find(px);
                    self.set_parent(y, canon_id);
                    // And here.
                    for id in self.set(y) {
                        fn_for_changed_set(id, y, canon_id);
                    }
                    self.exchange_siblings(x, y);
                    break canon_id;
                }
                self.set_parent(y, px);
                y = py;
            }
        }
    }

    pub fn set(&self, id: SSAId) -> SparseUnionFindSet<'_> {
        SparseUnionFindSet {
            start: id,
            curr: Some(id),
            uf: self,
        }
    }

    pub fn non_canon_ids(&self) -> Vec<SSAId> {
        self.parents.borrow().keys().cloned().collect()
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

impl<A: Domain> Version<A> {
    pub fn child(parent: Rc<Version<A>>) -> Self {
        let max_find_id = parent.max_find_id;
        let max_sibling_id = parent.max_sibling_id;
        let max_analysis_id = parent.max_analysis_id;
        let level = parent.level + 1;
        Self {
            uf: Default::default(),
            analysis: Default::default(),
            contradiction: parent.contradiction,
            parent: Some(parent),
            find_cache: Default::default(),
            analysis_cache: Default::default(),
            max_find_id,
            max_sibling_id,
            max_analysis_id,
            level,
            examined_ids: Default::default(),
        }
    }

    pub fn parent(&self) -> Option<&Rc<Version<A>>> {
        self.parent.as_ref()
    }

    pub fn level(&self) -> usize {
        self.level
    }

    pub fn lca<'a, F1, F2>(
        mut a: &'a Version<A>,
        mut b: &'a Version<A>,
        mut f1: F1,
        mut f2: F2,
    ) -> Option<Rc<Version<A>>>
    where
        F1: FnMut(&'a Version<A>),
        F2: FnMut(&'a Version<A>),
    {
        let mut a_rc: Option<&Rc<Version<A>>> = None;
        let mut b_rc: Option<&Rc<Version<A>>> = None;
        loop {
            if a.level < b.level {
                f2(b);
                let b_parent = b.parent.as_ref().unwrap();
                b_rc = Some(b_parent);
                b = b_parent;
            } else if a.level > b.level {
                f1(a);
                let a_parent = a.parent.as_ref().unwrap();
                a_rc = Some(a_parent);
                a = a_parent;
            } else if !eq(a, b) {
                f1(a);
                f2(b);
                let a_parent = a.parent.as_ref().unwrap();
                let b_parent = b.parent.as_ref().unwrap();
                a_rc = Some(a_parent);
                b_rc = Some(b_parent);
                a = a_parent;
                b = b_parent;
            } else {
                break a_rc.or(b_rc).map(|rc| Rc::clone(rc));
            }
        }
    }

    pub fn find_in_parent(&self, id: SSAId) -> SSAId {
        let mut find_cache = self.find_cache.borrow_mut();
        if let Some(cached) = find_cache.get(&id) {
            *cached
        } else if self.max_find_id < id {
            id
        } else {
            let parent = self
                .parent
                .as_ref()
                .map(|parent| parent.find(id))
                .unwrap_or(id);
            find_cache.insert(id, parent);
            parent
        }
    }

    pub fn find(&self, id: SSAId) -> SSAId {
        self.uf.find(self.find_in_parent(id))
    }

    fn analysis_in_parent(&self, id: SSAId) -> A {
        let mut analysis_cache = self.analysis_cache.borrow_mut();
        if let Some(cached) = analysis_cache.get(&id) {
            cached.clone()
        } else if self.max_analysis_id < id {
            A::top()
        } else {
            let parent = self
                .parent
                .as_ref()
                .map(|parent| parent.analysis(id))
                .unwrap_or_else(|| A::top());
            analysis_cache.insert(id, parent.clone());
            parent
        }
    }

    pub fn analysis(&self, mut id: SSAId) -> A {
        id = self.find(id);
        self.analysis
            .get(&id)
            .cloned()
            .unwrap_or_else(|| self.analysis_in_parent(id))
    }

    pub fn mark_contradiction(&mut self) {
        self.contradiction = true;
    }

    pub fn is_contradiction(&self) -> bool {
        self.contradiction
    }

    fn update_analysis<F>(&mut self, x: SSAId, y: SSAId, canon: SSAId, fn_for_changed_analysis: F)
    where
        F: FnOnce(SSAId, SSAId, A, A),
    {
        let x_analysis = self.analysis(x);
        let y_analysis = self.analysis(y);
        let combined = x_analysis.meet(&y_analysis);
        let (non_canon, old_analysis) = if canon == x {
            (y, x_analysis)
        } else {
            assert_eq!(canon, y);
            (x, y_analysis)
        };
        fn_for_changed_analysis(canon, non_canon, old_analysis, combined.clone());
        self.analysis.insert(canon, combined);
        self.analysis.remove(&non_canon);
        self.max_analysis_id = max(self.max_analysis_id, canon);
    }

    pub fn union(&mut self, mut x: SSAId, mut y: SSAId) -> SSAId {
        x = self.find(x);
        y = self.find(y);
        if x == y {
            x
        } else {
            let canon = self.uf.union(x, y);
            self.max_find_id = max(self.max_find_id, if canon == x { y } else { x });
            self.max_sibling_id = max(self.max_sibling_id, max(x, y));
            self.update_analysis(x, y, canon, |_, _, _, _| {});
            canon
        }
    }

    // See `SparseUnionFind::union_with` for an explanation of `fn_for_changed_set`.
    // `fn_for_changed_analysis` is called on the chosen canonical SSAId with its old and new
    // analysis values.
    pub fn union_with<F1, F2>(
        &mut self,
        mut x: SSAId,
        mut y: SSAId,
        mut fn_for_changed_set: F1,
        fn_for_changed_analysis: F2,
    ) -> SSAId
    where
        F1: FnMut(SSAId, SSAId, SSAId),
        F2: FnOnce(SSAId, SSAId, A, A),
    {
        x = self.find(x);
        y = self.find(y);
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
            self.max_find_id = max(self.max_find_id, if canon == x { y } else { x });
            self.max_sibling_id = max(self.max_sibling_id, max(x, y));
            self.update_analysis(x, y, canon, fn_for_changed_analysis);
            canon
        }
    }

    pub fn set<'a>(
        &'a self,
        id: SSAId,
        up_to: Option<&'a Version<A>>,
    ) -> impl Iterator<Item = SSAId> + 'a {
        let canon_id = self.find(id);
        if let Some(up_to) = up_to
            && eq(self, up_to)
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

    pub fn non_canon_ids_at_level(&self) -> Vec<SSAId> {
        self.uf.non_canon_ids()
    }

    pub fn analyzed_ids_at_level(&self) -> impl Iterator<Item = SSAId> + '_ {
        self.analysis.keys().cloned()
    }

    pub fn set_analysis(&mut self, id: SSAId, analysis: A) {
        if self.analysis(id) != analysis {
            self.analysis.insert(id, analysis);
            self.max_analysis_id = max(self.max_analysis_id, id);
        }
    }

    pub fn examine(&mut self, id: SSAId) {
        self.examined_ids.insert(id);
    }

    pub fn examined(&self) -> impl Iterator<Item = SSAId> + '_ {
        self.examined_ids.iter().cloned()
    }
}

impl<A: Domain> Iterator for VersionSet<'_, A> {
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
                        // that version (version must be an ancestor of the original version). If the
                        // parent version does not have any interesting siblings for the ID, then
                        // also stop going upwards.
                        if let Some(parent_version) = last_version.parent.as_ref()
                            && up_to
                                .map(|up_to| !eq(up_to, &**parent_version))
                                .unwrap_or(true)
                            && parent_version.max_sibling_id >= id
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
