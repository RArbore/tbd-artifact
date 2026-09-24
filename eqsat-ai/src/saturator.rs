use core::mem::take;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::dom::DomTree;
use crate::rw::{Tries, apply_rws};
use crate::ssa::{SSA, SSABlock, SSABlockId, SSAId, SSAProgram};
use crate::version::Version;

#[derive(Debug)]
enum VersionState {
    // If the version is mutable, it is a leaf version.
    Mutable(Version),
    // If the version is immutable, it is a parent version of some child version.
    Immutable(Rc<Version>),
}

impl AsRef<Version> for VersionState {
    fn as_ref(&self) -> &Version {
        use VersionState::*;
        match self {
            Mutable(version) => version,
            Immutable(version) => version,
        }
    }
}

// Because Rust does not have field borrows, we have to do silly things sometimes to convey to the
// borrow checker that we are not violating any of its rules. This struct should be considered as
// part of `Saturator` directly.
#[derive(Default)]
struct IDManager {
    // What nodes have either been:
    // 1. Added to the hash-cons...
    // 2. Have had their canonical SSAId changed (due to a union)...
    // ...since the last iteration of rewriting.
    delta: HashSet<SSAId>,
    // Incrementally maintain dominator analysis.
    dom_tree: DomTree,
    // Store an empty root version. This is needed so we have a well-defined LCA between old and new
    // versions for the entry block.
    root_version: Rc<Version>,
    // Store the latest version for each SSA block.
    versions: HashMap<SSABlockId, VersionState>,
    // Store the "current" version. Moving between versions requires careful maintenance of the delta
    // set, so we use `move_to_version` to explicitly change this member.
    current_version: Option<SSABlockId>,
    // Store the set of SSAIds that were examined in versions that we've since left. At any point in
    // time, if we intern a SSAId that is in this set, we treat it as a new node and add it to the
    // delta set (and remove it from this set), even if it was already in the hash-cons. When moving
    // out of a version with examined SSAIds, those SSAIds need to be added to `previously_examined`,
    // so that they are re-examined if they are re-interned. When moving into a version with examined
    // SSAIds, those SSAIds need to be removed from `previously_examined`, so that they are not re-
    // examined unnecessarily.
    previously_examined: HashSet<SSAId>,
}

#[derive(Default)]
pub struct Saturator {
    pub ssa: SSAProgram,
    ids: IDManager,
    // Whenever the abstract interpreter creates a new version, it always moves to that version next.
    // If that version is replacing some old version, we need to pop the old version and push the new
    // version, which requires delaying actually inserting the new version into `ids` until during
    // the move into it. This is kind of hacky.
    new_version: Option<(SSABlockId, VersionState)>,
}

impl IDManager {
    fn find(&mut self, mut id: SSAId) -> SSAId {
        if let Some(version) = self.current_version {
            id = self.find_in_version(id, version);
        }
        id
    }

    fn find_in_version(&mut self, id: SSAId, version: SSABlockId) -> SSAId {
        match self.versions.get_mut(&version).unwrap() {
            VersionState::Mutable(version) => version.find_mut(id),
            VersionState::Immutable(version) => version.find(id),
        }
    }

    fn union_with<F>(&mut self, x: SSAId, y: SSAId, mut f: F) -> SSAId
    where
        F: FnMut(SSAId, SSAId, SSAId),
    {
        let VersionState::Mutable(version) = self
            .versions
            .get_mut(&self.current_version.unwrap())
            .unwrap()
        else {
            panic!()
        };
        version.union_with(x, y, |id, old_canon_id, new_canon_id| {
            // Record any SSAId whose canonical SSAId changed as a delta ID. Notably, the SSAId
            // inserted here is itself *not* canonical.
            // NOTE: This should really ignore Param and Knot nodes, just as in `Saturator::intern`,
            // but we don't have a good way to map from SSAId to SSA in this context. It's fine for
            // these nodes to be added to the delta set, they will just be ignored by `apply_rws`.
            self.delta.insert(id);
            f(id, old_canon_id, new_canon_id);
        })
    }

    fn count(&self, id: SSAId) -> usize {
        self.current_version
            .map(|current_version| self.versions[&current_version].as_ref().count(id))
            .unwrap_or(1)
    }

    fn is_canonical(&self, ssa: SSA) -> bool {
        self.current_version
            .map(|current_version| self.versions[&current_version].as_ref().is_canonical(ssa))
            .unwrap_or(true)
    }

    fn canonicalize(&self, ssa: SSA) -> SSA {
        self.current_version
            .map(|current_version| self.versions[&current_version].as_ref().canonicalize(ssa))
            .unwrap_or(ssa)
    }
}

impl Saturator {
    pub fn find(&mut self, id: SSAId) -> SSAId {
        self.ids.find(id)
    }

    pub fn find_in_version(&mut self, id: SSAId, version: SSABlockId) -> SSAId {
        self.ids.find_in_version(id, version)
    }

    pub fn union(&mut self, x: SSAId, y: SSAId) -> SSAId {
        assert_eq!(self.ssa.ty(x), self.ssa.ty(y));
        self.ids.union_with(x, y, |_, _, _| {})
    }

    pub fn count(&self, id: SSAId) -> usize {
        self.ids.count(id)
    }

    pub fn version(&self, id: SSABlockId) -> &Version {
        self.ids.versions[&id].as_ref()
    }

    pub fn intern(&mut self, mut ssa: SSA) -> SSAId {
        let before = self.ssa.num_nodes();
        ssa = self.ids.canonicalize(ssa);
        let id = self.ssa.intern(ssa);
        let canon_id = if ssa.is_param_or_knot() {
            // Param and Knot nodes never get added to the delta set because they are never matched
            // on by any rules.
            self.ids.find(id)
        } else {
            let canon_id = self.ids.find(id);
            let after = self.ssa.num_nodes();
            if before != after || self.ids.previously_examined.remove(&canon_id) {
                let VersionState::Mutable(version) = self
                    .ids
                    .versions
                    .get_mut(&self.ids.current_version.unwrap())
                    .unwrap()
                else {
                    panic!()
                };
                version.examine(canon_id);
                self.ids.delta.insert(canon_id);
            }
            canon_id
        };
        canon_id
    }

    pub fn create_version(&mut self, block: SSABlockId) {
        // Update the dominator tree incrementally when adding new SSA blocks.
        self.ids
            .dom_tree
            .visit_block(block, self.ssa.get_block(block));

        use SSABlock::*;
        use VersionState::*;
        let pred_version_rc = match self.ssa.get_block(block) {
            Entry => None,
            Guard(pred, _, _) | Return(pred, _) => {
                let state = self.ids.versions.get_mut(pred).unwrap();
                let rc = match state {
                    Mutable(version) => {
                        // Why isn't there a core::mem primitive for this?
                        let rc = Rc::new(take(version));
                        *state = Immutable(Rc::clone(&rc));
                        rc
                    }
                    Immutable(rc) => Rc::clone(rc),
                };
                Some(rc)
            }
            Merge(pred1, pred2, _) => {
                let pred1 = self.ids.versions[&pred1].as_ref();
                let pred2 = self.ids.versions[&pred2].as_ref();
                // This looks weird, but we do want to make sure that we get an Rc in this situation.
                Some(Version::lca(pred1, pred2, |_| {}, |_| {}).unwrap())
            }
        };

        let version = pred_version_rc
            .map(|rc| Version::child(rc))
            .unwrap_or_else(|| Version::child(Rc::clone(&self.ids.root_version)));
        self.new_version = Some((block, VersionState::Mutable(version)));
    }

    fn commit_new_version(&mut self) {
        let Some((block, version)) = self.new_version.take() else {
            panic!()
        };
        self.ids.versions.insert(block, version);
    }

    fn pop_version(&mut self, block_id: SSABlockId) {
        // If the version for this block hasn't been committed yet, then there's nothing to do.
        if !self.ids.versions.contains_key(&block_id) {
            return;
        }

        // When popping a version, any examined nodes may need to be examined again.
        for id in self.ids.versions[&block_id].as_ref().examined() {
            self.ids.previously_examined.insert(id);
        }
    }

    fn push_version(&mut self, block_id: SSABlockId) {
        // If the version for this block hasn't been committed yet, then there's nothing to do.
        if !self.ids.versions.contains_key(&block_id) {
            return;
        }

        // When pushing a version, any examined nodes will have their examination inherited
        // by the destination version, so we don't need to re-examine them.
        for id in self.ids.versions[&block_id].as_ref().examined() {
            self.ids.previously_examined.remove(&id);
        }
    }

    pub fn move_to_version(&mut self, block: SSABlockId) {
        if let Some(last_block) = self.ids.current_version {
            assert!(self.ids.delta.is_empty());

            // Traverse up and down the dominator tree from the last block to the new block.
            let mut up_ids = vec![];
            let mut down_ids = vec![];
            self.ids.dom_tree.lca(
                last_block,
                block,
                |up_id| up_ids.push(up_id),
                |down_id| down_ids.push(down_id),
            );
            down_ids.reverse();

            for block_id in up_ids {
                self.pop_version(block_id);
            }

            for block_id in down_ids {
                self.push_version(block_id);
            }

            if let Some(block) = self.new_version.as_ref().map(|(block, _)| *block) {
                self.pop_version(block);
                self.commit_new_version();
                self.push_version(block);
            }
        } else {
            assert_eq!(self.ssa.get_block(block), &SSABlock::Entry);
            self.commit_new_version();
        }
        self.ids.current_version = Some(block);
    }

    pub fn saturate(&mut self) {
        if let VersionState::Immutable(_) = self.ids.versions[&self.ids.current_version.unwrap()] {
            assert!(self.ids.delta.is_empty());
            return;
        };
        while !self.ids.delta.is_empty() {
            // As usual, this song and dance is to please the borrow checker.
            let mut delta = take(&mut self.ids.delta);

            // Prepare worklist for rebuilding. The worklist should always contain only nodes that
            // use non-canonical SSAIds.
            let mut worklist = VecDeque::new();
            for id in &delta {
                // The only nodes in `delta` that should fail this check are new nodes.
                if *id != self.ids.find(*id) {
                    for user in self.ssa.users(*id) {
                        worklist.push_back(*user);
                    }
                }
            }

            // Perform rebuilding.
            while let Some(id) = worklist.pop_front() {
                let old_ssa = self.ssa.get(id);
                let new_ssa = self.ids.canonicalize(old_ssa);
                // We should only ever insert a node into the worklist if it's non-canonical.
                assert_ne!(old_ssa, new_ssa);
                let new_id = self.intern(new_ssa);
                self.ids.union_with(id, new_id, |id, _, _| {
                    for user in self.ssa.users(id) {
                        worklist.push_back(*user);
                    }
                });
            }
            // Unions during rebuilding might create more delta IDs. At this point, `self.ids.delta`
            // is empty before we apply rules.
            delta.extend(self.ids.delta.drain());

            let mut tries = Tries::default();
            // Add all the nodes into the "all" tries and add the delta nodes into the delta tries.
            // TODO: Incrementalize trie building!
            for id in delta {
                let node = self.ssa.get(id);
                if self.ids.is_canonical(node) {
                    tries.insert_tuple(self.ids.find(id), node, id, true);
                }
            }
            for id in 0..self.ssa.num_nodes() {
                let node = self.ssa.get(id);
                if self.ids.is_canonical(node) {
                    tries.insert_tuple(self.ids.find(id), node, id, false);
                }
            }

            apply_rws::<false>(&tries, self);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::nonssa::{BinaryOp, Type, UnaryOp};

    use super::*;

    #[test]
    fn saturator1() {
        let mut saturator = Saturator::default();
        let block_id = saturator.ssa.add_block(SSABlock::Entry);
        saturator.create_version(block_id);
        saturator.move_to_version(block_id);
        saturator.saturate();
        assert_eq!(saturator.ssa.num_nodes(), 0);

        use SSA::*;
        let p1 = saturator.intern(Param(0, Type::I64));
        let p2 = saturator.intern(Param(1, Type::I64));
        saturator.saturate();
        // Param(0), Param(1)
        assert_eq!(saturator.ssa.num_nodes(), 2);

        saturator.intern(Binary(BinaryOp::Add, p1, p2));
        saturator.saturate();
        // Param(0), Param(1), Add(p1, p2), Add(p2, p1)
        assert_eq!(saturator.ssa.num_nodes(), 4);

        saturator.union(p1, p2);
        saturator.saturate();
        // Param(0), Param(1), Add(p1, p2), Add(p2, p1), Add(p1, p1), Constant(2), Mul(c, p1), Mul(p1, c)
        assert_eq!(saturator.ssa.num_nodes(), 8);
    }

    #[test]
    fn saturator2() {
        let mut saturator = Saturator::default();
        let entry = saturator.ssa.add_block(SSABlock::Entry);
        saturator.create_version(entry);
        saturator.move_to_version(entry);

        use BinaryOp::*;
        use SSA::*;
        use UnaryOp::*;
        let one = saturator.intern(Constant(crate::nonssa::Constant::I64(1)));
        let p1 = saturator.intern(Param(0, Type::I64));
        let p2 = saturator.intern(Param(1, Type::I64));
        let n1 = saturator.intern(Unary(Neg, p1));
        let n2 = saturator.intern(Unary(Neg, p2));
        let eq1 = saturator.intern(Binary(EE, n1, one));
        saturator.saturate();

        saturator.union(p1, p2);
        saturator.saturate();

        let guard_true = saturator.ssa.add_block(SSABlock::Guard(entry, eq1, true));
        saturator.create_version(guard_true);
        saturator.move_to_version(guard_true);
        let add1 = saturator.intern(Binary(Add, n1, n2));
        let add2 = saturator.intern(Binary(Add, n2, n1));
        let eq2 = saturator.intern(Binary(NE, add1, add2));
        let false_constant = saturator.intern(Constant(crate::nonssa::Constant::Bool(false)));
        saturator.saturate();
        assert_eq!(saturator.find(false_constant), saturator.find(eq2));

        let guard_false = saturator
            .ssa
            .add_block(SSABlock::Guard(guard_true, eq1, false));
        saturator.create_version(guard_false);
        saturator.move_to_version(guard_false);
        let mul1 = saturator.intern(Binary(Mul, n2, one));
        let add1 = saturator.intern(Binary(Add, n1, n2));
        saturator.intern(Binary(Add, mul1, add1));
        saturator.saturate();

        saturator.move_to_version(guard_true);
        saturator.move_to_version(guard_false);
    }
}
