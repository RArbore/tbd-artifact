use core::mem::{replace, take};
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
// part of `Saturator` directly. It handles all the facilities that just deal with SSAIds.
#[derive(Default)]
struct IDManager {
    // What nodes have either been:
    // 1. Added to the hash-cons...
    // 2. Have had their canonical SSAId changed (due to a union)...
    // ...since the last iteration of rewriting.
    delta: HashSet<SSAId>,
    // Incrementally maintain dominator analysis.
    dom_tree: DomTree,
    // Store the latest version for each SSA block.
    versions: HashMap<SSABlockId, VersionState>,
    // Store the "current" version. Moving between versions requires careful maintenance of the delta
    // set, so we use `move_to_version` to explicitly change this member.
    current_version: Option<SSABlockId>,
    // Store the set of SSAIds that were "examined" in each version. A SSAId is considered "examined"
    // in a version if it was ever 1. added as a new node in the hash-cons while at that version or
    // 2. was ever interned when the SSAId was in `previously_examined` while at that version. When
    // moving out of a version with examined SSAIds, those SSAIds need to be added to
    // `previously_examined`, so that they are re-examined if they are re-interned. When moving
    // into a version with examined SSAIds, those SSAIds need to be removed from
    // `previously_examined`, so that they are not re-examined unnecessarily.
    examined_ids: HashMap<SSABlockId, HashSet<SSAId>>,
    // Store the set of SSAIds that were examined in versions that we've since left. At any point in
    // time, if we intern a SSAId that is in this set, we treat it as a new node and add it to the
    // delta set (and remove it from this set), even if it was already in the hash-cons.
    previously_examined: HashSet<SSAId>,
}

#[derive(Debug, Clone, Copy)]
enum TrieEdit {
    Intern {
        canon_id: SSAId,
        id: SSAId,
    },
    Union {
        id: SSAId,
        old_canon_id: SSAId,
        new_canon_id: SSAId,
    },
    RevertUnion {
        id: SSAId,
        old_canon_id: SSAId,
        new_canon_id: SSAId,
        parent_version: SSABlockId,
    },
}

#[derive(Default)]
pub struct Saturator {
    pub ssa: SSAProgram,
    ids: IDManager,
    // Incrementally maintain the tries that get used for e-matching.
    tries: Tries,
    // We can't edit the tries during e-matching because they are being iterated during e-matching,
    // so we delay editing the tries until after e-matching (and after rebuilding) by recording
    // intern and union operations.
    trie_edits: Vec<TrieEdit>,
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

    fn idom(&self, id: SSABlockId) -> Option<SSABlockId> {
        self.dom_tree.idom(id)
    }

    fn set_in_version(
        &self,
        id: SSAId,
        up_to: Option<SSABlockId>,
        version: SSABlockId,
    ) -> impl Iterator<Item = SSAId> + '_ {
        self.versions[&version].as_ref().set(id, up_to)
    }

    fn create_version(&mut self, block_id: SSABlockId, block: &SSABlock) {
        // Update the dominator tree incrementally when adding new SSA blocks.
        self.dom_tree.visit_block(block_id, block);
        let version = if let Some(idom) = self.dom_tree.idom(block_id) {
            let state = self.versions.get_mut(&idom).unwrap();
            use VersionState::*;
            let rc = match state {
                Mutable(version) => {
                    // Why isn't there a core::mem primitive for this?
                    let rc = Rc::new(replace(version, Version::root(!0)));
                    *state = Immutable(Rc::clone(&rc));
                    rc
                }
                Immutable(rc) => Rc::clone(rc),
            };
            Version::child(rc, block_id)
        } else {
            // The entry block gets the root version.
            Version::root(block_id)
        };
        self.versions
            .insert(block_id, VersionState::Mutable(version));
        // In the new version, nothing has been examined yet.
        self.examined_ids.insert(block_id, HashSet::new());
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
        println!(
            "union {} and {} in {:?} (rule)",
            x, y, self.ids.current_version
        );
        assert_eq!(self.ssa.ty(x), self.ssa.ty(y));
        self.ids.union_with(x, y, |id, old_canon_id, new_canon_id| {
            self.trie_edits.push(TrieEdit::Union {
                id,
                old_canon_id,
                new_canon_id,
            })
        })
    }

    pub fn count(&self, id: SSAId) -> usize {
        self.ids.count(id)
    }

    pub fn idom(&self, id: SSABlockId) -> Option<SSABlockId> {
        self.ids.idom(id)
    }

    pub fn set_in_version(
        &self,
        id: SSAId,
        up_to: Option<SSABlockId>,
        version: SSABlockId,
    ) -> impl Iterator<Item = SSAId> + '_ {
        self.ids.set_in_version(id, up_to, version)
    }

    pub fn intern(&mut self, mut ssa: SSA) -> SSAId {
        let before = self.ssa.num_nodes();
        ssa = self.ids.canonicalize(ssa);
        let id = self.ssa.intern(ssa);
        let (canon_id, after) = if ssa.is_param_or_knot() {
            // Param and Knot nodes never get added to the delta set because they are never matched
            // on by any rules.
            (self.ids.find(id), self.ssa.num_nodes())
        } else {
            let canon_id = self.ids.find(id);
            let after = self.ssa.num_nodes();
            if before != after || self.ids.previously_examined.remove(&canon_id) {
                self.ids
                    .examined_ids
                    .entry(self.ids.current_version.unwrap())
                    .or_default()
                    .insert(canon_id);
                self.ids.delta.insert(canon_id);
            }
            (canon_id, after)
        };
        if before != after {
            self.trie_edits.push(TrieEdit::Intern { canon_id, id });
        }
        canon_id
    }

    pub fn create_version(&mut self, block: SSABlockId) {
        self.ids.create_version(block, self.ssa.get_block(block));
    }

    pub fn move_to_version(&mut self, block: SSABlockId) {
        if let Some(last_block) = self.ids.current_version {
            if block == last_block {
                return;
            }
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
            println!(
                "moving from {} ({:?}) to {} ({:?}), up_ids: {:?}, down_ids: {:?}",
                last_block,
                self.ssa.get_block(last_block),
                block,
                self.ssa.get_block(block),
                up_ids,
                down_ids
            );

            for block_id in up_ids {
                // When popping a version, any examined nodes may need to be examined again.
                for id in &self.ids.examined_ids[&block_id] {
                    assert!(self.ids.previously_examined.insert(*id));
                }

                // And any unions that held in the popped version but not the parent version induce
                // edits in the tries.
                let version = self.ids.versions[&block_id].as_ref();
                let parent = version.parent().unwrap();
                for id in version.non_canon_ids_at_level() {
                    assert_eq!(id, version.find_in_parent(id));
                    let old_canon_id = version.find(id);
                    assert_ne!(old_canon_id, id);
                    for set_id in parent.set(id, None) {
                        self.trie_edits.push(TrieEdit::RevertUnion {
                            id: set_id,
                            old_canon_id,
                            new_canon_id: id,
                            parent_version: parent.block(),
                        });
                    }
                }
            }

            for block_id in down_ids {
                // When pushing a version, any examined nodes will have their examination inherited
                // by the destination version, so we don't need to re-examine them.
                for id in &self.ids.examined_ids[&block_id] {
                    self.ids.previously_examined.remove(id);
                }

                // And any unions that hold in the pushed version but not the parent version induce
                // edits in the tries.
                let version = self.ids.versions[&block_id].as_ref();
                let parent = version.parent().unwrap();
                for id in version.non_canon_ids_at_level() {
                    assert_eq!(id, version.find_in_parent(id));
                    let new_canon_id = version.find(id);
                    assert_ne!(new_canon_id, id);
                    for set_id in parent.set(id, None) {
                        self.trie_edits.push(TrieEdit::Union {
                            id: set_id,
                            old_canon_id: id,
                            new_canon_id,
                        });
                    }
                }
            }
        } else {
            assert_eq!(self.ssa.get_block(block), &SSABlock::Entry);
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
                println!(
                    "union {} and {} in {:?} (rebuild)",
                    id, new_id, self.ids.current_version
                );
                self.ids
                    .union_with(id, new_id, |id, old_canon_id, new_canon_id| {
                        self.trie_edits.push(TrieEdit::Union {
                            id,
                            old_canon_id,
                            new_canon_id,
                        });
                        for user in self.ssa.users(id) {
                            worklist.push_back(*user);
                        }
                    });
            }
            // Unions during rebuilding might create more delta IDs. At this point, `self.ids.delta`
            // is empty before we apply rules.
            delta.extend(self.ids.delta.drain());
            // Take all the accumulated trie edits and actually apply them. This incrementally
            // maintains the "all" nodes tries.
            take(&mut self.trie_edits)
                .into_iter()
                .for_each(|edit| self.apply_edit(edit));

            // We have to do this song and dance because we want to store the `Tries` struct across
            // calls to `saturate`, but `apply_rws` needs `self` for calls to `intern` and `union`
            // while it needs live references to tries being iterated.
            let mut tries = take(&mut self.tries);
            // Delta nodes get added to the delta tries every iteration.
            for id in delta {
                let node = self.ssa.get(id);
                if self.ids.is_canonical(node) {
                    tries.insert_tuple(self.ids.find(id), node, id, true);
                }
            }

            apply_rws::<false>(&tries, self);
            // The delta tries get created from scratch every iteration.
            tries.clear_delta();
            self.tries = tries;
        }
        self.check_trie_consistency();
    }

    fn apply_edit(&mut self, edit: TrieEdit) {
        println!("applying {:?}", edit);
        match edit {
            TrieEdit::Intern { canon_id, id } => {
                let node = self.ssa.get(id);
                self.tries.insert_tuple(canon_id, node, id, false);
            }
            TrieEdit::Union {
                id,
                old_canon_id,
                new_canon_id,
            } => {
                let node = self.ssa.get(id);
                if let Some(inserted_id) = self.tries.inserted_as(id)
                    && inserted_id != new_canon_id
                {
                    self.tries.remove_tuple(inserted_id, node, id);
                    self.tries.insert_tuple(new_canon_id, node, id, false);
                }
                for user in self.ssa.users(old_canon_id).cloned() {
                    let user_node = self.ssa.get(user);
                    if let Some(inserted_id) = self.tries.inserted_as(user) {
                        self.tries.remove_tuple(inserted_id, user_node, user);
                    }
                }
            }
            TrieEdit::RevertUnion {
                id,
                old_canon_id,
                new_canon_id,
                parent_version,
            } => {
                let node = self.ssa.get(id);
                if let Some(inserted_id) = self.tries.inserted_as(id)
                    && inserted_id != new_canon_id
                {
                    assert_eq!(inserted_id, old_canon_id,);
                    self.tries.remove_tuple(old_canon_id, node, id);
                    self.tries.insert_tuple(new_canon_id, node, id, false);
                }
                for user in self.ssa.users(id).cloned() {
                    let user_node = self.ssa.get(user);
                    let version = self.ids.versions[&parent_version].as_ref();
                    let user_canon = version.find(user);
                    if version.is_canonical(user_node) {
                        if let Some(inserted_id) = self.tries.inserted_as(user) {
                            assert_eq!(inserted_id, user_canon);
                        } else {
                            self.tries.insert_tuple(user_canon, user_node, user, false);
                        }
                    }
                }
            }
        }
    }

    pub fn check_trie_consistency(&mut self) {
        take(&mut self.trie_edits)
            .into_iter()
            .for_each(|edit| self.apply_edit(edit));
        let mut tries = Tries::default();
        for id in 0..self.ssa.num_nodes() {
            let node = self.ssa.get(id);
            let canon_id = self.ids.find(id);
            if self.ids.is_canonical(node) {
                tries.insert_tuple(canon_id, node, id, false);
            }
        }
        assert_eq!(tries, self.tries, "{:?}", self.ssa);
        println!("checked {:?}", tries);
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
        saturator.check_trie_consistency();
        saturator.saturate();
        saturator.check_trie_consistency();
        assert_eq!(saturator.ssa.num_nodes(), 0);

        use SSA::*;
        let p1 = saturator.intern(Param(0, Type::I64));
        let p2 = saturator.intern(Param(1, Type::I64));
        saturator.check_trie_consistency();
        saturator.saturate();
        saturator.check_trie_consistency();
        // Param(0), Param(1)
        assert_eq!(saturator.ssa.num_nodes(), 2);

        saturator.intern(Binary(BinaryOp::Add, p1, p2));
        saturator.check_trie_consistency();
        saturator.saturate();
        saturator.check_trie_consistency();
        // Param(0), Param(1), Add(p1, p2), Add(p2, p1)
        assert_eq!(saturator.ssa.num_nodes(), 4);

        saturator.union(p1, p2);
        saturator.check_trie_consistency();
        saturator.saturate();
        saturator.check_trie_consistency();
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
        saturator.check_trie_consistency();

        saturator.union(p1, p2);
        saturator.saturate();
        saturator.check_trie_consistency();

        let guard_true = saturator.ssa.add_block(SSABlock::Guard(entry, eq1, true));
        saturator.create_version(guard_true);
        saturator.move_to_version(guard_true);
        saturator.check_trie_consistency();
        let add1 = saturator.intern(Binary(Add, n1, n2));
        let add2 = saturator.intern(Binary(Add, n2, n1));
        let eq2 = saturator.intern(Binary(NE, add1, add2));
        let false_constant = saturator.intern(Constant(crate::nonssa::Constant::Bool(false)));
        saturator.saturate();
        saturator.check_trie_consistency();
        assert_eq!(saturator.find(false_constant), saturator.find(eq2));

        let guard_false = saturator
            .ssa
            .add_block(SSABlock::Guard(guard_true, eq1, false));
        saturator.create_version(guard_false);
        saturator.move_to_version(guard_false);
        saturator.check_trie_consistency();
        let mul1 = saturator.intern(Binary(Mul, n2, one));
        let add1 = saturator.intern(Binary(Add, n1, n2));
        saturator.intern(Binary(Add, mul1, add1));
        saturator.saturate();
        saturator.check_trie_consistency();

        saturator.move_to_version(guard_true);
        saturator.check_trie_consistency();
        saturator.move_to_version(guard_false);
        saturator.check_trie_consistency();
    }
}
