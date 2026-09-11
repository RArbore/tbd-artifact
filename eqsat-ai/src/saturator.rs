use std::collections::{HashSet, VecDeque};

use crate::rw::{Tries, apply_rws};
use crate::ssa::{SSA, SSAId, SSAProgram};
use crate::version::Version;

pub struct Saturator {
    ssa: SSAProgram,
    version: Version,

    // What nodes have either been:
    // 1. Added to the hash-cons...
    // 2. Have had their canonical SSAId changed...
    // ...since the last iteration of rewriting.
    delta: HashSet<SSAId>,
}

impl Saturator {
    pub fn intern(&mut self, ssa: SSA) -> SSAId {
        let before = self.ssa.num_nodes();
        let id = self.ssa.intern(ssa);
        let after = self.ssa.num_nodes();
        if before != after {
            self.delta.insert(id);
        }
        id
    }

    pub fn union(&mut self, x: SSAId, y: SSAId) {
        self.version.union_with(x, y, |id| {
            self.delta.insert(id);
        });
    }

    pub fn saturate(&mut self) {
        while !self.delta.is_empty() {
            // TODO: This rebuilds the tries from scratch. Do incremental trie construction!
            let mut tries = Tries::default();
            for id in 0..self.ssa.num_nodes() {
                let node = self.ssa.get(id);
                if self.version.is_canonical(node) {
                    tries.insert_tuple(self.version.find_mut(id), node, id, false);
                }
            }
            for id in &self.delta {
                let node = self.ssa.get(*id);
                if self.version.is_canonical(node) {
                    tries.insert_tuple(self.version.find_mut(*id), node, *id, true);
                }
            }
            self.delta.clear();

            apply_rws(&tries, self);
            self.rebuild();
        }
    }

    fn rebuild(&mut self) {
        let mut worklist = VecDeque::new();
        for id in &self.delta {
            // The only nodes in `delta` that should fail this check are new nodes.
            if *id != self.version.find_mut(*id) {
                for user in self.ssa.users(*id) {
                    worklist.push_back(*user);
                }
            }
        }

        while let Some(id) = worklist.pop_front() {
            let old_ssa = self.ssa.get(id);
            let new_ssa = self.version.canonicalize(old_ssa);
            // We should only ever insert a node into the worklist if it's non-canonical.
            assert_ne!(old_ssa, new_ssa);
            let new_id = self.ssa.intern(new_ssa);
            self.version.union_with(id, new_id, |id| {
                self.delta.insert(id);
                worklist.push_back(id);
            });
        }
    }
}
