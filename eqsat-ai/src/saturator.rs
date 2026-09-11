use std::collections::{HashSet, VecDeque};

use crate::rw::{Tries, apply_rws};
use crate::ssa::{SSA, SSAId, SSAProgram};
use crate::version::Version;

#[derive(Default)]
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
            self.rebuild();

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
                for user in self.ssa.users(id) {
                    worklist.push_back(*user);
                }
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::nonssa::BinaryOp;
    
    use super::*;

    #[test]
    fn saturator1() {
        let mut saturator = Saturator::default();
        saturator.saturate();
        assert_eq!(saturator.ssa.num_nodes(), 0);

        use SSA::*;
        let p1 = saturator.intern(Param(0));
        let p2 = saturator.intern(Param(1));
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
}
