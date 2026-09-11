use std::collections::HashSet;

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
}
