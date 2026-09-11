use std::collections::HashSet;

use crate::rw::{Tries, apply_rws};
use crate::ssa::{SSA, SSAId, SSAProgram};
use crate::version::Version;

pub struct Saturator {
    ssa: SSAProgram,
    version: Version,

    delta: HashSet<SSAId>,
}

impl Saturator {}
