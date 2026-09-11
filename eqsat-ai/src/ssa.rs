use std::collections::{HashMap, HashSet};
use symbol_table::GlobalSymbol as Symbol;

use crate::nonssa::{BinaryOp, BlockId, UnaryOp};

pub type SSAId = usize;
pub type SSABlockId = usize;
pub type KnotId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SSA {
    Constant(i32),
    Param(usize),
    Unary(UnaryOp, SSAId),
    Binary(BinaryOp, SSAId, SSAId),
    // Knots serve the function of phi functions in our SSA form. They can be thought of as block
    // arguments (see SSABlock::Merge below).
    Knot(KnotId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SSABlock {
    Entry,
    Guard(SSABlockId, SSAId),
    // The third field maps knots to SSA values corresponding to the two predecessors (think of these
    // like the inputs to a phi function).
    Merge(SSABlockId, SSABlockId, HashMap<KnotId, (SSAId, SSAId)>),
    Return(SSABlockId, Vec<SSAId>),
}

#[derive(Debug, Clone, Default)]
struct SSAHashCons {
    map: HashMap<SSA, SSAId>,
    vec: Vec<SSA>,
    users: HashMap<SSAId, HashSet<SSAId>>,
}

#[derive(Debug, Clone, Default)]
pub struct SSAProgram {
    ssa: SSAHashCons,
    cfg: Vec<SSABlock>,
    exits: HashMap<Symbol, SSABlockId>,

    // Intern tuples of BlockId and variable name to KnotId.
    knot_map: HashMap<(BlockId, Symbol), KnotId>,
}

impl SSAHashCons {
    fn num_nodes(&self) -> usize {
        assert_eq!(self.map.len(), self.vec.len());
        self.vec.len()
    }

    fn intern(&mut self, ssa: SSA) -> SSAId {
        let entry = self.map.entry(ssa);
        *entry.or_insert_with(|| {
            let id = self.vec.len();
            self.vec.push(ssa);
            use SSA::*;
            match ssa {
                Unary(_, input) => {
                    self.users.entry(input).or_default().insert(id);
                }
                Binary(_, lhs, rhs) => {
                    self.users.entry(lhs).or_default().insert(id);
                    self.users.entry(rhs).or_default().insert(id);
                }
                _ => {}
            }
            id
        })
    }

    fn get(&self, id: SSAId) -> SSA {
        self.vec[id]
    }

    pub fn users(&mut self, id: SSAId) -> &HashSet<SSAId> {
        self.users.entry(id).or_default()
    }
}

impl SSAProgram {
    pub fn num_nodes(&self) -> usize {
        self.ssa.num_nodes()
    }

    pub fn intern(&mut self, ssa: SSA) -> SSAId {
        self.ssa.intern(ssa)
    }

    pub fn get(&self, id: SSAId) -> SSA {
        self.ssa.get(id)
    }

    pub fn users(&mut self, id: SSAId) -> &HashSet<SSAId> {
        self.ssa.users(id)
    }

    pub fn add_block(&mut self, block: SSABlock) -> SSABlockId {
        let id = self.cfg.len();
        self.cfg.push(block);
        id
    }

    pub fn set_block(&mut self, block: SSABlock, id: SSABlockId) {
        self.cfg[id] = block;
    }

    pub fn get_block(&self, id: SSABlockId) -> &SSABlock {
        &self.cfg[id]
    }

    pub fn is_always_false(&self, id: SSAId) -> bool {
        self.ssa.get(id) == SSA::Constant(0)
    }

    pub fn is_always_true(&self, id: SSAId) -> bool {
        self.ssa.get(id) == SSA::Constant(1)
    }

    pub fn intern_knot(&mut self, block: BlockId, var: Symbol) -> KnotId {
        let new_id = self.knot_map.len();
        let entry = self.knot_map.entry((block, var));
        *entry.or_insert(new_id)
    }

    pub fn add_exit(&mut self, name: Symbol, return_block: SSABlockId) {
        self.exits.insert(name, return_block);
    }
}
