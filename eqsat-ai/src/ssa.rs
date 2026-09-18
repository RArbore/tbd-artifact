use std::collections::{HashMap, HashSet};
use symbol_table::GlobalSymbol as Symbol;

use crate::nonssa::{BinaryOp, Constant, Type, UnaryOp};

pub type SSAId = usize;
pub type SSABlockId = usize;
pub type KnotId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SSA {
    Constant(Constant),
    Param(usize, Type),
    Unary(UnaryOp, SSAId),
    Binary(BinaryOp, SSAId, SSAId),
    // Knots serve the function of phi functions in our SSA form. They can be thought of as block
    // arguments (see SSABlock::Merge below).
    Knot(KnotId, Type),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SSABlock {
    Entry,
    Guard(SSABlockId, SSAId, bool),
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
    types: Vec<Type>,
    cfg: Vec<SSABlock>,
    exits: HashMap<Symbol, SSABlockId>,
}

impl SSA {
    fn ty(&self, types: &Vec<Type>) -> Type {
        match *self {
            SSA::Constant(Constant::I64(_)) => Type::I64,
            SSA::Constant(Constant::Bool(_)) => Type::Bool,
            SSA::Param(_, ty) | SSA::Knot(_, ty) => ty,
            SSA::Unary(UnaryOp::Neg, input) => {
                assert_eq!(types[input], Type::I64);
                Type::I64
            }
            SSA::Unary(UnaryOp::Not, input) => {
                assert_eq!(types[input], Type::Bool);
                Type::Bool
            }
            SSA::Binary(op, lhs, rhs) => match op {
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
                    assert_eq!(types[lhs], Type::I64);
                    assert_eq!(types[rhs], Type::I64);
                    Type::I64
                }
                BinaryOp::And | BinaryOp::Or | BinaryOp::Xor => {
                    assert_eq!(types[lhs], Type::Bool);
                    assert_eq!(types[rhs], Type::Bool);
                    Type::Bool
                }
                BinaryOp::EE
                | BinaryOp::NE
                | BinaryOp::LT
                | BinaryOp::LE
                | BinaryOp::GT
                | BinaryOp::GE => {
                    assert_eq!(types[lhs], Type::I64);
                    assert_eq!(types[rhs], Type::I64);
                    Type::Bool
                }
            },
        }
    }

    pub fn is_param_or_knot(&self) -> bool {
        match self {
            SSA::Param(_, _) | SSA::Knot(_, _) => true,
            _ => false,
        }
    }
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
        let id = self.ssa.intern(ssa);
        if id >= self.types.len() {
            assert_eq!(id, self.types.len());
            self.types.push(ssa.ty(&self.types));
        }
        id
    }

    pub fn get(&self, id: SSAId) -> SSA {
        self.ssa.get(id)
    }

    pub fn ty(&self, id: SSAId) -> Type {
        self.types[id]
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

    pub fn exit(&self, name: Symbol) -> SSABlockId {
        self.exits[&name]
    }

    pub fn add_exit(&mut self, name: Symbol, return_block: SSABlockId) {
        self.exits.insert(name, return_block);
    }
}
