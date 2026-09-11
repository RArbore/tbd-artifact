use std::collections::{HashMap, HashSet};
use core::assert_matches;

use symbol_table::GlobalSymbol as Symbol;

use crate::nonssa::{Block, BlockId, Expr, NonSSAFunc};
use crate::ssa::{SSA, SSABlock, SSABlockId, SSAId, SSAProgram};

pub fn abstract_interpret(ssa: &mut SSAProgram, name: Symbol, nonssa: &NonSSAFunc) {
    use Block::*;
    assert_matches!(nonssa.cfg[0], Entry);
    let mut deps: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();
    for (id, block) in nonssa.cfg.iter().enumerate() {
        deps.entry(id).or_default();
        match block {
            Entry => assert_eq!(id, 0),
            Guard { pred, .. } | Assign { pred, .. } | Return { pred, .. } => {
                deps.entry(*pred).or_default().insert(id);
            }
            Merge { pred1, pred2 } => {
                deps.entry(*pred1).or_default().insert(id);
                deps.entry(*pred2).or_default().insert(id);
            }
        }
    }

    let mut context = AIContext {
        name,
        vars: Default::default(),
        blocks: Default::default(),
        ssa,
    };
    // A faster interpreter would walk the non-SSA CFG in WTO. We use a worklist for two reasons.
    // 1. Laziness.
    // 2. We could randomize the order of blocks in the worklist to stress test the interpreter.
    let mut worklist = vec![0];
    while let Some(block) = worklist.pop() {
        if context.visit_block(nonssa, block) {
            worklist.extend(deps[&block].iter());
        }
    }
}

// This is the data type that we would want to change to Okasaki maps to follow Lemerre's advice.
type VarMap = HashMap<Symbol, SSAId>;

#[derive(Debug)]
struct AIContext<'a> {
    name: Symbol,
    // At each (visited) original block, map each variable to an SSA value.
    vars: HashMap<BlockId, VarMap>,
    // Map each (visited) original block to a SSA block - also indicate whether this SSA block is
    // specific to this non-SSA block or not. Intuitively, a non-SSA block may go from not having a
    // SSA block made for it to having a SSA block made for it (but not the other way around) - when
    // this happens, we need to allocate a fresh SSABlockId for the created SSA block, but we only
    // want to do this once, so the analysis terminates.
    blocks: HashMap<BlockId, (SSABlockId, bool)>,

    ssa: &'a mut SSAProgram,
}

impl<'a> AIContext<'a> {
    fn update_vars(&mut self, block: BlockId, vars: VarMap) -> bool {
        if self
            .vars
            .get(&block)
            .map(|old_vars| old_vars != &vars)
            .unwrap_or(true)
        {
            self.vars.insert(block, vars);
            // If the variable mappings for this block changed, then we need to re-interpret its
            // successor blocks.
            true
        } else {
            false
        }
    }

    // The transfer function of a block does not depend on the kind of block of a predecessor, and
    // since SSABlockIds are stable, we will never need to re-interpret a successor block just
    // because a block gets re-interpreted as a new SSA block (however, if this re-interpretation
    // also results in an update in variables, see `update_vars`, then a re-interpretation of
    // successor blocks is warranted).
    fn update_new_block(&mut self, block_id: BlockId, new_ssa_block: SSABlock) -> SSABlockId {
        if let Some((old_ssa_block_id, true)) = self.blocks.get(&block_id) {
            // If we already created a new SSA block for this non-SSA block, re-use the SSABlockId.
            self.ssa.set_block(new_ssa_block, *old_ssa_block_id);
            *old_ssa_block_id
        } else {
            // If we haven't created a new SSA block for this non-SSA block (either because we
            // haven't visited this non-SSA block yet or because we have and previously assigned it
            // a non-fresh SSA block), then create a new SSABlockId and map the non-SSA block to it.
            let new_ssa_block_id = self.ssa.add_block(new_ssa_block);
            self.blocks.insert(block_id, (new_ssa_block_id, true));
            new_ssa_block_id
        }
    }

    fn update_block(&mut self, block_id: BlockId, ssa_block_id: SSABlockId) {
        assert!(
            self.blocks
                .get(&block_id)
                .map(|(_, fresh)| !fresh)
                .unwrap_or(true)
        );
        self.blocks.insert(block_id, (ssa_block_id, false));
    }

    fn is_bottom(&self, block_id: BlockId) -> bool {
        let has_vars = self.vars.contains_key(&block_id);
        let has_block = self.blocks.contains_key(&block_id);
        assert_eq!(has_vars, has_block);
        !has_vars
    }

    fn to_ssa_block(&self, block_id: BlockId) -> SSABlockId {
        self.blocks[&block_id].0
    }

    fn visit_block(&mut self, nonssa: &NonSSAFunc, block: BlockId) -> bool {
        use Block::*;
        match &nonssa.cfg[block] {
            Entry => self.visit_entry(nonssa, block),
            Guard { pred, cond } => self.visit_guard(block, *pred, cond),
            Assign { pred, var, expr } => self.visit_assign(block, *pred, *var, expr),
            Merge { pred1, pred2 } => self.visit_merge(block, *pred1, *pred2),
            Return { pred, exprs } => self.visit_return(block, *pred, exprs),
        }
    }

    fn visit_entry(&mut self, nonssa: &NonSSAFunc, block: BlockId) -> bool {
        self.update_new_block(block, SSABlock::Entry);
        let vars = nonssa
            .params
            .iter()
            .enumerate()
            .map(|(idx, param)| (*param, self.ssa.intern(SSA::Param(idx))))
            .collect();
        self.update_vars(block, vars)
    }

    fn visit_guard(&mut self, block: BlockId, pred: BlockId, cond: &Expr) -> bool {
        let value = visit_expr(&mut self.ssa, cond, &self.vars[&pred]);
        if self.ssa.is_always_false(value) {
            false
        } else {
            if self.ssa.is_always_true(value) {
                self.update_block(block, self.to_ssa_block(pred));
            } else {
                self.update_new_block(block, SSABlock::Guard(self.to_ssa_block(pred), value));
            }
            // Guards make no assignments.
            self.update_vars(block, self.vars[&pred].clone())
        }
    }

    fn visit_assign(&mut self, block: BlockId, pred: BlockId, var: Symbol, expr: &Expr) -> bool {
        self.update_block(block, self.to_ssa_block(pred));
        let mut vars = self.vars[&pred].clone();
        let value = visit_expr(&mut self.ssa, expr, &vars);
        vars.insert(var, value);
        self.update_vars(block, vars)
    }

    fn visit_merge(&mut self, block: BlockId, pred1: BlockId, pred2: BlockId) -> bool {
        // Merge nodes are the only nodes with multiple predecessors - this also means that they are
        // the only nodes that might get visited before one of their predecessors.
        match (self.is_bottom(pred1), self.is_bottom(pred2)) {
            (true, true) => false,
            (false, true) => {
                self.update_block(block, self.to_ssa_block(pred1));
                self.update_vars(block, self.vars[&pred1].clone())
            }
            (true, false) => {
                self.update_block(block, self.to_ssa_block(pred2));
                self.update_vars(block, self.vars[&pred2].clone())
            }
            (false, false) => {
                let vars1 = &self.vars[&pred1];
                let vars2 = &self.vars[&pred2];
                let ssa_pred1 = self.to_ssa_block(pred1);
                let ssa_pred2 = self.to_ssa_block(pred2);
                let mut new_vars = HashMap::new();
                let mut knot_values = HashMap::new();
                for (var, value1) in vars1 {
                    if let Some(value2) = vars2.get(var) {
                        if value1 == value2 {
                            new_vars.insert(*var, *value1);
                        } else {
                            let knot_id = self.ssa.intern_knot(block, *var);
                            let knot = self.ssa.intern(SSA::Knot(knot_id));
                            new_vars.insert(*var, knot);
                            knot_values.insert(knot_id, (*value1, *value2));
                        }
                    }
                }
                self.update_new_block(block, SSABlock::Merge(ssa_pred1, ssa_pred2, knot_values));
                self.update_vars(block, new_vars)
            }
        }
    }

    fn visit_return(&mut self, block: BlockId, pred: BlockId, exprs: &[Expr]) -> bool {
        let pred_vars = &self.vars[&pred];
        let values = exprs
            .into_iter()
            .map(|expr| visit_expr(&mut self.ssa, expr, pred_vars))
            .collect();
        let return_block_id =
            self.update_new_block(block, SSABlock::Return(self.to_ssa_block(pred), values));
        self.ssa.add_exit(self.name, return_block_id);
        // Returns have no successors;
        false
    }
}

// Can't be a member of AIContext because we don't have field borrows.
fn visit_expr(ssa: &mut SSAProgram, expr: &Expr, vars: &VarMap) -> SSAId {
    use Expr::*;
    match expr {
        Number { num } => ssa.intern(SSA::Constant(*num)),
        Variable { var } => vars[var],
        Unary { op, input } => {
            let input = visit_expr(ssa, input, vars);
            ssa.intern(SSA::Unary(*op, input))
        }
        Binary { op, lhs, rhs } => {
            let lhs = visit_expr(ssa, lhs, vars);
            let rhs = visit_expr(ssa, rhs, vars);
            ssa.intern(SSA::Binary(*op, lhs, rhs))
        }
    }
}
