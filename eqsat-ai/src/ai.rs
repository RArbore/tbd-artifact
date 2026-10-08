use std::collections::{BTreeSet, HashMap, HashSet, hash_map::Entry};

use symbol_table::GlobalSymbol as Symbol;

use crate::analysis::Domain;
use crate::nonssa::{Block, BlockId, Constant, Expr, NonSSAFunc, Type};
use crate::saturator::Saturator;
use crate::ssa::{Analysis, KnotId, SSA, SSABlock, SSABlockId, SSAId};

pub fn abstract_interpret(saturator: &mut Saturator, name: Symbol, nonssa: &NonSSAFunc) {
    let rpo = nonssa.rpo();
    let mut context = AIContext {
        name,
        vars: HashMap::new(),
        blocks: HashMap::new(),
        knot_map: KnotMap::default(),
        old_analyses: HashMap::new(),
        saturator,
    };

    let mut last_knot_count = None;
    loop {
        for block in &rpo {
            context.visit_block(&nonssa, *block);
        }
        if last_knot_count == Some(context.knot_map.num_knots()) {
            break;
        }
        last_knot_count = Some(context.knot_map.num_knots());
    }
}

// We map each program variable to a SSAId. This is the data type to change to Okasaki maps to follow
// Lemerre's advice.
type VarMap = HashMap<Symbol, SSAId>;

// Intern tuples of BlockId, variable sets, and analyses to KnotId.
#[derive(Debug, Default)]
struct KnotMap(HashMap<(BlockId, BTreeSet<Symbol>, Analysis), KnotId>);

impl KnotMap {
    fn intern_knot(&mut self, block: BlockId, var: BTreeSet<Symbol>, analysis: Analysis) -> KnotId {
        let new_id = self.0.len();
        let entry = self.0.entry((block, var, analysis));
        *entry.or_insert(new_id)
    }

    fn num_knots(&self) -> usize {
        self.0.len()
    }
}

struct AIContext<'a> {
    name: Symbol,
    // At each (visited) original block, map each variable to an SSA value.
    vars: HashMap<BlockId, VarMap>,
    // Map each (visited) original block to a SSA block.
    blocks: HashMap<BlockId, SSABlockId>,
    // Intern sets of variables and locations to KnotIds (knots are our name for "symbolic variables"
    // from Lemerre's paper).
    knot_map: KnotMap,
    // Old analyses along widening edges.
    old_analyses: HashMap<(SSABlockId, SSABlockId), Analysis>,
    // All building of the SSA program goes through the Saturator. This includes applying rewrite
    // rules and managing versions.
    saturator: &'a mut Saturator,
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

    fn update_block(&mut self, block_id: BlockId, new_ssa_block: SSABlock) -> SSABlockId {
        let ssa_block_id = if let Some(old_ssa_block_id) = self.blocks.get(&block_id) {
            // If we already created a SSA block for this non-SSA block, re-use the SSABlockId.
            self.saturator
                .ssa
                .set_block(new_ssa_block, *old_ssa_block_id);
            *old_ssa_block_id
        } else {
            // If we haven't created a SSA block for this non-SSA block, create a new SSABlockId.
            let new_ssa_block_id = self.saturator.ssa.add_block(new_ssa_block);
            self.blocks.insert(block_id, new_ssa_block_id);
            new_ssa_block_id
        };

        // Create a new version every time we visit a block. This also moves to the new version.
        self.saturator.create_version(ssa_block_id);
        ssa_block_id
    }

    fn is_bottom(&self, block_id: BlockId) -> bool {
        let has_vars = self.vars.contains_key(&block_id);
        if let Some(ssa_block_id) = self.blocks.get(&block_id) {
            assert!(has_vars);
            self.saturator.is_contradiction_in_version(*ssa_block_id)
        } else {
            assert!(!has_vars);
            true
        }
    }

    fn visit_expr(&mut self, expr: &Expr, vars: BlockId) -> SSAId {
        use Expr::*;
        match expr {
            Constant { val } => self.saturator.intern(SSA::Constant(*val)),
            Variable { var } => self.saturator.find(self.vars[&vars][var]),
            Unary { op, input } => {
                let input = self.visit_expr(input, vars);
                self.saturator.intern(SSA::Unary(*op, input))
            }
            Binary { op, lhs, rhs } => {
                let lhs = self.visit_expr(lhs, vars);
                let rhs = self.visit_expr(rhs, vars);
                self.saturator.intern(SSA::Binary(*op, lhs, rhs))
            }
        }
    }

    fn assume(&mut self, id: SSAId, direction: bool) {
        let val = self
            .saturator
            .intern(SSA::Constant(Constant::Bool(direction)));
        self.saturator.union(id, val);
    }

    fn visit_block(&mut self, nonssa: &NonSSAFunc, block: BlockId) {
        use Block::*;
        match &nonssa.cfg[block] {
            Entry => self.visit_entry(nonssa, block),
            Guard {
                pred,
                cond,
                direction,
            } => self.visit_guard(block, *pred, cond, *direction),
            Assign { pred, var, expr } => self.visit_assign(block, *pred, *var, expr),
            Merge { pred1, pred2 } => self.visit_merge(block, *pred1, *pred2),
            Return { pred, exprs } => self.visit_return(block, *pred, exprs),
        }
    }

    fn visit_entry(&mut self, nonssa: &NonSSAFunc, block: BlockId) {
        self.update_block(block, SSABlock::Entry);
        let vars = nonssa
            .params
            .iter()
            .enumerate()
            .map(|(idx, (param, ty))| {
                (
                    *param,
                    // There is no version for before the entry. That's fine, because we won't have
                    // equated function parameters with anything yet.
                    self.saturator.intern(SSA::Param(idx, *ty)),
                )
            })
            .collect();
        // This shouldn't find anything, but we need to clear the delta set.
        self.saturator.saturate();
        self.update_vars(block, vars);
    }

    fn visit_guard(&mut self, block: BlockId, pred: BlockId, cond: &Expr, direction: bool) {
        if self.is_bottom(pred) {
            return;
        }
        let ssa_pred = self.blocks[&pred];
        self.saturator.move_to_version(ssa_pred);
        let value = self.visit_expr(cond, pred);
        assert_eq!(self.saturator.ssa.ty(value), Type::Bool);
        let false_value = self.saturator.intern(SSA::Constant(Constant::Bool(false)));
        let true_value = self.saturator.intern(SSA::Constant(Constant::Bool(true)));

        // Saturate so that the condition is analyzed.
        self.saturator.saturate();
        let always_false = self.saturator.find(value) == self.saturator.find(false_value);
        let always_true = self.saturator.find(value) == self.saturator.find(true_value);
        assert!(!always_false || !always_true);

        if !(always_false && direction || always_true && !direction) {
            let ssa_block = if always_false && !direction || always_true && direction {
                self.update_block(block, SSABlock::Identity(ssa_pred))
            } else {
                let ssa_block =
                    self.update_block(block, SSABlock::Guard(ssa_pred, value, direction));

                // When the guard is necessary, we want to assume the guard condition is either true
                // or false (depending on `direction`) in the created version.
                self.assume(value, direction);
                // We need to saturate after the union from the assumption, since jumping to a
                // different version could cause the potential delta to be lost in this version.
                self.saturator.saturate();
                ssa_block
            };
            assert!(ssa_pred < ssa_block);
            // Guards make no assignments.
            self.update_vars(block, self.vars[&pred].clone());
        }
    }

    fn visit_assign(&mut self, block: BlockId, pred: BlockId, var: Symbol, expr: &Expr) {
        if self.is_bottom(pred) {
            return;
        }
        let ssa_pred = self.blocks[&pred];
        self.saturator.move_to_version(ssa_pred);
        let value = self.visit_expr(expr, pred);
        // We need to saturate after every assignment because a jump to an arbitrary other version
        // may cause the delta to be lost.
        self.saturator.saturate();
        let mut vars = self.vars[&pred].clone();
        let canon_id = self.saturator.find(value);
        vars.insert(var, canon_id);
        let ssa_block = self.update_block(block, SSABlock::Identity(ssa_pred));
        assert!(ssa_pred < ssa_block);
        self.update_vars(block, vars);
    }

    fn visit_merge(&mut self, block: BlockId, pred1: BlockId, pred2: BlockId) {
        // Merge nodes are the only nodes with multiple predecessors - this also means that they are
        // the only nodes that might get visited before one of their predecessors.
        match (self.is_bottom(pred1), self.is_bottom(pred2)) {
            (true, true) => {}
            (false, true) => {
                let ssa_pred = self.blocks[&pred1];
                let ssa_block = self.update_block(block, SSABlock::Identity(ssa_pred));
                assert!(ssa_pred < ssa_block);
                self.update_vars(block, self.vars[&pred1].clone());
            }
            (true, false) => {
                let ssa_pred = self.blocks[&pred2];
                let ssa_block = self.update_block(block, SSABlock::Identity(ssa_pred));
                assert!(ssa_pred < ssa_block);
                self.update_vars(block, self.vars[&pred2].clone());
            }
            (false, false) => {
                let ssa_pred1 = self.blocks[&pred1];
                let ssa_pred2 = self.blocks[&pred2];
                assert_ne!(ssa_pred1, ssa_pred2);

                // Saturate because discovered equalities may help us avoid making knots.
                self.saturator.move_to_version(ssa_pred1);
                self.saturator.saturate();
                self.saturator.move_to_version(ssa_pred2);
                self.saturator.saturate();

                // Helper to implement widening.
                let mut widen = |analysis, ssa_pred| {
                    let Some(ssa_block) = self.blocks.get(&block).cloned() else {
                        return analysis;
                    };
                    if ssa_pred < ssa_block {
                        return analysis;
                    }

                    match self.old_analyses.entry((ssa_pred, ssa_block)) {
                        Entry::Occupied(mut entry) => {
                            let widened = entry.get().widen(&analysis);
                            entry.insert(widened);
                            widened
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(analysis);
                            analysis
                        }
                    }
                };

                let mut pair_to_vars: HashMap<(SSAId, SSAId, Analysis), HashSet<Symbol>> =
                    HashMap::new();
                for (var, value1) in &self.vars[&pred1] {
                    if let Some(value2) = self.vars[&pred2].get(var) {
                        let value1 = self.saturator.find_in_version(*value1, ssa_pred1);
                        let value2 = self.saturator.find_in_version(*value2, ssa_pred2);
                        let analysis1 = widen(self.saturator.analysis_in_version(value1, ssa_pred1), ssa_pred1);
                        let analysis2 = widen(self.saturator.analysis_in_version(value2, ssa_pred2), ssa_pred2);
                        // Group variables by pair of joined SSAIds.
                        pair_to_vars
                            .entry((value1, value2, analysis1.join(&analysis2)))
                            .or_default()
                            .insert(*var);
                    }
                }

                // We create a single knot per set of variables sharing values.
                let mut knot_values = HashMap::new();
                let mut pair_to_knot = vec![];
                for ((value1, value2, analysis), vars) in pair_to_vars {
                    let knot_id =
                        self.knot_map
                            .intern_knot(block, vars.iter().cloned().collect(), analysis);
                    knot_values.insert(knot_id, (value1, value2));
                    pair_to_knot.push((value1, value2, vars, knot_id, analysis));
                }
                let new_block =
                    self.update_block(block, SSABlock::Merge(ssa_pred1, ssa_pred2, knot_values));
                assert_ne!(new_block, ssa_pred1);
                assert_ne!(new_block, ssa_pred2);

                // Now that we have a version for this block, merge the IDs in the intersection of
                // the sets in the predecessor versions with the knots.
                let mut new_vars = HashMap::new();
                for (value1, value2, vars, knot_id, analysis) in pair_to_knot {
                    let ty1 = self.saturator.ssa.ty(value1);
                    let ty2 = self.saturator.ssa.ty(value2);
                    assert_eq!(ty1, ty2);
                    let mut knot = self.saturator.intern(SSA::Knot(knot_id, ty1, analysis));

                    let idom = self.saturator.version(new_block).parent().unwrap();
                    let set1: HashSet<_> = self
                        .saturator
                        .version(ssa_pred1)
                        .set(value1, Some(idom))
                        .collect();
                    let set2: HashSet<_> = self
                        .saturator
                        .version(ssa_pred2)
                        .set(value2, Some(idom))
                        .collect();
                    for id in set1.intersection(&set2) {
                        knot = self.saturator.union(knot, *id);
                    }
                    for var in vars {
                        new_vars.insert(var, knot);
                    }
                }

                // We need to saturate after the unions above, since jumping to a different version
                // could cause the delta to be lost in this version.
                self.saturator.saturate();
                self.update_vars(block, new_vars);
            }
        }
    }

    fn visit_return(&mut self, block: BlockId, pred: BlockId, exprs: &[Expr]) {
        if self.is_bottom(pred) {
            return;
        }
        let ssa_pred = self.blocks[&pred];
        self.saturator.move_to_version(ssa_pred);
        let values: Vec<_> = exprs
            .into_iter()
            .map(|expr| self.visit_expr(expr, pred))
            .collect();

        // Saturate so that the returned SSAIds are analyzed.
        self.saturator.saturate();

        // Re-collect the values so that they are canonical SSAIds.
        let values = values
            .into_iter()
            .map(|id| self.saturator.find(id))
            .collect();
        let ssa_block = self.update_block(block, SSABlock::Return(ssa_pred, values));
        assert!(ssa_pred < ssa_block);
        self.saturator.ssa.add_exit(self.name, ssa_block);
    }
}
