use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use symbol_table::GlobalSymbol as Symbol;

use crate::analysis::Domain;
use crate::nonssa::{Block, BlockId, Constant, Expr, NonSSAFunc, State, Type, WTO};
use crate::saturator::Saturator;
use crate::ssa::{Analysis, KnotId, SSA, SSABlock, SSABlockId, SSAId};

const MAX_NARROW_ITERS: usize = 4;

// We map each program variable to a SSAId. This is the data type to change to Patricia trees to
// follow Lemerre's advice.
pub type VarMap = FxHashMap<Symbol, SSAId>;

pub struct AnalysisResult {
    pub vars: FxHashMap<BlockId, VarMap>,
    pub ssa_blocks: FxHashMap<BlockId, SSABlockId>,
    pub reachable_blocks: Vec<BlockId>,
    pub num_iterations: usize,
    pub num_interesting_visits: usize,
    pub num_rule_fires: usize,
}

pub fn abstract_interpret(
    saturator: &mut Saturator,
    name: Symbol,
    nonssa: &NonSSAFunc,
) -> AnalysisResult {
    let (wto, widening_edges) = nonssa.wto();
    let mut context = AIContext {
        name,
        vars: FxHashMap::default(),
        blocks: FxHashMap::default(),
        knot_map: KnotMap::default(),
        widening_edges,
        old_analyses: FxHashMap::default(),
        num_iterations: 0,
        num_interesting_visits: 0,
        saturator,
    };
    for wto in &wto {
        context.iterate_wto(&nonssa, wto);
    }
    let reachable_blocks = (0..nonssa.cfg.len())
        .filter(|id| !context.is_bottom(*id))
        .collect();
    AnalysisResult {
        vars: context.vars,
        ssa_blocks: context.blocks,
        reachable_blocks,
        num_iterations: context.num_iterations,
        num_interesting_visits: context.num_interesting_visits,
        num_rule_fires: context.saturator.num_rule_fires,
    }
}

// Intern tuples of BlockId, variable sets, and analyses to KnotId.
#[derive(Debug, Default)]
struct KnotMap(FxHashMap<(BlockId, BTreeSet<Symbol>, Analysis), KnotId>);

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
    vars: FxHashMap<BlockId, VarMap>,
    // Map each (visited) original block to a SSA block.
    blocks: FxHashMap<BlockId, SSABlockId>,
    // Intern sets of variables and locations to KnotIds (knots are our name for "symbolic variables"
    // from Lemerre's paper).
    knot_map: KnotMap,
    // Pre-computed widening edges. Maps merge blocks to predecessor on a widening edge, if any.
    widening_edges: FxHashMap<BlockId, BlockId>,
    // Old analyses along widening edges. Maps merge blocks and variables to the old analysis along a
    // widening edge, if any.
    old_analyses: FxHashMap<(BlockId, Symbol), Analysis>,
    // Track the number of iterations through the program, to determine when to stop narrowing.
    num_iterations: usize,
    // Track the number of blocks that were visited (and did something interesting), for statistics.
    num_interesting_visits: usize,
    // All building of the SSA program goes through the Saturator. This includes applying rewrite
    // rules and managing versions.
    saturator: &'a mut Saturator,
}

impl<'a> AIContext<'a> {
    fn iterate_wto(&mut self, nonssa: &NonSSAFunc, wto: &WTO) {
        match wto {
            WTO::Single(block) => self.visit_block(nonssa, *block),
            WTO::Component(head, wtos) => {
                let mut last_knot_count = None;
                loop {
                    self.visit_block(nonssa, *head);
                    for wto in wtos {
                        self.iterate_wto(nonssa, wto);
                    }
                    if last_knot_count == Some(self.knot_map.num_knots()) {
                        break;
                    }
                    last_knot_count = Some(self.knot_map.num_knots());
                }
            }
        }
    }

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

    fn visit_block(&mut self, nonssa: &NonSSAFunc, block: BlockId) {
        use Block::*;
        match &nonssa.cfg[block] {
            Entry => self.visit_entry(nonssa, block),
            Guard {
                pred,
                cond,
                direction,
            } => {
                if self.is_bottom(*pred) {
                    self.num_interesting_visits += 1;
                }
                self.visit_guard(block, *pred, cond, *direction);
            }
            Assign { pred, var, expr } => {
                if self.is_bottom(*pred) {
                    self.num_interesting_visits += 1;
                }
                self.visit_assign(block, *pred, *var, expr);
            }
            Merge { pred1, pred2 } => {
                if self.is_bottom(*pred1) || self.is_bottom(*pred2) {
                    self.num_interesting_visits += 1;
                }
                self.visit_merge(block, *pred1, *pred2);
            }
            Return { pred, exprs } => {
                if self.is_bottom(*pred) {
                    self.num_interesting_visits += 1;
                }
                self.visit_return(block, *pred, exprs);
            }
        }
    }

    fn visit_entry(&mut self, nonssa: &NonSSAFunc, block: BlockId) {
        self.update_block(block, SSABlock::Entry);
        self.saturator.intern(SSA::Constant(Constant::Bool(false)));
        self.saturator.intern(SSA::Constant(Constant::Bool(true)));
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
        // Saturate so that the delta from the condition is cleared.
        self.saturator.saturate();
        let canon_id = self.saturator.find(value);
        assert_eq!(self.saturator.ssa.ty(canon_id), Type::Bool);
        let ssa_block = self.update_block(block, SSABlock::Guard(ssa_pred, canon_id, direction));
        // Assume the guard condition is either true or false (depending on `direction`) in the
        // created version.
        let val = self
            .saturator
            .intern(SSA::Constant(Constant::Bool(direction)));
        self.saturator.union(canon_id, val);
        // We need to saturate after the union from the assumption, since jumping to a different
        // version could cause the potential delta to be lost in this version.
        self.saturator.saturate();
        assert!(ssa_pred < ssa_block);
        // Guards make no assignments.
        self.update_vars(block, self.vars[&pred].clone());
    }

    fn visit_assign(&mut self, block: BlockId, pred: BlockId, var: Symbol, expr: &Expr) {
        if self.is_bottom(pred) {
            return;
        }
        let ssa_pred = self.blocks[&pred];
        let ssa_block = self.update_block(block, SSABlock::Identity(ssa_pred));
        let value = self.visit_expr(expr, pred);
        // We need to saturate after every assignment to clear the delta set.
        self.saturator.saturate();
        let mut vars = self.vars[&pred].clone();
        let canon_id = self.saturator.find(value);
        vars.insert(var, canon_id);
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
                self.update_block(block, SSABlock::Identity(ssa_pred));
                self.update_vars(block, self.vars[&pred1].clone());
            }
            (true, false) => {
                let ssa_pred = self.blocks[&pred2];
                self.update_block(block, SSABlock::Identity(ssa_pred));
                self.update_vars(block, self.vars[&pred2].clone());
            }
            (false, false) => {
                let ssa_pred1 = self.blocks[&pred1];
                let ssa_pred2 = self.blocks[&pred2];
                assert_ne!(ssa_pred1, ssa_pred2);

                // Helper to implement widening.
                let mut widen = |mut analysis, var, pred| {
                    if let Some(edge) = self.widening_edges.get(&block)
                        && pred == *edge
                    {
                        if let Some(old_analysis) = self.old_analyses.get(&(block, var)) {
                            analysis = old_analysis.widen(&analysis);
                            if self.num_iterations >= MAX_NARROW_ITERS {
                                analysis = old_analysis.join(&analysis);
                            }
                        }
                        self.old_analyses.insert((block, var), analysis);
                    }
                    analysis
                };

                let mut pair_to_vars: FxHashMap<(SSAId, SSAId, Analysis), FxHashSet<Symbol>> =
                    FxHashMap::default();
                for (var, value1) in &self.vars[&pred1] {
                    if let Some(value2) = self.vars[&pred2].get(var) {
                        let value1 = self.saturator.find_in_version(*value1, ssa_pred1);
                        let value2 = self.saturator.find_in_version(*value2, ssa_pred2);
                        let analysis1 = widen(
                            self.saturator.analysis_in_version(value1, ssa_pred1),
                            *var,
                            pred1,
                        );
                        let analysis2 = widen(
                            self.saturator.analysis_in_version(value2, ssa_pred2),
                            *var,
                            pred2,
                        );
                        // Group variables by pair of joined SSAIds.
                        pair_to_vars
                            .entry((value1, value2, analysis1.join(&analysis2)))
                            .or_default()
                            .insert(*var);
                    }
                }

                // We create a single knot per set of variables sharing values.
                let mut knot_values = FxHashMap::default();
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
                let mut new_vars = FxHashMap::default();
                for (value1, value2, vars, knot_id, analysis) in pair_to_knot {
                    let ty1 = self.saturator.ssa.ty(value1);
                    let ty2 = self.saturator.ssa.ty(value2);
                    assert_eq!(ty1, ty2);
                    let mut knot = self.saturator.intern(SSA::Knot(knot_id, ty1, analysis));

                    let idom = self.saturator.version(new_block).parent().unwrap();
                    let set1: FxHashSet<_> = self
                        .saturator
                        .version(ssa_pred1)
                        .set(value1, Some(idom))
                        .collect();
                    let set2: FxHashSet<_> = self
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
        // Returns make no assignments.
        self.update_vars(block, self.vars[&pred].clone());
    }
}

pub fn check_trace_against_analysis(
    trace: &Vec<State>,
    vars: FxHashMap<BlockId, VarMap>,
    blocks: FxHashMap<BlockId, SSABlockId>,
    saturator: &mut Saturator,
) {
    // This is a hack to create scratch versions that inherit from the version at each block.
    let scratch = saturator.ssa.add_block(SSABlock::Identity(0));
    for State { location, store } in trace {
        saturator
            .ssa
            .set_block(SSABlock::Identity(blocks[location]), scratch);
        saturator.create_version(scratch);
        // Check if the store from the trace is consistent with the version by seeing if we can
        // derive a contradiction from asserting the constants from the store in the e-graph. If the
        // e-graph's concretization contains the constants, then the meet of everything will be non-
        // empty, so a contradiction won't be derived. Notably, this will also cover the case where
        // the trace reaches a location that we believe to be unreachable.
        for (var, cons) in store {
            // Traces don't drop out-of-scope variables. Treat a variable being absent from the
            // abstract store as top.
            if let Some(other_ssa_id) = vars[location].get(var) {
                let cons_ssa_id = saturator.intern(SSA::Constant(*cons));
                saturator.union(*other_ssa_id, cons_ssa_id);
            }
        }
        saturator.saturate();
        assert!(!saturator.is_contradiction_in_version(scratch));
    }
}
