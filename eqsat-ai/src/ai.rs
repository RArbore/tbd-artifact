use core::assert_matches;
use std::collections::{BTreeSet, HashMap, HashSet};

use symbol_table::GlobalSymbol as Symbol;

use crate::nonssa::{Block, BlockId, Constant, Expr, NonSSAFunc, Type};
use crate::saturator::Saturator;
use crate::ssa::{KnotId, SSA, SSABlock, SSABlockId, SSAId};

pub fn abstract_interpret(saturator: &mut Saturator, name: Symbol, nonssa: &NonSSAFunc) {
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
        vars: HashMap::new(),
        blocks: HashMap::new(),
        knot_map: KnotMap::default(),
        saturator,
    };

    // A faster interpreter would walk the non-SSA CFG in WTO. We use a worklist for two reasons.
    // 1. Laziness.
    // 2. We could randomize the order of blocks in the worklist to stress test the interpreter,
    //    because the order shouldn't affect the final results.
    let mut worklist = vec![0];
    while let Some(block) = worklist.pop() {
        if context.visit_block(nonssa, block) {
            worklist.extend(deps[&block].iter());
        }
    }
}

// This is the data type that we would want to change to Okasaki maps to follow Lemerre's advice.
type VarMap = HashMap<Symbol, SSAId>;

// Intern tuples of BlockId and variable sets to KnotId.
#[derive(Debug, Default)]
struct KnotMap(HashMap<(BlockId, BTreeSet<Symbol>), KnotId>);

impl KnotMap {
    fn intern_knot(&mut self, block: BlockId, var: BTreeSet<Symbol>) -> KnotId {
        let new_id = self.0.len();
        let entry = self.0.entry((block, var));
        *entry.or_insert(new_id)
    }
}

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
    // Intern sets of variables and locations to KnotIds (knots are our name for "symbolic variables"
    // from Lemerre's paper).
    knot_map: KnotMap,
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

    fn update_new_block(
        &mut self,
        block_id: BlockId,
        new_ssa_block: SSABlock,
    ) -> (bool, SSABlockId) {
        let (is_new, ssa_block_id) =
            if let Some((old_ssa_block_id, true)) = self.blocks.get(&block_id) {
                // If we already created a new SSA block for this non-SSA block, re-use the SSABlockId.
                self.saturator
                    .ssa
                    .set_block(new_ssa_block, *old_ssa_block_id);
                // Since we re-used the SSABlockId, we don't need to update successors.
                (false, *old_ssa_block_id)
            } else {
                // If we haven't created a new SSA block for this non-SSA block (either because we
                // haven't visited this non-SSA block yet or because we have and previously assigned it
                // a non-fresh SSA block), then create a new SSABlockId and map the non-SSA block to it.
                let new_ssa_block_id = self.saturator.ssa.add_block(new_ssa_block);
                self.blocks.insert(block_id, (new_ssa_block_id, true));
                // Since we changed the SSABlockId, we need to update successors.
                (true, new_ssa_block_id)
            };

        // Create a new version every time we visit a block.
        self.saturator.create_version(ssa_block_id);
        (is_new, ssa_block_id)
    }

    fn update_block(&mut self, block_id: BlockId, ssa_block_id: SSABlockId) -> bool {
        assert!(
            self.blocks
                .get(&block_id)
                .map(|(_, fresh)| !fresh)
                .unwrap_or(true)
        );
        if let Some((old_ssa_block_id, old_is_specific)) =
            self.blocks.insert(block_id, (ssa_block_id, false))
        {
            assert!(!old_is_specific);
            old_ssa_block_id != ssa_block_id
        } else {
            true
        }
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

    fn visit_block(&mut self, nonssa: &NonSSAFunc, block: BlockId) -> bool {
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

    fn visit_entry(&mut self, nonssa: &NonSSAFunc, block: BlockId) -> bool {
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
        self.update_new_block(block, SSABlock::Entry).0 | self.update_vars(block, vars)
    }

    fn visit_guard(&mut self, block: BlockId, pred: BlockId, cond: &Expr, direction: bool) -> bool {
        let ssa_pred = self.to_ssa_block(pred);
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

        if always_false && direction || always_true && !direction {
            false
        } else {
            let block_changed = if always_false && !direction || always_true && direction {
                self.update_block(block, ssa_pred)
            } else {
                let (block_changed, new_block) =
                    self.update_new_block(block, SSABlock::Guard(ssa_pred, value, direction));

                self.saturator.move_to_version(new_block);
                // When the guard is necessary, we want to assume the guard condition is either true
                // or false (depending on `direction`) in the created version.
                self.assume(value, direction);
                // We need to saturate after the union from the assumption, since jumping to a
                // different version could cause the potential delta to be lost in this version.
                self.saturator.saturate();
                block_changed
            };
            // Guards make no assignments.
            block_changed | self.update_vars(block, self.vars[&pred].clone())
        }
    }

    fn visit_assign(&mut self, block: BlockId, pred: BlockId, var: Symbol, expr: &Expr) -> bool {
        let ssa_pred = self.to_ssa_block(pred);
        self.saturator.move_to_version(ssa_pred);
        let value = self.visit_expr(expr, pred);
        // We need to saturate after every assignment because a jump to an arbitrary other version
        // may cause the delta to be lost.
        self.saturator.saturate();
        let mut vars = self.vars[&pred].clone();
        vars.insert(var, self.saturator.find(value));
        self.update_block(block, ssa_pred) | self.update_vars(block, vars)
    }

    fn visit_merge(&mut self, block: BlockId, pred1: BlockId, pred2: BlockId) -> bool {
        // Merge nodes are the only nodes with multiple predecessors - this also means that they are
        // the only nodes that might get visited before one of their predecessors.
        match (self.is_bottom(pred1), self.is_bottom(pred2)) {
            (true, true) => false,
            (false, true) => {
                self.update_block(block, self.to_ssa_block(pred1))
                    | self.update_vars(block, self.vars[&pred1].clone())
            }
            (true, false) => {
                self.update_block(block, self.to_ssa_block(pred2))
                    | self.update_vars(block, self.vars[&pred2].clone())
            }
            (false, false) => {
                let ssa_pred1 = self.to_ssa_block(pred1);
                let ssa_pred2 = self.to_ssa_block(pred2);
                assert_ne!(ssa_pred1, ssa_pred2);

                // Saturate because discovered equalities may help us avoid making knots.
                self.saturator.move_to_version(ssa_pred1);
                self.saturator.saturate();
                self.saturator.move_to_version(ssa_pred2);
                self.saturator.saturate();

                let mut pair_to_vars: HashMap<(SSAId, SSAId), HashSet<Symbol>> = HashMap::new();
                for (var, value1) in &self.vars[&pred1] {
                    if let Some(value2) = self.vars[&pred2].get(var) {
                        let value1 = self.saturator.find_in_version(*value1, ssa_pred1);
                        let value2 = self.saturator.find_in_version(*value2, ssa_pred2);
                        // Group variables by pair of joined SSAIds.
                        pair_to_vars
                            .entry((value1, value2))
                            .or_default()
                            .insert(*var);
                    }
                }

                // We create a single knot per set of variables sharing values.
                let mut knot_values = HashMap::new();
                let mut pair_to_knot = HashMap::new();
                for ((value1, value2), vars) in pair_to_vars {
                    let knot_id = self
                        .knot_map
                        .intern_knot(block, vars.iter().cloned().collect());
                    // Knots can't be unioned with anything in a version above the block they are
                    // defined in.
                    let ty1 = self.saturator.ssa.ty(value1);
                    let ty2 = self.saturator.ssa.ty(value2);
                    assert_eq!(ty1, ty2);
                    // In the predecessor versions, this Knot should not be unioned with anything.
                    let knot = self.saturator.intern(SSA::Knot(knot_id, ty1));
                    knot_values.insert(knot_id, (value1, value2));
                    pair_to_knot.insert((value1, value2), (vars, knot));
                }
                let (block_changed, new_block) = self
                    .update_new_block(block, SSABlock::Merge(ssa_pred1, ssa_pred2, knot_values));
                assert_ne!(new_block, ssa_pred1);
                assert_ne!(new_block, ssa_pred2);
                self.saturator.move_to_version(new_block);

                // Now that we have a version for this block, merge the IDs in the intersection of
                // the sets in the predecessor versions with the knots.
                let mut new_vars = HashMap::new();
                let idom = self.saturator.idom(new_block).unwrap();
                for ((value1, value2), (vars, knot)) in pair_to_knot {
                    let set1: HashSet<_> = self
                        .saturator
                        .set_in_version(value1, Some(idom), ssa_pred1)
                        .collect();
                    let set2: HashSet<_> = self
                        .saturator
                        .set_in_version(value2, Some(idom), ssa_pred2)
                        .collect();
                    for id in set1.intersection(&set2) {
                        self.saturator.union(knot, *id);
                    }
                    for var in vars {
                        new_vars.insert(var, self.saturator.find(knot));
                    }
                }

                // We need to saturate after the unions above, since jumping to a different version
                // could cause the delta to be lost in this version.
                self.saturator.saturate();
                block_changed | self.update_vars(block, new_vars)
            }
        }
    }

    fn visit_return(&mut self, block: BlockId, pred: BlockId, exprs: &[Expr]) -> bool {
        let ssa_pred = self.to_ssa_block(pred);
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
        self.update_new_block(block, SSABlock::Return(ssa_pred, values));
        self.saturator
            .ssa
            .add_exit(self.name, self.to_ssa_block(block));
        // Returns have no successors;
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::imp::ast::convert_to_cfg;
    use crate::imp::grammar::ProgramParser;
    use crate::nonssa::BinaryOp;

    use super::*;

    fn get_return_no_control_flow(text: &str) -> (SSAId, Saturator) {
        let parsed = ProgramParser::new().parse(text).unwrap();
        assert_eq!(parsed.len(), 1);
        let mut saturator = Saturator::default();
        for (name, ast) in parsed {
            let nonssa = convert_to_cfg(ast);
            abstract_interpret(&mut saturator, name, &nonssa);
            assert_eq!(saturator.ssa.get_block(0), &SSABlock::Entry);
            let SSABlock::Return(0, values) = saturator.ssa.get_block(1) else {
                panic!("{:?}", saturator.ssa)
            };
            assert_eq!(values.len(), 1);
            let value = values[0];
            saturator.check_trie_consistency();
            saturator.move_to_version(1);
            saturator.check_trie_consistency();
            return (value, saturator);
        }
        panic!()
    }

    fn get_return(text: &str) -> (SSAId, Saturator) {
        let parsed = ProgramParser::new().parse(text).unwrap();
        assert_eq!(parsed.len(), 1);
        let mut saturator = Saturator::default();
        for (name, ast) in parsed {
            let nonssa = convert_to_cfg(ast);
            abstract_interpret(&mut saturator, name, &nonssa);
            assert_eq!(saturator.ssa.get_block(0), &SSABlock::Entry);
            let exit = saturator.ssa.exit(name);
            let SSABlock::Return(_, values) = saturator.ssa.get_block(exit) else {
                panic!("{:?}", saturator.ssa)
            };
            assert_eq!(values.len(), 1);
            let value = values[0];
            saturator.check_trie_consistency();
            saturator.move_to_version(exit);
            //saturator.check_trie_consistency();
            return (value, saturator);
        }
        panic!()
    }

    #[test]
    fn ai1() {
        let text = r#"
fn basic() {
	x = 5;
	y = x + 7;
	z = x + 7;
	return y + z;
}
"#;
        let (value, mut saturator) = get_return_no_control_flow(text);
        let five = saturator.intern(SSA::Constant(Constant::I64(5)));
        let seven = saturator.intern(SSA::Constant(Constant::I64(7)));
        let add = saturator.intern(SSA::Binary(BinaryOp::Add, five, seven));
        let correct = saturator.intern(SSA::Binary(BinaryOp::Add, add, add));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai2() {
        let text = r#"
fn branch() {
	x = 5;
    if x == 5 {
        x = 9;
    }
	return x;
}
"#;
        let (value, mut saturator) = get_return_no_control_flow(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(9)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai3() {
        let text = r#"
fn add() {
	x = 5;
    y = 9;
	return x + y;
}
"#;
        let (value, mut saturator) = get_return_no_control_flow(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(14)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai4() {
        let text = r#"
fn loop() {
	x = 5;
    while x < 10 {
        if x > 4 {
            return x;
        }
        x = x + 3;
    }
    return 7;
}
"#;
        let (value, mut saturator) = get_return_no_control_flow(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(5)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai5() {
        let text = r#"
fn gvn(x: i64) {
	y = x;
	while x > 0 {
		x = x - 1;
		y = y - 1;
	}
	return x - y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(0)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai6() {
        let text = r#"
fn loop() {
	x = 5;
    if x > 3 {
        if x < 4 {
            return 1;
        } else {
            return 2;
        }
    } else {
        if x > 7 {
            return 3;
        } else {
            return 4;
        }
    }
}
"#;
        let (value, mut saturator) = get_return_no_control_flow(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(2)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai7() {
        let text = r#"
fn flow(x: bool) {
    if x {
        if x {
            y = 42;
        } else {
            y = 999;
        }
    } else {
        if x {
            y = 999;
        } else {
            y = 42;
        }
    }
    return y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(42)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai8() {
        let text = r#"
fn flow_constant_prop(x: bool) {
    if x {
        y = x;
    } else {
        y = !x;
    }
    return y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::Bool(true)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai9() {
        let text = r#"
fn flow_backwards(x: bool) {
    if !!!x {
        y = x;
    } else {
        y = !x;
    }
    return y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::Bool(false)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai10() {
        let text = r#"
fn flow_backwards_ee(x: i64, y: i64) {
    z = 0;
    if x == y {
        z = x - y;
    }
    return z;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(0)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai11() {
        let text = r#"
fn old_paper_example1(y: i64) {
    x = -6;
    z = 42;
    while y < 10 {
        y = y + 1;
        x = x + 8;
        lhs = x * y + y * 42;
        rhs = 2 * y + z * y;
        if lhs != rhs {
            z = 24;
        }
        x = x - 8;
    }
    return z + 7;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(49)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai12() {
        let text = r#"
fn old_paper_example2(x: i64) {
    y = x;
    while y < 10 {
        xt = x;
        x = y * y + y * 5;
        y = xt * y + xt * (5 + 0) ;
    }
    return x - y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(0)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai13() {
        let text = r#"
fn simplified(y: i64) {
    z = 42;
    while y < 10 {}
    return z + 7;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(49)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai14() {
        let text = r#"
fn tricky(x: bool) {
    if x {
        y = 7 + 2;
    } else {
        y = 7 + 2;
    }
    return y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(9)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai15() {
        let text = r#"
fn simplified(y: i64) {
    while y < 10 {
        y = y + 1;
        lhs = 3 * y;
        rhs = 2 * y;
        if lhs != rhs {}
    }
    return 7;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(7)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai16() {
        let text = r#"
fn tricky(x: bool) {
    if x {
        y = (7 + 2) + (3 + 4);
    } else {
        y = (6 + 3) + (2 + 5);
    }
    return y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Constant(Constant::I64(16)));
        assert_eq!(correct, value);
    }

    #[test]
    fn ai17() {
        let text = r#"
fn simplified(y: i64) {
    while y < 10 {}
    return y;
}
"#;
        let (value, mut saturator) = get_return(text);
        let correct = saturator.intern(SSA::Param(0, Type::I64));
        assert_eq!(correct, value);
        let correct = saturator.intern(SSA::Knot(0, Type::I64));
        assert_eq!(correct, value);
    }

    #[test]
    #[should_panic]
    fn bad_types1() {
        let text = r#"
fn simple() {
    x = 0 + true;
    return x;
}
"#;
        get_return(text);
    }

    #[test]
    #[should_panic]
    fn bad_types2() {
        let text = r#"
fn simple(x: i64) {
    if x {}
    return x;
}
"#;
        get_return(text);
    }

    #[test]
    #[should_panic]
    fn bad_types3() {
        let text = r#"
fn simple(x: bool) {
    if x {
        return 1;
    } else {
        return true;
    }
}
"#;
        get_return(text);
    }
}
