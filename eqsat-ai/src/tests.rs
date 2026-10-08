use std::collections::{HashMap, HashSet};
use std::ptr::eq;
use std::rc::Rc;

use rand::random;
use symbol_table::GlobalSymbol as Symbol;

use crate::ai::*;
use crate::analysis::*;
use crate::imp::ast::*;
use crate::imp::grammar::*;
use crate::nonssa::*;
use crate::saturator::*;
use crate::ssa::*;
use crate::trie::*;
use crate::version::*;

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
        saturator.move_to_version(exit);
        saturator.check_trie_consistency();
        return (value, saturator);
    }
    panic!()
}

#[test]
fn ai01() {
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
fn ai02() {
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
fn ai03() {
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
fn ai04() {
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
fn ai05() {
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
fn ai06() {
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
fn ai07() {
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
fn ai08() {
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
fn ai09() {
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
    return y + 0;
}
"#;
    let (value, mut saturator) = get_return(text);
    let correct = saturator.intern(SSA::Param(0, Type::I64));
    assert_eq!(correct, value);
    // NOTE: This may fail if we implement a backwards transfer for LT in KnownBits.
    let correct = saturator.intern(SSA::Knot(0, Type::I64, Analysis::identity()));
    assert_eq!(correct, value);
}

#[test]
fn ai18() {
    let text = r#"
fn kb(x: i64) {
    x = x & 4294967295;
    x = x & -4294967296;
    return x;
}
"#;
    let (value, mut saturator) = get_return(text);
    let correct = saturator.intern(SSA::Constant(Constant::I64(0)));
    assert_eq!(correct, value);
}

#[test]
fn ai19() {
    let text = r#"
fn contradiction(x: i64) {
    if x == 3 && x == 5 {
    } else {
        x = 4;
    }
    return x;
}
"#;
    let (value, mut saturator) = get_return(text);
    let correct = saturator.intern(SSA::Constant(Constant::I64(4)));
    let incorrect = saturator.intern(SSA::Constant(Constant::I64(5)));
    assert_eq!(correct, value);
    assert_ne!(incorrect, value);
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

#[test]
fn parse1() {
    let program = r#"
fn test1(x: bool) return x;
fn test2(y: i64) { y = 3; return y + 1; }
"#;
    let parsed = ProgramParser::new().parse(&program).unwrap();
    assert_eq!(
        format!("{}", parsed[&Symbol::from("test1")]),
        "fn test1(x: bool) return x;"
    );
    assert_eq!(
        format!("{}", parsed[&Symbol::from("test2")]),
        "fn test2(y: i64) { y = 3; return (y + 1); }"
    );
}

#[test]
fn parse2() {
    let program = r#"
fn test(x: i64, y: i64) { while x < 7 { x = x + 1; } if y < x { return y; } return x + 9; }
"#;
    let parsed = ProgramParser::new().parse(&program).unwrap();
    assert_eq!(
        format!("{}", parsed[&Symbol::from("test")]),
        "fn test(x: i64, y: i64) { while (x < 7) { { x = (x + 1); } } if (y < x) { { return y; } } else { { } } return (x + 9); }"
    );
}

#[test]
fn rpo1() {
    use Block::*;
    let cond = Expr::Constant {
        val: Constant::Bool(true),
    };
    let func = NonSSAFunc {
        name: "".into(),
        params: vec![],
        cfg: vec![
            Entry,
            Guard {
                pred: 0,
                cond: cond.clone(),
                direction: true,
            },
            Guard {
                pred: 0,
                cond,
                direction: true,
            },
            Merge { pred1: 1, pred2: 2 },
            Return {
                pred: 3,
                exprs: vec![],
            },
        ],
    };
    assert_eq!(func.rpo(), vec![0, 1, 2, 3, 4]);
}

#[test]
fn rpo2() {
    use Block::*;
    let cond = Expr::Constant {
        val: Constant::Bool(true),
    };
    let func = NonSSAFunc {
        name: "".into(),
        params: vec![],
        cfg: vec![
            Entry,
            Merge { pred1: 0, pred2: 2 },
            Guard {
                pred: 1,
                cond: cond.clone(),
                direction: true,
            },
            Guard {
                pred: 1,
                cond,
                direction: true,
            },
            Return {
                pred: 3,
                exprs: vec![],
            },
        ],
    };
    assert_eq!(func.rpo(), vec![0, 1, 2, 3, 4]);
}

#[test]
fn saturator1() {
    let mut saturator = Saturator::default();
    let block_id = saturator.ssa.add_block(SSABlock::Entry);
    saturator.create_version(block_id);
    saturator.move_to_version(block_id);
    saturator.saturate();
    assert_eq!(saturator.ssa.num_nodes(), 0);

    use SSA::*;
    let p1 = saturator.intern(Param(0, Type::I64));
    let p2 = saturator.intern(Param(1, Type::I64));
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

#[test]
fn saturator2() {
    let mut saturator = Saturator::default();
    let entry = saturator.ssa.add_block(SSABlock::Entry);
    saturator.create_version(entry);
    saturator.move_to_version(entry);

    use BinaryOp::*;
    use SSA::*;
    use UnaryOp::*;
    let one = saturator.intern(Constant(crate::nonssa::Constant::I64(1)));
    let p1 = saturator.intern(Param(0, Type::I64));
    let p2 = saturator.intern(Param(1, Type::I64));
    let n1 = saturator.intern(Unary(Neg, p1));
    let n2 = saturator.intern(Unary(Neg, p2));
    let eq1 = saturator.intern(Binary(EE, n1, one));
    saturator.saturate();

    saturator.union(p1, p2);
    saturator.saturate();

    let guard_true = saturator.ssa.add_block(SSABlock::Guard(entry, eq1, true));
    saturator.create_version(guard_true);
    saturator.move_to_version(guard_true);
    let add1 = saturator.intern(Binary(Add, n1, n2));
    let add2 = saturator.intern(Binary(Add, n2, n1));
    let eq2 = saturator.intern(Binary(NE, add1, add2));
    let false_constant = saturator.intern(Constant(crate::nonssa::Constant::Bool(false)));
    saturator.saturate();
    assert_eq!(saturator.find(false_constant), saturator.find(eq2));

    let guard_false = saturator
        .ssa
        .add_block(SSABlock::Guard(guard_true, eq1, false));
    saturator.create_version(guard_false);
    saturator.move_to_version(guard_false);
    let mul1 = saturator.intern(Binary(Mul, n2, one));
    let add1 = saturator.intern(Binary(Add, n1, n2));
    saturator.intern(Binary(Add, mul1, add1));
    saturator.saturate();

    saturator.move_to_version(guard_true);
    saturator.move_to_version(guard_false);
}

#[test]
fn trie1() {
    let mut trie1 = Trie::default();
    trie1.insert_tuple([0, 1].into_iter(), 7);
    trie1.insert_tuple([0, 2].into_iter(), 42);
    trie1.insert_tuple([0, 2].into_iter(), 43);
    assert_eq!(
        trie1,
        Trie::Internal(HashMap::from_iter([(
            0,
            Trie::Internal(HashMap::from_iter([
                (1, Trie::Leaf(HashSet::from_iter([7]))),
                (2, Trie::Leaf(HashSet::from_iter([42, 43])))
            ]))
        )]))
    );
    trie1.insert_tuple([0, 2].into_iter(), 44);
    trie1.remove_tuple([0, 2].into_iter(), 44);

    let mut trie2 = Trie::default();
    trie2.insert_tuple([0, 2].into_iter(), 43);
    trie2.insert_tuple([0, 2].into_iter(), 42);
    trie2.insert_tuple([0, 1].into_iter(), 7);
    assert_eq!(trie1, trie2);
    trie1.insert_tuple([0, 1].into_iter(), 9);
    assert_ne!(trie1, trie2);
    trie2.insert_tuple([0, 1].into_iter(), 9);
    assert_eq!(trie1, trie2);
    trie1.remove_tuple([0, 1].into_iter(), 9);
    assert_ne!(trie1, trie2);
    trie2.remove_tuple([0, 1].into_iter(), 9);
    assert_eq!(trie1, trie2);
}

#[test]
#[should_panic]
fn trie2() {
    let mut trie = Trie::default();
    trie.insert_tuple([0, 2].into_iter(), 9);
    trie.insert_tuple([0, 2, 3].into_iter(), 42);
}

#[test]
#[should_panic]
fn trie3() {
    let mut trie = Trie::default();
    trie.insert_tuple([0, 2, 3].into_iter(), 42);
    trie.remove_tuple([0, 2, 3].into_iter(), 41);
}

#[test]
#[should_panic]
fn trie4() {
    let mut trie = Trie::default();
    trie.insert_tuple([0, 2, 3].into_iter(), 42);
    trie.remove_tuple([0, 2, 1].into_iter(), 42);
}

#[test]
fn uf1() {
    let mut uf = SparseUnionFind::default();
    assert_eq!(uf.union(0, 4), 0);
    assert_eq!(uf.union(1, 3), 1);
    assert_eq!(uf.union(2, 5), 2);
    assert_eq!(uf.union(5, 9), 2);
    assert_eq!(uf.union(2, 9), 2);
    assert_eq!(uf.find(0), 0);
    assert_eq!(uf.find(4), 0);
    assert_eq!(uf.find(1), 1);
    assert_eq!(uf.find(3), 1);
    assert_eq!(uf.find(2), 2);
    assert_eq!(uf.find(5), 2);
    assert_eq!(uf.find(9), 2);
    assert_eq!(
        HashSet::from_iter([0, 4]),
        uf.set(4).collect::<HashSet<_>>()
    );
    assert_eq!(
        HashSet::from_iter([1, 3]),
        uf.set(1).collect::<HashSet<_>>()
    );
    assert_eq!(
        HashSet::from_iter([2, 5, 9]),
        uf.set(5).collect::<HashSet<_>>()
    );
    assert_eq!(
        HashSet::from_iter([3, 4, 5, 9]),
        uf.non_canon_ids().into_iter().collect::<HashSet<_>>()
    );

    assert_eq!(uf.union(4, 5), 0);
    assert_eq!(uf.find(2), 0);
    assert_eq!(uf.find(5), 0);
    assert_eq!(uf.find(9), 0);
    assert_eq!(
        HashSet::from_iter([0, 2, 4, 5, 9]),
        uf.set(9).collect::<HashSet<_>>()
    );
    assert_eq!(
        HashSet::from_iter([2, 3, 4, 5, 9]),
        uf.non_canon_ids().into_iter().collect::<HashSet<_>>()
    );
}

#[test]
fn uf2() {
    let mut uf = SparseUnionFind::default();
    for i in 0..100 {
        assert_ne!(uf.find(i), uf.find(i + 1));
        assert_eq!(uf.find(i), i);
    }
    for i in 0..100 {
        assert_eq!(uf.union(i, i + 1), 0);
    }
    for i in 0..100 {
        assert_eq!(uf.find(i), uf.find(i + 1));
    }
    for i in 100..200 {
        assert_ne!(uf.find(i), uf.find(i + 1));
    }
    assert_eq!(
        HashSet::from_iter(1..=100),
        uf.non_canon_ids().into_iter().collect::<HashSet<_>>()
    );
}

#[test]
fn uf3() {
    let mut uf = SparseUnionFind::default();
    let mut set = HashSet::new();
    uf.union_with(1, 2, |id, old_canon_id, new_canon_id| {
        set.insert(id);
        assert_eq!(old_canon_id, 2);
        assert_eq!(new_canon_id, 1);
    });
    assert_eq!(set, HashSet::from([2]));
    let mut set = HashSet::new();
    uf.union_with(2, 0, |id, old_canon_id, new_canon_id| {
        set.insert(id);
        assert_eq!(old_canon_id, 1);
        assert_eq!(new_canon_id, 0);
    });
    assert_eq!(set, HashSet::from([1, 2]));
    let mut set = HashSet::new();
    uf.union_with(3, 0, |id, old_canon_id, new_canon_id| {
        set.insert(id);
        assert_eq!(old_canon_id, 3);
        assert_eq!(new_canon_id, 0);
    });
    assert_eq!(set, HashSet::from([3]));
}

#[test]
fn luf1() {
    let mut parent = Version::<usize>::default();
    parent.set_analysis(0, 1);
    parent.set_analysis(1, 1);
    parent.set_analysis(2, 1);
    parent.set_analysis(3, 1);
    parent.set_analysis(4, 1);
    parent.union(0, 1);
    parent.union(2, 3);
    assert_eq!(parent.find(0), parent.find(1));
    assert_eq!(parent.find(2), parent.find(3));
    assert_ne!(parent.find(0), parent.find(2));
    assert_eq!(
        HashSet::from_iter([0, 1]),
        parent.set(1, None).collect::<HashSet<_>>()
    );
    assert_eq!(
        HashSet::from_iter([2, 3]),
        parent.set(2, None).collect::<HashSet<_>>()
    );
    assert_eq!(parent.analysis(0), 2);
    assert_eq!(parent.analysis(1), 2);
    assert_eq!(parent.analysis(2), 2);
    assert_eq!(parent.analysis(3), 2);
    assert_eq!(parent.analysis(4), 1);

    let parent = Rc::new(parent);
    let mut child = Version::child(Rc::clone(&parent));
    child.union(0, 3);
    assert_eq!(child.find(0), child.find(1));
    assert_eq!(child.find(2), child.find(3));
    assert_eq!(child.find(0), child.find(2));
    assert_eq!(child.find(0), child.find(3));
    assert_ne!(parent.find(0), parent.find(3));
    for i in [0, 1, 2, 3] {
        assert_eq!(
            HashSet::from_iter([0, 1, 2, 3]),
            child.set(i, None).collect::<HashSet<_>>()
        );
    }
    assert_eq!(
        HashSet::from_iter([0, 1]),
        parent.set(1, None).collect::<HashSet<_>>()
    );
    assert_eq!(
        HashSet::from_iter([2, 3]),
        parent.set(2, None).collect::<HashSet<_>>()
    );
    for i in [0, 1, 2, 3] {
        assert_eq!(
            HashSet::from_iter([0, 2]),
            child.set(i, Some(&*parent)).collect::<HashSet<_>>()
        );
    }
    assert_eq!(
        HashSet::from_iter([5]),
        child.set(5, Some(&*parent)).collect::<HashSet<_>>()
    );
    for i in [0, 1, 2, 3] {
        assert_eq!(
            HashSet::from_iter([child.find(i)]),
            child.set(i, Some(&child)).collect::<HashSet<_>>()
        );
        assert_eq!(
            HashSet::from_iter([parent.find(i)]),
            parent.set(i, Some(&*parent)).collect::<HashSet<_>>()
        );
    }
    assert_eq!(parent.analysis(0), 2);
    assert_eq!(parent.analysis(1), 2);
    assert_eq!(parent.analysis(2), 2);
    assert_eq!(parent.analysis(3), 2);
    assert_eq!(parent.analysis(4), 1);
    assert_eq!(child.analysis(0), 4);
    assert_eq!(child.analysis(1), 4);
    assert_eq!(child.analysis(2), 4);
    assert_eq!(child.analysis(3), 4);
    assert_eq!(child.analysis(4), 1);
    assert!(eq(
        &*Version::lca(&child, &parent, |_| {}, |_| {}).unwrap(),
        &*parent
    ));
}

#[test]
fn luf2() {
    let mut parent = Version::<usize>::default();
    parent.set_analysis(0, 1);
    parent.set_analysis(1, 1);
    parent.set_analysis(2, 1);
    parent.set_analysis(3, 1);
    parent.union(0, 1);
    parent.union(2, 3);
    assert_eq!(parent.analysis(0), 2);
    assert_eq!(parent.analysis(1), 2);
    assert_eq!(parent.analysis(2), 2);
    assert_eq!(parent.analysis(3), 2);

    let parent = Rc::new(parent);
    let mut child = Version::child(Rc::clone(&parent));
    let mut set = HashSet::new();
    child.union_with(
        0,
        3,
        |id, old_canon_id, new_canon_id| {
            set.insert(id);
            assert_eq!(old_canon_id, 2);
            assert_eq!(new_canon_id, 0);
        },
        |canon_id, non_canon_id, old_analysis, combined| {
            assert_eq!(canon_id, 0);
            assert_eq!(non_canon_id, 2);
            assert_eq!(old_analysis, 2);
            assert_eq!(combined, 4);
        },
    );
    assert_eq!(set, HashSet::from([2, 3]));
    assert_eq!(parent.analysis(0), 2);
    assert_eq!(parent.analysis(1), 2);
    assert_eq!(parent.analysis(2), 2);
    assert_eq!(parent.analysis(3), 2);
    assert_eq!(child.analysis(0), 4);
    assert_eq!(child.analysis(1), 4);
    assert_eq!(child.analysis(2), 4);
    assert_eq!(child.analysis(3), 4);
    assert!(eq(
        &*Version::lca(&child, &parent, |_| {}, |_| {}).unwrap(),
        &*parent
    ));
}

#[test]
fn known_bits1() {
    assert!(
        KnownBits {
            low_high: 42,
            concrete: !0
        }
        .is_constant(42)
    );
    assert_eq!(
        KnownBits {
            low_high: 42,
            concrete: !0
        }
        .try_constant(),
        Some(42)
    );
    assert!(
        KnownBits {
            low_high: 0,
            concrete: 0
        }
        .is_constant(777)
    );
    assert!(
        !KnownBits {
            low_high: 0,
            concrete: !0
        }
        .is_constant(777)
    );
    assert_eq!(
        KnownBits {
            low_high: 42,
            concrete: 0
        }
        .try_constant(),
        None
    );
    assert_eq!(
        KnownBits::from_constant(3).join(&KnownBits::from_constant(1)),
        KnownBits {
            low_high: 3,
            concrete: !2
        }
    );
}

#[test]
fn known_bits2() {
    for _ in 0..100 {
        let cons = random::<i64>();
        let kb = KnownBits::from_constant(cons);
        let not_kb = kb.bitwise_not();
        assert!(not_kb.is_constant(!cons));
    }
    for _ in 0..100 {
        let cons1 = random::<i64>();
        let cons2 = random::<i64>();
        let kb1 = KnownBits::from_constant(cons1);
        let kb2 = KnownBits::from_constant(cons2);
        assert_eq!(kb1.join(&kb2), kb2.join(&kb1));
        assert_eq!(kb1.meet(&kb2), kb2.meet(&kb1));
        assert_eq!(kb1.bitwise_and(&kb2), kb2.bitwise_and(&kb1));
        assert_eq!(kb1.bitwise_or(&kb2), kb2.bitwise_or(&kb1));
        assert_eq!(kb1.bitwise_xor(&kb2), kb2.bitwise_xor(&kb1));
        assert!(kb1.bitwise_and(&kb2).is_constant(cons1 & cons2));
        assert!(kb1.bitwise_or(&kb2).is_constant(cons1 | cons2));
        assert!(kb1.bitwise_xor(&kb2).is_constant(cons1 ^ cons2));
        assert!(kb1.leq(&KnownBits::top()));
        assert!(kb2.leq(&KnownBits::top()));
        assert!(KnownBits::bot().leq(&kb1));
        assert!(KnownBits::bot().leq(&kb2));
    }
}

#[test]
fn known_bits3() {
    for _ in 0..100 {
        let num = random::<u8>() % 10;
        let mut cons = vec![];
        let mut join = KnownBits::bot();
        let mut meet = KnownBits::top();
        for _ in 0..num {
            let kb = KnownBits::from_constant(random::<i64>());
            join = join.join(&kb);
            meet = meet.meet(&kb);
            cons.push(kb);
        }
        for i in 0..num {
            let kb = cons[i as usize];
            assert!(kb.leq(&join), "{:?}, {:?} is join of {} kbs", kb, join, num);
            assert!(meet.leq(&kb), "{:?}, {:?} is meet of {} kbs", kb, meet, num);
        }
    }
}

#[test]
fn known_bits4() {
    for _ in 0..100 {
        let num = random::<u8>() % 10;
        let mut cons1 = vec![];
        let mut cons2 = vec![];
        let mut join1 = KnownBits::bot();
        let mut join2 = KnownBits::bot();
        let mut meet1 = KnownBits::top();
        let mut meet2 = KnownBits::top();
        for _ in 0..num {
            let c1 = random::<i64>();
            let kb1 = KnownBits::from_constant(c1);
            join1 = join1.join(&kb1);
            meet1 = meet1.meet(&kb1);
            cons1.push(c1);
            let c2 = random::<i64>();
            let kb2 = KnownBits::from_constant(c2);
            join2 = join2.join(&kb2);
            meet2 = meet2.meet(&kb2);
            cons2.push(c2);
        }
        if num > 0 {
            assert!(meet1.leq(&join1));
            assert!(meet2.leq(&join2));
        }
        let join_and = join1.bitwise_and(&join2);
        let meet_and = meet1.bitwise_and(&meet2);
        let join_or = join1.bitwise_or(&join2);
        let meet_or = meet1.bitwise_or(&meet2);
        let join_xor = join1.bitwise_xor(&join2);
        let meet_xor = meet1.bitwise_xor(&meet2);
        for i in 0..num {
            let and = cons1[i as usize] & cons2[i as usize];
            let or = cons1[i as usize] | cons2[i as usize];
            let xor = cons1[i as usize] ^ cons2[i as usize];
            assert!(join_and.contains_constant(and));
            assert!(meet_and.is_constant(and));
            assert!(join_or.contains_constant(or));
            assert!(meet_or.is_constant(or));
            assert!(join_xor.contains_constant(xor));
            assert!(meet_xor.is_constant(xor));
        }
    }
}

#[test]
fn intervals1() {
    assert!(Interval::from_constant(42).is_constant(42));
    assert_eq!(Interval::from_constant(42).try_constant(), Some(42));
    assert!(Interval::Bot.is_constant(777));
    assert!(!Interval::Top.is_constant(777));
    assert_eq!(Interval::Top.try_constant(), None);
    assert_eq!(
        Interval::from_constant(3).join(&Interval::from_constant(1)),
        Interval::from_low_high(1, 3)
    );
    assert_eq!(
        Interval::from_constant(3).meet(&Interval::from_constant(1)),
        Interval::Bot
    );
}

#[test]
fn intervals2() {
    for i in 0..100 {
        let cons = if i == 0 {
            i64::MIN
        } else if i == 1 {
            i64::MAX
        } else {
            random::<i64>()
        };
        let int = Interval::from_constant(cons);
        let neg_int = int.neg();
        if let Some(neg_cons) = cons.checked_neg() {
            assert!(neg_int.is_constant(neg_cons));
        } else {
            assert_eq!(neg_int, Interval::Top);
        }
    }
    for _ in 0..100 {
        let cons1 = random::<i64>();
        let cons2 = random::<i64>();
        let int1 = Interval::from_constant(cons1);
        let int2 = Interval::from_constant(cons2);
        assert_eq!(int1.join(&int2), int2.join(&int1));
        assert_eq!(int1.meet(&int2), int2.meet(&int1));
        assert_eq!(int1.add(&int2), int2.add(&int1));
        assert_eq!(int1.mul(&int2), int2.mul(&int1));
        if let Some(add) = cons1.checked_add(cons2) {
            assert!(int1.add(&int2).is_constant(add));
        }
        if let Some(sub) = cons1.checked_sub(cons2) {
            assert!(int1.sub(&int2).is_constant(sub));
        }
        if let Some(mul) = cons1.checked_mul(cons2) {
            assert!(int1.mul(&int2).is_constant(mul));
        }
        assert!(int1.leq(&Interval::Top));
        assert!(int2.leq(&Interval::Top));
        assert!(Interval::Bot.leq(&int1));
        assert!(Interval::Bot.leq(&int2));
    }
}

#[test]
fn intervals3() {
    for _ in 0..100 {
        let num = random::<u8>() % 10;
        let mut cons = vec![];
        let mut join = Interval::Bot;
        let mut meet = Interval::Top;
        for _ in 0..num {
            let int = Interval::from_constant(random::<i64>());
            join = join.join(&int);
            meet = meet.meet(&int);
            cons.push(int);
        }
        for i in 0..num {
            let int = cons[i as usize];
            assert!(
                int.leq(&join),
                "{:?}, {:?} is join of {} ints",
                int,
                join,
                num
            );
            assert!(
                meet.leq(&int),
                "{:?}, {:?} is meet of {} ints",
                int,
                meet,
                num
            );
        }
    }
}

#[test]
fn intervals4() {
    for _ in 0..100 {
        let num = random::<u8>() % 10;
        let mut cons1 = vec![];
        let mut cons2 = vec![];
        let mut join1 = Interval::Bot;
        let mut join2 = Interval::Bot;
        let mut meet1 = Interval::Top;
        let mut meet2 = Interval::Top;
        for _ in 0..num {
            let c1 = random::<i64>();
            let int1 = Interval::from_constant(c1);
            join1 = join1.join(&int1);
            meet1 = meet1.meet(&int1);
            cons1.push(c1);
            let c2 = random::<i64>();
            let int2 = Interval::from_constant(c2);
            join2 = join2.join(&int2);
            meet2 = meet2.meet(&int2);
            cons2.push(c2);
        }
        if num > 0 {
            assert!(meet1.leq(&join1));
            assert!(meet2.leq(&join2));
        }
        let join_add = join1.add(&join2);
        let meet_add = meet1.add(&meet2);
        let join_sub = join1.sub(&join2);
        let meet_sub = meet1.sub(&meet2);
        let join_mul = join1.mul(&join2);
        let meet_mul = meet1.mul(&meet2);
        for i in 0..num {
            if let Some(add) = cons1[i as usize].checked_add(cons2[i as usize]) {
                assert!(join_add.contains_constant(add));
                assert!(meet_add.is_constant(add));
            }
            if let Some(sub) = cons1[i as usize].checked_sub(cons2[i as usize]) {
                assert!(join_sub.contains_constant(sub));
                assert!(meet_sub.is_constant(sub));
            }
            if let Some(mul) = cons1[i as usize].checked_mul(cons2[i as usize]) {
                assert!(join_mul.contains_constant(mul));
                assert!(meet_mul.is_constant(mul));
            }
        }
    }
}
