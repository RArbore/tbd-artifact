use core::fmt::{Display, Formatter, Result};
use std::collections::{HashMap, HashSet};

use symbol_table::GlobalSymbol as Symbol;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    I64,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Constant {
    Bool(bool),
    I64(i64),
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Neg,
    BitwiseNot,
    Not,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    And,
    Or,
    Xor,
    EE,
    NE,
    LT,
    LE,
    GT,
    GE,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Constant {
        val: Constant,
    },
    Variable {
        var: Symbol,
    },
    Unary {
        op: UnaryOp,
        input: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

pub type BlockId = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Block {
    Entry,
    Guard {
        pred: BlockId,
        cond: Expr,
        direction: bool,
    },
    Assign {
        pred: BlockId,
        var: Symbol,
        expr: Expr,
    },
    Merge {
        pred1: BlockId,
        pred2: BlockId,
    },
    Return {
        pred: BlockId,
        exprs: Vec<Expr>,
    },
}

#[derive(Debug)]
pub struct NonSSAFunc {
    pub name: Symbol,
    pub params: Vec<(Symbol, Type)>,
    pub cfg: Vec<Block>,
}

impl Constant {
    pub fn ty(&self) -> Type {
        match self {
            Constant::Bool(_) => Type::Bool,
            Constant::I64(_) => Type::I64,
        }
    }
}

impl Block {
    pub fn is_return(&self) -> bool {
        if let Block::Return { .. } = self {
            true
        } else {
            false
        }
    }
}

impl NonSSAFunc {
    pub fn rpo(&self) -> Vec<BlockId> {
        let mut succ: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
        for (id, block) in self.cfg.iter().enumerate().rev() {
            match block {
                Block::Entry => {}
                Block::Guard { pred, .. }
                | Block::Assign { pred, .. }
                | Block::Return { pred, .. } => {
                    succ.entry(*pred).or_default().push(id);
                }
                Block::Merge { pred1, pred2 } => {
                    succ.entry(*pred1).or_default().push(id);
                    succ.entry(*pred2).or_default().push(id);
                }
            }
        }
        let mut rpo = vec![];
        let mut visited = HashSet::new();
        self.rpo_helper(0, &succ, &mut rpo, &mut visited);
        rpo.reverse();
        rpo
    }

    fn rpo_helper(
        &self,
        id: BlockId,
        succ: &HashMap<BlockId, Vec<BlockId>>,
        rpo: &mut Vec<BlockId>,
        visited: &mut HashSet<BlockId>,
    ) {
        if visited.contains(&id) {
            return;
        }
        visited.insert(id);
        for id in succ.get(&id).unwrap_or(&vec![]) {
            self.rpo_helper(*id, succ, rpo, visited);
        }
        rpo.push(id);
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Type::Bool => write!(f, "bool"),
            Type::I64 => write!(f, "i64"),
        }
    }
}

impl Display for Constant {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Constant::Bool(val) => val.fmt(f),
            Constant::I64(val) => val.fmt(f),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Expr::Constant { val } => val.fmt(f),
            Expr::Variable { var } => var.as_str().fmt(f),
            Expr::Unary { op, input } => write!(f, "{}{}", op, input),
            Expr::Binary { op, lhs, rhs } => write!(f, "({} {} {})", lhs, op, rhs),
        }
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            UnaryOp::Neg => "-".fmt(f),
            UnaryOp::BitwiseNot => "~".fmt(f),
            UnaryOp::Not => "!".fmt(f),
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            BinaryOp::Add => "+".fmt(f),
            BinaryOp::Sub => "-".fmt(f),
            BinaryOp::Mul => "*".fmt(f),
            BinaryOp::BitwiseAnd => "&".fmt(f),
            BinaryOp::BitwiseOr => "|".fmt(f),
            BinaryOp::BitwiseXor => "^".fmt(f),
            BinaryOp::And => "&&".fmt(f),
            BinaryOp::Or => "||".fmt(f),
            BinaryOp::Xor => "^^".fmt(f),
            BinaryOp::EE => "==".fmt(f),
            BinaryOp::NE => "!=".fmt(f),
            BinaryOp::LT => "<".fmt(f),
            BinaryOp::LE => "<=".fmt(f),
            BinaryOp::GT => ">".fmt(f),
            BinaryOp::GE => ">=".fmt(f),
        }
    }
}

fn concrete_eval(expr: &Expr, store: &HashMap<Symbol, Constant>) -> Constant {
    match expr {
        Expr::Constant { val } => *val,
        Expr::Variable { var } => store[var],
        Expr::Unary { op, input } => {
            let input = concrete_eval(input, store);
            use UnaryOp::*;
            match op {
                Neg => {
                    let Constant::I64(input) = input else {
                        panic!()
                    };
                    Constant::I64(input.wrapping_neg())
                }
                BitwiseNot => {
                    let Constant::I64(input) = input else {
                        panic!()
                    };
                    Constant::I64(!input)
                }
                Not => {
                    let Constant::Bool(input) = input else {
                        panic!()
                    };
                    Constant::Bool(!input)
                }
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs = concrete_eval(lhs, store);
            let rhs = concrete_eval(rhs, store);
            use BinaryOp::*;
            match op {
                Add => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::I64(lhs.wrapping_add(rhs))
                }
                Sub => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::I64(lhs.wrapping_sub(rhs))
                }
                Mul => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::I64(lhs.wrapping_mul(rhs))
                }
                BitwiseAnd => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::I64(lhs & rhs)
                }
                BitwiseOr => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::I64(lhs | rhs)
                }
                BitwiseXor => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::I64(lhs ^ rhs)
                }
                And => {
                    let (Constant::Bool(lhs), Constant::Bool(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs & rhs)
                }
                Or => {
                    let (Constant::Bool(lhs), Constant::Bool(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs | rhs)
                }
                Xor => {
                    let (Constant::Bool(lhs), Constant::Bool(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs ^ rhs)
                }
                EE => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs == rhs)
                }
                NE => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs != rhs)
                }
                LT => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs < rhs)
                }
                LE => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs <= rhs)
                }
                GT => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs > rhs)
                }
                GE => {
                    let (Constant::I64(lhs), Constant::I64(rhs)) = (lhs, rhs) else {
                        panic!()
                    };
                    Constant::Bool(lhs >= rhs)
                }
            }
        }
    }
}

fn concrete_traversable(block: &Block, store: &HashMap<Symbol, Constant>) -> bool {
    if let Block::Guard {
        cond, direction, ..
    } = block
    {
        let Constant::Bool(cond) = concrete_eval(cond, store) else {
            panic!()
        };
        cond == *direction
    } else {
        true
    }
}

fn concrete_traverse(block: &Block, store: &mut HashMap<Symbol, Constant>) {
    if let Block::Assign { var, expr, .. } = block {
        store.insert(*var, concrete_eval(expr, store));
    }
}

#[derive(Debug)]
pub struct State {
    pub location: BlockId,
    pub store: HashMap<Symbol, Constant>,
}

pub fn concrete_interpret(func: &NonSSAFunc, args: &Vec<Constant>, fuel: usize) -> Vec<State> {
    let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for (id, block) in func.cfg.iter().enumerate() {
        succs.entry(id).or_default();
        use Block::*;
        match block {
            Entry => {}
            Guard { pred, .. } | Assign { pred, .. } | Return { pred, .. } => {
                succs.entry(*pred).or_default().push(id);
            }
            Merge { pred1, pred2 } => {
                succs.entry(*pred1).or_default().push(id);
                succs.entry(*pred2).or_default().push(id);
            }
        }
    }

    let mut location = 0;
    let mut store: HashMap<Symbol, Constant> = args
        .into_iter()
        .enumerate()
        .map(|(idx, cons)| {
            assert_eq!(cons.ty(), func.params[idx].1);
            (func.params[idx].0, *cons)
        })
        .collect();
    let mut trace = vec![];
    for _ in 0..fuel {
        trace.push(State {
            location,
            store: store.clone(),
        });
        let mut succs = succs[&location]
            .iter()
            .filter(|block| concrete_traversable(&func.cfg[**block], &store));
        let Some(succ) = succs.next() else { break };
        assert!(succs.next().is_none());
        location = *succ;
        let block = &func.cfg[location];
        concrete_traverse(block, &mut store);
    }
    trace
}
