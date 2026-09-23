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
    Not,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
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
            BinaryOp::And => "&".fmt(f),
            BinaryOp::Or => "|".fmt(f),
            BinaryOp::Xor => "^".fmt(f),
            BinaryOp::EE => "==".fmt(f),
            BinaryOp::NE => "!=".fmt(f),
            BinaryOp::LT => "<".fmt(f),
            BinaryOp::LE => "<=".fmt(f),
            BinaryOp::GT => ">".fmt(f),
            BinaryOp::GE => ">=".fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
