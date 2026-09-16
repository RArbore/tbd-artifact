use core::fmt::{Display, Formatter, Result};

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
            BinaryOp::EE => "==".fmt(f),
            BinaryOp::NE => "!=".fmt(f),
            BinaryOp::LT => "<".fmt(f),
            BinaryOp::LE => "<=".fmt(f),
            BinaryOp::GT => ">".fmt(f),
            BinaryOp::GE => ">=".fmt(f),
        }
    }
}
