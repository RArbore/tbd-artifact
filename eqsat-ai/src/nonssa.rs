use core::fmt::{Display, Formatter, Result};

use derive_more::FromStr;
use serde::Serialize;
use spytial::SpytialDecorators;
use symbol_table::GlobalSymbol as Symbol;

#[derive(
    Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, FromStr, Serialize, SpytialDecorators,
)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(
    Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash, FromStr, Serialize, SpytialDecorators,
)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, SpytialDecorators)]
#[attribute(field = "num")]
#[attribute(field = "op")]
#[attribute(field = "var")]
#[hide_atom(selector = "i32 + string + UnaryOp + BinaryOp")]
pub enum Expr {
    Number {
        num: i32,
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, SpytialDecorators)]
#[attribute(field = "var")]
#[hide_atom(selector = "u64")]
pub enum Block {
    Entry,
    Guard {
        pred: BlockId,
        cond: Expr,
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

#[derive(Debug, Serialize, SpytialDecorators)]
#[attribute(field = "name")]
#[hide_atom(selector = "string")]
pub struct NonSSAFunc {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub cfg: Vec<Block>,
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Expr::Number { num } => num.fmt(f),
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
