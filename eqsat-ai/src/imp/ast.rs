use core::fmt::{Display, Formatter, Result};

use symbol_table::GlobalSymbol as Symbol;

use crate::nonssa::{Block, BlockId, Expr, NonSSAFunc, UnaryOp};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImpFunc {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub body: ImpStmt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpStmt {
    Block {
        body: Vec<ImpStmt>,
    },
    Assign {
        var: Symbol,
        expr: Expr,
    },
    IfElse {
        cond: Expr,
        then_body: Box<ImpStmt>,
        else_body: Box<ImpStmt>,
    },
    While {
        cond: Expr,
        body: Box<ImpStmt>,
    },
    Return {
        exprs: Vec<Expr>,
    },
}

pub fn convert_to_cfg(func: ImpFunc) -> NonSSAFunc {
    let mut convert_context = ConvertContext {
        cfg: vec![Block::Entry],
        returns: vec![],
        num_returned: None,
    };
    convert_context.convert(0, func.body);

    if let Some(mut block) = convert_context.returns.get(0).copied() {
        for idx in 1..convert_context.returns.len() {
            block = convert_context.add_block(Block::Merge {
                pred1: block,
                pred2: convert_context.returns[idx],
            });
        }
        convert_context.add_block(Block::Return {
            pred: block,
            exprs: (0..convert_context.num_returned.unwrap())
                .map(|idx| Expr::Variable {
                    var: Symbol::from(format!("%{}", idx)),
                })
                .collect(),
        });
    }

    NonSSAFunc {
        name: func.name,
        params: func.params,
        cfg: convert_context.cfg,
    }
}

struct ConvertContext {
    cfg: Vec<Block>,
    returns: Vec<BlockId>,
    num_returned: Option<usize>,
}

impl ConvertContext {
    fn add_block(&mut self, block: Block) -> BlockId {
        let id = self.cfg.len();
        self.cfg.push(block);
        id
    }

    fn convert(&mut self, pred: BlockId, stmt: ImpStmt) -> Option<BlockId> {
        match stmt {
            ImpStmt::Block { body } => {
                let mut id = pred;
                for stmt in body {
                    id = self.convert(id, stmt)?;
                }
                Some(id)
            }
            ImpStmt::Assign { var, expr } => {
                Some(self.add_block(Block::Assign { pred, var, expr }))
            }
            ImpStmt::IfElse {
                cond,
                then_body,
                else_body,
            } => {
                let then_guard = self.add_block(Block::Guard {
                    pred,
                    cond: cond.clone(),
                });
                let else_guard = self.add_block(Block::Guard {
                    pred,
                    cond: Expr::Unary {
                        op: UnaryOp::Not,
                        input: Box::new(cond),
                    },
                });
                let then_block = self.convert(then_guard, *then_body);
                let else_block = self.convert(else_guard, *else_body);
                match (then_block, else_block) {
                    (Some(pred1), Some(pred2)) => {
                        Some(self.add_block(Block::Merge { pred1, pred2 }))
                    }
                    (None, block) | (block, None) => block,
                }
            }
            ImpStmt::While { cond, body } => {
                let header = self.add_block(Block::Entry);
                let then_guard = self.add_block(Block::Guard {
                    pred: header,
                    cond: cond.clone(),
                });
                let else_guard = self.add_block(Block::Guard {
                    pred: header,
                    cond: Expr::Unary {
                        op: UnaryOp::Not,
                        input: Box::new(cond),
                    },
                });
                let body_block = self.convert(then_guard, *body);
                self.cfg[header] = if let Some(body_block) = body_block {
                    Block::Merge {
                        pred1: pred,
                        pred2: body_block,
                    }
                } else {
                    Block::Guard {
                        pred,
                        cond: Expr::Number { num: 1 },
                    }
                };
                Some(else_guard)
            }
            ImpStmt::Return { exprs } => {
                let mut block = pred;
                assert!(self.num_returned.is_none() || self.num_returned == Some(exprs.len()));
                self.num_returned = Some(exprs.len());
                for (idx, expr) in exprs.into_iter().enumerate() {
                    block = self.add_block(Block::Assign {
                        pred: block,
                        var: Symbol::from(format!("%{}", idx)),
                        expr,
                    });
                }
                self.returns.push(block);
                None
            }
        }
    }
}

impl Display for ImpFunc {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "fn {}(", self.name.as_str())?;
        for idx in 0..self.params.len() {
            if idx != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", self.params[idx].as_str())?;
        }
        write!(f, ") {}", self.body)
    }
}

impl Display for ImpStmt {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            ImpStmt::Block { body } => {
                write!(f, "{{ ")?;
                for stmt in body {
                    stmt.fmt(f)?;
                    write!(f, " ")?;
                }
                write!(f, "}}")
            }
            ImpStmt::Assign { var, expr, .. } => write!(f, "{} = {};", var.as_str(), expr),
            ImpStmt::IfElse {
                cond,
                then_body,
                else_body,
                ..
            } => {
                write!(
                    f,
                    "if {} {{ {} }} else {{ {} }}",
                    cond, then_body, else_body
                )
            }
            ImpStmt::While { cond, body, .. } => write!(f, "while {} {{ {} }}", cond, body),
            ImpStmt::Return { exprs: expr, .. } => {
                write!(f, "return ")?;
                for idx in 0..expr.len() {
                    if idx != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", expr[idx])?;
                }
                write!(f, ";")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use symbol_table::GlobalSymbol as Symbol;

    use crate::imp::grammar::ProgramParser;

    #[test]
    fn parse1() {
        let program = r#"
fn test1(x) return x;
fn test2(y) { y = 3; return y + 1; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test1")]),
            "fn test1(x) return x;"
        );
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test2")]),
            "fn test2(y) { y = 3; return (y + 1); }"
        );
    }

    #[test]
    fn parse2() {
        let program = r#"
fn test(x, y) { while x < 7 { x = x + 1; } if y < x { return y; } return x + 9; }
"#;
        let parsed = ProgramParser::new().parse(&program).unwrap();
        assert_eq!(
            format!("{}", parsed[&Symbol::from("test")]),
            "fn test(x, y) { while (x < 7) { { x = (x + 1); } } if (y < x) { { return y; } } else { { } } return (x + 9); }"
        );
    }
}
