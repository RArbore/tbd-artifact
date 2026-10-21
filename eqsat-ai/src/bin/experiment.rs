use std::collections::HashMap;

use rand::prelude::*;
use rand::rngs::Xoshiro128PlusPlus;
use symbol_table::GlobalSymbol as Symbol;

use eqsat_ai::ai::{abstract_interpret, check_trace_against_analysis};
use eqsat_ai::imp::ast::{ImpFunc, ImpStmt, convert_to_cfg};
use eqsat_ai::nonssa::{BinaryOp, Constant, Expr, Type, UnaryOp, concrete_interpret};
use eqsat_ai::saturator::Saturator;

fn sample_constant<R: Rng>(ty: Type, rng: &mut R) -> Constant {
    match ty {
        Type::Bool => Constant::Bool(rng.random()),
        Type::I64 => Constant::I64(rng.random()),
    }
}

fn sample_type<R: Rng>(rng: &mut R) -> Type {
    if rng.random() { Type::Bool } else { Type::I64 }
}

fn sample_expr<R: Rng>(
    ty: Type,
    in_scope: &mut HashMap<Symbol, Type>,
    rng: &mut R,
    juice: usize,
) -> Expr {
    if juice == 0 {
        return Expr::Constant {
            val: sample_constant(ty, rng),
        };
    }
    use BinaryOp::*;
    use UnaryOp::*;
    match rng.random_range(0..4) {
        0 => Expr::Constant {
            val: sample_constant(ty, rng),
        },
        1 => {
            let mut iter_of_ty = in_scope.iter().filter(|(_, var_ty)| **var_ty == ty);
            let num_of_ty = iter_of_ty.clone().count();
            if num_of_ty == 0 {
                return sample_expr(ty, in_scope, rng, juice - 1);
            }
            let (var, _) = iter_of_ty.nth(rng.random_range(0..num_of_ty)).unwrap();
            Expr::Variable { var: *var }
        }
        2 => match ty {
            Type::Bool => {
                let input = Box::new(sample_expr(ty, in_scope, rng, juice - 1));
                Expr::Unary { op: Not, input }
            }
            Type::I64 => {
                let input = Box::new(sample_expr(ty, in_scope, rng, juice - 1));
                if rng.random() {
                    Expr::Unary { op: Neg, input }
                } else {
                    Expr::Unary {
                        op: BitwiseNot,
                        input,
                    }
                }
            }
        },
        3 => match ty {
            Type::Bool => {
                let (op, input_ty) = match rng.random_range(0..9) {
                    0 => (And, Type::Bool),
                    1 => (Or, Type::Bool),
                    2 => (Xor, Type::Bool),
                    3 => (EE, Type::I64),
                    4 => (NE, Type::I64),
                    5 => (LT, Type::I64),
                    6 => (LE, Type::I64),
                    7 => (GT, Type::I64),
                    8 => (GE, Type::I64),
                    _ => panic!(),
                };
                let lhs = Box::new(sample_expr(input_ty, in_scope, rng, juice - 1));
                let rhs = Box::new(sample_expr(input_ty, in_scope, rng, juice - 1));
                Expr::Binary { op, lhs, rhs }
            }
            Type::I64 => {
                let op = match rng.random_range(0..6) {
                    0 => Add,
                    1 => Sub,
                    2 => Mul,
                    3 => BitwiseAnd,
                    4 => BitwiseOr,
                    5 => BitwiseXor,
                    _ => panic!(),
                };
                let lhs = Box::new(sample_expr(Type::I64, in_scope, rng, juice - 1));
                let rhs = Box::new(sample_expr(Type::I64, in_scope, rng, juice - 1));
                Expr::Binary { op, lhs, rhs }
            }
        },
        _ => panic!(),
    }
}

fn sample_stmt<R: Rng>(in_scope: &mut HashMap<Symbol, Type>, rng: &mut R, juice: usize) -> ImpStmt {
    if juice == 0 {
        return ImpStmt::Block { body: vec![] };
    }
    match rng.random_range(0..4) {
        0 => {
            let mut body = vec![];
            while rng.random_ratio(4, 5) {
                body.push(sample_stmt(in_scope, rng, juice - 1));
            }
            ImpStmt::Block { body }
        }
        1 => {
            let (var, ty) = if !in_scope.is_empty() && rng.random_ratio(3, 5) {
                let (var, ty) = in_scope
                    .iter()
                    .nth(rng.random_range(0..in_scope.len()))
                    .unwrap();
                (*var, *ty)
            } else {
                (format!("{}", in_scope.len()).into(), sample_type(rng))
            };
            let expr = sample_expr(ty, in_scope, rng, juice - 1);
            ImpStmt::Assign { var, expr }
        }
        2 => {
            let cond = sample_expr(Type::Bool, in_scope, rng, juice - 1);
            let then_body = Box::new(sample_stmt(&mut in_scope.clone(), rng, juice - 1));
            let else_body = Box::new(sample_stmt(&mut in_scope.clone(), rng, juice - 1));
            ImpStmt::IfElse {
                cond,
                then_body,
                else_body,
            }
        }
        3 => {
            let cond = sample_expr(Type::Bool, in_scope, rng, juice - 1);
            let body = Box::new(sample_stmt(&mut in_scope.clone(), rng, juice - 1));
            ImpStmt::While { cond, body }
        }
        _ => panic!(),
    }
}

fn generate_func<R: Rng>(rng: &mut R) -> ImpFunc {
    let mut in_scope = HashMap::new();
    let mut params = vec![];

    while rng.random() {
        let param = format!("{}", params.len()).into();
        let ty = sample_type(rng);
        params.push((param, ty));
        in_scope.insert(param, ty);
    }

    let body = sample_stmt(&mut in_scope, rng, 10);

    ImpFunc {
        name: "func".into(),
        params,
        body,
    }
}

fn main() {
    for i in 0..100 {
        let mut rng = Xoshiro128PlusPlus::seed_from_u64(i);
        let func = generate_func(&mut rng);
        let mut args = vec![];
        for (_, ty) in &func.params {
            args.push(sample_constant(*ty, &mut rng));
        }
        println!("{func}");
        let nonssa = convert_to_cfg(func);
        let trace = concrete_interpret(&nonssa, &args, 100);
        let mut saturator = Saturator::default();
        let (vars, blocks) = abstract_interpret(&mut saturator, nonssa.name, &nonssa);
        check_trace_against_analysis(&trace, vars, blocks, &mut saturator);
        println!("CHECKED {i}");
    }
}
