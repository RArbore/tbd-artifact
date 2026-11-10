use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use clap::Parser;
use rand::prelude::*;
use rand::rngs::Xoshiro128PlusPlus;
use rayon::prelude::*;
use symbol_table::GlobalSymbol as Symbol;

use eqsat_ai::ai::{abstract_interpret, check_trace_against_analysis};
use eqsat_ai::imp::ast::{ImpFunc, ImpStmt, convert_to_cfg};
use eqsat_ai::imp::grammar::ProgramParser;
use eqsat_ai::nonssa::{BinaryOp, Constant, Expr, NonSSAFunc, Type, UnaryOp, concrete_interpret};
use eqsat_ai::saturator::Saturator;

const NUM_GENERATED: u64 = 10000;
const NUM_GENERATED_PER_IF: u64 = 100;
const INITIAL_JUICE: usize = 5;

#[derive(Debug, Parser)]
struct Args {
    #[arg(short, long)]
    index: Option<u64>,
    #[arg(short, long)]
    text: Option<String>,
    #[arg(short, long, default_value = "10")]
    max_saturate_iters: usize,
    #[arg(long, action)]
    enable_rws: bool,
    #[arg(long, action)]
    no_check: bool,
    #[arg(long, short, action)]
    parallel: bool,
    #[arg(long, action)]
    preceding_ifs: bool,
}

struct Sampler<R: Rng> {
    in_scope: BTreeMap<Symbol, Type>,
    num_vars: usize,
    rng: R,
}

impl<R: Rng> Sampler<R> {
    fn sample_constant(&mut self, ty: Type) -> Constant {
        match ty {
            Type::Bool => Constant::Bool(self.rng.random()),
            Type::I64 => Constant::I64(self.rng.random()),
        }
    }

    fn sample_type(&mut self) -> Type {
        if self.rng.random() {
            Type::Bool
        } else {
            Type::I64
        }
    }

    fn sample_leaf_expr(&mut self, ty: Type) -> Expr {
        match self.rng.random_range(0..10) {
            0..3 => Expr::Constant {
                val: self.sample_constant(ty),
            },
            3..10 => {
                let mut iter_of_ty = self.in_scope.iter().filter(|(_, var_ty)| **var_ty == ty);
                let num_of_ty = iter_of_ty.clone().count();
                if num_of_ty == 0 {
                    Expr::Constant {
                        val: self.sample_constant(ty),
                    }
                } else {
                    let (var, _) = iter_of_ty.nth(self.rng.random_range(0..num_of_ty)).unwrap();
                    Expr::Variable { var: *var }
                }
            }
            _ => panic!(),
        }
    }

    fn sample_expr(&mut self, ty: Type) -> Expr {
        use BinaryOp::*;
        use UnaryOp::*;
        match self.rng.random_range(0..10) {
            0..3 => self.sample_leaf_expr(ty),
            3..5 => match ty {
                Type::Bool => {
                    let input = Box::new(self.sample_leaf_expr(ty));
                    Expr::Unary { op: Not, input }
                }
                Type::I64 => {
                    let input = Box::new(self.sample_leaf_expr(ty));
                    if self.rng.random() {
                        Expr::Unary { op: Neg, input }
                    } else {
                        Expr::Unary {
                            op: BitwiseNot,
                            input,
                        }
                    }
                }
            },
            5..10 => match ty {
                Type::Bool => {
                    let (op, input_ty) = match self.rng.random_range(0..9) {
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
                    let lhs = Box::new(self.sample_leaf_expr(input_ty));
                    let rhs = Box::new(self.sample_leaf_expr(input_ty));
                    Expr::Binary { op, lhs, rhs }
                }
                Type::I64 => {
                    let op = match self.rng.random_range(0..6) {
                        0 => Add,
                        1 => Sub,
                        2 => Mul,
                        3 => BitwiseAnd,
                        4 => BitwiseOr,
                        5 => BitwiseXor,
                        _ => panic!(),
                    };
                    let lhs = Box::new(self.sample_leaf_expr(Type::I64));
                    let rhs = Box::new(self.sample_leaf_expr(Type::I64));
                    Expr::Binary { op, lhs, rhs }
                }
            },
            _ => panic!(),
        }
    }

    fn sample_assigns_and_ifs(&mut self, preceding_ifs: u64) -> ImpStmt {
        let mut body = vec![];
        let mut prob = 100;
        while body.is_empty() || self.rng.random_ratio(prob, prob + 1) {
            let var = if !self.in_scope.is_empty() && self.rng.random_ratio(3, 5) {
                *self
                    .in_scope
                    .iter()
                    .nth(self.rng.random_range(0..self.in_scope.len()))
                    .unwrap()
                    .0
            } else {
                let new = format!("v{}", self.num_vars).into();
                self.num_vars += 1;
                new
            };
            let expr = self.sample_expr(Type::I64);
            self.in_scope.insert(var, Type::I64);
            body.push(ImpStmt::Assign { var, expr });
            prob -= 1;
        }
        let mut sequence = vec![];
        for _ in 0..preceding_ifs {
            sequence.push(ImpStmt::IfElse {
                cond: Expr::Variable {
                    var: format!("b").into(),
                },
                then_body: Box::new(ImpStmt::Block { body: vec![] }),
                else_body: Box::new(ImpStmt::Block { body: vec![] }),
            })
        }
        sequence.push(ImpStmt::Block { body });
        ImpStmt::Block { body: sequence }
    }

    fn sample_stmt(&mut self, juice: usize) -> ImpStmt {
        if juice == 0 {
            return ImpStmt::Block { body: vec![] };
        }
        let choice = if juice == INITIAL_JUICE {
            4
        } else {
            self.rng.random_range(0..10)
        };
        match choice {
            0..4 => {
                let mut body = vec![];
                let mut prob = 30;
                while body.is_empty() || self.rng.random_ratio(prob, prob + 1) {
                    let (var, ty) = if !self.in_scope.is_empty() && self.rng.random_ratio(7, 10) {
                        let (var, ty) = self
                            .in_scope
                            .iter()
                            .nth(self.rng.random_range(0..self.in_scope.len()))
                            .unwrap();
                        (*var, *ty)
                    } else {
                        let new = (format!("v{}", self.num_vars).into(), self.sample_type());
                        self.num_vars += 1;
                        new
                    };
                    let expr = self.sample_expr(ty);
                    self.in_scope.insert(var, ty);
                    body.push(ImpStmt::Assign { var, expr });
                    prob -= 1;
                }
                ImpStmt::Block { body }
            }
            4..7 => {
                let mut body = vec![];
                let mut prob = 10;
                while body.is_empty() || self.rng.random_ratio(prob, prob + 1) {
                    body.push(self.sample_stmt(juice - 1));
                    prob -= 1;
                }
                ImpStmt::Block { body }
            }
            7..9 => {
                let cond = self.sample_expr(Type::Bool);
                let old_in_scope = self.in_scope.clone();
                let then_body = Box::new(self.sample_stmt(juice - 1));
                self.in_scope = old_in_scope.clone();
                let else_body = Box::new(self.sample_stmt(juice - 1));
                self.in_scope = old_in_scope;
                ImpStmt::IfElse {
                    cond,
                    then_body,
                    else_body,
                }
            }
            9..10 => {
                let cond = self.sample_expr(Type::Bool);
                let old_in_scope = self.in_scope.clone();
                let body = Box::new(self.sample_stmt(juice - 1));
                self.in_scope = old_in_scope;
                ImpStmt::While { cond, body }
            }
            _ => panic!(),
        }
    }
}

fn generate_func<R: Rng>(sampler: &mut Sampler<R>, preceding_ifs: Option<u64>) -> ImpFunc {
    let mut params = vec![];
    if preceding_ifs.is_some() {
        let param = format!("b").into();
        params.push((param, Type::Bool));
    }
    while sampler.rng.random_ratio(3, 5) {
        let param = format!("v{}", sampler.num_vars).into();
        let ty = sampler.sample_type();
        params.push((param, ty));
        sampler.in_scope.insert(param, ty);
        sampler.num_vars += 1;
    }

    let body = if let Some(preceding_ifs) = preceding_ifs {
        sampler.sample_assigns_and_ifs(preceding_ifs)
    } else {
        sampler.sample_stmt(INITIAL_JUICE)
    };

    ImpFunc {
        name: "func".into(),
        params,
        body,
    }
}

#[derive(Debug)]
struct Stats {
    #[allow(dead_code)]
    concrete_interpret_time: Duration,
    abstract_interpret_time: Duration,
    #[allow(dead_code)]
    checking_time: Duration,
    num_blocks: usize,
    num_reachable_blocks: usize,
    max_component_iterations: usize,
    num_interesting_visits: usize,
    num_rule_fires: usize,
    max_version_level: usize,
}

fn check_func(
    nonssa: NonSSAFunc,
    args: Vec<Constant>,
    max_saturate_iters: usize,
    enable_rws: bool,
    no_check: bool,
) -> Stats {
    let concrete_interpret_time = Instant::now();
    let trace = concrete_interpret(&nonssa, &args, 100);
    let concrete_interpret_time = concrete_interpret_time.elapsed();

    let mut saturator = Saturator::new(max_saturate_iters, enable_rws);
    let abstract_interpret_time = Instant::now();
    let result = abstract_interpret(&mut saturator, nonssa.name, &nonssa);
    let abstract_interpret_time = abstract_interpret_time.elapsed();
    let max_version_level = result
        .ssa_blocks
        .values()
        .map(|ssa_block_id| saturator.version(*ssa_block_id).level())
        .max()
        .unwrap_or(0);

    let checking_time = Instant::now();
    if !no_check {
        check_trace_against_analysis(&trace, result.vars, result.ssa_blocks, &mut saturator);
    }
    let checking_time = checking_time.elapsed();
    Stats {
        concrete_interpret_time,
        abstract_interpret_time,
        checking_time,
        num_blocks: nonssa.cfg.len(),
        num_reachable_blocks: result.reachable_blocks.len(),
        max_component_iterations: result.max_component_iterations,
        num_interesting_visits: result.num_interesting_visits,
        num_rule_fires: result.num_rule_fires,
        max_version_level,
    }
}

fn main() {
    let args = Args::parse();
    match (args.index, args.text) {
        (None, None) => {
            let range = if args.preceding_ifs {
                NUM_GENERATED + NUM_GENERATED_PER_IF
            } else {
                NUM_GENERATED
            };
            let iter_func = |i| {
                let seed = if args.preceding_ifs {
                    i / (range / NUM_GENERATED_PER_IF)
                } else {
                    i
                };
                let num_ifs = if args.preceding_ifs {
                    Some(10 * (i % (range / NUM_GENERATED_PER_IF)))
                } else {
                    None
                };
                let mut sampler = Sampler {
                    in_scope: BTreeMap::new(),
                    num_vars: 0,
                    rng: Xoshiro128PlusPlus::seed_from_u64(seed),
                };
                let func = generate_func(&mut sampler, num_ifs);
                let mut func_args = vec![];
                for (_, ty) in &func.params {
                    func_args.push(sampler.sample_constant(*ty));
                }
                let nonssa = convert_to_cfg(func);
                let stats = check_func(
                    nonssa,
                    func_args,
                    args.max_saturate_iters,
                    args.enable_rws,
                    args.no_check,
                );
                println!(
                    "{},{},{},{},{},{},{},{},{},{}",
                    seed,
                    num_ifs.unwrap_or(0),
                    args.max_saturate_iters,
                    stats.num_blocks,
                    stats.num_reachable_blocks,
                    stats.max_component_iterations,
                    stats.num_interesting_visits,
                    stats.num_rule_fires,
                    stats.max_version_level,
                    stats.abstract_interpret_time.as_micros()
                );
            };
            if args.parallel {
                (0..range).into_par_iter().for_each(iter_func);
            } else {
                (0..range).for_each(iter_func);
            }
        }
        (None, Some(text)) => {
            assert!(!args.parallel);
            assert!(!args.preceding_ifs);
            let mut sampler = Sampler {
                in_scope: BTreeMap::new(),
                num_vars: 0,
                rng: Xoshiro128PlusPlus::seed_from_u64(0),
            };
            let funcs = ProgramParser::new().parse(&text).unwrap();
            for (_, func) in funcs {
                let mut func_args = vec![];
                for (_, ty) in &func.params {
                    func_args.push(sampler.sample_constant(*ty));
                }
                println!("{func}");
                let nonssa = convert_to_cfg(func);
                let stats = check_func(
                    nonssa,
                    func_args,
                    args.max_saturate_iters,
                    args.enable_rws,
                    args.no_check,
                );
                println!("{:?}", stats);
            }
        }
        (Some(index), None) => {
            assert!(!args.parallel);
            assert!(!args.preceding_ifs);
            let mut sampler = Sampler {
                in_scope: BTreeMap::new(),
                num_vars: 0,
                rng: Xoshiro128PlusPlus::seed_from_u64(index),
            };
            let func = generate_func(&mut sampler, None);
            let mut func_args = vec![];
            for (_, ty) in &func.params {
                func_args.push(sampler.sample_constant(*ty));
            }
            println!("{func}");
            let nonssa = convert_to_cfg(func);
            let stats = check_func(
                nonssa,
                func_args,
                args.max_saturate_iters,
                args.enable_rws,
                args.no_check,
            );
            println!("{:?}", stats);
        }
        (Some(_), Some(_)) => panic!("can't provide both index and text of program to examine"),
    }
}
