use clap::Parser;

use eqsat_ai::ai::abstract_interpret;
use eqsat_ai::imp::ast::{ImpFunc, ImpStmt, convert_to_cfg};
use eqsat_ai::imp::grammar::ProgramParser;
use eqsat_ai::saturator::Saturator;

#[derive(Debug, Parser)]
struct Args {
    text: String,
    #[arg(short, long, default_value = "5")]
    max_saturate_iters: usize,
    #[arg(short, long)]
    stat_threshold: Option<usize>,
}

fn evaluate(func: &ImpFunc, max_saturate_iters: usize) -> usize {
    let nonssa = convert_to_cfg(func.clone());
    let mut saturator = Saturator::new(max_saturate_iters, true);
    let result = abstract_interpret(&mut saturator, nonssa.name, &nonssa);
    result.num_rule_fires
}

fn minimize(stmt: &mut ImpStmt) -> bool {
    let mut removed_anything = false;
    match stmt {
        ImpStmt::Block { body } => {
            for idx in (0..body.len()).rev() {
                removed_anything |= minimize(&mut body[idx]);
                if let ImpStmt::Block { body: subbody } = &body[idx]
                    && subbody.is_empty()
                {
                    body.remove(idx);
                    removed_anything = true;
                }
            }
            if body.len() == 1 {
                *stmt = body.remove(0);
            }
        }
        ImpStmt::IfElse {
            cond: _,
            then_body,
            else_body,
        } => {
            if rand::random_ratio(1, 50) {
                *stmt = ImpStmt::Block { body: vec![] };
                removed_anything = true;
            } else if rand::random_ratio(1, 50) {
                minimize(then_body);
                minimize(else_body);
                *stmt = *if rand::random() { then_body } else { else_body }.clone();
                removed_anything = true;
            } else {
                removed_anything |= minimize(then_body);
                removed_anything |= minimize(else_body);
            }
        }
        ImpStmt::While { cond: _, body } => {
            if rand::random_ratio(1, 50) {
                *stmt = ImpStmt::Block { body: vec![] };
                removed_anything = true;
            } else if rand::random_ratio(1, 50) {
                minimize(body);
                *stmt = *body.clone();
                removed_anything = true;
            } else {
                removed_anything |= minimize(body);
            }
        }
        _ => {}
    };
    removed_anything
}

fn main() {
    let args = Args::parse();
    let funcs = ProgramParser::new().parse(&args.text).unwrap();
    for (_, mut func) in funcs {
        let initial_stat = evaluate(&func, args.max_saturate_iters);
        println!("Initial statistic: {}", initial_stat);
        let threshold = args.stat_threshold.unwrap_or(initial_stat);
        let mut iters_since_successful_edit = 0;
        while iters_since_successful_edit < 1000 {
            let old_func = func.clone();
            println!("Minimizing...");
            while !minimize(&mut func.body) {}
            println!("Evaluating...");
            let stat = evaluate(&func, args.max_saturate_iters);
            if stat >= threshold {
                println!("New program has {} statistic: {}", stat, func);
                iters_since_successful_edit = 0;
            } else {
                func = old_func;
                iters_since_successful_edit += 1;
                println!("Edit #{} failed...", iters_since_successful_edit);
            }
        }
        println!("Minimized program: {}", func);
    }
}
