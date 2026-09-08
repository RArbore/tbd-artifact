use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

use clap::Parser;

use eqsat_ai::ai::abstract_interpret;
use eqsat_ai::imp::ast::convert_to_cfg;
use eqsat_ai::imp::grammar::ProgramParser;
use eqsat_ai::ssa::SSAProgram;

#[derive(Debug, Parser)]
struct Args {
    input: PathBuf,
}

fn main() {
    let args = Args::parse();
    let mut file = File::open(&args.input).unwrap();
    let mut contents = "".to_string();
    file.read_to_string(&mut contents).unwrap();
    let parsed = ProgramParser::new().parse(&contents).unwrap();
    let mut ssa = SSAProgram::default();
    for (name, ast) in parsed {
        let nonssa = convert_to_cfg(ast);
        abstract_interpret(&mut ssa, name, &nonssa);
    }
    println!("{:?}", ssa);
}
