use std::env::{current_dir, var};
use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

use compile_rw::compile_rw;

fn main() {
    lalrpop::process_root().unwrap();

    // Compile rewrite rules into Rust code that implements the required relational e-matching.
    let mut file = File::open(current_dir().unwrap().join("src/rw.rules")).unwrap();
    let mut contents = "".to_string();
    file.read_to_string(&mut contents).unwrap();
    let compiled = compile_rw(&contents);

    // Write the compiled code into OUT_DIR.
    let mut out = PathBuf::new();
    out.push(var("OUT_DIR").unwrap());
    out.push("rw.rs");
    let mut file = File::create(out).unwrap();
    write!(file, "{}", compiled).unwrap();
}
