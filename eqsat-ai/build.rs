use std::env::current_dir;
use std::fs::File;
use std::io::Read;

use compile_rw::compile_rw;

fn main() {
    lalrpop::process_root().unwrap();

    // Compile rewrite rules into Rust code that implements the required relational e-matching.
    let mut file = File::open(current_dir().unwrap().join("src/rw.rules")).unwrap();
    let mut contents = "".to_string();
    file.read_to_string(&mut contents).unwrap();
    compile_rw(&contents);
}
