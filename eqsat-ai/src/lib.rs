pub mod ai;
pub mod imp;
pub mod nonssa;
pub mod saturator;
pub mod ssa;
pub mod trie;
pub mod version;

#[cfg(test)]
mod tests;

#[allow(non_snake_case, path_statements, unused_mut, unused_variables)]
pub mod rw {
    include!(concat!(env!("OUT_DIR"), "/rw.rs"));
}
