pub mod ai;
pub mod imp;
pub mod nonssa;
pub mod saturator;
pub mod ssa;
pub mod trie;
pub mod version;

#[allow(non_snake_case, unused_mut, unused_variables)]
pub mod rw {
    include!(concat!(env!("OUT_DIR"), "/rw.rs"));
}
