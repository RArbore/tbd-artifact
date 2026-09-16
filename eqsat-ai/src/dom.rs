use core::cmp::max;
use std::collections::HashMap;

use crate::ssa::{SSABlock, SSABlockId};

// Store immediate dominators among SSA blocks, as well as level in the dominator tree (to assist in
// computing LCAs).
#[derive(Debug, Default, PartialEq, Eq)]
pub struct DomTree(HashMap<SSABlockId, (SSABlockId, usize)>);

impl DomTree {
    pub fn idom(&self, id: SSABlockId) -> Option<SSABlockId> {
        self.0.get(&id).map(|(idom, _)| *idom)
    }

    // We incrementally maintain dominance information among created SSA blocks, so that we can
    // create the version hierarchy properly. Dominance information for any given block may be out of
    // date, just like any other analysis.
    pub fn visit_block(&mut self, id: SSABlockId, block: &SSABlock) {
        use SSABlock::*;
        match block {
            Entry => {}
            Guard(pred, _, _) | Return(pred, _) => {
                let level = self.0.get(pred).map(|(_, level)| *level).unwrap_or(0);
                self.0.insert(id, (*pred, level + 1));
            }
            Merge(pred1, pred2, _) => {
                self.0.insert(id, self.lca_and_level(*pred1, *pred2));
            }
        }
    }

    fn lca_and_level(&self, a: SSABlockId, b: SSABlockId) -> (SSABlockId, usize) {
        let idom = |id| self.0.get(&id).cloned().unwrap_or((id, 0));
        let (mut parent1, mut level1) = idom(a);
        let (mut parent2, mut level2) = idom(b);

        // Traverse up the dominator tree until we find a common ancestor. This traversal goes bottom
        // up, so this is the least common ancestor.
        loop {
            if level1 < level2 {
                (parent2, level2) = idom(parent2);
            } else if level1 > level2 {
                (parent1, level1) = idom(parent1);
            } else if parent1 != parent2 {
                assert_ne!(level1, 1);
                assert_ne!(level2, 1);
                (parent1, level1) = idom(parent1);
                (parent2, level2) = idom(parent2);
            } else {
                break (parent1, max(level1, 1));
            }
        }
    }

    pub fn lca(&self, a: SSABlockId, b: SSABlockId) -> SSABlockId {
        self.lca_and_level(a, b).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dom1() {
        use SSABlock::*;
        let mut dom = DomTree::default();
        dom.visit_block(0, &Entry);
        dom.visit_block(1, &Guard(0, 0, true));
        dom.visit_block(2, &Guard(0, 0, true));
        dom.visit_block(3, &Merge(1, 2, HashMap::new()));
        dom.visit_block(4, &Return(3, vec![]));
        assert_eq!(
            dom,
            DomTree(HashMap::from_iter([
                (1, (0, 1)),
                (2, (0, 1)),
                (3, (0, 1)),
                (4, (3, 2)),
            ]))
        );
    }

    #[test]
    fn dom2() {
        use SSABlock::*;
        let mut dom = DomTree::default();
        dom.visit_block(0, &Entry);
        dom.visit_block(1, &Guard(0, 0, true));
        dom.visit_block(2, &Merge(0, 1, HashMap::new()));
        dom.visit_block(1, &Guard(2, 0, true));
        dom.visit_block(2, &Merge(0, 1, HashMap::new()));
        dom.visit_block(3, &Guard(2, 0, true));
        dom.visit_block(4, &Return(3, vec![]));
        assert_eq!(
            dom,
            DomTree(HashMap::from_iter([
                (2, (0, 1)),
                (1, (2, 2)),
                (3, (2, 2)),
                (4, (3, 3)),
            ]))
        );
    }
}
