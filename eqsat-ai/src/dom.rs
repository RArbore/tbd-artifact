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
                self.0
                    .insert(id, self.lca_and_level(*pred1, *pred2, |_| {}, |_| {}));
            }
        }
    }

    fn lca_and_level<F1, F2>(
        &self,
        mut a: SSABlockId,
        mut b: SSABlockId,
        mut f1: F1,
        mut f2: F2,
    ) -> (SSABlockId, usize)
    where
        F1: FnMut(SSABlockId),
        F2: FnMut(SSABlockId),
    {
        let idom = |id| self.0.get(&id).cloned().unwrap_or((id, 0));
        let (mut parent1, mut level1) = idom(a);
        let (mut parent2, mut level2) = idom(b);

        // Traverse up the dominator tree until we find a common ancestor. This traversal goes bottom
        // up, so this is the least common ancestor.
        loop {
            if level1 < level2 {
                f2(b);
                b = parent2;
                (parent2, level2) = idom(parent2);
            } else if level1 > level2 {
                f1(a);
                a = parent1;
                (parent1, level1) = idom(parent1);
            } else if a != b {
                assert_ne!(level1, 0);
                assert_ne!(level2, 0);
                f1(a);
                f2(b);
                a = parent1;
                b = parent2;
                (parent1, level1) = idom(parent1);
                (parent2, level2) = idom(parent2);
            } else {
                assert_eq!(level1, level2);
                break (a, level1 + 1);
            }
        }
    }

    pub fn lca<F1, F2>(&self, a: SSABlockId, b: SSABlockId, f1: F1, f2: F2) -> SSABlockId
    where
        F1: FnMut(SSABlockId),
        F2: FnMut(SSABlockId),
    {
        self.lca_and_level(a, b, f1, f2).0
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::min;

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

        let mut v1 = vec![];
        let mut v2 = vec![];
        let lca = dom.lca_and_level(2, 4, |id| v1.push(id), |id| v2.push(id));
        assert_eq!(lca, (0, 1));
        assert_eq!(v1, vec![2]);
        assert_eq!(v2, vec![4, 3]);
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

        let mut v1 = vec![];
        let mut v2 = vec![];
        let lca = dom.lca_and_level(3, 4, |id| v1.push(id), |id| v2.push(id));
        assert_eq!(lca, (3, 3));
        assert_eq!(v1, vec![]);
        assert_eq!(v2, vec![4]);
    }

    #[test]
    fn dom3() {
        let mut dom = DomTree::default();
        dom.visit_block(0, &SSABlock::Entry);
        for i in 0..10 {
            dom.visit_block(i + 1, &SSABlock::Guard(i, 0, true));
        }

        for i in 0..10 {
            assert_eq!(dom.0[&(i + 1)], (i, i + 1));
            for j in 0..10 {
                let mut v1 = vec![];
                let mut v2 = vec![];
                let lca = dom.lca_and_level(i, j, |id| v1.push(id), |id| v2.push(id));
                let min = min(i, j);
                assert_eq!(lca, (min, min + 1));
                assert_eq!(v1, (min..i).map(|x| i - x + min).collect::<Vec<_>>());
                assert_eq!(v2, (min..j).map(|x| j - x + min).collect::<Vec<_>>());
            }
        }

        for i in 0..10 {
            dom.visit_block(i + 11, &SSABlock::Merge(i, i + 1, HashMap::new()));
        }
        for i in 0..10 {
            assert_eq!(dom.0[&(i + 11)], (i, i + 1));
            for j in 0..10 {
                let mut v1 = vec![];
                let mut v2 = vec![];
                let lca = dom.lca_and_level(i + 11, j, |id| v1.push(id), |id| v2.push(id));
                let min = min(i, j);
                assert_eq!(lca, (min, min + 1));
                let mut correct_v1 = vec![i + 11];
                correct_v1.extend((min..i).map(|x| i - x + min));
                assert_eq!(v1, correct_v1);
                assert_eq!(v2, (min..j).map(|x| j - x + min).collect::<Vec<_>>());
            }
        }
    }
}
