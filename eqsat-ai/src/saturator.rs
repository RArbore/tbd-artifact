use core::mem::take;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::analysis::{Domain, Interval, KnownBits};
use crate::rw::{Tries, apply_rws};
use crate::ssa::{Analysis, SSA, SSABlock, SSABlockId, SSAId, SSAProgram};
use crate::version::Version;

#[derive(Debug)]
enum VersionState {
    // If the version is mutable, it is a leaf version.
    Mutable(Version<Analysis>),
    // If the version is immutable, it is a parent version of some child version.
    Immutable(Rc<Version<Analysis>>),
}

impl AsRef<Version<Analysis>> for VersionState {
    fn as_ref(&self) -> &Version<Analysis> {
        use VersionState::*;
        match self {
            Mutable(version) => version,
            Immutable(version) => version,
        }
    }
}

#[derive(Debug)]
enum NodeTrieEdit {
    Intern {
        id: SSAId,
        canon_id: SSAId,
    },
    ResetRoot {
        id: SSAId,
    },
    PushUnion {
        newly_non_canon_id: SSAId,
    },
    PopUnion {
        newly_canon_id: SSAId,
        parent: Rc<Version<Analysis>>,
    },
}

#[derive(Debug)]
enum AnalysisTrieEdit {
    AddAnalysis { id: SSAId, analysis: Analysis },
    RemoveAnalysis { id: SSAId },
}

pub struct Saturator {
    // What nodes have either been:
    // 1. Added to the hash-cons...
    // 2. Have had their canonical SSAId changed (due to a union)...
    // ...since the last iteration of rewriting.
    delta: FxHashSet<SSAId>,
    // What nodes have either been:
    // 1. `Saturator::analyze_analysis` called on their ID...
    // 2. Unioned with another node...
    // ...and their analysis value changed since the last iteration of rewriting.
    delta_analysis: FxHashSet<SSAId>,
    // Keep track of which tuples in the trie are inserted with what root SSAId.
    tuples_using_in_root: FxHashMap<SSAId, FxHashSet<SSAId>>,
    // Keep track of the analysis that each SSAId is inserted into the tries with.
    analysis_for_root: FxHashMap<SSAId, Analysis>,
    // Store an empty root version. This is needed so we have a well-defined LCA between old and new
    // versions for the entry block.
    root_version: Rc<Version<Analysis>>,
    // Store the latest version for each SSA block.
    versions: FxHashMap<SSABlockId, VersionState>,
    // Store the "current" version. Moving between versions requires careful maintenance of the delta
    // set, so we use `move_to_version` to explicitly change this member.
    current_version: Option<SSABlockId>,
    // Store the set of SSAIds that were examined in versions that we've since left. At any point in
    // time, if we intern a SSAId that is in this set, we treat it as a new node and add it to the
    // delta set (and remove it from this set), even if it was already in the hash-cons. When moving
    // out of a version with examined SSAIds, those SSAIds need to be added to `previously_examined`,
    // so that they are re-examined if they are re-interned. When moving into a version with examined
    // SSAIds, those SSAIds need to be removed from `previously_examined`, so that they are not re-
    // examined unnecessarily.
    previously_examined: FxHashSet<SSAId>,
    // The SSA program being created.
    pub ssa: SSAProgram,
    // The tries for the "current" version.
    tries: Tries,
    // Queue up edits to the node and analysis tries.
    node_trie_edits: Vec<NodeTrieEdit>,
    analysis_trie_edits: Vec<AnalysisTrieEdit>,
    // Keep track of some statistics and whether we are running "rw" rules.
    pub num_rule_fires: usize,
    max_num_rule_fires: usize,
    enable_rws: bool,
}

impl Saturator {
    pub fn new(max_num_rule_fires: usize, enable_rws: bool) -> Self {
        Self {
            delta: Default::default(),
            delta_analysis: Default::default(),
            tuples_using_in_root: Default::default(),
            analysis_for_root: Default::default(),
            root_version: Default::default(),
            versions: Default::default(),
            current_version: Default::default(),
            previously_examined: Default::default(),
            ssa: Default::default(),
            tries: Default::default(),
            node_trie_edits: Default::default(),
            analysis_trie_edits: Default::default(),
            num_rule_fires: 0,
            max_num_rule_fires,
            enable_rws,
        }
    }

    pub fn find_in_version(&self, id: SSAId, version: SSABlockId) -> SSAId {
        self.versions[&version].as_ref().find(id)
    }

    pub fn find(&self, mut id: SSAId) -> SSAId {
        if let Some(version) = self.current_version {
            id = self.find_in_version(id, version);
        }
        id
    }

    pub fn union(&mut self, x: SSAId, y: SSAId) -> (SSAId, SSAId) {
        assert_eq!(self.ssa.ty(x), self.ssa.ty(y));
        let VersionState::Mutable(version) = self
            .versions
            .get_mut(&self.current_version.unwrap())
            .unwrap()
        else {
            panic!()
        };
        let (canon, non_canon) = version.union(x, y);
        if canon != non_canon {
            self.delta.extend(
                self.tuples_using_in_root
                    .entry(non_canon)
                    .or_default()
                    .iter(),
            );
            self.node_trie_edits.push(NodeTrieEdit::PushUnion {
                newly_non_canon_id: non_canon,
            });
            for set_id in self
                .tuples_using_in_root
                .entry(non_canon)
                .or_default()
                .iter()
            {
                self.node_trie_edits
                    .push(NodeTrieEdit::ResetRoot { id: *set_id });
            }

            let new_analysis = version.analysis(canon);
            if self.analysis_for_root.get(&canon).cloned() != Some(new_analysis) {
                self.delta_analysis.insert(canon);
                self.analysis_trie_edits
                    .push(AnalysisTrieEdit::AddAnalysis {
                        id: canon,
                        analysis: new_analysis,
                    })
            }
            self.analysis_trie_edits
                .push(AnalysisTrieEdit::RemoveAnalysis { id: non_canon });
        }
        (canon, non_canon)
    }

    pub fn version(&self, id: SSABlockId) -> &Version<Analysis> {
        self.versions[&id].as_ref()
    }

    pub fn analysis(&self, id: SSAId) -> Analysis {
        if let Some(version) = self.current_version {
            self.analysis_in_version(id, version)
        } else {
            Analysis::top()
        }
    }

    pub fn analysis_in_version(&self, id: SSAId, version: SSABlockId) -> Analysis {
        self.versions[&version].as_ref().analysis(id)
    }

    pub fn mark_contradiction(&mut self) {
        let VersionState::Mutable(version) = self
            .versions
            .get_mut(&self.current_version.unwrap())
            .unwrap()
        else {
            panic!()
        };
        version.mark_contradiction();
    }

    pub fn is_contradiction_in_version(&self, version: SSABlockId) -> bool {
        self.versions[&version].as_ref().is_contradiction()
    }

    fn is_canonical(&self, ssa: SSA) -> bool {
        self.current_version
            .map(|current_version| self.versions[&current_version].as_ref().is_canonical(ssa))
            .unwrap_or(true)
    }

    fn canonicalize(&self, ssa: SSA) -> SSA {
        self.current_version
            .map(|current_version| self.versions[&current_version].as_ref().canonicalize(ssa))
            .unwrap_or(ssa)
    }

    pub fn intern(&mut self, mut ssa: SSA) -> SSAId {
        let before = self.ssa.num_nodes();
        ssa = self.canonicalize(ssa);
        let id = self.ssa.intern(ssa);
        let canon_id = self.find(id);
        let after = self.ssa.num_nodes();
        if (before != after || self.previously_examined.remove(&canon_id))
            && let VersionState::Mutable(version) = self
                .versions
                .get_mut(&self.current_version.unwrap())
                .unwrap()
        {
            version.examine(canon_id);
            self.delta.insert(canon_id);
        }
        if before != after {
            assert_eq!(id, canon_id);
            self.tuples_using_in_root
                .entry(canon_id)
                .or_default()
                .insert(id);
            self.node_trie_edits
                .push(NodeTrieEdit::Intern { id, canon_id });
            self.analysis_trie_edits
                .push(AnalysisTrieEdit::AddAnalysis {
                    id,
                    analysis: Analysis::top(),
                });
        }
        canon_id
    }

    pub fn analyze_kb(&mut self, id: SSAId, kb: KnownBits) {
        self.analyze(id, (kb, Interval::Top));
    }

    pub fn analyze_int(&mut self, id: SSAId, int: Interval) {
        self.analyze(id, (KnownBits::top(), int));
    }

    pub fn analyze(&mut self, mut id: SSAId, analysis: Analysis) {
        // Other rules that may have executed since we edited the trie may have caused unions.
        id = self.find(id);
        let VersionState::Mutable(version) = self
            .versions
            .get_mut(&self.current_version.unwrap())
            .unwrap()
        else {
            panic!()
        };
        let old_analysis = version.analysis(id);
        let new_analysis = old_analysis.meet(&analysis);
        if old_analysis != new_analysis {
            version.set_analysis(id, new_analysis);
            self.delta_analysis.insert(id);
            self.analysis_trie_edits
                .push(AnalysisTrieEdit::AddAnalysis {
                    id,
                    analysis: new_analysis,
                });
        }
    }

    pub fn create_version(&mut self, block: SSABlockId) {
        use SSABlock::*;
        use VersionState::*;
        let pred_version_rc = match self.ssa.get_block(block) {
            Entry => None,
            Identity(pred) | Guard(pred, _, _) | Return(pred, _) => {
                let state = self.versions.get_mut(pred).unwrap();
                let rc = match state {
                    Mutable(version) => {
                        // Why isn't there a core::mem primitive for this?
                        let rc = Rc::new(take(version));
                        *state = Immutable(Rc::clone(&rc));
                        rc
                    }
                    Immutable(rc) => Rc::clone(rc),
                };
                Some(rc)
            }
            Merge(pred1, pred2, _) => {
                let pred1 = self.versions[&pred1].as_ref();
                let pred2 = self.versions[&pred2].as_ref();
                // This looks weird, but we do want to make sure that we get an Rc in this situation.
                Some(Version::lca(pred1, pred2, |_| {}, |_| {}).unwrap())
            }
        };

        let version = pred_version_rc
            .map(|rc| Version::child(rc))
            .unwrap_or_else(|| Version::child(Rc::clone(&self.root_version)));
        self.traverse_to_version(&version);
        self.versions.insert(block, VersionState::Mutable(version));
        self.current_version = Some(block);
    }

    pub fn traverse_to_version(&mut self, version: &Version<Analysis>) {
        assert!(self.delta.is_empty());
        assert!(self.delta_analysis.is_empty());
        self.apply_edits();
        let last_version = self
            .current_version
            .map(|last_block| self.versions[&last_block].as_ref())
            .unwrap_or(&self.root_version);

        // Traverse up and down the version hierarchy from the last version to the current version.
        let mut up_versions = vec![];
        let mut down_versions = vec![];
        Version::lca(
            last_version,
            version,
            |up_version| up_versions.push(up_version),
            |down_version| down_versions.push(down_version),
        );
        down_versions.reverse();

        for version in up_versions {
            // When popping a version, any examined nodes may need to be re-examined.
            for id in version.examined() {
                self.previously_examined.insert(id);
            }

            // And any unions that held in the popped version but not its parent induce trie edits.
            let parent = version.parent().unwrap();
            for id in version.non_canon_ids_at_level() {
                assert_eq!(id, version.find_in_parent(id));
                let old_canon_id = version.find(id);
                assert_ne!(old_canon_id, id);
                Self::apply_node_edit(
                    NodeTrieEdit::PopUnion {
                        newly_canon_id: id,
                        parent: Rc::clone(parent),
                    },
                    &version,
                    &self.ssa,
                    &mut self.tries,
                    &mut self.tuples_using_in_root,
                );
                for set_id in parent.set(id, None) {
                    self.node_trie_edits
                        .push(NodeTrieEdit::ResetRoot { id: set_id });
                }

                let analysis = parent.analysis(id);
                Self::apply_analysis_edit(
                    AnalysisTrieEdit::AddAnalysis { id, analysis },
                    &mut self.tries,
                    &mut self.analysis_for_root,
                );
            }

            // And any nodes with version-specific analysis values induce trie edits.
            for id in version.analyzed_ids_at_level() {
                assert_eq!(id, version.find(id));
                let analysis = parent.analysis(id);
                Self::apply_analysis_edit(
                    AnalysisTrieEdit::AddAnalysis { id, analysis },
                    &mut self.tries,
                    &mut self.analysis_for_root,
                );
            }
        }

        for version in down_versions {
            // When pushing a version, any already examined nodes don't need to be re-examined.
            for id in version.examined() {
                self.previously_examined.remove(&id);
            }

            // And any unions that hold in the pushed version but not its parent induce trie edits.
            let parent = version.parent().unwrap();
            for id in version.non_canon_ids_at_level() {
                assert_eq!(id, version.find_in_parent(id));
                let new_canon_id = version.find(id);
                assert_ne!(new_canon_id, id);
                Self::apply_node_edit(
                    NodeTrieEdit::PushUnion {
                        newly_non_canon_id: id,
                    },
                    &version,
                    &self.ssa,
                    &mut self.tries,
                    &mut self.tuples_using_in_root,
                );
                for set_id in parent.set(id, None) {
                    self.node_trie_edits
                        .push(NodeTrieEdit::ResetRoot { id: set_id });
                }

                Self::apply_analysis_edit(
                    AnalysisTrieEdit::RemoveAnalysis { id },
                    &mut self.tries,
                    &mut self.analysis_for_root,
                );
            }

            // And any nodes with version-specific analysis values induce trie edits.
            for id in version.analyzed_ids_at_level() {
                assert_eq!(id, version.find(id));
                let analysis = version.analysis(id);
                Self::apply_analysis_edit(
                    AnalysisTrieEdit::AddAnalysis { id, analysis },
                    &mut self.tries,
                    &mut self.analysis_for_root,
                );
            }
        }
    }

    pub fn move_to_version(&mut self, block: SSABlockId) {
        if self.current_version == Some(block) {
            return;
        }
        let version = self.versions.remove(&block).unwrap();
        self.traverse_to_version(version.as_ref());
        self.versions.insert(block, version);
        self.current_version = Some(block);
    }

    fn apply_node_edit(
        edit: NodeTrieEdit,
        current_version: &Version<Analysis>,
        ssa: &SSAProgram,
        tries: &mut Tries,
        tuples_using_in_root: &mut FxHashMap<SSAId, FxHashSet<SSAId>>,
    ) {
        use NodeTrieEdit::*;
        match edit {
            Intern { id, canon_id } => {
                tries.insert_tuple(canon_id, ssa.get(id), id, false);
                tuples_using_in_root.entry(canon_id).or_default().insert(id);
            }
            ResetRoot { id: non_canon_id } => {
                let node = ssa.get(non_canon_id);
                let canon_id = current_version.find(non_canon_id);
                if let Some(inserted_id) = tries.inserted_as(non_canon_id)
                    && inserted_id != canon_id
                {
                    tries.remove_tuple(inserted_id, node, non_canon_id);
                    tuples_using_in_root
                        .entry(inserted_id)
                        .or_default()
                        .remove(&non_canon_id);
                    tries.insert_tuple(canon_id, node, non_canon_id, false);
                    tuples_using_in_root
                        .entry(canon_id)
                        .or_default()
                        .insert(non_canon_id);
                }
            }
            PushUnion { newly_non_canon_id } => {
                for user in ssa.users(newly_non_canon_id).cloned() {
                    if let Some(inserted_id) = tries.inserted_as(user) {
                        tries.remove_tuple(inserted_id, ssa.get(user), user);
                        tuples_using_in_root
                            .entry(inserted_id)
                            .or_default()
                            .remove(&user);
                    }
                }
            }
            PopUnion {
                newly_canon_id,
                parent,
            } => {
                for user in ssa.users(newly_canon_id).cloned() {
                    let user_node = ssa.get(user);
                    if parent.is_canonical(user_node) {
                        let user_canon = parent.find(user);
                        if let Some(inserted_id) = tries.inserted_as(user) {
                            assert_eq!(inserted_id, user_canon);
                        } else {
                            tries.insert_tuple(user_canon, user_node, user, false);
                            tuples_using_in_root
                                .entry(user_canon)
                                .or_default()
                                .insert(user);
                        }
                    }
                }
            }
        }
    }

    fn apply_analysis_edit(
        edit: AnalysisTrieEdit,
        tries: &mut Tries,
        analysis_for_root: &mut FxHashMap<SSAId, Analysis>,
    ) {
        use AnalysisTrieEdit::*;
        match edit {
            AddAnalysis { id, analysis } => {
                if let Some(analysis) = tries.inserted_analysis(id) {
                    tries.remove_analysis(id, analysis);
                    assert_eq!(analysis_for_root.remove(&id), Some(analysis));
                }
                tries.insert_analysis(id, analysis, false);
                assert_eq!(analysis_for_root.insert(id, analysis), None);
            }
            RemoveAnalysis { id } => {
                if let Some(analysis) = tries.inserted_analysis(id) {
                    tries.remove_analysis(id, analysis);
                    assert_eq!(analysis_for_root.remove(&id), Some(analysis));
                }
            }
        }
    }

    fn apply_edits(&mut self) {
        let current_version = self
            .current_version
            .map(|current_block| self.versions[&current_block].as_ref())
            .unwrap_or(&self.root_version);
        for edit in take(&mut self.node_trie_edits) {
            Self::apply_node_edit(
                edit,
                current_version,
                &self.ssa,
                &mut self.tries,
                &mut self.tuples_using_in_root,
            );
        }
        for edit in take(&mut self.analysis_trie_edits) {
            Self::apply_analysis_edit(edit, &mut self.tries, &mut self.analysis_for_root);
        }
    }

    pub fn saturate(&mut self) {
        if let VersionState::Immutable(_) = self.versions[&self.current_version.unwrap()] {
            assert!(self.delta.is_empty());
            assert!(self.delta_analysis.is_empty());
            return;
        };
        let threshold = self.num_rule_fires + self.max_num_rule_fires;
        while self.num_rule_fires < threshold {
            if (self.delta.is_empty() && self.delta_analysis.is_empty())
                || self.is_contradiction_in_version(self.current_version.unwrap())
            {
                break;
            }
            self.apply_edits();

            // Prepare worklist for rebuilding. The worklist should always contain only nodes that
            // use non-canonical SSA
            let mut worklist = VecDeque::new();
            for id in &self.delta {
                // The only nodes in `delta` that should fail this check are new nodes.
                if *id != self.find(*id) {
                    for user in self.ssa.users(*id) {
                        worklist.push_back(*user);
                    }
                }
            }

            // Perform rebuilding.
            while let Some(id) = worklist.pop_front() {
                let old_ssa = self.ssa.get(id);
                let new_ssa = self.canonicalize(old_ssa);
                if old_ssa != new_ssa {
                    let new_id = self.intern(new_ssa);
                    let (canon, non_canon) = self.union(id, new_id);
                    if canon != non_canon {
                        // All users of the newly non-canonical node need to be canonicalized.
                        for user in self.ssa.users(non_canon) {
                            worklist.push_back(*user);
                        }
                    }
                }
            }

            self.apply_edits();
            let mut tries = take(&mut self.tries);
            // Each iteration, construct the delta tries from scratch.
            for id in &self.delta {
                let node = self.ssa.get(*id);
                if self.is_canonical(node) {
                    tries.insert_tuple(self.find(*id), node, *id, true);
                }
            }
            for id in &self.delta_analysis {
                if *id == self.find(*id) {
                    tries.insert_analysis(*id, self.analysis(*id), true);
                }
            }
            self.delta.clear();
            self.delta_analysis.clear();

            apply_rws::<false>(self, &tries, self.enable_rws, threshold);
            tries.clear_delta();
            self.tries = tries;
        }
        self.delta.clear();
        self.delta_analysis.clear();
        self.apply_edits();
    }

    pub fn check_trie_consistency(&self) {
        assert!(self.node_trie_edits.is_empty());
        assert!(self.analysis_trie_edits.is_empty());
        let mut correct = Tries::default();
        let mut tuples_using_in_root: FxHashMap<SSAId, FxHashSet<SSAId>> = FxHashMap::default();
        let mut analysis_for_root: FxHashMap<SSAId, Analysis> = FxHashMap::default();
        for id in 0..self.ssa.num_nodes() {
            let node = self.ssa.get(id);
            let canon_id = self.find(id);
            if self.is_canonical(node) {
                correct.insert_tuple(canon_id, node, id, false);
                tuples_using_in_root.entry(canon_id).or_default().insert(id);
            }
            if id == canon_id {
                let analysis = self.analysis(id);
                correct.insert_analysis(id, analysis, false);
                analysis_for_root.insert(id, analysis);
            }
        }
        assert_eq!(
            tuples_using_in_root.into_iter().collect::<BTreeMap<_, _>>(),
            self.tuples_using_in_root
                .iter()
                .filter(|(_, tuples)| !tuples.is_empty())
                .map(|(root, tuples)| (*root, tuples.clone()))
                .collect()
        );
        assert_eq!(analysis_for_root, self.analysis_for_root);
        assert_eq!(correct, self.tries);
    }
}
