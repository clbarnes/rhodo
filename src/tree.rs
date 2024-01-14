use crate::error::{EdgeBuild, IdAbsent, IdPresent, InvalidId};
use crate::{Node, NodeId};
use std::fmt::Debug;

use crate::iter::{DfsEdges, RootwardIterator, SlabsIterator};
use crate::util::{FastMap, FastSet};

pub struct Tree<D = (), N: NodeId = u64> {
    pub(crate) nodes: FastMap<N, Node<D, N>>,
    root: N,
    branches: FastSet<N>,
    leaves: FastSet<N>,
}

impl<D: Clone, N: NodeId> Clone for Tree<D, N> {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            root: self.root,
            branches: self.branches.clone(),
            leaves: self.leaves.clone(),
        }
    }
}

impl<D: Debug, N: NodeId> Debug for Tree<D, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Tree")
            .field("root", &self.root)
            .field("branches", &self.branches)
            .field("leaves", &self.leaves)
            .field("nodes", &self.nodes)
            .finish()
    }
}

impl<D, N: NodeId> PartialEq for Tree<D, N> {
    fn eq(&self, other: &Self) -> bool {
        self.nodes == other.nodes
            && self.root == other.root
            && self.branches == other.branches
            && self.leaves == other.leaves
    }
}

/// Struct representing a Strahler number calculation for a single branch node.
#[derive(Debug, Clone, Default)]
struct StrahlerCounter {
    children_remaining: usize,
    /// Counts of how many children have a given Strahler number
    child_strahlers: FastMap<usize, usize>,
}

impl StrahlerCounter {
    fn new(n_children: usize) -> Self {
        Self {
            children_remaining: n_children,
            child_strahlers: FastMap::with_capacity(n_children),
        }
    }

    /// Register a child node as having a particular Strahler number.
    ///
    /// If there are no more children to count,
    /// return [Some] containing the branch's Strahler number;
    /// otherwise, return [None].
    fn add(&mut self, child_strahler: usize) -> Option<usize> {
        self.child_strahlers
            .entry(child_strahler)
            .and_modify(|e| *e += 1)
            .or_insert(1);
        self.children_remaining = self.children_remaining.saturating_sub(1);
        if self.children_remaining == 0 {
            Some(self.index())
        } else {
            None
        }
    }

    /// Calculate the Strahler number based on the existing registered children.
    ///
    /// If the highest child Strahler number is held by a single child,
    /// return that.
    /// If it is shared by more than one child, return that plus one.
    fn index(&self) -> usize {
        let (num, count) =
            self.child_strahlers
                .iter()
                .fold((0, 0), |(num, count), (this_num, this_count)| {
                    if this_num > &num {
                        (*this_num, *this_count)
                    } else {
                        (num, count)
                    }
                });

        match count {
            // no children
            0 => 1,
            1 => num,
            _ => num + 1,
        }
    }
}

type Bisected<D, N> = (Option<Tree<D, N>>, Tree<D, N>);

impl<D, N: NodeId> Tree<D, N> {
    /// Create a new tree with a root node.
    pub fn new(root_id: N, root_data: D) -> Self {
        let mut nodes = FastMap::default();
        nodes.insert(root_id, Node::new(root_id, root_data));
        let mut leaves = FastSet::default();
        leaves.insert(root_id);

        Self {
            nodes,
            root: root_id,
            branches: FastSet::default(),
            leaves,
        }
    }

    pub fn leaves(&self) -> &FastSet<N> {
        &self.leaves
    }

    pub fn branches(&self) -> &FastSet<N> {
        &self.branches
    }

    /// Extend tree from tuples of `(parent_id, child_id, child_data)`.
    /// Parents must already exist in the tree before a child is added.
    pub fn add_edges<I: IntoIterator<Item = (N, N, D)>>(
        &mut self,
        edges: I,
    ) -> Result<usize, InvalidId<N>> {
        let mut count: usize = 0;
        for (parent_id, child_id, child_data) in edges.into_iter() {
            self.add_child(parent_id, child_id, child_data)?;
            count += 1;
        }
        Ok(count)
    }

    /// Build a tree from an iterator of edges of `(Option<parent_id>, child_id, child_data)`.
    /// The first item must have `parent_id = None`; all subsequent items must have `Some`.
    /// Parents must be defined before their children.
    pub fn new_from_edges<I: IntoIterator<Item = (Option<N>, N, D)>>(
        edges: I,
    ) -> Result<Self, EdgeBuild<N>> {
        let mut it = edges.into_iter();
        let (pre_root, root, data) = it.next().ok_or(EdgeBuild::NoRoot)?;
        if let Some(pr) = pre_root {
            Err(InvalidId::Absent(IdAbsent::from(pr)))?;
        }
        let mut tree = Self::new(root, data);
        for (parent_id_o, child_id, child_data) in it {
            let Some(parent_id) = parent_id_o else {
                return Err(EdgeBuild::MultipleRoots(vec![root, child_id]));
            };
            tree.add_child(parent_id, child_id, child_data)?;
        }
        Ok(tree)
    }

    /// Get a reference to the ID of the root node.
    pub fn root(&self) -> &N {
        &self.root
    }

    /// Add a node which is a child to an existing node.
    pub fn add_child(
        &mut self,
        parent_id: N,
        child_id: N,
        child_data: D,
    ) -> Result<&Node<D, N>, InvalidId<N>> {
        // todo: error: child exists, parent does not exist
        if self.has_node(&child_id) {
            Err(IdPresent::from(child_id))?;
        }

        let parent = self
            .nodes
            .get_mut(&parent_id)
            .ok_or(IdAbsent::from(parent_id))?;
        parent.children.insert(child_id);

        if parent.children.len() == 2 {
            self.branches.insert(parent_id);
        }

        self.leaves.remove(&parent_id);
        self.leaves.insert(child_id);

        let mut node = Node::new(child_id, child_data);
        node.parent = Some(parent_id);
        Ok(self.nodes.entry(child_id).or_insert(node))
    }

    /// Check whether a node exists.
    pub fn has_node(&self, node_id: &N) -> bool {
        self.nodes.contains_key(node_id)
    }

    /// Check whether an edge exists.
    /// If either node does not exist, returns false.
    pub fn has_edge(&self, parent_id: &N, child_id: &N) -> bool {
        let Ok(child) = self.node(child_id) else {
            return false;
        };
        if let Some(parent) = child.parent() {
            &parent == parent_id
        } else {
            false
        }
    }

    /// Remove an existing non-root node, returning its former state.
    ///
    /// Creates edges from the node's parent to its children.
    pub fn remove(&mut self, id: N) -> Result<Node<D, N>, IdAbsent<N>> {
        let removed = self.remove_unchecked(id)?;
        let parent_id = removed.parent.expect("Removed the root");

        for child_id in removed.children.iter() {
            self.node_mut(child_id)?.parent = Some(parent_id);
        }

        let parent = self.node_mut(&parent_id)?;
        parent.children.remove(&id);
        for child_id in removed.children.iter() {
            parent.children.insert(*child_id);
        }

        match parent.children.len() {
            0 => {
                self.branches.remove(&id);
                self.leaves.insert(id);
            }
            1 => {
                self.branches.remove(&id);
                self.leaves.remove(&id);
            }
            _ => {
                self.leaves.remove(&id);
                self.branches.insert(id);
            }
        };
        Ok(removed)
    }

    /// Removes a non-root node without creating edges from its parent to its children.
    pub(crate) fn remove_unchecked(&mut self, id: N) -> Result<Node<D, N>, IdAbsent<N>> {
        if self.root == id {
            panic!("Cannot remove the root node");
        }
        self.branches.remove(&id);
        self.leaves.remove(&id);
        self.nodes.remove(&id).ok_or(IdAbsent::from(id))
    }

    /// Add a new node in between two nodes which already have an edge between them.
    pub fn interpose(
        &mut self,
        id: N,
        data: D,
        parent_id: N,
        child_id: N,
    ) -> Result<&Node<D, N>, InvalidId<N>> {
        if self.has_node(&id) {
            Err(IdPresent::from(id))?;
        }

        {
            let parent = self.node_mut(&parent_id)?;

            if !parent.remove_child(&child_id) {
                Err(IdAbsent::from(id))?;
            }

            parent.children.insert(id);
        }

        let child = self.node_mut(&child_id)?;
        child.parent = Some(id);

        let mut new = Node::new(id, data);
        new.parent = Some(parent_id);
        new.children.insert(child_id);

        Ok(self.nodes.entry(id).or_insert(new))
    }

    /// Add a node which is a parent to the current root.
    pub fn add_root(&mut self, id: N, data: D) -> Result<&Node<D, N>, InvalidId<N>> {
        if self.has_node(&id) {
            Err(IdPresent::from(id))?;
        }
        let old_root_id = self.root;
        let new = {
            let old_root = self.node_mut(&old_root_id)?;
            old_root.parent = Some(id);

            let mut new = Node::new(id, data);
            new.children.insert(old_root_id);
            new
        };

        self.root = id;
        Ok(self.nodes.entry(id).or_insert(new))
    }

    /// Get a reference to the node struct with the given ID.
    pub fn node(&self, id: &N) -> Result<&Node<D, N>, IdAbsent<N>> {
        self.nodes.get(id).ok_or(IdAbsent::from(*id))
    }

    pub fn nodes(&self) -> &FastMap<N, Node<D, N>> {
        &self.nodes
    }

    /// Get a mutable reference to the node struct with the given ID.
    pub(crate) fn node_mut(&mut self, id: &N) -> Result<&mut Node<D, N>, IdAbsent<N>> {
        self.nodes.get_mut(id).ok_or(IdAbsent::from(*id))
    }

    pub fn data(&self, id: &N) -> Result<&D, IdAbsent<N>> {
        self.node(id).map(|n| n.data())
    }

    pub fn data_mut(&mut self, id: &N) -> Result<&mut D, IdAbsent<N>> {
        self.node_mut(id).map(|n| n.data_mut())
    }

    /// Get an iterator of node IDs from the given ID to the root.
    pub fn ancestors(&self, id: N) -> Result<impl Iterator<Item = N> + '_, IdAbsent<N>> {
        RootwardIterator::new(self, id)
    }

    /// Get an iterator of node IDs from the given ID to its descendants in depth-first pre-order with children addressed in arbitrary order.
    ///
    /// Uses `.dfs_edges()` internally.
    pub fn dfs(&self, id: N) -> Result<impl Iterator<Item = N> + '_, IdAbsent<N>> {
        self.dfs_edges(id).map(|it| it.map(|(_, c, _)| c))
    }

    /// Get an iterator of `(parent, child, &data)`.
    ///
    /// Depth-first pre-order with children addressed in arbitrary order.
    /// `parent` may be `None` in the first item only, if that item's second element is the tree root.
    pub fn dfs_edges(
        &self,
        id: N,
    ) -> Result<impl Iterator<Item = (Option<N>, N, &D)> + '_, IdAbsent<N>> {
        DfsEdges::new(self, id)
    }

    /// Get an iterator of vecs of unbranched nodes.
    ///
    /// The first element's first element is the root; all subsequent elements' first element is a branch.
    /// All elements' last element is a branch or leaf.
    ///
    /// Nodes are visited in the same order as in `my_tree.dfs(my_tree.root)`.
    pub fn slabs(&self, id: &N) -> Result<impl Iterator<Item = Vec<N>> + '_, IdAbsent<N>> {
        SlabsIterator::new(self, *id)
    }

    /// Re-root the tree at the given node.
    pub fn reroot(&mut self, new_root: N) -> Result<&mut Self, IdAbsent<N>> {
        let ids: Vec<_> = self.ancestors(new_root)?.collect();
        match ids.len() {
            0 => return Err(new_root.into()),
            1 => return Ok(self), // already root
            _ => (),
        };
        self.node_mut(ids.first().unwrap())
            .unwrap()
            .switch_parent(None)?;
        for cp in ids.as_slice().windows(2) {
            let old_child_id = cp[0];
            let old_parent_id = cp[1];
            self.node_mut(&old_parent_id)
                .unwrap()
                .switch_parent(Some(old_child_id))?;
        }
        self.root = new_root;
        Ok(self)
    }

    /// Splits the tree into 2 by cutting the edge *above* `new_root`.
    ///
    /// The first element is the part of the tree above the cut
    /// (which may be `None` if the given node was the original root);
    /// the second element is the part of the tree below the cut, rooted at the given node.
    pub fn bisect(mut self, new_root: N) -> Result<Bisected<D, N>, IdAbsent<N>> {
        use crate::node::NodeType::*;
        // break the existing edges by removing parent and child relationships
        let root_mut = self.node_mut(&new_root)?;
        let Some(old_parent_id) = root_mut.parent else {
            return Ok((None, self));
        };
        root_mut.parent = None;
        let old_parent = self.node_mut(&old_parent_id).unwrap();
        old_parent.remove_child(&new_root);
        // also need to update leaves and branches on parent node
        match old_parent.children().len() {
            0 => self.leaves.insert(old_parent_id),
            1 => self.branches.remove(&old_parent_id),
            _ => false, // doesn't matter, discarded
        };

        // could use existing as capacity guide?
        let mut nodes = FastMap::default();
        let mut branches = FastSet::default();
        let mut leaves = FastSet::default();

        let to_transfer: Vec<_> = self.dfs(new_root).unwrap().collect();

        for node_id in to_transfer.into_iter() {
            let node = self.remove_unchecked(node_id).unwrap();
            match node.node_type() {
                Leaf => leaves.insert(node_id),
                Branch(_) => branches.insert(node_id),
                _ => false, // discarded
            };
            nodes.insert(node_id, node);
        }

        Ok((
            Some(self),
            Self {
                nodes,
                root: new_root,
                branches,
                leaves,
            },
        ))
    }

    /// Break up tree into runs of nodes, where each one ends with a leaf,
    /// the last is guaranteed to contain the root and the leaf the longest path from the root,
    /// and all others start with a branch.
    ///
    /// e.g.
    ///
    /// ```text
    /// 1─2─3─4
    ///   └─5
    /// ```
    ///
    /// becomes `[[2, 5], [1, 2, 3, 4]]`.
    pub(crate) fn runs(&self, root: &N) -> Result<Vec<Vec<N>>, IdAbsent<N>> {
        // todo: this is all wrong

        // first contains the root
        let mut slabs: Vec<_> = self.slabs(root)?.collect();
        // slabs sharing a proximal node
        let mut shared_parent: Vec<Vec<N>> = Vec::default();

        let mut out = Vec::with_capacity(self.leaves.len());

        while let Some(mut next_slab) = slabs.pop() {
            if shared_parent.is_empty()
                || next_slab.first().unwrap() == shared_parent.first().unwrap().first().unwrap()
            {
                shared_parent.push(next_slab);
                continue;
            }
            shared_parent.sort_by_key(|v| v.len());
            next_slab.extend(shared_parent.pop().unwrap().into_iter().skip(1));
            out.append(&mut shared_parent);
            shared_parent.push(next_slab);
        }

        shared_parent.sort_by_key(|v| v.len());
        out.extend(shared_parent);

        Ok(out)
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn strahler(&self) -> FastMap<N, usize> {
        let mut branch_strahlers: FastMap<_, _> = self
            .branches
            .iter()
            .map(|n| {
                (
                    *n,
                    StrahlerCounter::new(self.node(n).unwrap().children().len()),
                )
            })
            .collect();

        let mut out = FastMap::with_capacity(self.len());

        for leaf in self.leaves.iter() {
            let mut this_strahler = 1;
            out.insert(*leaf, this_strahler);
            for proximal in self.ancestors(*leaf).unwrap() {
                // if it's a branch...
                if let Some(prox_count) = branch_strahlers.get_mut(&proximal) {
                    // if this is the last child of this branch...
                    if let Some(s) = prox_count.add(this_strahler) {
                        this_strahler = s;
                    } else {
                        break;
                    }
                }
                out.insert(proximal, this_strahler);
            }
        }

        out
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::debug::TreeGen;

    use super::*;

    type Simple = Tree<(), u64>;

    pub fn make_tree<T: NodeId>(runs: Vec<Vec<T>>) -> Tree<(), T> {
        let mut t = Tree::new(*runs.first().unwrap().first().unwrap(), ());
        for run in runs.into_iter() {
            for p_c in run.windows(2) {
                t.add_child(p_c[0], p_c[1], ()).unwrap();
            }
        }
        t
    }

    pub fn rand_tree<D, F: Fn(usize, &mut fastrand::Rng) -> D>(
        rng: &mut fastrand::Rng,
        n_nodes: usize,
        leaf_p: f64,
        branch_p: f64,
        data_fn: F,
    ) -> Tree<D, usize> {
        TreeGen::new(n_nodes, leaf_p, branch_p, data_fn).gen(rng)
    }

    #[test]
    fn can_fuzz_tree() {
        let n = 10_000;
        let leaf_p = 0.1;
        let branch_p = 0.2;
        let mut rng = fastrand::Rng::with_seed(1991);
        for _ in 0..10 {
            let t = rand_tree(&mut rng, n, leaf_p, branch_p, |_, _| ());
            assert_eq!(t.len(), n)
        }
    }

    pub fn format_tree<N: NodeId + Ord, D: Debug>(t: Tree<D, N>) -> String {
        let mut s = String::new();
        t.format_tree(&mut s).unwrap();
        s
    }

    /// ```text
    /// 1─2─3─4
    ///   └─5
    /// ```
    pub fn make_basic() -> Simple {
        make_tree(vec![vec![1, 2, 3, 4], vec![2, 5]])
    }

    #[test]
    fn fmt_tree() {
        let t = make_basic();
        let _s = format_tree(t);
        let mut rng = fastrand::Rng::with_seed(1991);
        let t2 = rand_tree(&mut rng, 10_000, 0.1, 0.2, |_, _| ());
        let _s2 = format_tree(t2);
        // panic!("\n{s2}\n");
    }

    #[test]
    fn construct() {
        let t = make_basic();
        assert_eq!(t.nodes.len(), 5);
        assert_eq!(t.branches, vec![2].into_iter().collect());
        assert_eq!(t.leaves, vec![4, 5].into_iter().collect());
    }

    #[test]
    fn edges() {
        let t = make_basic();
        let edges = t
            .nodes
            .into_iter()
            .fold(Vec::default(), |mut v, (id, node)| {
                for c in node.children() {
                    v.push((id, *c));
                }
                v
            });
        assert_eq!(edges.len(), 4);
        // todo: check valid order
        // edges.sort_by_key(|(p, _)| *p);
        // assert_eq!(edges, vec![(1, 2), (2, 3), (2, 5), (3, 4)]);
    }

    #[test]
    fn dfs() {
        let t = make_basic();
        let nodes: FastSet<_> = t.dfs(t.root).unwrap().collect();
        assert_eq!(nodes.len(), 5);
        // todo: check valid order
        // assert_eq!(nodes, vec![1, 2, 5, 3, 4]);
    }

    #[test]
    fn slabs() {
        let t = make_basic();
        let slabs: Vec<_> = t.slabs(t.root()).unwrap().collect();
        assert_eq!(slabs.len(), 3);
        assert!(slabs.contains(&vec![1, 2]));
        assert!(slabs.contains(&vec![2, 5]));
        assert!(slabs.contains(&vec![2, 3, 4]));

        // assert_eq!(slabs, vec![vec![1, 2], vec![2, 5], vec![2, 3, 4]]);
    }

    #[test]
    fn runs() {
        let t = make_basic();
        let runs = t.runs(t.root()).unwrap();
        assert_eq!(runs, vec![vec![2, 5], vec![1, 2, 3, 4]]);
    }

    #[test]
    fn bisect() {
        let t = make_basic();
        let (prox_opt, dist) = t.bisect(3).unwrap();
        assert_eq!(
            prox_opt.unwrap(),
            Tree::new_from_edges(vec![(None, 1, ()), (Some(1), 2, ()), (Some(2), 5, ()),]).unwrap()
        );
        assert_eq!(
            dist,
            Tree::new_from_edges(vec![(None, 3, ()), (Some(3), 4, ()),]).unwrap()
        );
    }

    #[test]
    fn strahler_simple() {
        let t = make_basic();
        assert_eq!(
            t.strahler(),
            vec![(3, 1), (4, 1), (5, 1), (2, 2), (1, 2),]
                .into_iter()
                .collect()
        )
    }
}
