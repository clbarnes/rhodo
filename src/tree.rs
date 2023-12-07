use crate::error::{EdgeBuild, IdAbsent, IdPresent, InvalidId};
use crate::{Node, NodeId};
use std::collections::VecDeque;
use std::{collections::HashMap, fmt::Debug};

// only used internally
use ahash::{AHashMap, AHashSet};

use crate::iter::{DfsEdges, RootwardIterator, RootwardSlabIterator, SlabsIterator};

pub struct Tree<D = (), N: NodeId = u64> {
    nodes: AHashMap<N, Node<D, N>>,
    root: N,
    branches: AHashSet<N>,
    leaves: AHashSet<N>,
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

type Bisected<D, N> = (Option<Tree<D, N>>, Tree<D, N>);

impl<D, N: NodeId> Tree<D, N> {
    /// Create a new tree with a root node.
    pub fn new(root_id: N, root_data: D) -> Self {
        let mut nodes = AHashMap::default();
        nodes.insert(root_id, Node::new(root_id, root_data));
        let mut leaves = AHashSet::default();
        leaves.insert(root_id);

        Self {
            nodes,
            root: root_id,
            branches: AHashSet::default(),
            leaves,
        }
    }

    pub fn is_branch(&self, id: &N) -> Result<bool, IdAbsent<N>> {
        self.node(id).map(|n| n.is_branch())
    }

    pub fn is_leaf(&self, id: &N) -> Result<bool, IdAbsent<N>> {
        self.node(id).map(|n| n.is_leaf())
    }

    pub fn is_root(&self, id: &N) -> Result<bool, IdAbsent<N>> {
        self.node(id).map(|n| n.is_root())
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
        if self.contains(&child_id) {
            Err(IdPresent::from(child_id))?;
        }

        let parent = self
            .nodes
            .get_mut(&parent_id)
            .ok_or(IdAbsent::from(parent_id))?;
        parent.children.push(child_id);

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
    pub fn contains(&self, node_id: &N) -> bool {
        self.nodes.contains_key(node_id)
    }

    /// Check whether an edge exists.
    /// If either node does not exist, returns false.
    pub fn contains_edge(&self, parent_id: &N, child_id: &N) -> bool {
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
    pub fn remove(&mut self, id: N) -> Result<Node<D, N>, IdAbsent<N>> {
        if self.root == id {
            panic!("Cannot remove the root node");
        }
        let removed = self.nodes.remove(&id).ok_or(IdAbsent::from(id))?;
        let parent_id = removed.parent.expect("Removed the root");

        for child_id in removed.children.iter() {
            self.node_mut(child_id)?.parent = Some(parent_id);
        }
        let parent = self.node_mut(&parent_id)?;
        for child_id in removed.children.iter() {
            parent.children.push(*child_id);
        }
        Ok(removed)
    }

    /// Add a new node in between two nodes which already have an edge between them.
    pub fn interpose(
        &mut self,
        id: N,
        data: D,
        parent_id: N,
        child_id: N,
    ) -> Result<&Node<D, N>, InvalidId<N>> {
        if self.contains(&id) {
            Err(IdPresent::from(id))?;
        }

        {
            let parent = self.node_mut(&parent_id)?;

            if !parent.remove_child(&child_id) {
                Err(IdAbsent::from(id))?;
            }

            parent.children.push(id);
        }

        let child = self.node_mut(&child_id)?;
        child.parent = Some(id);

        let mut new = Node::new(id, data);
        new.parent = Some(parent_id);
        new.children.push(child_id);

        Ok(self.nodes.entry(id).or_insert(new))
    }

    /// Add a node which is a parent to the current root.
    pub fn add_root(&mut self, id: N, data: D) -> Result<&Node<D, N>, InvalidId<N>> {
        if self.contains(&id) {
            Err(IdPresent::from(id))?;
        }
        let old_root_id = self.root;
        let new = {
            let old_root = self.node_mut(&old_root_id)?;
            old_root.parent = Some(id);

            let mut new = Node::new(id, data);
            new.children.push(old_root.id());
            new
        };

        self.root = id;
        Ok(self.nodes.entry(id).or_insert(new))
    }

    /// Get a reference to the node struct with the given ID.
    pub fn node(&self, id: &N) -> Result<&Node<D, N>, IdAbsent<N>> {
        self.nodes.get(id).ok_or(IdAbsent::from(*id))
    }

    /// Get a mutable reference to the node struct with the given ID.
    pub fn node_mut(&mut self, id: &N) -> Result<&mut Node<D, N>, IdAbsent<N>> {
        self.nodes.get_mut(id).ok_or(IdAbsent::from(*id))
    }

    /// Get an iterator of node IDs from the given ID to the root.
    pub fn ancestors(&self, id: N) -> Result<impl Iterator<Item = N> + '_, IdAbsent<N>> {
        RootwardIterator::new(self, id)
    }

    /// Get an iterator of node IDs from the given ID to its descendants in depth-first pre-order with children addressed in reverse insertion order.
    ///
    /// Uses `.dfs_edges()` internally.
    pub fn dfs(&self, id: N) -> Result<impl Iterator<Item = N> + '_, IdAbsent<N>> {
        self.dfs_edges(id).map(|it| it.map(|(_, c, _)| c))
    }

    /// Get an iterator of `(parent, child, &data)`.
    ///
    /// Depth-first pre-order with children addressed in reverse insertion order.
    /// `parent` may be `None` in the first item only, if that item's second element is the tree root.
    pub fn dfs_edges(
        &self,
        id: N,
    ) -> Result<impl Iterator<Item = (Option<N>, N, &D)> + '_, IdAbsent<N>> {
        DfsEdges::new_from(self, id)
    }

    /// Get an iterator of vecs of unbranched nodes.
    ///
    /// The first element's first element is the root; all subsequent elements' first element is a branch.
    /// All elements' last element is a branch or leaf.
    ///
    /// Nodes are visited in the same order as in `my_tree.dfs(my_tree.root)`.
    pub fn slabs(&self, id: &N) -> Result<impl Iterator<Item = Vec<N>> + '_, IdAbsent<N>> {
        SlabsIterator::new_from_root(self, *id)
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
        // break the existing edges by removing parent and child relationships
        let root_mut = self.node_mut(&new_root)?;
        let Some(old_parent_id) = root_mut.parent else {
            return Ok((None, self));
        };
        root_mut.parent = None;
        let parent_mut = self.node_mut(&old_parent_id).unwrap();
        parent_mut.remove_child(&new_root);
        // also need to update leaves and branches on parent node
        match parent_mut.children().len() {
            0 => self.leaves.insert(old_parent_id),
            1 => self.branches.remove(&old_parent_id),
            _ => false, // doesn't matter, discarded
        };

        // could use existing as capacity guide?
        let mut nodes = AHashMap::default();
        let mut branches = AHashSet::default();
        let mut leaves = AHashSet::default();

        let to_transfer: Vec<_> = self.dfs(new_root).unwrap().collect();

        for node_id in to_transfer.into_iter() {
            let node = self.nodes.remove(&node_id).unwrap();
            if self.branches.remove(&node_id) {
                branches.insert(node_id);
            } else if self.leaves.remove(&node_id) {
                leaves.insert(node_id);
            }
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
    /// the last is guaranteed to contain the root and the leaf furthest from the root,
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
    pub fn runs(&self, root: &N) -> Result<Vec<Vec<N>>, IdAbsent<N>> {
        let mut slabs: Vec<_> = self.slabs(root)?.collect();
        let mut shared_parent: Vec<Vec<N>> = Vec::default();

        let mut out = Vec::default();

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

    pub fn strahler(&self) -> HashMap<N, usize> {
        let mut out = HashMap::with_capacity(self.len());
        let mut to_visit = VecDeque::default();
        for lf in self.leaves.iter() {
            out.insert(*lf, 1);
            to_visit.push_back(*lf);
        }

        let mut visited_branches = AHashSet::with_capacity(self.branches.len() + 1);

        while let Some(distal) = to_visit.pop_front() {
            let this_strahler = *out.get(&distal).unwrap();
            let mut it = RootwardSlabIterator::new(self, &distal).unwrap();
            it.next().unwrap();

            if let Some(last_id) = it
                .map(|n| {
                    out.entry(n)
                        .and_modify(|s| {
                            if s == &this_strahler {
                                *s += 1
                            }
                        })
                        .or_insert(this_strahler);
                    n
                })
                .last()
            {
                if visited_branches.insert(last_id) {
                    to_visit.push_back(last_id);
                }
            }
        }

        out
    }
}

#[cfg(test)]
pub(crate) mod tests {
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

    /// ```text
    /// 1─2─3─4
    ///   └─5
    /// ```
    pub fn make_basic() -> Simple {
        make_tree(vec![vec![1, 2, 3, 4], vec![2, 5]])
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
        let mut edges = t
            .nodes
            .into_iter()
            .fold(Vec::default(), |mut v, (id, node)| {
                for c in node.children() {
                    v.push((id, *c));
                }
                v
            });
        edges.sort_by_key(|(p, _)| *p);
        assert_eq!(edges, vec![(1, 2), (2, 3), (2, 5), (3, 4)]);
    }

    #[test]
    fn dfs() {
        let t = make_basic();
        let nodes: Vec<_> = t.dfs(t.root).unwrap().collect();
        assert_eq!(nodes, vec![1, 2, 5, 3, 4]);
    }

    #[test]
    fn slabs() {
        let t = make_basic();
        let slabs: Vec<_> = t.slabs(t.root()).unwrap().collect();
        assert_eq!(slabs, vec![vec![1, 2], vec![2, 5], vec![2, 3, 4]]);
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
