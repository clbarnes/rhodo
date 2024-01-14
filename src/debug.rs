use crate::{FastMap, NodeId, Tree};
use ascii_tree::{write_tree, Tree as ATree};
pub use fastrand;
use std::{collections::VecDeque, fmt::Debug};

impl<N: NodeId + Ord, D: Debug> Tree<D, N> {
    /// Print an ASCII representation of the tree.
    ///
    /// Mainly for debugging purposes.
    /// An `&mut` to an empty `String` makes for a good `w`.
    pub fn format_tree<W: core::fmt::Write>(&self, w: &mut W) -> core::fmt::Result {
        use crate::node::NodeType;
        let mut nodes: Vec<_> = self.dfs(*self.root()).unwrap().collect();
        let mut anodes = FastMap::with_capacity(self.leaves().len());
        while let Some(nid) = nodes.pop() {
            let node = self.node(&nid).unwrap();
            let name = format!("{:?}: {:?}", nid, node.data());
            let anode = match node.node_type() {
                NodeType::Leaf => ATree::Leaf(vec![name]),
                NodeType::Slab(c_id) => ATree::Node(name, vec![anodes.remove(&c_id).unwrap()]),
                NodeType::Branch(c_ids) => {
                    let mut v: Vec<_> = c_ids.iter().collect();
                    v.sort();
                    ATree::Node(
                        name,
                        v.into_iter().map(|id| anodes.remove(id).unwrap()).collect(),
                    )
                }
            };
            anodes.insert(nid, anode);
        }
        assert_eq!(anodes.len(), 1);
        let anode = anodes.into_iter().map(|(_, v)| v).next().unwrap();
        write_tree(w, &anode)
    }
}

/// Utility for creating random trees.
pub struct TreeGen<D, F: Fn(usize, &mut fastrand::Rng) -> D> {
    pub n_nodes: usize,
    /// The chance of a node being a leaf.
    /// Ignored if this would end the tree prematurely.
    pub leaf: f64,
    /// The chance of an extra child being added to a non-leaf node (repeats until failure).
    /// Ignored if this would overrun the desired number of nodes.
    pub branch_p: f64,
    /// A function to calculate the node's data based on its ID and a random number generator.
    pub data_fn: F,
}

impl<D, F: Fn(usize, &mut fastrand::Rng) -> D> TreeGen<D, F> {
    pub fn new(n_nodes: usize, leaf_p: f64, branch_p: f64, data_fn: F) -> Self {
        Self {
            n_nodes,
            leaf: leaf_p,
            branch_p,
            data_fn,
        }
    }

    pub fn gen(&self, rng: &mut fastrand::Rng) -> Tree<D, usize> {
        let mut parents = VecDeque::default();
        let mut t = Tree::new(0, (self.data_fn)(0, rng));
        parents.push_back(0);
        let mut planned = self.n_nodes - 1;
        for child_id in 1..self.n_nodes {
            let parent_id = parents.pop_front().unwrap();
            t.add_child(parent_id, child_id, (self.data_fn)(child_id, rng))
                .unwrap();
            if planned == 0 || (!parents.is_empty() && rng.f64() < self.leaf) {
                continue;
            }
            parents.push_back(child_id);
            planned -= 1;
            while planned > 0 && rng.f64() < self.branch_p {
                parents.push_back(child_id);
                planned -= 1;
            }
        }
        t
    }
}
