use crate::{
    algos::StrahlerCounter,
    error::{IdAbsent, IdPresent, InvalidId},
    hash::{FastMap, FastSet, HashMapExt},
    spatial::Precision,
    Location, Node, NodeId, Tree,
};

/// Struct for splitting, pruning, and joining trees.
pub struct TreeSurgeon<D, N: NodeId>(Tree<D, N>);

impl<D, N: NodeId> From<Tree<D, N>> for TreeSurgeon<D, N> {
    fn from(value: Tree<D, N>) -> Self {
        Self(value)
    }
}

impl<D, N: NodeId> From<TreeSurgeon<D, N>> for Tree<D, N> {
    fn from(value: TreeSurgeon<D, N>) -> Self {
        value.0
    }
}

impl<D, N: NodeId> TreeSurgeon<D, N> {
    pub fn into_inner(self) -> Tree<D, N> {
        self.into()
    }

    /// Graft another tree onto this one as a child of the given node.
    pub fn graft(&mut self, parent: N, other: Tree<D, N>) -> Result<(), InvalidId<N>> {
        let other_root = other.root;
        if !self.0.node_mut(&parent)?.children.insert(other.root) {
            Err(IdPresent::from(other.root))?;
        }
        if !self.0.leaves.remove(&parent) {
            self.0.branches.insert(parent);
        }
        self.0.leaves.extend(other.leaves);
        self.0.branches.extend(other.branches);
        for (id, n) in other.nodes {
            if self.0.nodes.insert(id, n).is_some() {
                Err(IdPresent::from(id))?;
            }
        }
        self.0.node_mut(&other_root)?.parent = Some(parent);
        Ok(())
    }

    /// Make the given node the new root; remove all nodes above it and in sibling branches.
    ///
    /// Returns removed nodes.
    pub fn prune_above(&mut self, new_root: N) -> Result<Vec<Node<D, N>>, IdAbsent<N>> {
        if &new_root == self.0.root() {
            return Ok(vec![]);
        }

        let mut ancs = vec![];
        let mut prev = new_root;
        let mut to_prune_below = vec![];

        // traverse to the root, keeping track of all of the visited nodes' siblings
        for anc in self.0.ancestors(new_root)?.skip(1) {
            ancs.push(anc);
            let n = self.0.nodes.get(&anc).unwrap();
            if let crate::node::NodeType::Branch(cs) = n.node_type() {
                for c in cs.iter() {
                    if c != &prev {
                        to_prune_below.push(*c);
                    }
                }
            };
            prev = anc;
        }

        let mut out = Vec::default();

        // prune below each sibling, and then remove the sibling itself
        for c in to_prune_below {
            out.extend(self.prune_below_including(c)?);
        }

        // remove the ancestors
        for anc in ancs {
            out.push(self.0.remove_unchecked(anc)?);
        }
        self.0.reroot(new_root)?;
        Ok(out)
    }

    fn prune_below_including(
        &mut self,
        proximal_removed: N,
    ) -> Result<Vec<Node<D, N>>, IdAbsent<N>> {
        let mut out = self.prune_below(proximal_removed)?;
        out.push(self.0.remove(proximal_removed)?);
        Ok(out)
    }

    /// Removes the slab containing the given node, and everything below it.
    ///
    /// Returns removed nodes.
    pub fn prune_containing(&mut self, node: N) -> Result<Vec<Node<D, N>>, IdAbsent<N>> {
        let mut it = self.0.ancestors(node)?;
        let mut child = it.next().unwrap();

        for parent in it {
            let n = self.0.node(&parent).unwrap();
            if let crate::node::NodeType::Branch(_) = n.node_type() {
                break;
            };
            child = parent;
        }
        self.prune_below(child)
    }

    /// Remove all nodes below the given node.
    ///
    /// Returns removed nodes.
    pub fn prune_below(&mut self, new_leaf: N) -> Result<Vec<Node<D, N>>, IdAbsent<N>> {
        let v = self.0.dfs(new_leaf)?.skip(1).collect::<Vec<_>>();
        let mut out = Vec::with_capacity(v.len() + 1);
        for n in v {
            out.push(self.0.remove_unchecked(n)?);
        }
        self.0.node_mut(&new_leaf)?.children.clear();
        self.0.leaves.insert(new_leaf);
        Ok(out)
    }

    /// Splits the tree into 2 by cutting the edge *above* `new_root`.
    ///
    /// Returns the upper portion, which may be `None` (if `new_root` was the original root).
    pub fn split_above(&mut self, new_root: N) -> Result<Option<Tree<D, N>>, IdAbsent<N>> {
        use crate::node::NodeType::*;

        // break the existing edges by removing parent and child relationships
        let root_mut = self.0.node_mut(&new_root)?;
        let Some(old_parent_id) = root_mut.parent else {
            return Ok(None);
        };
        root_mut.parent = None;
        let old_parent = self.0.node_mut(&old_parent_id).unwrap();
        old_parent.remove_child(&new_root);
        // also need to update leaves and branches on parent node
        match old_parent.children().len() {
            0 => self.0.leaves.insert(old_parent_id),
            1 => self.0.branches.remove(&old_parent_id),
            _ => false, // doesn't matter, discarded
        };

        // could use existing as capacity guide?
        let mut nodes = FastMap::default();
        let mut branches = FastSet::default();
        let mut leaves = FastSet::default();

        let to_transfer: Vec<_> = self.0.dfs(new_root).unwrap().collect();

        for node_id in to_transfer.into_iter() {
            let node = self.0.remove_unchecked(node_id).unwrap();
            match node.node_type() {
                Leaf => leaves.insert(node_id),
                Branch(_) => branches.insert(node_id),
                _ => false, // discarded
            };
            nodes.insert(node_id, node);
        }

        let lower = Tree {
            nodes,
            root: new_root,
            branches,
            leaves,
        };
        Ok(Some(std::mem::replace(&mut self.0, lower)))
    }

    /// Remove all nodes further than the given path length from the root,
    /// returning removed nodes.
    pub fn prune_beyond_steps(&mut self, steps: usize) -> Vec<Node<D, N>> {
        let mut to_visit = vec![(self.0.node(&self.0.root).unwrap(), 0)];
        let mut to_prune = vec![];
        while let Some((parent, from_root)) = to_visit.pop() {
            for c in parent.children().iter() {
                let child = self.0.node(c).unwrap();
                let child_dist = from_root + 1;
                if child_dist <= steps {
                    to_visit.push((child, child_dist));
                } else {
                    to_prune.push(child.id());
                }
            }
        }
        to_prune
            .into_iter()
            .flat_map(|p| self.prune_below_including(p).unwrap())
            .collect()
    }

    /// Remove all nodes more than the given number of branches from the root,
    /// returning removed nodes.
    pub fn prune_beyond_branches(&mut self, n_branches: usize) -> Vec<Node<D, N>> {
        let mut to_visit = vec![(self.0.node(&self.0.root).unwrap(), 0)];
        let mut to_prune = vec![];
        while let Some((parent, from_root)) = to_visit.pop() {
            match parent.node_type() {
                crate::node::NodeType::Branch(cs) => {
                    if from_root >= n_branches {
                        to_prune.push(parent.id());
                    } else {
                        to_visit
                            .extend(cs.iter().map(|c| (self.0.node(c).unwrap(), from_root + 1)));
                    }
                }
                crate::node::NodeType::Slab(c) => {
                    to_visit.push((self.0.node(&c).unwrap(), from_root))
                }
                _ => (),
            }
        }
        to_prune
            .into_iter()
            .flat_map(|p| self.prune_below(p).unwrap())
            .collect()
    }

    /// Remove nodes whose strahler index is below the given threshold, returning removed nodes.
    pub fn prune_below_strahler(&mut self, threshold: usize) -> Vec<Node<D, N>> {
        let mut branch_strahlers: FastMap<_, _> = self
            .0
            .branches()
            .iter()
            .map(|n| {
                (
                    *n,
                    StrahlerCounter::new(self.0.node(n).unwrap().children().len()),
                )
            })
            .collect();

        let mut to_prune = vec![];

        let mut child_strahlers = FastMap::with_capacity(self.0.len());

        for leaf in self.0.leaves().iter() {
            let mut this_strahler = 1;
            let mut distal = *leaf;
            for proximal in self.0.ancestors(*leaf).unwrap() {
                // if it's a branch...
                if let Some(prox_count) = branch_strahlers.get_mut(&proximal) {
                    child_strahlers.insert(distal, this_strahler);
                    // if this is the last child of this branch...
                    if let Some(s) = prox_count.add(this_strahler) {
                        match s.cmp(&threshold) {
                            std::cmp::Ordering::Equal => {
                                for c_id in self.0.node(&proximal).unwrap().children().iter() {
                                    if child_strahlers.get(c_id).unwrap() < &threshold {
                                        to_prune.push(*c_id);
                                    }
                                }
                            }
                            std::cmp::Ordering::Greater => {
                                break;
                            }
                            _ => (),
                        };
                        this_strahler = s;
                    } else {
                        break;
                    }
                }
                distal = proximal;
            }
        }

        to_prune
            .into_iter()
            .flat_map(|c| self.prune_below_including(c).unwrap_or_default())
            .collect()
    }
}

// todo: make generic over dimensionality
impl<D: Location<3>, N: NodeId> TreeSurgeon<D, N> {
    /// Remove all nodes further than the given geodesic distance from the root,
    /// returning removed nodes.
    pub fn prune_beyond_distance(&mut self, dist: Precision) -> Vec<Node<D, N>> {
        let mut to_visit = vec![(self.0.node(&self.0.root).unwrap(), 0.0)];
        let mut to_prune = vec![];
        while let Some((parent, from_root)) = to_visit.pop() {
            to_visit.extend(parent.children().iter().filter_map(|c| {
                let child = self.0.node(c).unwrap();
                let child_dist = from_root + parent.data().distance_to(child.data());
                if child_dist <= dist {
                    Some((child, child_dist))
                } else {
                    to_prune.push(child.id());
                    None
                }
            }));
        }
        to_prune
            .into_iter()
            .flat_map(|p| self.prune_below_including(p).unwrap())
            .collect()
    }

    /// Remove short terminal branches, returning removed nodes.
    ///
    /// Recursive: if a branch has all but one of its children removed, it may be removed if the next branch up is close enough.
    pub fn prune_twigs(&mut self, threshold: Precision) -> Vec<Node<D, N>> {
        // todo: test this hard

        // child ID, distance from leaf
        let mut to_visit: Vec<_> = self
            .0
            .leaves()
            .iter()
            .map(|n| (self.0.node(n).unwrap(), 0.0))
            .collect();

        // {branch: [(child, dist), ...]}
        // This will only contain sub-threshold branches
        let mut branch_children_dists = FastMap::default();

        let mut to_prune = Vec::default();

        while let Some((distal_node, mut dist)) = to_visit.pop() {
            let Some(prox_id) = distal_node.parent else {
                continue;
            };

            let prox_node = self.0.node(&prox_id).unwrap();
            let edge_dist = distal_node.data().distance_to(prox_node.data());
            dist += edge_dist;
            if dist > threshold {
                // do not go higher, this branch cannot be pruned
                continue;
            }
            match prox_node.node_type() {
                crate::node::NodeType::Branch(_cs) => (),
                _ => {
                    // slab; keep traversing up
                    to_visit.push((prox_node, dist));
                    continue;
                }
            }

            // add the branch's child and distance from leaf to branch
            branch_children_dists
                .entry(prox_id)
                .or_insert_with(Vec::default)
                .push((distal_node.id(), dist));

            if !to_visit.is_empty() {
                // we have more leaves to visit, keep going
                continue;
            }

            // we have visited all leaves, so all branches in branch_children_dists have all sub-threshold children enumerated

            for (branch_id, children_dists) in branch_children_dists.drain() {
                let branch_node = self.0.node(&branch_id).unwrap();
                if branch_node.children.len() > children_dists.len() {
                    // if branches have other children (which lead to supra-threshold slabs), we can prune all of these
                    to_prune.extend(children_dists.into_iter().map(|(c, _d)| c));
                    // and we don't need to traverse higher
                } else {
                    // if branches have no supra-threshold, we just want to keep the longest
                    let mut it = children_dists.into_iter();
                    let (mut longest_c, mut longest_d) = it.next().unwrap();
                    for (c, d) in it {
                        if d > longest_d {
                            longest_d = d;
                            to_prune.push(longest_c);
                            longest_c = c;
                        } else {
                            to_prune.push(c);
                        }
                    }
                    // and we need to traverse higher from here
                    to_visit.push((branch_node, longest_d));
                }
            }

            // the next traversal upwards will be from branch to branch
        }

        to_prune
            .into_iter()
            .flat_map(|n| {
                if n == self.0.root {
                    vec![]
                } else {
                    // we might try to prune a parent branch,
                    // and then some child branch, so paper over the IdAbsent errors
                    self.prune_below_including(n).unwrap_or_default()
                }
            })
            .collect()
    }
}
