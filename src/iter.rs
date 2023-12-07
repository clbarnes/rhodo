use crate::{error::IdAbsent, NodeId, Tree};

/// Iterate over a slab of nodes towards the root.
///
/// The first element is the given start point.
/// The last node is the closest branch (or the root) *other* than the start point.
pub struct RootwardSlabIterator<'t, D, N: NodeId> {
    curr_id: Option<N>,
    tree: &'t Tree<D, N>,
    first: bool,
}

impl<'t, D, N: NodeId> RootwardSlabIterator<'t, D, N> {
    pub(crate) fn new(tree: &'t Tree<D, N>, id: &N) -> Result<Self, IdAbsent<N>> {
        if !tree.contains(id) {
            return Err(IdAbsent::from(*id));
        }
        Ok(Self {
            curr_id: Some(*id),
            tree,
            first: true,
        })
    }
}

impl<'t, D, N: NodeId> Iterator for RootwardSlabIterator<'t, D, N> {
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        let to_return = self.curr_id?;
        let node = self.tree.node(&to_return).ok()?;
        if !self.first && node.children().len() > 1 {
            self.curr_id = None;
        } else {
            self.curr_id = node.parent();
        }
        self.first = false;

        Some(to_return)
    }
}

/// Unlike the [RootwardSlabIterator], does not continue if the starting node is itself a branch.
pub struct LeafwardSlabIterator<'t, D, N: NodeId> {
    curr_id: Option<N>,
    tree: &'t Tree<D, N>,
}

impl<'t, D, N: NodeId> LeafwardSlabIterator<'t, D, N> {
    pub(crate) fn new(tree: &'t Tree<D, N>, id: &N) -> Result<Self, IdAbsent<N>> {
        if !tree.contains(id) {
            return Err(IdAbsent::from(*id));
        }
        Ok(Self {
            curr_id: Some(*id),
            tree,
        })
    }
}

impl<'t, D, N: NodeId> Iterator for LeafwardSlabIterator<'t, D, N> {
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        let to_return = self.curr_id?;
        let children = self.tree.node(&to_return).ok()?.children();
        if children.len() == 1 {
            self.curr_id = Some(*children.first().unwrap());
        } else {
            self.curr_id = None;
        }

        Some(to_return)
    }
}

/// An iterator over a node's ancestors.
pub struct RootwardIterator<'t, D, N: NodeId> {
    curr_id: Option<N>,
    tree: &'t Tree<D, N>,
}

impl<'t, D, N: NodeId> RootwardIterator<'t, D, N> {
    pub(crate) fn new(tree: &'t Tree<D, N>, id: N) -> Result<Self, IdAbsent<N>> {
        if !tree.contains(&id) {
            return Err(IdAbsent::from(id));
        }
        Ok(Self {
            curr_id: Some(id),
            tree,
        })
    }
}

impl<'t, D, N: NodeId> Iterator for RootwardIterator<'t, D, N> {
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        let to_return = self.curr_id?;
        self.curr_id = self.tree.node(&to_return).ok().and_then(|n| n.parent());
        Some(to_return)
    }
}

/// Iterator over edges in depth-first pre-order, with children addressed in reverse insertion order.
///
/// Only the first item's first element may be None.
pub struct DfsEdges<'t, D, N: NodeId> {
    to_visit: Vec<(Option<N>, N)>,
    tree: &'t Tree<D, N>,
}

impl<'t, D, N: NodeId> DfsEdges<'t, D, N> {
    // fn new(tree: &'t Tree<D, N>) -> Self {
    //     Self {
    //         to_visit: vec![(None, tree.root)],
    //         tree,
    //     }
    // }

    pub(crate) fn new_from(tree: &'t Tree<D, N>, root: N) -> Result<Self, IdAbsent<N>> {
        let node = tree.node(&root)?.parent();
        Ok(Self {
            to_visit: vec![(node, root)],
            tree,
        })
    }
}

impl<'t, D, N: NodeId> Iterator for DfsEdges<'t, D, N> {
    type Item = (Option<N>, N, &'t D);

    fn next(&mut self) -> Option<Self::Item> {
        let (parent, this_id) = self.to_visit.pop()?;
        let node = self.tree.node(&this_id).ok()?;
        self.to_visit
            .extend(node.children.iter().map(|c| (Some(this_id), *c)));
        Some((parent, this_id, node.data()))
    }
}

pub struct SlabsIterator<'t, D, N: NodeId> {
    /// First element is the proximal end of the slab,
    /// the second element is the next node down.
    to_visit: Vec<(N, Option<N>)>,
    tree: &'t Tree<D, N>,
}

impl<'t, D, N: NodeId> SlabsIterator<'t, D, N> {
    pub(crate) fn new_from_root(tree: &'t Tree<D, N>, root: N) -> Result<Self, IdAbsent<N>> {
        let root_node = tree.node(&root)?;
        let mut to_visit: Vec<(N, Option<N>)> = root_node
            .children()
            .iter()
            .map(|c| (root, Some(*c)))
            .collect();
        if to_visit.is_empty() {
            to_visit.push((tree.root, None))
        }
        Ok(Self { to_visit, tree })
    }
}

impl<'t, D, N: NodeId> Iterator for SlabsIterator<'t, D, N> {
    type Item = Vec<N>;

    fn next(&mut self) -> Option<Self::Item> {
        let (root, first_opt) = self.to_visit.pop()?;

        let Some(first_id) = first_opt else {
            return Some(vec![root]);
        };

        let mut out = Vec::default();
        out.push(root);

        out.extend(LeafwardSlabIterator::new(self.tree, &first_id).unwrap());

        let last_id = out.last().unwrap();
        let last_node = self.tree.node(last_id).unwrap();
        for c in last_node.children() {
            self.to_visit.push((*last_id, Some(*c)));
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::{make_basic, make_tree};

    #[test]
    fn rootward_slab() {
        let t = make_basic();
        assert_eq!(
            vec![5, 2],
            RootwardSlabIterator::new(&t, &5)
                .unwrap()
                .collect::<Vec<_>>()
        );
        assert_eq!(
            vec![4, 3, 2],
            RootwardSlabIterator::new(&t, &4)
                .unwrap()
                .collect::<Vec<_>>()
        );
        assert_eq!(
            vec![2, 1],
            RootwardSlabIterator::new(&t, &2)
                .unwrap()
                .collect::<Vec<_>>()
        );
    }
}
