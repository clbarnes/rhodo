use crate::{
    hash::{FastMap, HashMapExt},
    NodeId, Tree,
};

/// Struct representing a Strahler number calculation for a single branch node.
#[derive(Debug, Clone, Default)]
pub(crate) struct StrahlerCounter {
    children_remaining: usize,
    /// Counts of how many children have a given Strahler number
    child_strahlers: FastMap<usize, usize>,
}

impl StrahlerCounter {
    pub(crate) fn new(n_children: usize) -> Self {
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
    pub(crate) fn add(&mut self, child_strahler: usize) -> Option<usize> {
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

pub fn strahler<D, N: NodeId>(tree: &Tree<D, N>) -> FastMap<N, usize> {
    let mut branch_strahlers: FastMap<_, _> = tree
        .branches()
        .iter()
        .map(|n| {
            (
                *n,
                StrahlerCounter::new(tree.node(n).unwrap().children().len()),
            )
        })
        .collect();

    let mut out = FastMap::with_capacity(tree.len());

    for leaf in tree.leaves().iter() {
        let mut this_strahler = 1;
        out.insert(*leaf, this_strahler);
        for proximal in tree.ancestors(*leaf).unwrap() {
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

#[cfg(test)]
mod tests {
    use crate::tests::make_basic;

    use super::*;

    #[test]
    fn strahler_simple() {
        let t = make_basic();
        assert_eq!(
            strahler(&t),
            vec![(3, 1), (4, 1), (5, 1), (2, 2), (1, 2),]
                .into_iter()
                .collect()
        )
    }
}
