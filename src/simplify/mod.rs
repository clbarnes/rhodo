use crate::{
    hash::{FastMap, HashMapExt},
    spatial::{Precision, UpdateLocation},
    Location, Node, NodeId, Point, Tree,
};
use simples::{
    nalgebra::Point as NPoint,
    simplify::{rdp::rdp_keep, sample_every, vw::vw_keep},
    smooth::{smooth_convolve, Gaussian},
};

const GAUSSIAN_WIDTH: Precision = 3.0;

pub struct ParentDistance<const D: usize> {
    pub path_length: usize,
    pub geodesic_distance: Precision,
    pub location: [f64; D],
}

/// Function for use with [slab_simplify] which keeps the location of each node intact,
/// but also its original path length and geodesic distance to its new parent.
pub fn spatial_slab_simplify<const K: usize, N: NodeId, D: Location<K>>(
    t: &Tree<D, N>,
    slab: Option<&[N]>,
) -> ParentDistance<K> {
    let Some(sl) = slab else {
        return ParentDistance {
            path_length: 0,
            geodesic_distance: 0.0,
            location: t
                .node(t.root())
                .expect("slab comes from tree")
                .data()
                .location(),
        };
    };

    let path_length = sl.len() - 1;
    let mut sl_iter = sl.iter().map(|nid| t.node(nid).unwrap());
    let mut prev_node = sl_iter.next().unwrap();
    let mut dist = 0.0;
    for curr_node in sl_iter {
        dist += prev_node.data().distance_to(curr_node.data());
        prev_node = curr_node;
    }
    ParentDistance {
        path_length,
        geodesic_distance: dist,
        location: prev_node.data().location(),
    }
}

impl<const D: usize> Location<D> for ParentDistance<D> {
    fn location(&self) -> crate::Point<D> {
        self.location
    }
}

/// Generate a simplified version of a tree: just root, branches, and leaves.
///
/// `data_fn` is a function which generates the data to be stored on a node.
/// It takes a reference to the original tree,
/// and an optional slice of node IDs representing a slab of unbranched nodes,
/// where the first item is the root or proximal branch
/// and the last item is a distal branch or leaf
/// (see `Tree.slabs()`).
///
/// If the slab is `None`, generate the data for the root (same in input and output trees).
/// Otherwise, generate the data for the leaf or distal branch which is at the end of the slab.
///
/// See [spatial_slab_simplify] for an example such function.
pub fn slab_simplify<N: NodeId, D, D2, F: Fn(&Tree<D, N>, Option<&[N]>) -> D2>(
    tree: &Tree<D, N>,
    data_fn: F,
) -> Tree<D2, N> {
    let d1 = data_fn(tree, None);
    let mut t = Tree::new(*tree.root(), d1);
    if tree.len() == 1 {
        return t;
    }
    for slab in tree.slabs(tree.root()).expect("using root") {
        let parent = slab.first().expect("has parent and child");
        let child = slab.first().expect("has parent and child");
        let child_data = data_fn(tree, Some(slab.as_slice()));
        t.add_child(*parent, *child, child_data).unwrap();
    }
    t
}

/// Sample points from this tree, slab-wise.
///
/// All branches and leaves are included;
/// otherwise, 1 point is included every `distance` along each slab from leaf to root.
pub fn resample_slabs<const K: usize, N: NodeId, D: Location<K>>(
    tree: &Tree<D, N>,
    distance: Precision,
) -> impl Iterator<Item = Vec<[Precision; K]>> + '_ {
    tree.slabs(tree.root()).unwrap().map(move |mut nids| {
        let mut pts = Vec::with_capacity(nids.len());
        while let Some(n) = nids.pop() {
            pts.push(tree.node(&n).unwrap().data().location().into());
        }

        // todo: break order by not bothering with this reversal?
        let mut out_pts = sample_every(pts.as_slice(), distance, 0.0);
        let mut out = Vec::with_capacity(out_pts.len());
        while let Some(p) = out_pts.pop() {
            out.push(p.into())
        }
        out
    })
}

fn invert_keep<N: NodeId>(orig_ids: Vec<N>, to_keep: Vec<usize>, to_remove: &mut Vec<N>) {
    let mut orig_it = orig_ids.into_iter().enumerate();
    for keep_idx in to_keep.into_iter() {
        // we can't use `for` loop here because it would own orig_it
        #[allow(clippy::while_let_on_iterator)]
        while let Some((idx, orig)) = orig_it.next() {
            if idx >= keep_idx {
                break;
            } else {
                to_remove.push(orig);
            }
        }
    }
}

fn decimate_nodes<
    const K: usize,
    D: Location<K>,
    N: NodeId,
    F: Fn(&[simples::nalgebra::Point<Precision, K>]) -> Vec<usize>,
>(
    tree: &mut Tree<D, N>,
    keeper: F,
) -> Vec<Node<D, N>> {
    let mut to_remove = Vec::default();
    for slab in tree.slabs(tree.root()).unwrap() {
        let locs: Vec<_> = slab
            .iter()
            .map(|nid| tree.node(nid).unwrap().data().location().into())
            .collect();
        let keepers = keeper(locs.as_slice());
        invert_keep(slab, keepers, &mut to_remove);
    }
    to_remove
        .into_iter()
        .map(|nid| tree.remove(nid).unwrap())
        .collect()
}

/// Simplify the tree by removing slab nodes using the [Ramer-Douglass-Peucker](https://en.wikipedia.org/wiki/Ramer%E2%80%93Douglas%E2%80%93Peucker_algorithm) algorithm.
///
/// Returns the removed nodes.
pub fn rdp_nodes<const K: usize, D: Location<K>, N: NodeId>(
    tree: &mut Tree<D, N>,
    epsilon: Precision,
) -> Vec<Node<D, N>> {
    decimate_nodes(tree, move |pts| rdp_keep(pts, epsilon))
}

/// Simplify the tree by removing slab nodes using the [Visvalingam-Whyatt](https://en.wikipedia.org/wiki/Visvalingam%E2%80%93Whyatt_algorithm) algorithm.
///
/// Returns the removed nodes.
pub fn vw_nodes<const K: usize, D: Location<K>, N: NodeId>(
    tree: &mut Tree<D, N>,
    n_points: usize,
) -> Vec<Node<D, N>> {
    decimate_nodes(tree, move |pts| vw_keep(pts, n_points))
}

/// Smooth the points of each slab in the tree with a gaussian kernel.
///
/// The root, branches, and leaves stay in the same position.
/// There is a cut-off 3 standard deviations away from the point in question.
pub fn smooth_gaussian<const K: usize, D: UpdateLocation<K>, N: NodeId>(
    tree: &mut Tree<D, N>,
    stdev: Precision,
) {
    let mut new_locs: FastMap<N, Point<K>> = FastMap::with_capacity(tree.len());
    let kernel = Gaussian::new(stdev, GAUSSIAN_WIDTH);
    for slab in tree.slabs(tree.root()).unwrap() {
        let pts: Vec<NPoint<Precision, K>> = slab
            .iter()
            .map(|n| tree.node(n).unwrap().data().location().into())
            .collect();
        for (new_pt, n) in smooth_convolve(pts.as_slice(), kernel)
            .into_iter()
            .zip(slab.into_iter())
        {
            new_locs.insert(n, new_pt.coords.into());
        }
    }

    for (n, loc) in new_locs.into_iter() {
        tree.node_mut(&n).unwrap().data_mut().update_location(loc);
    }
}
