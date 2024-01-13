use std::ops::Add;

use num_traits::Zero;

use crate::{FastMap, Node, NodeId, Tree};

pub type Precision = f64;
pub type Point3 = [Precision; 3];

pub trait Location {
    fn location(&self) -> Point3;

    /// The squared euclidean distance to another location.
    fn distance2_to<L: Location>(&self, other: &L) -> Precision {
        let mut squares_total = 0.0;
        for (a, b) in self.location().iter().zip(other.location().iter()) {
            let diff = a - b;
            squares_total += diff * diff;
        }
        squares_total
    }

    /// The euclidean distance to another location.
    fn distance_to<L: Location>(&self, other: &L) -> Precision {
        self.distance2_to(other).sqrt()
    }

    /// Where you would end up if you travelled `distance` towards `other`,
    /// and the overshoot: how far past the point you have travelled
    /// (negative if the point was not reached).
    fn project_towards<L: Location>(&self, other: &L, distance: Precision) -> (Point3, Precision) {
        let self_loc = self.location();
        let distance_to = self.distance_to(other);
        if distance_to * distance == 0.0 {
            return (self_loc, 0.0);
        }
        let mut out = [0.0, 0.0, 0.0];
        for (idx, (a, b)) in self_loc.iter().zip(other.location().iter()).enumerate() {
            let diff = b - a;
            out[idx] = a + (diff / distance_to) * distance;
        }
        (out, distance - distance_to)
    }
}

impl Location for Point3 {
    fn location(&self) -> Point3 {
        *self
    }
}

impl Location for &Point3 {
    fn location(&self) -> Point3 {
        **self
    }
}

impl<T, L: Location> Location for (T, L) {
    fn location(&self) -> Point3 {
        self.1.location()
    }
}

impl<T, L: Location> Location for &(T, L) {
    fn location(&self) -> Point3 {
        self.1.location()
    }
}

impl<D: Location, N: NodeId> Location for Node<D, N> {
    fn location(&self) -> Point3 {
        self.data().location()
    }
}

impl<D: Location, N: NodeId> Location for &Node<D, N> {
    fn location(&self) -> Point3 {
        self.data().location()
    }
}

impl<D: Location, N: NodeId> Tree<D, N> {
    /// Total length of all edges in the tree.
    pub fn length(&self) -> Precision {
        self.dfs_edges(*self.root())
            .unwrap()
            .filter_map(|(p_id, _, d)| p_id.map(|p_id| self.node(&p_id).unwrap().distance_to(d)))
            .sum()
    }

    /// Create a lookup table of spatial distance along paths between all pairs of nodes.
    pub fn geodesic_matrix(&self) -> DistanceMatrix<N, Precision> {
        let cap = self.nodes().len();
        let mut dm = DistanceMatrix::with_capacity(cap);
        if cap <= 1 {
            return dm;
        }
        let edges: Vec<_> = self.dfs_edges(*self.root()).unwrap().collect();
        for (idx, (_, c1, _)) in edges[..edges.len() - 1].iter().enumerate() {
            for (p2_opt, c2, d2) in edges[idx + 1..].iter() {
                let p2 = p2_opt.unwrap();
                let p_dist = dm.get(c1, &p2).unwrap();
                let edge_len = self.node(&p2).unwrap().distance_to(*d2);
                dm.insert(c1, c2, p_dist + edge_len);
            }
        }
        dm
    }
}

pub struct DistanceMatrix<N, T>
where
    N: NodeId,
    T: Zero + Add<T, Output = T> + Clone,
{
    indices: FastMap<N, usize>,
    distances: Vec<Option<T>>,
    next_idx: usize,
    capacity: usize,
}

impl<N, T> DistanceMatrix<N, T>
where
    N: NodeId,
    T: Zero + Add<T, Output = T> + Clone,
{
    #[cfg(test)]
    pub(crate) fn new_unchecked(indices: FastMap<N, usize>, distances: Vec<Option<T>>) -> Self {
        let len = indices.len();
        let dist_len = len.saturating_sub(1) * (len) / 2;
        if distances.len() != dist_len {
            panic!("Expected {} distances, got {}", dist_len, distances.len());
        }
        Self {
            indices,
            distances,
            next_idx: len,
            capacity: len,
        }
    }

    pub(crate) fn with_capacity(n: usize) -> Self {
        let dist_len = n.saturating_sub(1) * (n) / 2;
        Self {
            indices: FastMap::with_capacity(n),
            distances: vec![None; dist_len],
            next_idx: 0,
            capacity: n,
        }
    }

    pub(crate) fn insert(&mut self, k1: &N, k2: &N, dist: T) {
        if k1 == k2 {
            return;
        }
        let mut clos = || {
            if self.next_idx >= self.capacity {
                panic!("Exceeded capacity");
            };
            let ret = self.next_idx;
            self.next_idx += 1;
            ret
        };
        let idx1 = { *self.indices.entry(*k1).or_insert_with(&mut clos) };
        let idx2 = { *self.indices.entry(*k2).or_insert_with(&mut clos) };
        let flat = self.flat_idx(idx1, idx2).unwrap();
        self.distances.insert(flat, Some(dist))
    }

    pub(crate) fn flat_idx(&self, idx1: usize, idx2: usize) -> Option<usize> {
        if idx1 >= self.next_idx || idx2 >= self.next_idx || idx1 == idx2 {
            return None;
        }
        let (low, upp) = if idx1 < idx2 {
            (idx1, idx2)
        } else {
            (idx2, idx1)
        };

        // https://stackoverflow.com/a/36867493/2700168
        Some(self.capacity * low - low * (low + 1) / 2 + upp - 1 - low)
    }

    pub fn get(&self, k1: &N, k2: &N) -> Option<T> {
        if k1 == k2 {
            return Some(T::zero());
        }
        let idx1 = self.indices.get(k1)?;
        let idx2 = self.indices.get(k2)?;
        let flat = self.flat_idx(*idx1, *idx2)?;
        self.distances.get(flat)?.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type SpatialTree = Tree<Point3>;

    pub fn make_tree(runs: Vec<Vec<(u64, Point3)>>) -> Tree<Point3, u64> {
        let (r_id, r_p) = runs.first().unwrap().first().unwrap();
        let mut t = Tree::new(*r_id, *r_p);
        for run in runs.into_iter() {
            for p_c in run.windows(2) {
                t.add_child(p_c[0].0, p_c[1].0, p_c[1].1).unwrap();
            }
        }
        t
    }

    /// ```text
    /// 0 1 2 3 4
    /// 1 1─2─3─4
    ///     |
    /// 2   5
    /// ```
    pub fn make_basic() -> SpatialTree {
        make_tree(vec![
            vec![
                (1, [0.0, 1.0, 1.0]),
                (2, [0.0, 1.0, 2.0]),
                (3, [0.0, 1.0, 3.0]),
                (4, [0.0, 1.0, 4.0]),
            ],
            vec![(2, [0.0, 1.0, 2.0]), (5, [0.0, 2.0, 2.0])],
        ])
    }

    #[test]
    fn length() {
        let t = make_basic();
        assert_eq!(t.length(), 4.0)
    }

    fn assert_geodesic(geo: &DistanceMatrix<u64, f64>, k1: u64, k2: u64, expected: f64) {
        assert_eq!(geo.get(&k1, &k2), Some(expected))
    }

    #[test]
    fn geodesic() {
        let t = make_basic();
        let geo = t.geodesic_matrix();
        assert_geodesic(&geo, 1, 1, 0.0);
        assert_geodesic(&geo, 1, 4, 3.0);
        assert_geodesic(&geo, 1, 5, 2.0);
        assert_geodesic(&geo, 4, 5, 3.0);
    }

    fn simple_dists() -> DistanceMatrix<u64, f64> {
        let keys = vec![1, 2, 3, 4, 5];
        let indices: FastMap<_, _> = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(idx, k)| (k, idx))
            .collect();
        let distances = vec![
            1.0, 2.0, 3.0, 2.0, // 1 -> 2,3,4,5
            1.0, 2.0, 1.0, // 2 -> 3,4,5
            1.0, 2.0, // 3 -> 4,5
            3.0, // 4 -> 5
        ]
        .into_iter()
        .map(|v| Some(v))
        .collect();
        DistanceMatrix::new_unchecked(indices, distances)
    }

    #[test]
    fn flat_idx() {
        let dm = simple_dists();
        assert_eq!(dm.flat_idx(10, 11), None); // does not exist
        assert_eq!(dm.flat_idx(0, 0), None); // same
        assert_eq!(dm.flat_idx(0, 1), Some(0)); // same
        assert_eq!(dm.flat_idx(3, 4), Some(9)); // same
    }
}