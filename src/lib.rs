pub mod iter;

pub mod error;

mod node;
pub use node::{Node, NodeId};

mod tree;
pub use tree::Tree;

mod spatial;
pub use spatial::{Location, Point};

pub mod hash;

#[cfg(any(feature = "debug", test))]
pub mod debug;

#[cfg(feature = "swc-neuron")]
pub mod swc;
#[cfg(feature = "swc-neuron")]
pub use swc_neuron;

pub mod algos;

mod surgeon;
pub use surgeon::TreeSurgeon;

pub mod simplify;

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
}
