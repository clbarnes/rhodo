use std::fmt::Debug;
use std::hash::Hash;

use crate::error::IdAbsent;
use crate::hash::FastSet;

/// Node IDs should have <= 8 bytes as the fast lookup tables
/// used internally have very poor collision resistance.
pub trait NodeId: Debug + Copy + Hash + Eq {}

impl<T: Debug + Copy + Hash + Eq> NodeId for T {}

// pub trait NodeData: Debug + Clone {}
// impl<D: Debug + Clone> NodeData for D {}

pub struct Node<D, N: NodeId = u64> {
    id: N,
    pub(crate) parent: Option<N>,
    pub(crate) children: FastSet<N>,
    data: D,
}

impl<D, N: NodeId> PartialEq for Node<D, N> {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id() && self.parent == other.parent && self.children == other.children
    }
}

impl<D: Debug, N: NodeId> Debug for Node<D, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("id", &self.id)
            .field("parent", &self.parent)
            .field("children", &self.children)
            .field("data", &self.data)
            .finish()
    }
}

impl<D: Clone, N: NodeId> Clone for Node<D, N> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            parent: self.parent,
            children: self.children.clone(),
            data: self.data.clone(),
        }
    }
}

pub enum NodeType<'s, N: NodeId> {
    Leaf,
    /// Contains the ID of the child
    Slab(N),
    /// Contains the IDs of the children
    Branch(&'s FastSet<N>),
}

impl<D, N: NodeId> Node<D, N> {
    pub(crate) fn new(id: N, data: D) -> Self {
        Self {
            id,
            parent: None,
            children: FastSet::default(),
            data,
        }
    }

    pub fn map_data<D2, F: Fn(D) -> D2>(self, f: F) -> Node<D2, N> {
        Node {
            id: self.id,
            parent: self.parent,
            children: self.children,
            data: f(self.data),
        }
    }

    pub fn data(&self) -> &D {
        &self.data
    }

    pub fn data_mut(&mut self) -> &mut D {
        &mut self.data
    }

    pub fn children(&self) -> &FastSet<N> {
        &self.children
    }

    pub fn parent(&self) -> Option<N> {
        self.parent
    }

    pub fn id(&self) -> N {
        self.id
    }

    pub(crate) fn remove_child(&mut self, id: &N) -> bool {
        self.children.remove(id)
    }

    /// Given the ID of one of the child nodes, make that child the node's new parent.
    /// Returns the previous parent, if present.
    pub(crate) fn switch_parent(&mut self, id: Option<N>) -> Result<Option<N>, IdAbsent<N>> {
        if let Some(c) = id {
            if !self.remove_child(&c) {
                return Err(c.into());
            }
        }
        let old_parent_opt = self.parent;
        if let Some(old_parent) = old_parent_opt {
            self.children.insert(old_parent);
        }
        self.parent = id;
        Ok(old_parent_opt)
    }

    /// Iterate over parent (first, if present) and children.
    pub fn neighbours(&self) -> impl Iterator<Item = &N> {
        self.parent.iter().chain(self.children.iter())
    }

    /// Count number of children and parent
    pub fn n_neighbours(&self) -> usize {
        let out = self.children.len();
        if self.parent.is_some() {
            out + 1
        } else {
            out
        }
    }

    pub fn node_type(&self) -> NodeType<N> {
        let c = self.children();
        match c.len() {
            0 => NodeType::Leaf,
            1 => NodeType::Slab(*c.iter().next().unwrap()),
            _ => NodeType::Branch(c),
        }
    }

    pub fn is_root(&self) -> bool {
        self.parent.is_none()
    }
}
