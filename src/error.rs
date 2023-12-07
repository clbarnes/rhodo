use thiserror as te;

use crate::NodeId;

#[derive(Debug, te::Error)]
#[error("Node ID not found: {0:?}")]
pub struct IdAbsent<N: NodeId>(#[from] N);

#[derive(Debug, te::Error)]
#[error("Node ID already exists: {0:?}")]
pub struct IdPresent<N: NodeId>(#[from] N);

#[derive(Debug, te::Error)]
pub enum InvalidId<N: NodeId> {
    #[error(transparent)]
    Present(#[from] IdPresent<N>),
    #[error(transparent)]
    Absent(#[from] IdAbsent<N>),
}

#[derive(Debug, te::Error)]
pub enum EdgeBuild<N: NodeId> {
    #[error(transparent)]
    Id(#[from] InvalidId<N>),
    #[error("No root node")]
    NoRoot,
    #[error("Multiple roots found, including {0:?}")]
    MultipleRoots(#[from] Vec<N>),
}
