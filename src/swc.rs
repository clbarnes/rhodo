use std::io::{self, BufRead};

pub use swc_neuron;
use swc_neuron::SampleId;
use swc_neuron::SwcParseError;
use swc_neuron::{structures::StructureIdentifier, SwcSample};
use thiserror::Error;

use crate::error::{EdgeBuild, IdAbsent, InvalidId};
use crate::spatial::{Location, Point, UpdateLocation};
use crate::Tree;

pub struct SwcData<S: StructureIdentifier> {
    pub location: Point<3>,
    pub structure: S,
    pub radius: f64,
}

impl<S: StructureIdentifier> From<&SwcSample<S>> for SwcData<S> {
    fn from(s: &SwcSample<S>) -> Self {
        Self {
            location: [s.x, s.y, s.z],
            structure: s.structure,
            radius: s.radius,
        }
    }
}

impl<S: StructureIdentifier> Location<3> for SwcData<S> {
    fn location(&self) -> Point<3> {
        self.location
    }
}

impl<S: StructureIdentifier> UpdateLocation<3> for SwcData<S> {
    fn update_location(&mut self, loc: Point<3>) {
        self.location = loc;
    }
}

// #[derive(Error, Debug)]
// pub enum SwcReadError {
//     #[error(transparent)]
//     EdgeBuild(#[from] EdgeBuild<u64>),
//     #[error(transparent)]
//     Swc(#[from] SwcParseError),
// }

// pub fn read_swc<S: StructureIdentifier, R: BufRead>(
//     reader: R,
// ) -> Result<Tree<SwcData<S>, usize>, SwcReadError> {
//     SwcLines::<S, R>::new(reader)?.filter()
// }

pub fn swc_to_tree<S: StructureIdentifier, T: IntoIterator<Item = SwcSample<S>>>(
    samples: T,
) -> Result<Tree<SwcData<S>, SampleId>, EdgeBuild<SampleId>> {
    let mut it = samples.into_iter();
    let r = it.next().ok_or(EdgeBuild::NoRoot)?;
    if let Some(p) = r.parent_id {
        return Err(InvalidId::Absent(IdAbsent::from(p)).into());
    }
    let mut t = Tree::new(r.sample_id, (&r).into());
    for s in it {
        let p = s
            .parent_id
            .ok_or(EdgeBuild::MultipleRoots(vec![s.sample_id, r.sample_id]))?;
        t.add_child(p, s.sample_id, (&s).into())?;
    }
    Ok(t)
}

pub trait HasSwcData<S: StructureIdentifier>: Location<3> {
    fn radius(&self) -> f64;

    fn structure(&self) -> S;
}

impl<S: StructureIdentifier> HasSwcData<S> for SwcData<S> {
    fn radius(&self) -> f64 {
        self.radius
    }

    fn structure(&self) -> S {
        self.structure
    }
}

pub fn tree_to_swc<S: StructureIdentifier, D: HasSwcData<S>>(
    tree: &Tree<D, SampleId>,
) -> impl Iterator<Item = SwcSample<S>> + '_ {
    tree.dfs_edges(*tree.root()).unwrap().map(|(p, c, d)| {
        let loc = d.location();
        SwcSample {
            sample_id: c,
            structure: d.structure(),
            x: loc[0],
            y: loc[1],
            z: loc[2],
            radius: d.radius(),
            parent_id: p,
        }
    })
}
