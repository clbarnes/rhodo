use std::io::{self, BufRead, Write};

pub use swc_neuron;
use swc_neuron::{structures::StructureIdentifier, SwcSample};
use swc_neuron::{Header, SampleId, SwcLines};

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

pub fn read_swc<S: StructureIdentifier, R: BufRead>(
    reader: R,
) -> Result<Tree<SwcData<S>, SampleId>, String> {
    let mut it = SwcLines::<S, R>::new(reader)
        .map_err(|_e| "could not read header".to_string())?
        .filter_map(|res| {
            let ln = match res {
                Ok(ln) => ln,
                Err(e) => return Some(Err(e)),
            };
            match ln {
                swc_neuron::SwcLine::Comment(_c) => None,
                swc_neuron::SwcLine::Sample(s) => Some(Ok(s)),
            }
        });

    let r = it
        .next()
        .ok_or("no root".to_string())?
        .map_err(|e| e.to_string())?;

    if let Some(_p) = r.parent_id {
        return Err("id absent".into());
    }

    let mut t = Tree::new(r.sample_id, (&r).into());
    for res in it {
        let s = match res {
            Ok(s) => s,
            Err(e) => return Err(e.to_string()),
        };
        let p = s
            .parent_id
            .ok_or(EdgeBuild::MultipleRoots(vec![s.sample_id, r.sample_id]))
            .map_err(|e| e.to_string())?;
        t.add_child(p, s.sample_id, (&s).into())
            .map_err(|e| e.to_string())?;
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

pub fn write_swc<S: StructureIdentifier, D: HasSwcData<S>, W: Write, H: Header>(
    tree: &Tree<D, SampleId>,
    header: Option<H>,
    mut writer: W,
) -> io::Result<()> {
    if let Some(h) = header {
        for line in h.to_string().lines() {
            write!(writer, "#")?;
            writeln!(writer, "{}", line)?;
        }
    }
    for (p, c, d) in tree.dfs_edges(*tree.root()).unwrap() {
        let loc = d.location();
        let sample = SwcSample {
            sample_id: c,
            structure: d.structure(),
            x: loc[0],
            y: loc[1],
            z: loc[2],
            radius: d.radius(),
            parent_id: p,
        };
        writeln!(writer, "{}", sample.to_string())?;
    }
    Ok(())
}
