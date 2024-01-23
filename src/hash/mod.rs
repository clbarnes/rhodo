use std::hash::{BuildHasher, Hasher};

mod map;
mod set;

pub use map::IndexMap;
pub use set::IndexSet;

#[derive(Copy, Clone, Debug, Default)]
pub struct IndexHasher {
    state: u64,
}

impl Hasher for IndexHasher {
    fn finish(&self) -> u64 {
        self.state
    }

    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.state = self.state.rotate_left(8) | u64::from(*b);
        }
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct IndexHasherFactory {}

impl BuildHasher for IndexHasherFactory {
    type Hasher = IndexHasher;

    fn build_hasher(&self) -> Self::Hasher {
        IndexHasher::default()
    }
}
