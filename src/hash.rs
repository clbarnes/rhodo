use std::collections::{HashMap, HashSet};
pub use std::hash::BuildHasherDefault;
use std::hash::Hasher;

pub use ahash::{HashMapExt, HashSetExt, RandomState as ARandomState};

type IndexMap<K, V, S = BuildIndexHasher> = HashMap<K, V, S>;
type IndexSet<T, S = BuildIndexHasher> = HashSet<T, S>;

/// A very fast hashmap only valid for keys <= 8 bytes.
pub type FastMap<K, V> = IndexMap<K, V>;

/// A very fast hashset only valid for keys <= 8 bytes.
pub type FastSet<T> = IndexSet<T>;

/// Fast hasher only valid for types <= 8 bytes.
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
            self.state = self.state.rotate_left(8) ^ u64::from(*b);
        }
    }
}

pub type BuildIndexHasher = BuildHasherDefault<IndexHasher>;
