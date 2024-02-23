use ahash::AHasher;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use criterion::{black_box, criterion_group, criterion_main, Criterion};

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

fn run_hash<H: Hasher + Default, T: Hash>(val: T) -> u64 {
    let mut h = H::default();
    val.hash(&mut h);
    h.finish()
}

pub fn bench_hash(c: &mut Criterion) {
    let mut rng = fastrand::Rng::with_seed(1991);
    let value = rng.u64(..);
    let mut group = c.benchmark_group("hashers u64");

    group.bench_function("DefaultHasher", |b| {
        b.iter(|| run_hash::<DefaultHasher, _>(black_box(value)))
    });
    group.bench_function("AHasher", |b| {
        b.iter(|| run_hash::<AHasher, _>(black_box(value)))
    });
    group.bench_function("IndexHasher", |b| {
        b.iter(|| run_hash::<IndexHasher, _>(black_box(value)))
    });
    group.finish();
}

criterion_group!(benches, bench_hash);
criterion_main!(benches);
