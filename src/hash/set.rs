use super::IndexHasherFactory;
use std::collections::{hash_set, HashSet};
use std::fmt::{self, Debug};
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;
use std::ops::{BitAnd, BitOr, BitXor, Deref, DerefMut, Sub};

#[cfg(feature = "serde")]
use serde::{
    de::{Deserialize, Deserializer},
    ser::{Serialize, Serializer},
};

/// A [`HashSet`](std::collections::HashSet) using [`IndexHasherFactory`](crate::IndexHasherFactory) to hash the items.
#[derive(Clone)]
pub struct IndexSet<T, S = IndexHasherFactory>(HashSet<T, S>);

impl<T, S: Default> Default for IndexSet<T, S> {
    fn default() -> Self {
        Self(HashSet::default())
    }
}

impl<T> From<HashSet<T, IndexHasherFactory>> for IndexSet<T> {
    fn from(item: HashSet<T, IndexHasherFactory>) -> Self {
        IndexSet(item)
    }
}

impl<T, const N: usize> From<[T; N]> for IndexSet<T>
where
    T: Eq + Hash,
{
    /// # Examples
    ///
    /// ```
    /// use rhodo::hash::IndexSet;
    ///
    /// let set1 = IndexSet::from([1, 2, 3, 4]);
    /// let set2: IndexSet<_> = [1, 2, 3, 4].into();
    /// assert_eq!(set1, set2);
    /// ```
    fn from(arr: [T; N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<T> Into<HashSet<T, IndexHasherFactory>> for IndexSet<T> {
    fn into(self) -> HashSet<T, IndexHasherFactory> {
        self.0
    }
}

impl<T> IndexSet<T, IndexHasherFactory> {
    /// This crates a hashset using [IndexHasherFactory::new].
    /// See the documentation in [RandomSource] for notes about key strength.
    pub fn new() -> Self {
        IndexSet(HashSet::with_hasher(IndexHasherFactory::default()))
    }

    /// This crates a hashset with the specified capacity using [IndexHasherFactory::new].
    /// See the documentation in [RandomSource] for notes about key strength.
    pub fn with_capacity(capacity: usize) -> Self {
        IndexSet(HashSet::with_capacity_and_hasher(
            capacity,
            IndexHasherFactory::default(),
        ))
    }
}

impl<T, S> IndexSet<T, S>
where
    S: BuildHasher,
{
    pub fn with_hasher(hash_builder: S) -> Self {
        IndexSet(HashSet::with_hasher(hash_builder))
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        IndexSet(HashSet::with_capacity_and_hasher(capacity, hash_builder))
    }
}

impl<T, S> Deref for IndexSet<T, S> {
    type Target = HashSet<T, S>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, S> DerefMut for IndexSet<T, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, S> PartialEq for IndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    fn eq(&self, other: &IndexSet<T, S>) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T, S> Eq for IndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

impl<T, S> BitOr<&IndexSet<T, S>> for &IndexSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    type Output = IndexSet<T, S>;

    /// Returns the union of `self` and `rhs` as a new `IndexSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rhodo::hash::IndexSet;
    ///
    /// let a: IndexSet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: IndexSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set = &a | &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 3, 4, 5];
    /// for x in &set {
    ///     assert!(expected.contains(x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitor(self, rhs: &IndexSet<T, S>) -> IndexSet<T, S> {
        IndexSet(self.0.bitor(&rhs.0))
    }
}

impl<T, S> BitAnd<&IndexSet<T, S>> for &IndexSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    type Output = IndexSet<T, S>;

    /// Returns the intersection of `self` and `rhs` as a new `IndexSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rhodo::hash::IndexSet;
    ///
    /// let a: IndexSet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: IndexSet<_> = vec![2, 3, 4].into_iter().collect();
    ///
    /// let set = &a & &b;
    ///
    /// let mut i = 0;
    /// let expected = [2, 3];
    /// for x in &set {
    ///     assert!(expected.contains(x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitand(self, rhs: &IndexSet<T, S>) -> IndexSet<T, S> {
        IndexSet(self.0.bitand(&rhs.0))
    }
}

impl<T, S> BitXor<&IndexSet<T, S>> for &IndexSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    type Output = IndexSet<T, S>;

    /// Returns the symmetric difference of `self` and `rhs` as a new `IndexSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rhodo::hash::IndexSet;
    ///
    /// let a: IndexSet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: IndexSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set = &a ^ &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 4, 5];
    /// for x in &set {
    ///     assert!(expected.contains(x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn bitxor(self, rhs: &IndexSet<T, S>) -> IndexSet<T, S> {
        IndexSet(self.0.bitxor(&rhs.0))
    }
}

impl<T, S> Sub<&IndexSet<T, S>> for &IndexSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    type Output = IndexSet<T, S>;

    /// Returns the difference of `self` and `rhs` as a new `IndexSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rhodo::hash::IndexSet;
    ///
    /// let a: IndexSet<_> = vec![1, 2, 3].into_iter().collect();
    /// let b: IndexSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set = &a - &b;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2];
    /// for x in &set {
    ///     assert!(expected.contains(x));
    ///     i += 1;
    /// }
    /// assert_eq!(i, expected.len());
    /// ```
    fn sub(self, rhs: &IndexSet<T, S>) -> IndexSet<T, S> {
        IndexSet(self.0.sub(&rhs.0))
    }
}

impl<T, S> Debug for IndexSet<T, S>
where
    T: Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

impl<T> FromIterator<T> for IndexSet<T, IndexHasherFactory>
where
    T: Eq + Hash,
{
    /// This crates a hashset from the provided iterator using [IndexHasherFactory::new].
    /// See the documentation in [RandomSource] for notes about key strength.
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> IndexSet<T> {
        let mut inner = HashSet::with_hasher(IndexHasherFactory::default());
        inner.extend(iter);
        IndexSet(inner)
    }
}

impl<'a, T, S> IntoIterator for &'a IndexSet<T, S> {
    type Item = &'a T;
    type IntoIter = hash_set::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.0).iter()
    }
}

impl<T, S> IntoIterator for IndexSet<T, S> {
    type Item = T;
    type IntoIter = hash_set::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T, S> Extend<T> for IndexSet<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

impl<'a, T, S> Extend<&'a T> for IndexSet<T, S>
where
    T: 'a + Eq + Hash + Copy,
    S: BuildHasher,
{
    #[inline]
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.0.extend(iter)
    }
}

#[cfg(feature = "serde")]
impl<T> Serialize for IndexSet<T>
where
    T: Serialize + Eq + Hash,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.deref().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T> Deserialize<'de> for IndexSet<T>
where
    T: Deserialize<'de> + Eq + Hash,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let hash_set = HashSet::deserialize(deserializer);
        hash_set.map(|hash_set| Self(hash_set))
    }

    fn deserialize_in_place<D: Deserializer<'de>>(
        deserializer: D,
        place: &mut Self,
    ) -> Result<(), D::Error> {
        HashSet::deserialize_in_place(deserializer, place)
    }
}

#[cfg(all(test, feature = "serde"))]
mod test {
    use super::*;

    #[test]
    fn test_serde() {
        let mut set = IndexSet::new();
        set.insert("for".to_string());
        set.insert("bar".to_string());
        let mut serialization = serde_json::to_string(&set).unwrap();
        let mut deserialization: IndexSet<String> = serde_json::from_str(&serialization).unwrap();
        assert_eq!(deserialization, set);

        set.insert("baz".to_string());
        serialization = serde_json::to_string(&set).unwrap();
        let mut deserializer = serde_json::Deserializer::from_str(&serialization);
        IndexSet::deserialize_in_place(&mut deserializer, &mut deserialization).unwrap();
        assert_eq!(deserialization, set);
    }
}
