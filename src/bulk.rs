//! Bulk operations on typed collections: reading the entries that match a
//! predicate, and removing or changing all of them in one call.
//!
//! Each one reads first and writes after, so it never writes while it's
//! iterating, and writes nothing at all when nothing matches. In
//! [`History::transact`], a call that matches nothing doesn't make the
//! transaction commit. Like [`Map::remove`], none of them create a missing
//! collection.
//!
//! [`History::transact`]: crate::History::transact

use std::borrow::Borrow;

use crate::collections::{ReadHashMap, WriteHashMap};
use crate::core::Core;
use crate::error::Result;
use crate::typed::{KeyCodec, Map, Set, ValueCodec};

impl<K: KeyCodec + ?Sized, V: ValueCodec> Map<K, V>
where
    K::Owned: Borrow<K>,
{
    /// The keys whose entries match `matches`, in hash order.
    pub fn keys_where<C: Core>(
        &self,
        parent: &ReadHashMap<'_, C>,
        mut matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<Vec<K::Owned>> {
        let mut keys = Vec::new();
        for entry in self.iter(parent)? {
            let (key, value) = entry?;
            if matches(&key, &value) {
                keys.push(key);
            }
        }
        Ok(keys)
    }

    /// The entries that match `matches`, in hash order.
    pub fn entries_where<C: Core>(
        &self,
        parent: &ReadHashMap<'_, C>,
        mut matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<Vec<(K::Owned, V::Owned)>> {
        let mut entries = Vec::new();
        for entry in self.iter(parent)? {
            let (key, value) = entry?;
            if matches(&key, &value) {
                entries.push((key, value));
            }
        }
        Ok(entries)
    }

    /// Keeps only the entries for which `keep` returns `true`, removing the
    /// rest, and returns how many were removed. If none were, nothing is
    /// written. Every value is decoded, so one that doesn't decode is an
    /// [`Error::Decode`](crate::Error::Decode) and nothing is removed.
    pub fn retain<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut keep: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<usize> {
        let mut hashes = Vec::new();
        for entry in self.iter(parent)? {
            let (key, value) = entry?;
            if !keep(&key, &value) {
                hashes.push(parent.hash(key.borrow().encode_key()));
            }
        }
        if hashes.is_empty() {
            return Ok(0);
        }
        let mut map = self.collection_mut(parent)?;
        let mut removed = 0;
        for hash in &hashes {
            if map.remove_by_hash(hash)? {
                removed += 1;
            }
        }
        Ok(removed)
    }

    /// Removes each of `keys` that has a value, and returns how many did.
    /// Missing keys are skipped without writing, so if none of them had a
    /// value, nothing is written. The keys can be owned or borrowed: for a
    /// `str` key, a `Vec<String>` or an array of `&str`s.
    pub fn remove_all<C: Core, Q: Borrow<K>>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        keys: impl IntoIterator<Item = Q>,
    ) -> Result<usize> {
        let mut removed = 0;
        for key in keys {
            if self.remove(parent, key.borrow())? {
                removed += 1;
            }
        }
        Ok(removed)
    }

    /// Runs `change` on a copy of each value that matches `matches`, writes
    /// back the ones it changed, and returns how many it wrote.
    ///
    /// A value counts as changed if it isn't equal (by [`PartialEq`]) to
    /// the value before `change`, so a value that `change` leaves the same,
    /// or sets back to what it was, isn't written. If none changed, nothing
    /// is written.
    ///
    /// The values are decoded as [`ValueCodec::Owned`] and written back
    /// through [`Borrow`], so this works for `String` (a `str` to write) and
    /// `Json<T>` (a `T`) alike.
    pub fn update_where<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
        mut change: impl FnMut(&mut V::Owned),
    ) -> Result<usize>
    where
        V::Owned: Clone + PartialEq + Borrow<V::Borrowed>,
    {
        let changed = self.changed_where(parent, &mut matches, &mut change)?;
        for Changed { key, new, .. } in &changed {
            self.put(parent, key.borrow(), new.borrow())?;
        }
        Ok(changed.len())
    }

    /// The entries that `update_where` would change.
    pub(crate) fn changed_where<C: Core>(
        &self,
        parent: &ReadHashMap<'_, C>,
        matches: &mut impl FnMut(&K::Owned, &V::Owned) -> bool,
        change: &mut impl FnMut(&mut V::Owned),
    ) -> Result<Vec<Changed<K::Owned, V::Owned>>>
    where
        V::Owned: Clone + PartialEq,
    {
        let mut changed = Vec::new();
        for entry in self.iter(parent)? {
            let (key, value) = entry?;
            if matches(&key, &value) {
                let mut new = value.clone();
                change(&mut new);
                if new != value {
                    changed.push(Changed { key, old: value, new });
                }
            }
        }
        Ok(changed)
    }
}

/// An entry that [`Map::update_where`] changes.
pub(crate) struct Changed<K, V> {
    pub(crate) key: K,
    pub(crate) old: V,
    pub(crate) new: V,
}

impl<K: KeyCodec + ?Sized> Set<K>
where
    K::Owned: Borrow<K>,
{
    /// Keeps only the keys for which `keep` returns `true`, removing the
    /// rest, and returns how many were removed. If none were, nothing is
    /// written.
    pub fn retain<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut keep: impl FnMut(&K::Owned) -> bool,
    ) -> Result<usize> {
        let mut hashes = Vec::new();
        for key in self.iter(parent)? {
            let key = key?;
            if !keep(&key) {
                hashes.push(parent.hash(key.borrow().encode_key()));
            }
        }
        if hashes.is_empty() {
            return Ok(0);
        }
        let mut set = self.collection_mut(parent)?;
        let mut removed = 0;
        for hash in &hashes {
            if set.remove_by_hash(hash)? {
                removed += 1;
            }
        }
        Ok(removed)
    }

    /// Removes each of `keys` that's in the set, and returns how many were.
    /// Missing keys are skipped without writing, so if none of them were in
    /// the set, nothing is written.
    pub fn remove_all<C: Core, Q: Borrow<K>>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        keys: impl IntoIterator<Item = Q>,
    ) -> Result<usize> {
        let mut removed = 0;
        for key in keys {
            if self.remove(parent, key.borrow())? {
                removed += 1;
            }
        }
        Ok(removed)
    }
}
