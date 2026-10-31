//! Bulk operations on typed collections: reading the entries that match a
//! predicate, and removing or changing all of them in one call.
//!
//! Each one reads first and writes after, so it never writes while it's
//! iterating, and writes nothing at all when nothing matches. In
//! [`History::transact`], a call that matches nothing doesn't make the
//! transaction commit. Like [`Map::remove`], none of them create a missing
//! collection.
//!
//! Each has one implementation, which takes an [`EntryHook`] that's told
//! about every entry it removes or changes: the public methods pass
//! [`NoHook`], and an [`IndexedMap`](crate::IndexedMap) passes one that
//! updates its indexes.
//!
//! [`History::transact`]: crate::History::transact

use std::borrow::Borrow;
use std::collections::BTreeSet;

use crate::collections::{ReadHashMap, WriteHashMap, WriteHashSet, has_value};
use crate::core::Core;
use crate::error::{Error, Result};
use crate::typed::{KeyCodec, Map, Set, ValueCodec, read_key, with_context};

/// Told about each entry a bulk operation on a [`Map`] removes or changes,
/// before the map is written. `primary` is the key as stored.
pub(crate) trait EntryHook<V: ValueCodec> {
    /// Whether [`EntryHook::on_remove`] needs the old value, so removals
    /// that otherwise wouldn't read it decode it.
    const WANTS_VALUES: bool;

    /// `primary` is removed. `old` is its value, if
    /// [`EntryHook::WANTS_VALUES`] is set or the operation read it anyway.
    fn on_remove(&mut self, primary: &[u8], old: Option<&V::Owned>);

    /// `primary` changes from `old` to `new`.
    fn on_change(&mut self, primary: &[u8], old: &V::Owned, new: &V::Owned);
}

/// The [`EntryHook`] of a plain [`Map`], which does nothing.
pub(crate) struct NoHook;

impl<V: ValueCodec> EntryHook<V> for NoHook {
    const WANTS_VALUES: bool = false;

    fn on_remove(&mut self, _: &[u8], _: Option<&V::Owned>) {}

    fn on_change(&mut self, _: &[u8], _: &V::Owned, _: &V::Owned) {}
}

/// A decoded entry, with its key as stored and the hash it's stored at.
pub(crate) struct Entry<K, V> {
    pub(crate) hash: Vec<u8>,
    pub(crate) primary: Vec<u8>,
    pub(crate) key: K,
    pub(crate) value: V,
}

impl<K: KeyCodec + ?Sized, V: ValueCodec> Map<K, V> {
    /// The keys whose entries match `matches`, in hash order.
    pub fn keys_where<C: Core>(
        &self,
        parent: &ReadHashMap<'_, C>,
        matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<Vec<K::Owned>> {
        Ok(self.entries_where(parent, matches)?.into_iter().map(|(key, _)| key).collect())
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
        keep: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<usize> {
        self.retain_with(parent, keep, &mut NoHook)
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
        self.remove_all_with(parent, keys, &mut NoHook)
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
        matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
        change: impl FnMut(&mut V::Owned),
    ) -> Result<usize>
    where
        V::Owned: Clone + PartialEq + Borrow<V::Borrowed>,
    {
        self.update_where_with(parent, matches, change, &mut NoHook)
    }

    pub(crate) fn retain_with<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut keep: impl FnMut(&K::Owned, &V::Owned) -> bool,
        hook: &mut impl EntryHook<V>,
    ) -> Result<usize> {
        let mut hashes = Vec::new();
        self.for_each_entry(parent, |entry| {
            if !keep(&entry.key, &entry.value) {
                hook.on_remove(&entry.primary, Some(&entry.value));
                hashes.push(entry.hash);
            }
        })?;
        remove_hashes(&hashes, || self.collection_mut(parent))
    }

    pub(crate) fn remove_all_with<C: Core, Q: Borrow<K>, H: EntryHook<V>>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        keys: impl IntoIterator<Item = Q>,
        hook: &mut H,
    ) -> Result<usize> {
        let Some(map) = self.collection(parent)? else { return Ok(0) };
        let mut seen = BTreeSet::new();
        let mut hashes = Vec::new();
        for key in keys {
            let key = key.borrow();
            let primary = key.encode_key();
            let hash = map.hash(&primary);
            if seen.contains(&hash) {
                continue;
            }
            let Some(cursor) = map.get_value_cursor_by_hash(&hash)? else { continue };
            let old = match H::WANTS_VALUES {
                true => Some(V::read(&cursor).map_err(|err| context(err, self.name(), || format!("{key:?}")))?),
                false => None,
            };
            hook.on_remove(&primary, old.as_ref());
            seen.insert(hash.clone());
            hashes.push(hash);
        }
        remove_hashes(&hashes, || self.collection_mut(parent))
    }

    pub(crate) fn update_where_with<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
        mut change: impl FnMut(&mut V::Owned),
        hook: &mut impl EntryHook<V>,
    ) -> Result<usize>
    where
        V::Owned: Clone + PartialEq + Borrow<V::Borrowed>,
    {
        let mut changed = Vec::new();
        self.for_each_entry(parent, |entry| {
            if matches(&entry.key, &entry.value) {
                let mut new = entry.value.clone();
                change(&mut new);
                if new != entry.value {
                    hook.on_change(&entry.primary, &entry.value, &new);
                    changed.push((entry.hash, new));
                }
            }
        })?;
        if changed.is_empty() {
            return Ok(0);
        }
        // the entries are there, keys and all, so only the values are written
        let mut map = self.collection_mut(parent)?;
        for (hash, value) in &changed {
            V::write(value.borrow(), &mut map.put_cursor_by_hash(hash)?)?;
        }
        Ok(changed.len())
    }

    /// Runs `f` on each entry, decoded, in hash order. Empty values are
    /// skipped, as [`Map::iter`] skips them. Everything is read before
    /// `f` returns, so the caller can write afterwards.
    pub(crate) fn for_each_entry<C: Core>(
        &self,
        parent: &ReadHashMap<'_, C>,
        mut f: impl FnMut(Entry<K::Owned, V::Owned>),
    ) -> Result<()> {
        let Some(map) = self.collection(parent)? else { return Ok(()) };
        for kv in map.entries()? {
            let kv = kv?;
            if !has_value(&kv.value_cursor) {
                continue;
            }
            let primary = read_key::<C, [u8]>(self.name(), &kv.key_cursor, &kv.hash)?;
            let key = K::decode_key(primary.clone())
                .map_err(|err| context(err, self.name(), || format!("{:?}", String::from_utf8_lossy(&primary))))?;
            let value = V::read(&kv.value_cursor).map_err(|err| context(err, self.name(), || format!("{key:?}")))?;
            f(Entry { hash: kv.hash, primary, key, value });
        }
        Ok(())
    }
}

impl<K: KeyCodec + ?Sized> Set<K> {
    /// Keeps only the keys for which `keep` returns `true`, removing the
    /// rest, and returns how many were removed. If none were, nothing is
    /// written.
    pub fn retain<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut keep: impl FnMut(&K::Owned) -> bool,
    ) -> Result<usize> {
        let Some(set) = self.collection(parent)? else { return Ok(0) };
        let mut hashes = Vec::new();
        for cursor in set.iter()? {
            let kv = cursor?.read_key_value_pair()?;
            if !keep(&read_key::<C, K>(self.name(), &kv.key_cursor, &kv.hash)?) {
                hashes.push(kv.hash);
            }
        }
        remove_hashes(&hashes, || self.collection_mut(parent))
    }

    /// Removes each of `keys` that's in the set, and returns how many were.
    /// Missing keys are skipped without writing, so if none of them were in
    /// the set, nothing is written.
    pub fn remove_all<C: Core, Q: Borrow<K>>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        keys: impl IntoIterator<Item = Q>,
    ) -> Result<usize> {
        let Some(set) = self.collection(parent)? else { return Ok(0) };
        let mut hashes = BTreeSet::new();
        for key in keys {
            let hash = parent.hash(key.borrow().encode_key());
            if !hashes.contains(&hash) && set.get_slot_by_hash(&hash)?.is_some() {
                hashes.insert(hash);
            }
        }
        remove_hashes(&Vec::from_iter(hashes), || self.collection_mut(parent))
    }
}

/// A collection that removes keys by hash.
trait RemoveByHash {
    fn remove_hash(&mut self, hash: &[u8]) -> Result<bool>;
}

impl<C: Core> RemoveByHash for WriteHashMap<'_, C> {
    fn remove_hash(&mut self, hash: &[u8]) -> Result<bool> {
        self.remove_by_hash(hash)
    }
}

impl<C: Core> RemoveByHash for WriteHashSet<'_, C> {
    fn remove_hash(&mut self, hash: &[u8]) -> Result<bool> {
        self.remove_by_hash(hash)
    }
}

/// Removes the keys with `hashes` from the collection that `open` opens for
/// writing, and returns how many were there. It's only opened if there's
/// something to remove, since opening it is a write.
fn remove_hashes<T: RemoveByHash>(hashes: &[Vec<u8>], open: impl FnOnce() -> Result<T>) -> Result<usize> {
    if hashes.is_empty() {
        return Ok(0);
    }
    let mut collection = open()?;
    let mut removed = 0;
    for hash in hashes {
        if collection.remove_hash(hash)? {
            removed += 1;
        }
    }
    Ok(removed)
}

/// Adds the collection's name and a key to an error from a codec.
fn context(err: Error, name: &str, key: impl FnOnce() -> String) -> Error {
    with_context(err, name, || Some(key()))
}
