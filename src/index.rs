//! Secondary indexes on typed maps: an [`Index`] looks entries up by a key
//! derived from their values, and an [`IndexedMap`] writes to a map and
//! keeps its indexes up to date in the same transaction.
//!
//! ```
//! use xitdb::{Database, History, Index, IndexedMap, Map};
//!
//! const OWNERS: Map<str, String> = Map::new("owners");
//! // repositories by the first letter of their owner
//! const BY_INITIAL: Index<str, String, str> =
//!     Index::new(OWNERS, "owners-by-initial", |owner| owner.get(..1).map(str::to_owned));
//! const INDEXED_OWNERS: IndexedMap<str, String> = IndexedMap::new(OWNERS, &[&BY_INITIAL]);
//!
//! # fn main() -> xitdb::Result<()> {
//! let db = Database::in_memory()?;
//! let history = History::new(&db)?;
//! history.transact(|moment| {
//!     INDEXED_OWNERS.put(moment, "xitdb", "radar")?;
//!     INDEXED_OWNERS.put(moment, "xitdb-rs", "u9g")
//! })?;
//! assert_eq!(BY_INITIAL.get(&history.latest()?, "r")?, ["xitdb"]);
//! # Ok(())
//! # }
//! ```

use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::bulk::Changed;
use crate::collections::{ReadHashMap, ReadHashSet, WriteHashMap, has_value};
use crate::core::Core;
use crate::error::{Error, Result};
use crate::typed::{KeyCodec, Map, MapIter, ValueCodec, read_key, with_context};

/// A secondary index on a [`Map<K, V>`](Map): a key of type `I` derived
/// from each value, and, for each such key, the primary keys of the
/// entries whose values have it.
///
/// Like a [`Map`], it holds no data, so declare it once as a `const`. The
/// function that derives the index key from a value must not capture
/// anything, so it can be a `fn` pointer; it gets the value as a
/// [`ValueCodec::Borrowed`] (a `str` for `String` values, a `T` for
/// `Json<T>`). An index is one-to-many: any number of entries can share an
/// index key, and [`Index::get`] returns all of them. An entry whose index
/// key is `None` isn't indexed.
///
/// An index is only kept up to date by writes through an [`IndexedMap`]
/// that includes it. Writes through the plain [`Map`], or untyped code,
/// leave it stale, and so does adding an index to a map that already has
/// data: [`Index::rebuild`] makes it match the map again.
///
/// It's stored as a plain hash map under `name` in the same parent as the
/// map, from each index key to a hash set of primary keys, both as their
/// [`KeyCodec`] bytes. An index key's set is removed when its last entry
/// is, so [`Index::keys`] only returns keys that some entry has.
pub struct Index<K: ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> {
    map: Map<K, V>,
    name: &'static str,
    key: fn(&V::Borrowed) -> Option<I::Owned>,
}

impl<K: ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> Clone for Index<K, V, I> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> Copy for Index<K, V, I> {}

impl<K: ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> fmt::Debug for Index<K, V, I> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Index").field("map", &self.map.name()).field("name", &self.name).finish()
    }
}

impl<K: ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> Index<K, V, I> {
    /// An index of `map`, stored under `name`, that indexes each value by
    /// what `key` returns for it.
    pub const fn new(map: Map<K, V>, name: &'static str, key: fn(&V::Borrowed) -> Option<I::Owned>) -> Self {
        Index { map, name, key }
    }

    /// The map this indexes.
    pub const fn map(&self) -> Map<K, V> {
        self.map
    }

    /// The key the index is stored under in its parent.
    pub const fn name(&self) -> &'static str {
        self.name
    }
}

impl<K: KeyCodec + ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> Index<K, V, I>
where
    I::Owned: Borrow<I>,
{
    /// The primary keys of the entries whose index key is `key`, in hash
    /// order. Empty if there are none, or the index is missing.
    pub fn get<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &I) -> Result<Vec<K::Owned>> {
        let Some(sets) = storage(self.name).collection(parent)? else { return Ok(Vec::new()) };
        let set = sets.get_set(key.encode_key());
        let Some(set) = set.map_err(|err| with_context(err, self.name, || Some(format!("{key:?}"))))? else {
            return Ok(Vec::new());
        };
        let mut keys = Vec::new();
        for cursor in set.iter()? {
            let kv = cursor?.read_key_value_pair()?;
            keys.push(read_key::<C, K>(self.name, &kv.key_cursor, &kv.hash)?);
        }
        Ok(keys)
    }

    /// The entries whose index key is `key`, read from the map. A primary
    /// key that's missing from the map, which only a stale index has, is
    /// skipped.
    pub fn entries<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &I) -> Result<Vec<(K::Owned, V::Owned)>>
    where
        K::Owned: Borrow<K>,
    {
        let mut entries = Vec::new();
        for primary in self.get(parent, key)? {
            if let Some(value) = self.map.get(parent, primary.borrow())? {
                entries.push((primary, value));
            }
        }
        Ok(entries)
    }

    /// The distinct index keys, in hash order.
    pub fn keys<C: Core>(&self, parent: &ReadHashMap<'_, C>) -> Result<Vec<I::Owned>> {
        let Some(sets) = storage(self.name).collection(parent)? else { return Ok(Vec::new()) };
        let mut keys = Vec::new();
        for kv in sets.entries()? {
            let kv = kv?;
            if has_value(&kv.value_cursor) {
                keys.push(read_key::<C, I>(self.name, &kv.key_cursor, &kv.hash)?);
            }
        }
        Ok(keys)
    }

    /// Makes the index match the map's current entries, creating it if
    /// it's missing and some entry has an index key, and returns whether it
    /// changed anything. Use it to
    /// index existing data, for example in a migration that adds the
    /// index, or to fix an index that went stale.
    ///
    /// It reads the whole map and the whole index, and only writes the
    /// differences, so on an index that's up to date it writes nothing.
    pub fn rebuild<C: Core>(&self, parent: &mut WriteHashMap<'_, C>) -> Result<bool>
    where
        K::Owned: Borrow<K>,
        V::Owned: Borrow<V::Borrowed>,
    {
        rebuild(parent, self.map, self, self.name)
    }
}

/// An [`Index`] with its index key type erased, so an [`IndexedMap`] can
/// keep indexes with different key types. It's implemented by [`Index`];
/// there's no need to implement it otherwise.
pub trait MapIndex<K: ?Sized, V: ValueCodec> {
    /// The name of the map it indexes.
    fn map_name(&self) -> &'static str;

    /// The key the index is stored under in its parent.
    fn index_name(&self) -> &'static str;

    /// The index key of `value`, encoded, or `None` if it isn't indexed.
    fn index_key(&self, value: &V::Borrowed) -> Option<Vec<u8>>;
}

impl<K: ?Sized, V: ValueCodec, I: KeyCodec + ?Sized> MapIndex<K, V> for Index<K, V, I>
where
    I::Owned: Borrow<I>,
{
    fn map_name(&self) -> &'static str {
        self.map.name()
    }

    fn index_name(&self) -> &'static str {
        self.name
    }

    fn index_key(&self, value: &V::Borrowed) -> Option<Vec<u8>> {
        (self.key)(value).map(|key| key.borrow().encode_key().into_owned())
    }
}

/// A [`Map`] together with its [`Index`]es, whose writes keep every index
/// up to date in the same transaction.
///
/// Reads can go through it or straight through the map, since they don't
/// touch the indexes. Each write reads the entries it changes before
/// writing them (an extra read for [`IndexedMap::put`]), and then writes an
/// index only where an entry's index key changed: adding the primary key
/// to the new key's set and removing it from the old one's. Like the
/// [`Map`] methods, those that remove or change nothing write nothing, so
/// in [`History::transact`] they don't make the transaction commit.
///
/// A value that doesn't decode can't be unindexed, so writing over or
/// removing it through an `IndexedMap` is an
/// [`Error::Decode`](crate::Error::Decode); write through the [`Map`] and
/// then [`IndexedMap::rebuild`].
///
/// [`History::transact`]: crate::History::transact
pub struct IndexedMap<K: ?Sized + 'static, V: ValueCodec + 'static> {
    map: Map<K, V>,
    indexes: &'static [&'static dyn MapIndex<K, V>],
}

impl<K: ?Sized, V: ValueCodec> Clone for IndexedMap<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: ?Sized, V: ValueCodec> Copy for IndexedMap<K, V> {}

impl<K: ?Sized, V: ValueCodec> fmt::Debug for IndexedMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let indexes: Vec<_> = self.indexes.iter().map(|index| index.index_name()).collect();
        f.debug_struct("IndexedMap").field("map", &self.map.name()).field("indexes", &indexes).finish()
    }
}

impl<K: ?Sized, V: ValueCodec> IndexedMap<K, V> {
    /// `map` with `indexes`, which must all be indexes of `map`: writes
    /// panic if one isn't.
    pub const fn new(map: Map<K, V>, indexes: &'static [&'static dyn MapIndex<K, V>]) -> Self {
        IndexedMap { map, indexes }
    }

    pub const fn map(&self) -> Map<K, V> {
        self.map
    }

    pub const fn indexes(&self) -> &'static [&'static dyn MapIndex<K, V>] {
        self.indexes
    }

    /// Checks that every index is of this map. Trait methods can't run in a
    /// `const fn`, so writes check it rather than [`IndexedMap::new`].
    fn check(&self) {
        for index in self.indexes {
            assert_eq!(index.map_name(), self.map.name(), "index {:?} is of another map", index.index_name());
        }
    }
}

impl<K: KeyCodec + ?Sized, V: ValueCodec> IndexedMap<K, V>
where
    K::Owned: Borrow<K>,
    V::Owned: Borrow<V::Borrowed>,
{
    /// Like [`Map::get`].
    pub fn get<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &K) -> Result<Option<V::Owned>> {
        self.map.get(parent, key)
    }

    /// Like [`Map::contains`].
    pub fn contains<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &K) -> Result<bool> {
        self.map.contains(parent, key)
    }

    /// Like [`Map::iter`].
    pub fn iter<'a, C: Core>(&self, parent: &ReadHashMap<'a, C>) -> Result<MapIter<'a, C, K, V>> {
        self.map.iter(parent)
    }

    /// Like [`Map::put`], and moves `key` to `value`'s index keys.
    pub fn put<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K, value: &V::Borrowed) -> Result<()> {
        self.check();
        let old = self.map.get(parent, key)?;
        self.map.put(parent, key, value)?;
        self.reindex(parent, key, old.as_ref().map(Borrow::borrow), Some(value))
    }

    /// Like [`Map::remove`], and removes `key` from its index keys.
    pub fn remove<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K) -> Result<bool> {
        self.check();
        let Some(old) = self.map.get(parent, key)? else { return Ok(false) };
        self.map.remove(parent, key)?;
        self.reindex(parent, key, Some(old.borrow()), None)?;
        Ok(true)
    }

    /// Like [`Map::remove_all`].
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

    /// Like [`Map::retain`].
    pub fn retain<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut keep: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<usize> {
        self.check();
        let removed = self.map.entries_where(parent, |key, value| !keep(key, value))?;
        for (key, old) in &removed {
            self.map.remove(parent, key.borrow())?;
            self.reindex(parent, key.borrow(), Some(old.borrow()), None)?;
        }
        Ok(removed.len())
    }

    /// Like [`Map::update_where`].
    pub fn update_where<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        mut matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
        mut change: impl FnMut(&mut V::Owned),
    ) -> Result<usize>
    where
        V::Owned: Clone + PartialEq,
    {
        self.check();
        let changed = self.map.changed_where(parent, &mut matches, &mut change)?;
        for Changed { key, old, new } in &changed {
            self.map.put(parent, key.borrow(), new.borrow())?;
            self.reindex(parent, key.borrow(), Some(old.borrow()), Some(new.borrow()))?;
        }
        Ok(changed.len())
    }

    /// Runs [`Index::rebuild`] for every index, and returns whether any
    /// changed.
    pub fn rebuild<C: Core>(&self, parent: &mut WriteHashMap<'_, C>) -> Result<bool> {
        self.check();
        let mut changed = false;
        for index in self.indexes {
            changed |= rebuild(parent, self.map, *index, index.index_name())?;
        }
        Ok(changed)
    }

    /// Moves `key` from the index keys of `old` to those of `new`, in every
    /// index where they differ.
    fn reindex<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        key: &K,
        old: Option<&V::Borrowed>,
        new: Option<&V::Borrowed>,
    ) -> Result<()> {
        let primary = key.encode_key();
        for index in self.indexes {
            let old = old.and_then(|value| index.index_key(value));
            let new = new.and_then(|value| index.index_key(value));
            if old == new {
                continue;
            }
            if let Some(old) = old {
                unindex(parent, index.index_name(), &old, &primary)?;
            }
            if let Some(new) = new {
                add_to_index(parent, index.index_name(), &new, &primary)?;
            }
        }
        Ok(())
    }
}

/// [`Index::rebuild`], for any [`MapIndex`] of `map` stored under `name`.
fn rebuild<C: Core, K: KeyCodec + ?Sized, V: ValueCodec>(
    parent: &mut WriteHashMap<'_, C>,
    map: Map<K, V>,
    index: &dyn MapIndex<K, V>,
    name: &'static str,
) -> Result<bool>
where
    K::Owned: Borrow<K>,
    V::Owned: Borrow<V::Borrowed>,
{
    let mut wanted = IndexBytes::new();
    for entry in map.iter(parent)? {
        let (primary, value) = entry?;
        if let Some(key) = index.index_key(value.borrow()) {
            wanted.entry(key).or_default().insert(primary.borrow().encode_key().into_owned());
        }
    }
    let found = read_index(parent, name)?;
    if found == wanted {
        return Ok(false);
    }

    let mut sets = storage(name).collection_mut(parent)?;
    for key in found.keys().filter(|key| !wanted.contains_key(*key)) {
        sets.remove(key)?;
    }
    for (key, primaries) in &wanted {
        let stale = found.get(key);
        if stale == Some(primaries) {
            continue;
        }
        let mut set = sets.put_set(key).map_err(|err| context(err, name, key))?;
        for primary in stale.into_iter().flatten().filter(|primary| !primaries.contains(*primary)) {
            set.remove(primary)?;
        }
        for primary in primaries.iter().filter(|primary| !stale.is_some_and(|stale| stale.contains(*primary))) {
            set.put(primary)?;
        }
    }
    Ok(true)
}

/// An index read into memory: index keys and their primary keys, as bytes.
type IndexBytes = BTreeMap<Vec<u8>, BTreeSet<Vec<u8>>>;

/// Every index key in the index stored under `name`, and its primary keys,
/// as bytes.
fn read_index<C: Core>(parent: &ReadHashMap<'_, C>, name: &'static str) -> Result<IndexBytes> {
    let mut found = BTreeMap::new();
    let Some(sets) = storage(name).collection(parent)? else { return Ok(found) };
    for kv in sets.entries()? {
        let kv = kv?;
        let key = read_key::<C, [u8]>(name, &kv.key_cursor, &kv.hash)?;
        let mut primaries = BTreeSet::new();
        if has_value(&kv.value_cursor) {
            let set = ReadHashSet::new(kv.value_cursor).map_err(|err| context(err, name, &key))?;
            for cursor in set.iter()? {
                let kv = cursor?.read_key_value_pair()?;
                primaries.insert(read_key::<C, [u8]>(name, &kv.key_cursor, &kv.hash)?);
            }
        }
        found.insert(key, primaries);
    }
    Ok(found)
}

/// Where the index under `name` is stored: a map from index keys to sets
/// of primary keys, which [`Map`]'s checks open as a hash map.
fn storage(name: &'static str) -> Map<[u8], ()> {
    Map::new(name)
}

/// Adds the index's name and an index key to an error.
fn context(err: Error, name: &str, key: &[u8]) -> Error {
    with_context(err, name, || Some(format!("{:?}", String::from_utf8_lossy(key))))
}

/// Adds `primary` to the set of `key` in the index stored under `name`,
/// unless it's there already.
fn add_to_index<C: Core>(
    parent: &mut WriteHashMap<'_, C>,
    name: &'static str,
    key: &[u8],
    primary: &[u8],
) -> Result<()> {
    let storage = storage(name);
    let context = |err| context(err, name, key);
    if let Some(sets) = storage.collection(parent)? {
        if let Some(set) = sets.get_set(key).map_err(context)? {
            if set.contains(primary)? {
                return Ok(());
            }
        }
    }
    storage.collection_mut(parent)?.put_set(key).map_err(context)?.put(primary)
}

/// Removes `primary` from the set of `key` in the index stored under
/// `name`, and the set if that leaves it empty. Writes nothing if it isn't
/// there.
fn unindex<C: Core>(parent: &mut WriteHashMap<'_, C>, name: &'static str, key: &[u8], primary: &[u8]) -> Result<()> {
    let storage = storage(name);
    let context = |err| context(err, name, key);
    let Some(sets) = storage.collection(parent)? else { return Ok(()) };
    let Some(set) = sets.get_set(key).map_err(context)? else { return Ok(()) };
    if !set.contains(primary)? {
        return Ok(());
    }
    let mut sets = storage.collection_mut(parent)?;
    let mut set = sets.put_set(key).map_err(context)?;
    set.remove(primary)?;
    if set.keys()?.next().is_none() {
        sets.remove(key)?;
    }
    Ok(())
}
