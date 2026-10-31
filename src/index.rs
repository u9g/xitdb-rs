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

use crate::bulk::{Entry, EntryHook};
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
/// is, and reads treat an empty set (which other code could write) like a
/// missing one, so [`Index::keys`] only returns keys that some entry has.
/// Since the index is written as hash sets, its name can't be the map's
/// name, or another index's in the same [`IndexedMap`].
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
    ///
    /// Panics if `name` is the map's name, since writing the index would
    /// corrupt the map; in a `const`, that's a compile error.
    pub const fn new(map: Map<K, V>, name: &'static str, key: fn(&V::Borrowed) -> Option<I::Owned>) -> Self {
        assert!(!same_name(map.name(), name), "an index can't be stored under the name of the map it indexes");
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

    /// The distinct index keys that some entry has, in hash order.
    pub fn keys<C: Core>(&self, parent: &ReadHashMap<'_, C>) -> Result<Vec<I::Owned>> {
        let Some(sets) = storage(self.name).collection(parent)? else { return Ok(Vec::new()) };
        let mut keys = Vec::new();
        for kv in sets.entries()? {
            let kv = kv?;
            if !has_value(&kv.value_cursor) {
                continue;
            }
            let key = read_key::<C, I>(self.name, &kv.key_cursor, &kv.hash)?;
            let set = ReadHashSet::new(kv.value_cursor)
                .map_err(|err| with_context(err, self.name, || Some(format!("{key:?}"))))?;
            if set.keys()?.next().is_some() {
                keys.push(key);
            }
        }
        Ok(keys)
    }

    /// Makes the index match the map's current entries, and returns whether
    /// it changed anything. Use it to index existing data, for example in a
    /// migration that adds the index, or to fix an index that went stale.
    ///
    /// It reads the whole map and the whole index, and only writes the
    /// differences (including removing empty sets), so on an index that's
    /// up to date it writes nothing.
    pub fn rebuild<C: Core>(&self, parent: &mut WriteHashMap<'_, C>) -> Result<bool>
    where
        V::Owned: Borrow<V::Borrowed>,
    {
        rebuild(parent, self.map, &[self])
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
/// touch the indexes. Its bulk operations are the [`Map`]'s own, which
/// report each entry they remove or change, and [`IndexedMap::put`] reads
/// the entry it replaces. The index changes are collected, and then each
/// index is opened for writing once, and each of its sets once, only where
/// an entry's index key changed: the primary key is added to the new key's
/// set and removed from the old one's. Like the [`Map`] methods, those that
/// remove or change nothing write nothing, so in [`History::transact`] they
/// don't make the transaction commit.
///
/// Every write checks that the indexes are of this map, and that no two of
/// the map and its indexes share a name, and panics if not.
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
    /// `map` with `indexes`, which must all be indexes of `map`, each under
    /// its own name: writes panic if not.
    pub const fn new(map: Map<K, V>, indexes: &'static [&'static dyn MapIndex<K, V>]) -> Self {
        IndexedMap { map, indexes }
    }

    pub const fn map(&self) -> Map<K, V> {
        self.map
    }

    pub const fn indexes(&self) -> &'static [&'static dyn MapIndex<K, V>] {
        self.indexes
    }

    /// Checks that every index is of this map, and that no two of the map
    /// and its indexes share a name, since writing an index there would
    /// corrupt the other. Trait methods can't run in a `const fn`, so
    /// writes check this rather than [`IndexedMap::new`].
    fn check(&self) {
        let map = self.map.name();
        for (i, index) in self.indexes.iter().enumerate() {
            let name = index.index_name();
            assert_eq!(index.map_name(), map, "index {name:?} is of another map than {map:?}");
            assert_ne!(name, map, "index {name:?} is stored under the name of the map it indexes");
            for other in &self.indexes[..i] {
                assert_ne!(other.index_name(), name, "two indexes of {map:?} are stored under {name:?}");
            }
        }
    }
}

impl<K: KeyCodec + ?Sized, V: ValueCodec> IndexedMap<K, V>
where
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
        let mut updates = self.updates();
        let old = self.map.get(parent, key)?;
        self.map.put(parent, key, value)?;
        updates.record(&key.encode_key(), old.as_ref().map(Borrow::borrow), Some(value));
        updates.write(parent)
    }

    /// Like [`Map::remove`], and removes `key` from its index keys.
    pub fn remove<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K) -> Result<bool> {
        Ok(self.remove_all(parent, [key])? > 0)
    }

    /// Like [`Map::remove_all`].
    pub fn remove_all<C: Core, Q: Borrow<K>>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        keys: impl IntoIterator<Item = Q>,
    ) -> Result<usize> {
        let mut updates = self.updates();
        let removed = self.map.remove_all_with(parent, keys, &mut updates)?;
        updates.write(parent)?;
        Ok(removed)
    }

    /// Like [`Map::retain`].
    pub fn retain<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        keep: impl FnMut(&K::Owned, &V::Owned) -> bool,
    ) -> Result<usize> {
        let mut updates = self.updates();
        let removed = self.map.retain_with(parent, keep, &mut updates)?;
        updates.write(parent)?;
        Ok(removed)
    }

    /// Like [`Map::update_where`].
    pub fn update_where<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        matches: impl FnMut(&K::Owned, &V::Owned) -> bool,
        change: impl FnMut(&mut V::Owned),
    ) -> Result<usize>
    where
        V::Owned: Clone + PartialEq,
    {
        let mut updates = self.updates();
        let changed = self.map.update_where_with(parent, matches, change, &mut updates)?;
        updates.write(parent)?;
        Ok(changed)
    }

    /// Runs [`Index::rebuild`] for every index, reading the map once, and
    /// returns whether any changed.
    pub fn rebuild<C: Core>(&self, parent: &mut WriteHashMap<'_, C>) -> Result<bool> {
        self.check();
        rebuild(parent, self.map, self.indexes)
    }

    fn updates(&self) -> IndexUpdates<K, V> {
        self.check();
        IndexUpdates { indexes: self.indexes, changes: vec![BTreeMap::new(); self.indexes.len()] }
    }
}

/// For each index key, whether each primary key is added to its set
/// (`true`) or removed from it (`false`).
type SetUpdates = BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, bool>>;

/// The index changes of a write through an [`IndexedMap`], collected so
/// each index and each set is opened once.
struct IndexUpdates<K: ?Sized + 'static, V: ValueCodec + 'static> {
    indexes: &'static [&'static dyn MapIndex<K, V>],
    /// One per index.
    changes: Vec<SetUpdates>,
}

impl<K: ?Sized, V: ValueCodec> IndexUpdates<K, V> {
    /// Moves `primary` from the index keys of `old` to those of `new`, in
    /// every index where they differ. A later change of the same primary
    /// key replaces an earlier one.
    fn record(&mut self, primary: &[u8], old: Option<&V::Borrowed>, new: Option<&V::Borrowed>) {
        for (index, changes) in self.indexes.iter().zip(&mut self.changes) {
            let old = old.and_then(|value| index.index_key(value));
            let new = new.and_then(|value| index.index_key(value));
            if old == new {
                continue;
            }
            if let Some(old) = old {
                changes.entry(old).or_default().insert(primary.to_vec(), false);
            }
            if let Some(new) = new {
                changes.entry(new).or_default().insert(primary.to_vec(), true);
            }
        }
    }

    /// Writes the changes that aren't there yet.
    fn write<C: Core>(self, parent: &mut WriteHashMap<'_, C>) -> Result<()> {
        for (index, changes) in self.indexes.iter().zip(self.changes) {
            let name = index.index_name();
            let plan = plan_updates(parent, name, changes)?;
            write_plan(parent, name, plan)?;
        }
        Ok(())
    }
}

impl<K: ?Sized, V: ValueCodec> EntryHook<V> for IndexUpdates<K, V>
where
    V::Owned: Borrow<V::Borrowed>,
{
    const WANTS_VALUES: bool = true;

    fn on_remove(&mut self, primary: &[u8], old: Option<&V::Owned>) {
        self.record(primary, old.map(Borrow::borrow), None);
    }

    fn on_change(&mut self, primary: &[u8], old: &V::Owned, new: &V::Owned) {
        self.record(primary, Some(old.borrow()), Some(new.borrow()));
    }
}

/// The writes to one index key's set.
struct SetChange {
    key: Vec<u8>,
    adds: Vec<Vec<u8>>,
    removes: Vec<Vec<u8>>,
    /// Whether to remove the whole set.
    drop: bool,
}

/// The writes `changes` need in the index under `name`: the primary keys
/// to add that aren't in their sets, and to remove that are.
fn plan_updates<C: Core>(
    parent: &ReadHashMap<'_, C>,
    name: &'static str,
    changes: SetUpdates,
) -> Result<Vec<SetChange>> {
    let mut plan = Vec::new();
    if changes.is_empty() {
        return Ok(plan);
    }
    let sets = storage(name).collection(parent)?;
    for (key, primaries) in changes {
        let set = match &sets {
            Some(sets) => sets.get_set(&key).map_err(|err| context(err, name, &key))?,
            None => None,
        };
        let mut change = SetChange { key, adds: Vec::new(), removes: Vec::new(), drop: false };
        for (primary, add) in primaries {
            let present = match &set {
                Some(set) => set.contains(&primary)?,
                None => false,
            };
            match (add, present) {
                (true, false) => change.adds.push(primary),
                (false, true) => change.removes.push(primary),
                _ => {}
            }
        }
        if !change.adds.is_empty() || !change.removes.is_empty() {
            plan.push(change);
        }
    }
    Ok(plan)
}

/// Writes `plan` to the index under `name`, opening the index once and
/// each set once, and nothing at all if `plan` is empty. A set that's left
/// empty is removed.
fn write_plan<C: Core>(parent: &mut WriteHashMap<'_, C>, name: &'static str, plan: Vec<SetChange>) -> Result<()> {
    if plan.is_empty() {
        return Ok(());
    }
    let mut sets = storage(name).collection_mut(parent)?;
    for change in plan {
        if !change.drop {
            let mut set = sets.put_set(&change.key).map_err(|err| context(err, name, &change.key))?;
            for primary in &change.removes {
                set.remove(primary)?;
            }
            for primary in &change.adds {
                set.put(primary)?;
            }
            if !change.adds.is_empty() || set.keys()?.next().is_some() {
                continue;
            }
        }
        sets.remove(&change.key)?;
    }
    Ok(())
}

/// An index read into memory: index keys and their primary keys, as bytes.
type IndexBytes = BTreeMap<Vec<u8>, BTreeSet<Vec<u8>>>;

/// Rebuilds `indexes` of `map` (see [`Index::rebuild`]), reading the map
/// once for all of them, and returns whether any changed.
fn rebuild<C: Core, K: KeyCodec + ?Sized, V: ValueCodec>(
    parent: &mut WriteHashMap<'_, C>,
    map: Map<K, V>,
    indexes: &[&dyn MapIndex<K, V>],
) -> Result<bool>
where
    V::Owned: Borrow<V::Borrowed>,
{
    let mut wanted = vec![IndexBytes::new(); indexes.len()];
    map.for_each_entry(parent, |Entry { primary, value, .. }| {
        for (index, wanted) in indexes.iter().zip(&mut wanted) {
            if let Some(key) = index.index_key(value.borrow()) {
                wanted.entry(key).or_default().insert(primary.clone());
            }
        }
    })?;

    let mut changed = false;
    for (index, wanted) in indexes.iter().zip(wanted) {
        let name = index.index_name();
        let found = read_index(parent, name)?;
        let mut plan = Vec::new();
        for key in found.keys().filter(|key| !wanted.contains_key(*key)) {
            plan.push(SetChange { key: key.clone(), adds: Vec::new(), removes: Vec::new(), drop: true });
        }
        for (key, primaries) in wanted {
            let stale = found.get(&key).cloned().unwrap_or_default();
            let adds: Vec<_> = primaries.difference(&stale).cloned().collect();
            let removes: Vec<_> = stale.difference(&primaries).cloned().collect();
            if !adds.is_empty() || !removes.is_empty() {
                plan.push(SetChange { key, adds, removes, drop: false });
            }
        }
        changed |= !plan.is_empty();
        write_plan(parent, name, plan)?;
    }
    Ok(changed)
}

/// Every index key in the index stored under `name`, and its primary keys,
/// as bytes. An empty set reads as an empty set of primary keys.
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

/// Whether two names are the same, in a `const fn`.
const fn same_name(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}
