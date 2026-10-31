//! Typed wrappers around cursors for each data structure.
//!
//! Each `ReadX` wrapper only reads. Each `WriteX` wrapper dereferences to
//! its `ReadX` counterpart, viewing the same cursor it writes through, so
//! reads always see its latest writes.

use std::ops::{Deref, DerefMut};

use crate::core::Core;
use crate::cursor::{CursorIterator, ReadCursor, ReadKvPairCursor, WriteCursor};
use crate::data::{Bytes, Data};
use crate::error::{Error, Result};
use crate::path::{HashMapGetTarget, PathPart, SortedMapGetTarget};
use crate::slot::{Slot, Tag};

/// Implements a zero-cost cast from a reference to the wrapped type to a
/// reference to the wrapper. The wrapper must be `#[repr(transparent)]`.
macro_rules! ref_cast {
    ($wrapper:ident, $inner:ident) => {
        const _: () = assert!(
            std::mem::size_of::<$wrapper<'static, crate::CoreMemory>>()
                == std::mem::size_of::<$inner<'static, crate::CoreMemory>>()
        );

        impl<'a, C: Core> $wrapper<'a, C> {
            #[allow(dead_code)]
            fn from_ref<'r>(inner: &'r $inner<'a, C>) -> &'r $wrapper<'a, C> {
                // SAFETY: the wrapper is repr(transparent) over the inner type
                unsafe { &*(inner as *const $inner<'a, C> as *const $wrapper<'a, C>) }
            }

            #[allow(dead_code)]
            fn from_mut<'r>(inner: &'r mut $inner<'a, C>) -> &'r mut $wrapper<'a, C> {
                // SAFETY: the wrapper is repr(transparent) over the inner type
                unsafe { &mut *(inner as *mut $inner<'a, C> as *mut $wrapper<'a, C>) }
            }
        }
    };
}

/// Checks a cursor's tag before wrapping it.
fn check_tag<C: Core>(cursor: &ReadCursor<'_, C>, allowed: &[Tag]) -> Result<()> {
    let tag = cursor.resolved()?.slot.tag;
    if tag == Tag::None || allowed.contains(&tag) { Ok(()) } else { Err(Error::UnexpectedTag) }
}

/// Checks that an existing value can be opened as a collection with `tag`
/// by a `put_map`-style method: it must be missing, empty, or exactly that
/// kind of collection.
fn check_put_tag(slot: Option<Slot>, tag: Tag) -> Result<()> {
    match slot {
        Some(slot) if slot.tag != Tag::None && slot.tag != tag => Err(Error::UnexpectedTag),
        _ => Ok(()),
    }
}

/// Maps "key not found" to `false`, as remove methods report it.
fn removed(result: Result<WriteCursor<'_, impl Core>>) -> Result<bool> {
    match result {
        Ok(_) => Ok(true),
        Err(Error::KeyNotFound) => Ok(false),
        Err(err) => Err(err),
    }
}

/// Iterates over the key-value pairs of a map, yielding cursors to each
/// pair's key and value. Made by [`ReadHashMap::entries`] and
/// [`ReadSortedMap::entries`].
pub struct KvPairIterator<'a, C: Core> {
    iter: CursorIterator<'a, C>,
}

impl<'a, C: Core> Iterator for KvPairIterator<'a, C> {
    type Item = Result<ReadKvPairCursor<'a, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|cursor| cursor?.read_key_value_pair())
    }
}

/// Iterates over the keys of a set, yielding cursors to them. Made by
/// [`ReadHashSet::keys`] and [`ReadSortedSet::keys`].
pub struct KeyIterator<'a, C: Core> {
    pairs: KvPairIterator<'a, C>,
}

impl<'a, C: Core> Iterator for KeyIterator<'a, C> {
    type Item = Result<ReadCursor<'a, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.pairs.next().map(|kv| Ok(kv?.key_cursor))
    }
}

impl<'a, C: Core> From<WriteCursor<'a, C>> for ReadCursor<'a, C> {
    fn from(cursor: WriteCursor<'a, C>) -> Self {
        cursor.read
    }
}

impl<'a, C: Core> From<&WriteCursor<'a, C>> for ReadCursor<'a, C> {
    fn from(cursor: &WriteCursor<'a, C>) -> Self {
        cursor.read.clone()
    }
}

impl<'a, C: Core> From<&ReadCursor<'a, C>> for ReadCursor<'a, C> {
    fn from(cursor: &ReadCursor<'a, C>) -> Self {
        cursor.clone()
    }
}

// ArrayList

/// A growable array, read-only.
#[repr(transparent)]
pub struct ReadArrayList<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadArrayList, ReadCursor);

impl<'a, C: Core> ReadArrayList<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::ArrayList])?;
        Ok(ReadArrayList { cursor })
    }

    pub fn cursor(&self) -> &ReadCursor<'a, C> {
        &self.cursor
    }

    pub fn slot(&self) -> Result<Slot> {
        self.cursor.slot()
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }

    /// The item at `index`, or `None` if it's out of range. Negative
    /// indexes count from the end.
    pub fn get_cursor(&self, index: i64) -> Result<Option<ReadCursor<'a, C>>> {
        self.cursor.read_path(&[PathPart::ArrayListGet(index)])
    }

    pub fn get_slot(&self, index: i64) -> Result<Option<Slot>> {
        self.cursor.read_path_slot(&[PathPart::ArrayListGet(index)])
    }

    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        self.cursor.iter()
    }

    /// Iterates starting at `index`, seeking straight to it instead of
    /// walking from the front. Negative indexes count from the end.
    pub fn iter_from(&self, index: i64) -> Result<CursorIterator<'a, C>> {
        CursorIterator::array_list_from(&self.cursor, index)
    }
}

/// A growable array.
#[repr(transparent)]
pub struct WriteArrayList<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}
ref_cast!(WriteArrayList, WriteCursor);

impl<'a, C: Core> Deref for WriteArrayList<'a, C> {
    type Target = ReadArrayList<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadArrayList::from_ref(&self.cursor.read)
    }
}

impl<'a, C: Core> WriteArrayList<'a, C> {
    /// Initializes an array list at the cursor, unless there already is one.
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        Ok(WriteArrayList { cursor: cursor.write_path(&[PathPart::ArrayListInit])? })
    }

    pub fn write_cursor(&self) -> &WriteCursor<'a, C> {
        &self.cursor
    }

    pub fn put<'d>(&mut self, index: i64, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[PathPart::ArrayListGet(index), PathPart::WriteData(&data)])?;
        Ok(())
    }

    pub fn put_cursor(&mut self, index: i64) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::ArrayListGet(index)])
    }

    pub fn append<'d>(&mut self, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[PathPart::ArrayListAppend, PathPart::WriteData(&data)])?;
        Ok(())
    }

    pub fn append_cursor(&mut self) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::ArrayListAppend])
    }

    /// Returns the hash map at `index`, initializing it first if the item
    /// is empty. An existing map keeps its contents. Anything else at
    /// `index`, including a hash set or a counted map, is an
    /// [`Error::UnexpectedTag`], and an index out of range is an
    /// [`Error::KeyNotFound`]; either way nothing is written.
    ///
    /// The map can only be written to within the transaction that made it,
    /// so this must run inside one (for example in
    /// [`WriteArrayList::append_context`]). On a top-level list outside a
    /// transaction, it returns [`Error::ExpectedTxStart`] without writing
    /// anything.
    pub fn put_map(&mut self, index: i64) -> Result<WriteHashMap<'a, C>> {
        let init = PathPart::HashMapInit { counted: false, set: false };
        Ok(WriteHashMap { cursor: self.put_collection(index, init, Tag::HashMap)? })
    }

    /// Like [`WriteArrayList::put_map`], for a hash set.
    pub fn put_set(&mut self, index: i64) -> Result<WriteHashSet<'a, C>> {
        let init = PathPart::HashMapInit { counted: false, set: true };
        Ok(WriteHashSet { cursor: self.put_collection(index, init, Tag::HashSet)? })
    }

    /// Like [`WriteArrayList::put_map`], for an array list.
    pub fn put_list(&mut self, index: i64) -> Result<WriteArrayList<'a, C>> {
        Ok(WriteArrayList { cursor: self.put_collection(index, PathPart::ArrayListInit, Tag::ArrayList)? })
    }

    /// Appends a new, empty hash map and returns it, in one write. Like
    /// [`WriteArrayList::put_map`], this must run inside a transaction; on
    /// a top-level list outside one, it returns [`Error::ExpectedTxStart`]
    /// without appending anything.
    pub fn append_map(&mut self) -> Result<WriteHashMap<'a, C>> {
        let init = PathPart::HashMapInit { counted: false, set: false };
        Ok(WriteHashMap { cursor: self.append_collection(init)? })
    }

    /// Like [`WriteArrayList::append_map`], for a hash set.
    pub fn append_set(&mut self) -> Result<WriteHashSet<'a, C>> {
        let init = PathPart::HashMapInit { counted: false, set: true };
        Ok(WriteHashSet { cursor: self.append_collection(init)? })
    }

    /// Like [`WriteArrayList::append_map`], for an array list.
    pub fn append_list(&mut self) -> Result<WriteArrayList<'a, C>> {
        Ok(WriteArrayList { cursor: self.append_collection(PathPart::ArrayListInit)? })
    }

    // checks the existing item before writing, then initializes the
    // collection in the same write path as the lookup
    fn put_collection(&mut self, index: i64, init: PathPart<'_>, tag: Tag) -> Result<WriteCursor<'a, C>> {
        self.cursor.check_in_transaction()?;
        check_put_tag(self.get_slot(index)?, tag)?;
        self.cursor.write_path(&[PathPart::ArrayListGet(index), init])
    }

    fn append_collection(&mut self, init: PathPart<'_>) -> Result<WriteCursor<'a, C>> {
        self.cursor.check_in_transaction()?;
        self.cursor.write_path(&[PathPart::ArrayListAppend, init])
    }

    /// Appends `data`, then runs `f` with a cursor to the new item, in one
    /// write. On a top-level history, this is a transaction: `data` is
    /// usually the previous moment, which `f` then changes, and if `f`
    /// fails, the transaction is discarded.
    pub fn append_context<'d>(
        &mut self,
        data: impl Into<Data<'d>>,
        f: impl FnOnce(&mut WriteCursor<'a, C>) -> Result<()>,
    ) -> Result<()> {
        let data = data.into();
        self.cursor.write_path_context(&[PathPart::ArrayListAppend, PathPart::WriteData(&data)], f)?;
        Ok(())
    }

    /// Shrinks the list to its first `size` items.
    pub fn slice(&mut self, size: i64) -> Result<()> {
        self.cursor.write_path(&[PathPart::ArrayListSlice(size)])?;
        Ok(())
    }
}

// LinkedArrayList

/// An array that can also be efficiently sliced, concatenated, and
/// inserted into, read-only.
#[repr(transparent)]
pub struct ReadLinkedArrayList<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadLinkedArrayList, ReadCursor);

impl<'a, C: Core> ReadLinkedArrayList<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::LinkedArrayList])?;
        Ok(ReadLinkedArrayList { cursor })
    }

    pub fn cursor(&self) -> &ReadCursor<'a, C> {
        &self.cursor
    }

    pub fn slot(&self) -> Result<Slot> {
        self.cursor.slot()
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }

    pub fn get_cursor(&self, index: i64) -> Result<Option<ReadCursor<'a, C>>> {
        self.cursor.read_path(&[PathPart::LinkedArrayListGet(index)])
    }

    pub fn get_slot(&self, index: i64) -> Result<Option<Slot>> {
        self.cursor.read_path_slot(&[PathPart::LinkedArrayListGet(index)])
    }

    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        self.cursor.iter()
    }

    /// Iterates starting at `index`, seeking straight to it instead of
    /// walking from the front. Negative indexes count from the end.
    pub fn iter_from(&self, index: i64) -> Result<CursorIterator<'a, C>> {
        CursorIterator::linked_array_list_from(&self.cursor, index)
    }
}

/// An array that can also be efficiently sliced, concatenated, and
/// inserted into.
#[repr(transparent)]
pub struct WriteLinkedArrayList<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}
ref_cast!(WriteLinkedArrayList, WriteCursor);

impl<'a, C: Core> Deref for WriteLinkedArrayList<'a, C> {
    type Target = ReadLinkedArrayList<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadLinkedArrayList::from_ref(&self.cursor.read)
    }
}

impl<'a, C: Core> WriteLinkedArrayList<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        Ok(WriteLinkedArrayList { cursor: cursor.write_path(&[PathPart::LinkedArrayListInit])? })
    }

    pub fn write_cursor(&self) -> &WriteCursor<'a, C> {
        &self.cursor
    }

    pub fn put<'d>(&mut self, index: i64, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[PathPart::LinkedArrayListGet(index), PathPart::WriteData(&data)])?;
        Ok(())
    }

    pub fn put_cursor(&mut self, index: i64) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::LinkedArrayListGet(index)])
    }

    pub fn append<'d>(&mut self, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[PathPart::LinkedArrayListAppend, PathPart::WriteData(&data)])?;
        Ok(())
    }

    pub fn append_cursor(&mut self) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::LinkedArrayListAppend])
    }

    /// Keeps the `size` items starting at `offset`.
    pub fn slice(&mut self, offset: i64, size: i64) -> Result<()> {
        self.cursor.write_path(&[PathPart::LinkedArrayListSlice { offset, size }])?;
        Ok(())
    }

    /// Appends the items of another linked array list.
    pub fn concat(&mut self, list: Slot) -> Result<()> {
        self.cursor.write_path(&[PathPart::LinkedArrayListConcat(list)])?;
        Ok(())
    }

    /// Inserts `data` before the item at `index`.
    pub fn insert<'d>(&mut self, index: i64, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[PathPart::LinkedArrayListInsert(index), PathPart::WriteData(&data)])?;
        Ok(())
    }

    pub fn insert_cursor(&mut self, index: i64) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::LinkedArrayListInsert(index)])
    }

    pub fn remove(&mut self, index: i64) -> Result<()> {
        self.cursor.write_path(&[PathPart::LinkedArrayListRemove(index)])?;
        Ok(())
    }
}

// HashMap

/// Key-value pairs stored by the hash of their key, read-only.
#[repr(transparent)]
pub struct ReadHashMap<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadHashMap, ReadCursor);

impl<'a, C: Core> ReadHashMap<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::HashMap, Tag::HashSet])?;
        Ok(ReadHashMap { cursor })
    }

    pub fn cursor(&self) -> &ReadCursor<'a, C> {
        &self.cursor
    }

    pub fn slot(&self) -> Result<Slot> {
        self.cursor.slot()
    }

    /// Iterates over cursors to the key-value pairs.
    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        self.cursor.iter()
    }

    /// Like [`ReadHashMap::iter`], but yields the key and value cursors of
    /// each pair, as [`ReadCursor::read_key_value_pair`] returns them.
    pub fn entries(&self) -> Result<KvPairIterator<'a, C>> {
        Ok(KvPairIterator { iter: self.cursor.iter()? })
    }

    fn hash(&self, key: impl AsRef<[u8]>) -> Vec<u8> {
        self.cursor.db.digest(key.as_ref())
    }

    // the value of `key`, or `None` if it isn't in the map or its value is
    // empty. the typed getters treat both the same way.
    fn get_value_cursor(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadCursor<'a, C>>> {
        Ok(self.get_cursor(key)?.filter(|cursor| cursor.slot_ptr.slot.tag != Tag::None))
    }

    /// The hash map at `key`. Like all the typed getters, this returns
    /// `None` if `key` isn't in the map or its value is empty (written as
    /// [`Data::None`]), and [`Error::UnexpectedTag`] if the value is of
    /// another type.
    ///
    /// This accepts what [`ReadHashMap::new`] accepts, so a hash set reads
    /// as a map whose values are empty, but a counted map is an
    /// [`Error::UnexpectedTag`]; read one with
    /// `ReadCountedHashMap::new(map.get_cursor(key)?.unwrap())`.
    pub fn get_map(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadHashMap<'a, C>>> {
        self.get_value_cursor(key)?.map(ReadHashMap::new).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for a hash set. A counted set is an
    /// [`Error::UnexpectedTag`].
    pub fn get_set(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadHashSet<'a, C>>> {
        self.get_value_cursor(key)?.map(ReadHashSet::new).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for an array list.
    pub fn get_list(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadArrayList<'a, C>>> {
        self.get_value_cursor(key)?.map(ReadArrayList::new).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for a byte array. See
    /// [`ReadCursor::read_bytes`] for `max_size`.
    pub fn get_bytes(&self, key: impl AsRef<[u8]>, max_size: Option<u64>) -> Result<Option<Vec<u8>>> {
        self.get_value_cursor(key)?.map(|cursor| cursor.read_bytes(max_size)).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for a string. Invalid UTF-8 is an
    /// [`Error::InvalidUtf8`] (see [`ReadCursor::read_string`]).
    pub fn get_string(&self, key: impl AsRef<[u8]>, max_size: Option<u64>) -> Result<Option<String>> {
        self.get_value_cursor(key)?.map(|cursor| cursor.read_string(max_size)).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for a signed integer.
    pub fn get_int(&self, key: impl AsRef<[u8]>) -> Result<Option<i64>> {
        self.get_value_cursor(key)?.map(|cursor| cursor.read_int()).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for an unsigned integer.
    pub fn get_uint(&self, key: impl AsRef<[u8]>) -> Result<Option<u64>> {
        self.get_value_cursor(key)?.map(|cursor| cursor.read_uint()).transpose()
    }

    /// Like [`ReadHashMap::get_map`], for a float.
    pub fn get_float(&self, key: impl AsRef<[u8]>) -> Result<Option<f64>> {
        self.get_value_cursor(key)?.map(|cursor| cursor.read_float()).transpose()
    }

    /// The value of `key`, or `None` if it isn't in the map.
    pub fn get_cursor(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadCursor<'a, C>>> {
        self.get_cursor_by_hash(&self.hash(key))
    }

    pub fn get_slot(&self, key: impl AsRef<[u8]>) -> Result<Option<Slot>> {
        self.get_slot_by_hash(&self.hash(key))
    }

    /// The stored key, or `None` if it isn't in the map.
    pub fn get_key_cursor(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadCursor<'a, C>>> {
        self.get_key_cursor_by_hash(&self.hash(key))
    }

    pub fn get_key_slot(&self, key: impl AsRef<[u8]>) -> Result<Option<Slot>> {
        self.get_key_slot_by_hash(&self.hash(key))
    }

    pub fn get_key_value_pair(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadKvPairCursor<'a, C>>> {
        self.get_key_value_pair_by_hash(&self.hash(key))
    }

    pub fn get_cursor_by_hash(&self, hash: &[u8]) -> Result<Option<ReadCursor<'a, C>>> {
        self.cursor.read_path(&[PathPart::HashMapGet(HashMapGetTarget::Value(hash))])
    }

    pub fn get_slot_by_hash(&self, hash: &[u8]) -> Result<Option<Slot>> {
        self.cursor.read_path_slot(&[PathPart::HashMapGet(HashMapGetTarget::Value(hash))])
    }

    pub fn get_key_cursor_by_hash(&self, hash: &[u8]) -> Result<Option<ReadCursor<'a, C>>> {
        self.cursor.read_path(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))])
    }

    pub fn get_key_slot_by_hash(&self, hash: &[u8]) -> Result<Option<Slot>> {
        self.cursor.read_path_slot(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))])
    }

    pub fn get_key_value_pair_by_hash(&self, hash: &[u8]) -> Result<Option<ReadKvPairCursor<'a, C>>> {
        match self.cursor.read_path(&[PathPart::HashMapGet(HashMapGetTarget::KvPair(hash))])? {
            Some(cursor) => Ok(Some(cursor.read_key_value_pair()?)),
            None => Ok(None),
        }
    }
}

/// Key-value pairs stored by the hash of their key.
#[repr(transparent)]
pub struct WriteHashMap<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}
ref_cast!(WriteHashMap, WriteCursor);

impl<'a, C: Core> Deref for WriteHashMap<'a, C> {
    type Target = ReadHashMap<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadHashMap::from_ref(&self.cursor.read)
    }
}

impl<'a, C: Core> WriteHashMap<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        Ok(WriteHashMap { cursor: cursor.write_path(&[PathPart::HashMapInit { counted: false, set: false }])? })
    }

    pub fn write_cursor(&self) -> &WriteCursor<'a, C> {
        &self.cursor
    }

    /// Sets `key` to `data`.
    pub fn put<'d>(&mut self, key: impl AsRef<[u8]>, data: impl Into<Data<'d>>) -> Result<()> {
        let key = key.as_ref();
        self.put_key_and_value(&self.hash(key), Data::bytes(key), data.into())
    }

    /// Stores `key` and returns a cursor to its value.
    pub fn put_cursor(&mut self, key: impl AsRef<[u8]>) -> Result<WriteCursor<'a, C>> {
        let key = key.as_ref();
        let hash = self.hash(key);
        self.put_key_by_hash(&hash, Data::bytes(key))?;
        self.put_cursor_by_hash(&hash)
    }

    /// Returns the hash map at `key`, first storing `key` and initializing
    /// the map if `key` is missing or its value is empty. An existing map
    /// keeps its contents. Any other value, including a hash set or a
    /// counted map, is an [`Error::UnexpectedTag`], and nothing is written.
    /// The key and the map are written in one write.
    ///
    /// The map can only be written to within the transaction that made it,
    /// so this must run inside one (for example in
    /// [`WriteArrayList::append_context`]). On a top-level map outside a
    /// transaction, it returns [`Error::ExpectedTxStart`] without writing
    /// anything.
    pub fn put_map(&mut self, key: impl AsRef<[u8]>) -> Result<WriteHashMap<'a, C>> {
        let init = PathPart::HashMapInit { counted: false, set: false };
        Ok(WriteHashMap { cursor: self.put_collection(key.as_ref(), init, Tag::HashMap)? })
    }

    /// Like [`WriteHashMap::put_map`], for a hash set.
    pub fn put_set(&mut self, key: impl AsRef<[u8]>) -> Result<WriteHashSet<'a, C>> {
        let init = PathPart::HashMapInit { counted: false, set: true };
        Ok(WriteHashSet { cursor: self.put_collection(key.as_ref(), init, Tag::HashSet)? })
    }

    /// Like [`WriteHashMap::put_map`], for an array list.
    pub fn put_list(&mut self, key: impl AsRef<[u8]>) -> Result<WriteArrayList<'a, C>> {
        Ok(WriteArrayList { cursor: self.put_collection(key.as_ref(), PathPart::ArrayListInit, Tag::ArrayList)? })
    }

    /// Sets the stored key of `key` to `data`, if it isn't set yet.
    pub fn put_key<'d>(&mut self, key: impl AsRef<[u8]>, data: impl Into<Data<'d>>) -> Result<()> {
        let hash = self.hash(key);
        self.put_key_by_hash(&hash, data)
    }

    pub fn put_key_cursor(&mut self, key: impl AsRef<[u8]>) -> Result<WriteCursor<'a, C>> {
        let hash = self.hash(key);
        self.put_key_cursor_by_hash(&hash)
    }

    /// Removes `key`, returning whether it was in the map.
    pub fn remove(&mut self, key: impl AsRef<[u8]>) -> Result<bool> {
        let hash = self.hash(key);
        self.remove_by_hash(&hash)
    }

    /// Like [`WriteHashMap::put`], but the stored key keeps the format tag
    /// of `key`.
    pub fn put_bytes<'d>(&mut self, key: Bytes<'_>, data: impl Into<Data<'d>>) -> Result<()> {
        let hash = self.hash(&key.value);
        self.put_key_and_value(&hash, Data::Bytes(key), data.into())
    }

    pub fn put_cursor_bytes(&mut self, key: Bytes<'_>) -> Result<WriteCursor<'a, C>> {
        let hash = self.hash(&key.value);
        self.put_key_by_hash(&hash, Data::Bytes(key))?;
        self.put_cursor_by_hash(&hash)
    }

    pub fn put_by_hash<'d>(&mut self, hash: &[u8], data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[PathPart::HashMapGet(HashMapGetTarget::Value(hash)), PathPart::WriteData(&data)])?;
        Ok(())
    }

    pub fn put_cursor_by_hash(&mut self, hash: &[u8]) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::HashMapGet(HashMapGetTarget::Value(hash))])
    }

    pub fn put_key_by_hash<'d>(&mut self, hash: &[u8], data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        // the key is written in the same write as the lookup, so a root map
        // does both in one transaction. keys are only written if empty,
        // because their value should always be the same at a given hash.
        self.cursor.write_path_context(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))], |cursor| {
            cursor.write_if_empty(data)
        })?;
        Ok(())
    }

    pub fn put_key_cursor_by_hash(&mut self, hash: &[u8]) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))])
    }

    pub fn remove_by_hash(&mut self, hash: &[u8]) -> Result<bool> {
        removed(self.cursor.write_path(&[PathPart::HashMapRemove(hash)]))
    }

    // checks the existing value before writing, then writes the key (if
    // it's empty) and initializes the collection in one write
    fn put_collection(&mut self, key: &[u8], init: PathPart<'_>, tag: Tag) -> Result<WriteCursor<'a, C>> {
        self.cursor.check_in_transaction()?;
        let hash = self.hash(key);
        check_put_tag(self.get_slot_by_hash(&hash)?, tag)?;
        let mut collection = None;
        self.cursor.write_path_context(&[PathPart::HashMapGet(HashMapGetTarget::KvPair(&hash))], |cursor| {
            let mut kv = cursor.read_key_value_pair()?;
            kv.key_cursor.write_if_empty(Data::bytes(key))?;
            collection = Some(kv.value_cursor.write_path(&[init])?);
            Ok(())
        })?;
        Ok(collection.expect("the context function ran"))
    }

    // writes the key (if it's empty) and the value in one write, so a root
    // map does it in one transaction
    fn put_key_and_value(&mut self, hash: &[u8], key: Data<'_>, data: Data<'_>) -> Result<()> {
        self.cursor.write_path_context(&[PathPart::HashMapGet(HashMapGetTarget::KvPair(hash))], |cursor| {
            let mut kv = cursor.read_key_value_pair()?;
            kv.key_cursor.write_if_empty(key)?;
            kv.value_cursor.write(data)
        })?;
        Ok(())
    }
}

/// A [`ReadHashMap`] that maintains a count of its contents.
#[repr(transparent)]
pub struct ReadCountedHashMap<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadCountedHashMap, ReadCursor);

impl<'a, C: Core> Deref for ReadCountedHashMap<'a, C> {
    type Target = ReadHashMap<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadHashMap::from_ref(&self.cursor)
    }
}

impl<'a, C: Core> ReadCountedHashMap<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::CountedHashMap, Tag::CountedHashSet])?;
        Ok(ReadCountedHashMap { cursor })
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }
}

/// A [`WriteHashMap`] that maintains a count of its contents.
#[repr(transparent)]
pub struct WriteCountedHashMap<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}

impl<'a, C: Core> Deref for WriteCountedHashMap<'a, C> {
    type Target = WriteHashMap<'a, C>;
    fn deref(&self) -> &Self::Target {
        WriteHashMap::from_ref(&self.cursor)
    }
}

impl<C: Core> DerefMut for WriteCountedHashMap<'_, C> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        WriteHashMap::from_mut(&mut self.cursor)
    }
}

impl<'a, C: Core> WriteCountedHashMap<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        check_tag(cursor, &[Tag::CountedHashMap, Tag::CountedHashSet])?;
        Ok(WriteCountedHashMap { cursor: cursor.write_path(&[PathPart::HashMapInit { counted: true, set: false }])? })
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }
}

// HashSet

/// Keys stored by their hash, read-only. Useful for checking membership.
#[repr(transparent)]
pub struct ReadHashSet<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadHashSet, ReadCursor);

impl<'a, C: Core> ReadHashSet<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::HashMap, Tag::HashSet])?;
        Ok(ReadHashSet { cursor })
    }

    pub fn cursor(&self) -> &ReadCursor<'a, C> {
        &self.cursor
    }

    pub fn slot(&self) -> Result<Slot> {
        self.cursor.slot()
    }

    /// Iterates over cursors to the key-value pairs. The values are always
    /// empty.
    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        self.cursor.iter()
    }

    /// Like [`ReadHashSet::iter`], but yields cursors to the keys
    /// themselves.
    pub fn keys(&self) -> Result<KeyIterator<'a, C>> {
        Ok(KeyIterator { pairs: KvPairIterator { iter: self.cursor.iter()? } })
    }

    /// The stored key, or `None` if it isn't in the set.
    pub fn get_cursor(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadCursor<'a, C>>> {
        self.get_cursor_by_hash(&self.cursor.db.digest(key.as_ref()))
    }

    pub fn get_slot(&self, key: impl AsRef<[u8]>) -> Result<Option<Slot>> {
        self.get_slot_by_hash(&self.cursor.db.digest(key.as_ref()))
    }

    pub fn contains(&self, key: impl AsRef<[u8]>) -> Result<bool> {
        Ok(self.get_cursor(key)?.is_some())
    }

    pub fn get_cursor_by_hash(&self, hash: &[u8]) -> Result<Option<ReadCursor<'a, C>>> {
        self.cursor.read_path(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))])
    }

    pub fn get_slot_by_hash(&self, hash: &[u8]) -> Result<Option<Slot>> {
        self.cursor.read_path_slot(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))])
    }
}

/// Keys stored by their hash. Useful for checking membership.
#[repr(transparent)]
pub struct WriteHashSet<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}
ref_cast!(WriteHashSet, WriteCursor);

impl<'a, C: Core> Deref for WriteHashSet<'a, C> {
    type Target = ReadHashSet<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadHashSet::from_ref(&self.cursor.read)
    }
}

impl<'a, C: Core> WriteHashSet<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        Ok(WriteHashSet { cursor: cursor.write_path(&[PathPart::HashMapInit { counted: false, set: true }])? })
    }

    pub fn write_cursor(&self) -> &WriteCursor<'a, C> {
        &self.cursor
    }

    pub fn put(&mut self, key: impl AsRef<[u8]>) -> Result<()> {
        let key = key.as_ref();
        let hash = self.cursor.db.digest(key);
        self.put_by_hash(&hash, Data::bytes(key))
    }

    pub fn put_cursor(&mut self, key: impl AsRef<[u8]>) -> Result<WriteCursor<'a, C>> {
        let hash = self.cursor.db.digest(key.as_ref());
        self.put_cursor_by_hash(&hash)
    }

    /// Removes `key`, returning whether it was in the set.
    pub fn remove(&mut self, key: impl AsRef<[u8]>) -> Result<bool> {
        let hash = self.cursor.db.digest(key.as_ref());
        self.remove_by_hash(&hash)
    }

    /// Like [`WriteHashSet::put`], but the stored key keeps the format tag
    /// of `key`.
    pub fn put_bytes(&mut self, key: Bytes<'_>) -> Result<()> {
        let hash = self.cursor.db.digest(&key.value);
        self.put_by_hash(&hash, Data::Bytes(key))
    }

    pub fn put_by_hash<'d>(&mut self, hash: &[u8], data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        // the key is written in the same write as the lookup, so a root set
        // does both in one transaction
        self.cursor.write_path_context(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))], |cursor| {
            cursor.write_if_empty(data)
        })?;
        Ok(())
    }

    pub fn put_cursor_by_hash(&mut self, hash: &[u8]) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::HashMapGet(HashMapGetTarget::Key(hash))])
    }

    pub fn remove_by_hash(&mut self, hash: &[u8]) -> Result<bool> {
        removed(self.cursor.write_path(&[PathPart::HashMapRemove(hash)]))
    }
}

/// A [`ReadHashSet`] that maintains a count of its contents.
#[repr(transparent)]
pub struct ReadCountedHashSet<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}

impl<'a, C: Core> Deref for ReadCountedHashSet<'a, C> {
    type Target = ReadHashSet<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadHashSet::from_ref(&self.cursor)
    }
}

impl<'a, C: Core> ReadCountedHashSet<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::CountedHashMap, Tag::CountedHashSet])?;
        Ok(ReadCountedHashSet { cursor })
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }
}

/// A [`WriteHashSet`] that maintains a count of its contents.
#[repr(transparent)]
pub struct WriteCountedHashSet<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}

impl<'a, C: Core> Deref for WriteCountedHashSet<'a, C> {
    type Target = WriteHashSet<'a, C>;
    fn deref(&self) -> &Self::Target {
        WriteHashSet::from_ref(&self.cursor)
    }
}

impl<C: Core> DerefMut for WriteCountedHashSet<'_, C> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        WriteHashSet::from_mut(&mut self.cursor)
    }
}

impl<'a, C: Core> WriteCountedHashSet<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        check_tag(cursor, &[Tag::CountedHashMap, Tag::CountedHashSet])?;
        Ok(WriteCountedHashSet { cursor: cursor.write_path(&[PathPart::HashMapInit { counted: true, set: true }])? })
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }
}

// SortedMap

/// Key-value pairs whose byte-array keys are kept in lexicographic order,
/// read-only.
#[repr(transparent)]
pub struct ReadSortedMap<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadSortedMap, ReadCursor);

fn sorted_rank<C: Core>(cursor: &ReadCursor<'_, C>, key: &[u8]) -> Result<i64> {
    let slot = cursor.slot()?;
    if slot.tag == Tag::None {
        return Ok(0);
    }
    let header = cursor.db.read_btree_header(slot.value)?;
    cursor.db.sorted_rank(header.root_ptr, key)
}

fn index_key_value_pair<'a, C: Core>(
    cursor: &ReadCursor<'a, C>,
    index: i64,
) -> Result<Option<ReadKvPairCursor<'a, C>>> {
    match cursor.read_path(&[PathPart::SortedMapGetIndex(index)])? {
        Some(cursor) => Ok(Some(cursor.read_key_value_pair()?)),
        None => Ok(None),
    }
}

impl<'a, C: Core> ReadSortedMap<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::SortedMap, Tag::SortedSet])?;
        Ok(ReadSortedMap { cursor })
    }

    pub fn cursor(&self) -> &ReadCursor<'a, C> {
        &self.cursor
    }

    pub fn slot(&self) -> Result<Slot> {
        self.cursor.slot()
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }

    /// Iterates over cursors to the key-value pairs in key order.
    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        self.cursor.iter()
    }

    /// Like [`ReadSortedMap::iter`], but yields the key and value cursors
    /// of each pair, as [`ReadCursor::read_key_value_pair`] returns them.
    pub fn entries(&self) -> Result<KvPairIterator<'a, C>> {
        Ok(KvPairIterator { iter: self.cursor.iter()? })
    }

    /// Iterates in key order, starting at the first entry with a key >=
    /// `start_key`.
    pub fn iter_from(&self, start_key: impl AsRef<[u8]>) -> Result<CursorIterator<'a, C>> {
        CursorIterator::sorted_from_key(&self.cursor, start_key.as_ref())
    }

    /// Iterates in key order, starting at the entry with rank
    /// `start_index`. Negative indexes count from the end.
    pub fn iter_from_index(&self, start_index: i64) -> Result<CursorIterator<'a, C>> {
        CursorIterator::sorted_from_index(&self.cursor, start_index)
    }

    /// The value of `key`, or `None` if it isn't in the map.
    pub fn get_cursor(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadCursor<'a, C>>> {
        self.cursor.read_path(&[PathPart::SortedMapGet(SortedMapGetTarget::Value(key.as_ref()))])
    }

    pub fn get_slot(&self, key: impl AsRef<[u8]>) -> Result<Option<Slot>> {
        self.cursor.read_path_slot(&[PathPart::SortedMapGet(SortedMapGetTarget::Value(key.as_ref()))])
    }

    pub fn get_key_value_pair(&self, key: impl AsRef<[u8]>) -> Result<Option<ReadKvPairCursor<'a, C>>> {
        match self.cursor.read_path(&[PathPart::SortedMapGet(SortedMapGetTarget::KvPair(key.as_ref()))])? {
            Some(cursor) => Ok(Some(cursor.read_key_value_pair()?)),
            None => Ok(None),
        }
    }

    /// The key-value pair at rank `index`. Negative indexes count from the
    /// end.
    pub fn get_index_key_value_pair(&self, index: i64) -> Result<Option<ReadKvPairCursor<'a, C>>> {
        index_key_value_pair(&self.cursor, index)
    }

    /// The number of keys strictly less than `key`.
    pub fn rank(&self, key: impl AsRef<[u8]>) -> Result<i64> {
        sorted_rank(&self.cursor, key.as_ref())
    }
}

/// Key-value pairs whose byte-array keys are kept in lexicographic order.
#[repr(transparent)]
pub struct WriteSortedMap<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}

impl<'a, C: Core> Deref for WriteSortedMap<'a, C> {
    type Target = ReadSortedMap<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadSortedMap::from_ref(&self.cursor.read)
    }
}

impl<'a, C: Core> WriteSortedMap<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        Ok(WriteSortedMap { cursor: cursor.write_path(&[PathPart::SortedMapInit { set: false }])? })
    }

    pub fn write_cursor(&self) -> &WriteCursor<'a, C> {
        &self.cursor
    }

    pub fn put<'d>(&mut self, key: impl AsRef<[u8]>, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        self.cursor.write_path(&[
            PathPart::SortedMapGet(SortedMapGetTarget::Value(key.as_ref())),
            PathPart::WriteData(&data),
        ])?;
        Ok(())
    }

    pub fn put_cursor(&mut self, key: impl AsRef<[u8]>) -> Result<WriteCursor<'a, C>> {
        self.cursor.write_path(&[PathPart::SortedMapGet(SortedMapGetTarget::Value(key.as_ref()))])
    }

    /// Removes `key`, returning whether it was in the map.
    pub fn remove(&mut self, key: impl AsRef<[u8]>) -> Result<bool> {
        removed(self.cursor.write_path(&[PathPart::SortedMapRemove(key.as_ref())]))
    }
}

// SortedSet

/// Byte-array keys kept in lexicographic order, read-only.
#[repr(transparent)]
pub struct ReadSortedSet<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}
ref_cast!(ReadSortedSet, ReadCursor);

impl<'a, C: Core> ReadSortedSet<'a, C> {
    pub fn new(cursor: impl Into<ReadCursor<'a, C>>) -> Result<Self> {
        let cursor = cursor.into();
        check_tag(&cursor, &[Tag::SortedMap, Tag::SortedSet])?;
        Ok(ReadSortedSet { cursor })
    }

    pub fn cursor(&self) -> &ReadCursor<'a, C> {
        &self.cursor
    }

    pub fn slot(&self) -> Result<Slot> {
        self.cursor.slot()
    }

    pub fn count(&self) -> Result<i64> {
        self.cursor.count()
    }

    /// Iterates over cursors to the key-value pairs in key order. The
    /// values are always empty.
    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        self.cursor.iter()
    }

    /// Like [`ReadSortedSet::iter`], but yields cursors to the keys
    /// themselves, in order.
    pub fn keys(&self) -> Result<KeyIterator<'a, C>> {
        Ok(KeyIterator { pairs: KvPairIterator { iter: self.cursor.iter()? } })
    }

    pub fn iter_from(&self, start_key: impl AsRef<[u8]>) -> Result<CursorIterator<'a, C>> {
        CursorIterator::sorted_from_key(&self.cursor, start_key.as_ref())
    }

    pub fn iter_from_index(&self, start_index: i64) -> Result<CursorIterator<'a, C>> {
        CursorIterator::sorted_from_index(&self.cursor, start_index)
    }

    pub fn get_index_key_value_pair(&self, index: i64) -> Result<Option<ReadKvPairCursor<'a, C>>> {
        index_key_value_pair(&self.cursor, index)
    }

    pub fn contains(&self, key: impl AsRef<[u8]>) -> Result<bool> {
        let path = [PathPart::SortedMapGet(SortedMapGetTarget::Key(key.as_ref()))];
        Ok(self.cursor.read_path(&path)?.is_some())
    }

    /// The number of keys strictly less than `key`.
    pub fn rank(&self, key: impl AsRef<[u8]>) -> Result<i64> {
        sorted_rank(&self.cursor, key.as_ref())
    }
}

/// Byte-array keys kept in lexicographic order.
#[repr(transparent)]
pub struct WriteSortedSet<'a, C: Core> {
    cursor: WriteCursor<'a, C>,
}

impl<'a, C: Core> Deref for WriteSortedSet<'a, C> {
    type Target = ReadSortedSet<'a, C>;
    fn deref(&self) -> &Self::Target {
        ReadSortedSet::from_ref(&self.cursor.read)
    }
}

impl<'a, C: Core> WriteSortedSet<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        Ok(WriteSortedSet { cursor: cursor.write_path(&[PathPart::SortedMapInit { set: true }])? })
    }

    pub fn write_cursor(&self) -> &WriteCursor<'a, C> {
        &self.cursor
    }

    pub fn put(&mut self, key: impl AsRef<[u8]>) -> Result<()> {
        self.cursor.write_path(&[PathPart::SortedMapGet(SortedMapGetTarget::Key(key.as_ref()))])?;
        Ok(())
    }

    /// Removes `key`, returning whether it was in the set.
    pub fn remove(&mut self, key: impl AsRef<[u8]>) -> Result<bool> {
        removed(self.cursor.write_path(&[PathPart::SortedMapRemove(key.as_ref())]))
    }
}
