use crate::data::Data;
use crate::slot::{Slot, Tag};
use vstd::prelude::*;

/// Whether a path traversal may write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteMode {
    ReadOnly,
    ReadWrite,
}

/// Which part of a hash map entry a [`PathPart::HashMapGet`] points at.
/// Each variant holds the hash of the key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HashMapGetTarget<'p> {
    KvPair(&'p [u8]),
    Key(&'p [u8]),
    Value(&'p [u8]),
}

impl<'p> HashMapGetTarget<'p> {
    pub fn hash(&self) -> &'p [u8] {
        match *self {
            HashMapGetTarget::KvPair(hash)
            | HashMapGetTarget::Key(hash)
            | HashMapGetTarget::Value(hash) => hash,
        }
    }
}

/// Which part of a sorted map entry a [`PathPart::SortedMapGet`] points at.
/// Each variant holds the key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SortedMapGetTarget<'p> {
    KvPair(&'p [u8]),
    Key(&'p [u8]),
    Value(&'p [u8]),
}

impl<'p> SortedMapGetTarget<'p> {
    pub fn key(&self) -> &'p [u8] {
        match *self {
            SortedMapGetTarget::KvPair(key)
            | SortedMapGetTarget::Key(key)
            | SortedMapGetTarget::Value(key) => key,
        }
    }
}

/// One step of a path through the database. This is the low-level API that
/// the data structure wrappers (like [`WriteHashMap`](crate::WriteHashMap))
/// are built on.
#[derive(Debug, Clone, Copy)]
pub enum PathPart<'p> {
    ArrayListInit,
    ArrayListGet(i64),
    ArrayListAppend,
    ArrayListSlice(i64),
    LinkedArrayListInit,
    LinkedArrayListGet(i64),
    LinkedArrayListAppend,
    LinkedArrayListSlice { offset: i64, size: i64 },
    LinkedArrayListConcat(Slot),
    LinkedArrayListInsert(i64),
    LinkedArrayListRemove(i64),
    HashMapInit { counted: bool, set: bool },
    HashMapGet(HashMapGetTarget<'p>),
    HashMapRemove(&'p [u8]),
    SortedMapInit { set: bool },
    SortedMapGet(SortedMapGetTarget<'p>),
    SortedMapGetIndex(i64),
    SortedMapRemove(&'p [u8]),
    WriteData(&'p Data<'p>),
}

impl PathPart<'_> {
    /// The collection tag that an init path part creates, if any.
    pub(crate) fn init_tag(&self) -> Option<Tag> {
        match *self {
            PathPart::ArrayListInit => Some(Tag::ArrayList),
            PathPart::LinkedArrayListInit => Some(Tag::LinkedArrayList),
            PathPart::HashMapInit { counted, set } => Some(hash_map_tag(counted, set)),
            PathPart::SortedMapInit { set } => Some(sorted_map_tag(set)),
            _ => None,
        }
    }

    /// The init path part for a collection tag, if any.
    pub(crate) fn init_for(tag: Tag) -> Option<PathPart<'static>> {
        match tag {
            Tag::ArrayList => Some(PathPart::ArrayListInit),
            Tag::LinkedArrayList => Some(PathPart::LinkedArrayListInit),
            Tag::HashMap => Some(PathPart::HashMapInit { counted: false, set: false }),
            Tag::HashSet => Some(PathPart::HashMapInit { counted: false, set: true }),
            Tag::CountedHashMap => Some(PathPart::HashMapInit { counted: true, set: false }),
            Tag::CountedHashSet => Some(PathPart::HashMapInit { counted: true, set: true }),
            Tag::SortedMap => Some(PathPart::SortedMapInit { set: false }),
            Tag::SortedSet => Some(PathPart::SortedMapInit { set: true }),
            _ => None,
        }
    }
}

verus! {

pub(crate) fn hash_map_tag(counted: bool, set: bool) -> (r: Tag)
    ensures
        r == (if counted { if set { Tag::CountedHashSet } else { Tag::CountedHashMap } } else { if set { Tag::HashSet } else { Tag::HashMap } }),
{
    match (counted, set) {
        (true, true) => Tag::CountedHashSet,
        (true, false) => Tag::CountedHashMap,
        (false, true) => Tag::HashSet,
        (false, false) => Tag::HashMap,
    }
}

pub(crate) fn sorted_map_tag(set: bool) -> (r: Tag)
    ensures
        r == (if set { Tag::SortedSet } else { Tag::SortedMap }),
{
    if set { Tag::SortedSet } else { Tag::SortedMap }
}

} // verus!
