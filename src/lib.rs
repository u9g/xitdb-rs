//! An immutable, embedded database. This is a Rust port of
//! [xitdb](https://github.com/xit-vcs/xitdb), and reads and writes the same
//! file format as the other implementations.
//!
//! * Each transaction efficiently creates a new "copy" of the database, and
//!   past copies can still be read from and reverted to.
//! * Supports storing in a single file as well as purely in-memory use.
//! * Incrementally reads and writes, so file-based databases can contain
//!   larger-than-memory datasets.
//! * Reads never block writes, and a database can be read from multiple
//!   threads/processes without locks.
//! * No query engine of any kind. You just write data structures (primarily
//!   an [`WriteArrayList`] and [`WriteHashMap`]) that can be nested
//!   arbitrarily.
//!
//! # Example
//!
//! ```
//! use xitdb::{CoreMemory, Data, Database, Hasher, ReadArrayList, ReadHashMap, WriteArrayList, WriteHashMap};
//!
//! # fn main() -> xitdb::Result<()> {
//! let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
//!
//! // the top-level data structure is an array list, so each transaction is
//! // stored as an item in it, and past copies of the db stay readable
//! let mut history = WriteArrayList::new(&mut db.root_cursor())?;
//!
//! // a transaction: append a copy of the latest moment, then change it
//! let last = history.get_slot(-1)?;
//! history.append_context(last, |cursor| {
//!     let mut moment = WriteHashMap::new(cursor)?;
//!     moment.put("foo", "foo")?;
//!     let mut fruits = WriteArrayList::new(&mut moment.put_cursor("fruits")?)?;
//!     fruits.append("apple")?;
//!     fruits.append("pear")?;
//!     Ok(())
//! })?;
//!
//! // read the most recent moment
//! let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
//! let foo = moment.get_cursor("foo")?.unwrap().read_bytes(Some(1024))?;
//! assert_eq!(foo, b"foo");
//! let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
//! assert_eq!(fruits.count()?, 2);
//! # Ok(())
//! # }
//! ```

// runs the README's examples as doctests
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;

mod btree;
mod bulk;
mod collections;
mod compact;
mod core;
mod crc64;
mod cursor;
mod data;
mod database;
mod error;
mod file_offset_map;
mod format;
mod hasher;
mod history;
mod index;
mod migrate;
mod path;
mod record;
#[cfg(feature = "serde")]
mod replica_serde;
mod slot;
mod sorted;
#[cfg(feature = "serde")]
mod structured;
mod typed;

pub use crate::collections::{KeyIterator, KvPairIterator};
pub use crate::collections::{
    ReadArrayList, ReadCountedHashMap, ReadCountedHashSet, ReadHashMap, ReadHashSet, ReadLinkedArrayList,
    ReadSortedMap, ReadSortedSet, WriteArrayList, WriteCountedHashMap, WriteCountedHashSet, WriteHashMap,
    WriteHashSet, WriteLinkedArrayList, WriteSortedMap, WriteSortedSet,
};
pub use crate::compact::{MemoryOffsetMap, OffsetMap};
pub use crate::core::{Core, CoreBufferedFile, CoreFile, CoreMemory, DEFAULT_BUFFER_SIZE, DynCore};
pub use crate::cursor::{
    CursorIterator, CursorReader, CursorWriter, ReadCursor, ReadKvPairCursor, WriteCursor, WriteKvPairCursor,
};
pub use crate::data::{Bytes, Data};
pub use crate::database::Database;
pub use crate::error::{DecodeError, Error, Result, SerializeError};
pub use crate::file_offset_map::FileOffsetMap;
pub use crate::format::{Header, ReplicaState, root_trailer_checksum};
pub use crate::hasher::{Hasher, bytes_to_id, id_to_bytes};
pub use crate::history::History;
pub use crate::index::{Index, IndexedMap, MapIndex};
pub use crate::migrate::{LAYOUT_VERSION_KEY, Migrated, Migration, Migrations};
pub use crate::path::{HashMapGetTarget, PathPart, SortedMapGetTarget, WriteMode};
pub use crate::record::{LazyMap, Record};
pub use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};
pub use crate::typed::{BOOL_FORMAT_TAG, KeyCodec, Map, MapIter, Set, SetIter, ValueCodec};
#[cfg(feature = "serde")]
pub use crate::typed::{JSON_FORMAT_TAG, Json};
#[cfg(feature = "serde")]
pub use crate::structured::{Structured, get_structured, put_structured, read_structured, write_structured};
#[cfg(feature = "derive")]
pub use xitdb_derive::Record;

/// What `#[derive(Record)]` generates calls these. Not public API.
#[doc(hidden)]
pub mod __private {
    pub use crate::record::{
        field_changed, missing_field, read_field, read_record, write_changed_field, write_field, write_record,
        write_record_changed,
    };
}

/// Constants describing the file format.
pub mod consts {
    pub use crate::format::{
        ARRAY_LIST_HEADER_LENGTH, BTREE_HEADER_LENGTH, BTREE_SLOT_COUNT, HEADER_LENGTH, INDEX_BLOCK_SIZE,
        MAGIC_NUMBER, ROOT_HEADER_END, ROOT_HEADER_LENGTH, ROOT_HEADER_START, ROOT_TRAILER_LENGTH, SLOT_COUNT,
        VERSION,
    };
}
