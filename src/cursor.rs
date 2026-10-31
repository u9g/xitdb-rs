use std::io;
use std::ops::Deref;

use crate::core::Core;
use crate::data::{Bytes, Data};
use crate::database::{ContextFn, Database, is_root};
use crate::error::{Error, Result};
use crate::format::*;
use crate::path::{PathPart, WriteMode};
use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};
use crate::sorted::short_bytes_value;

/// A read-only pointer to a slot in the database.
pub struct ReadCursor<'a, C: Core> {
    pub slot_ptr: SlotPointer,
    pub db: &'a Database<C>,
}

impl<C: Core> Clone for ReadCursor<'_, C> {
    fn clone(&self) -> Self {
        ReadCursor { slot_ptr: self.slot_ptr, db: self.db }
    }
}

impl<C: Core> std::fmt::Debug for ReadCursor<'_, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReadCursor").field("slot_ptr", &self.slot_ptr).finish_non_exhaustive()
    }
}

impl<'a, C: Core> ReadCursor<'a, C> {
    pub fn new(slot_ptr: SlotPointer, db: &'a Database<C>) -> ReadCursor<'a, C> {
        ReadCursor { slot_ptr, db }
    }

    /// The slot this cursor points to. For a root cursor, it reads the root
    /// again (see [`ReadCursor::resolved`]).
    pub fn slot(&self) -> Result<Slot> {
        Ok(self.resolved()?.slot)
    }

    /// A root cursor only has a snapshot of the root slot, which goes stale
    /// after the next transaction, so read it again. The result points at
    /// the copy of the root slot in the newest trailer, not the root header,
    /// so it is a fixed snapshot: the trailer never changes, so everything
    /// read through it comes from one commit, even if more are made.
    pub fn resolved(&self) -> Result<SlotPointer> {
        if is_root(&self.slot_ptr) {
            let header = self.db.read_root_header()?;
            if header.file_size < ROOT_TRAILER_LENGTH as i64 {
                return Err(Error::InvalidDatabase);
            }
            // the root slot is the first thing in the trailer
            let position = header.file_size - ROOT_TRAILER_LENGTH as i64;
            return Ok(SlotPointer::new(Some(position), header.root));
        }
        Ok(self.slot_ptr)
    }

    pub(crate) fn resolved_cursor(&self) -> Result<ReadCursor<'a, C>> {
        Ok(ReadCursor { slot_ptr: self.resolved()?, db: self.db })
    }

    /// Follows `path`, returning `None` if a key or index along it doesn't
    /// exist.
    pub fn read_path(&self, path: &[PathPart<'_>]) -> Result<Option<ReadCursor<'a, C>>> {
        let start = self.resolved()?;
        // reads never copy, so they need no freeze point
        match self.db.read_slot_pointer(WriteMode::ReadOnly, path, 0, start, 0, &mut None) {
            Ok(slot_ptr) => Ok(Some(ReadCursor { slot_ptr, db: self.db })),
            Err(Error::KeyNotFound) => Ok(None),
            Err(err) => Err(err),
        }
    }

    /// Like [`ReadCursor::read_path`], but returns only the slot.
    pub fn read_path_slot(&self, path: &[PathPart<'_>]) -> Result<Option<Slot>> {
        Ok(self.read_path(path)?.map(|cursor| cursor.slot_ptr.slot))
    }

    pub fn read_uint(&self) -> Result<u64> {
        let slot = self.slot()?;
        if slot.tag != Tag::Uint {
            return Err(Error::UnexpectedTag);
        }
        if slot.value < 0 {
            return Err(Error::ExpectedUnsignedLong);
        }
        Ok(slot.value as u64)
    }

    pub fn read_int(&self) -> Result<i64> {
        let slot = self.slot()?;
        if slot.tag != Tag::Int {
            return Err(Error::UnexpectedTag);
        }
        Ok(slot.value)
    }

    pub fn read_float(&self) -> Result<f64> {
        let slot = self.slot()?;
        if slot.tag != Tag::Float {
            return Err(Error::UnexpectedTag);
        }
        Ok(f64::from_bits(slot.value as u64))
    }

    /// Reads a byte array. If `max_size` is given and the array is longer,
    /// this returns [`Error::StreamTooLong`]; `None` means no limit (like
    /// passing 0 in the Go implementation). An empty slot reads as an empty
    /// array.
    pub fn read_bytes(&self, max_size: Option<u64>) -> Result<Vec<u8>> {
        Ok(self.read_bytes_object(max_size)?.value.into_owned())
    }

    /// Reads a byte array as a UTF-8 string, like
    /// [`ReadCursor::read_bytes`]. Invalid UTF-8 is an
    /// [`Error::InvalidUtf8`] rather than being replaced, so a byte array
    /// that isn't a string can't be silently misread as one.
    pub fn read_string(&self, max_size: Option<u64>) -> Result<String> {
        String::from_utf8(self.read_bytes(max_size)?).map_err(|err| Error::InvalidUtf8(err.utf8_error()))
    }

    /// Reads a byte array along with its format tag.
    pub fn read_bytes_object(&self, max_size: Option<u64>) -> Result<Bytes<'static>> {
        let slot_ptr = self.resolved()?;
        let too_long = |size: u64| max_size.is_some_and(|max| size > max);
        match slot_ptr.slot.tag {
            Tag::None => Ok(Bytes::default()),
            Tag::Bytes => {
                let value_size = self.db.read_i64_at(slot_ptr.slot.value)?;
                if value_size < 0 {
                    return Err(Error::ExpectedUnsignedLong);
                }
                if too_long(value_size as u64) {
                    return Err(Error::StreamTooLong);
                }
                let mut value = vec![0u8; self.db.checked_len(slot_ptr.slot.value + 8, value_size)?];
                self.db.seek(slot_ptr.slot.value + 8)?;
                self.db.read_bytes(&mut value)?;
                let format_tag = if slot_ptr.slot.full {
                    let mut tag = [0u8; 2];
                    self.db.read_bytes(&mut tag)?;
                    Some(tag)
                } else {
                    None
                };
                Ok(Bytes { value: value.into(), format_tag })
            }
            Tag::ShortBytes => {
                let (buf, len) = short_bytes_value(slot_ptr.slot);
                if too_long(len as u64) {
                    return Err(Error::StreamTooLong);
                }
                let format_tag = slot_ptr.slot.full.then(|| [buf[6], buf[7]]);
                Ok(Bytes { value: buf[..len].to_vec().into(), format_tag })
            }
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// For a cursor to a key-value pair (as yielded when iterating a map or
    /// set), cursors to the key and the value.
    pub fn read_key_value_pair(&self) -> Result<ReadKvPairCursor<'a, C>> {
        let slot_ptr = self.resolved()?;
        let kv = self.db.read_kv_pair(slot_ptr.slot)?;
        let key_slot_pos = slot_ptr.slot.value + self.db.kv_key_offset(slot_ptr.slot.tag);
        let value_slot_pos = key_slot_pos + SLOT_LENGTH as i64;
        Ok(ReadKvPairCursor {
            value_cursor: ReadCursor::new(SlotPointer::new(Some(value_slot_pos), kv.value_slot), self.db),
            key_cursor: ReadCursor::new(SlotPointer::new(Some(key_slot_pos), kv.key_slot), self.db),
            hash: kv.hash,
        })
    }

    /// An incremental reader for a byte array.
    pub fn reader(&self) -> Result<CursorReader<'a, C>> {
        let slot_ptr = self.resolved()?;
        match slot_ptr.slot.tag {
            Tag::Bytes => {
                let size = self.db.read_i64_at(slot_ptr.slot.value)?;
                let start_position = slot_ptr.slot.value + 8;
                let size = self.db.checked_len(start_position, size)? as u64;
                let start_position = start_position as u64;
                Ok(CursorReader { db: self.db, size, start_position, relative_position: 0, inline: None })
            }
            Tag::ShortBytes => {
                // short bytes are stored in the slot itself, which we already have
                let (buf, len) = short_bytes_value(slot_ptr.slot);
                Ok(CursorReader { db: self.db, size: len as u64, start_position: 0, relative_position: 0, inline: Some(buf) })
            }
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// Whether writing `data` here would leave the slot as it is. Anything
    /// that fits in a slot, which is everything but a byte array too long
    /// to (see [`Bytes::is_short`]), is compared by the slot alone: the
    /// type, the value, and any format tag must all be the same. So
    /// [`Data::Int`] 1 isn't [`Data::Uint`] 1, floats are compared by their
    /// bits (`-0.0` isn't `0.0`, and a NaN equals the same NaN), and
    /// [`Data::Slot`] equals only that exact slot, so a copy of a
    /// collection at another position isn't equal to it.
    ///
    /// [`Data::None`] equals only a slot it was written to, not one that
    /// was never written. An empty byte array is short bytes, so it equals
    /// neither. A long byte array equals stored bytes with the same length
    /// and format tag, and then the same contents, which are read in
    /// chunks rather than all at once. Bytes stored as a long byte array
    /// (as [`WriteCursor::writer`] does) don't equal short data, even with
    /// the same contents, because writing it would store it differently.
    pub fn equals<'d>(&self, data: impl Into<Data<'d>>) -> Result<bool> {
        self.equals_data(&data.into())
    }

    pub(crate) fn equals_data(&self, data: &Data<'_>) -> Result<bool> {
        let slot = self.slot()?;
        let bytes = match (data.inline_slot(), data) {
            (Some(inline), _) => return Ok(slot == inline),
            (None, Data::Bytes(bytes)) => bytes,
            (None, _) => unreachable!("only long byte arrays aren't inline"),
        };
        if slot.tag != Tag::Bytes || slot.full != bytes.format_tag.is_some() {
            return Ok(false);
        }
        let len = bytes.value.len() as i64;
        if self.db.read_i64_at(slot.value)? != len {
            return Ok(false);
        }
        let start = slot.value + 8;
        if let Some(format_tag) = bytes.format_tag {
            let mut stored = [0u8; 2];
            self.db.read_at(start + len, &mut stored)?;
            if stored != format_tag {
                return Ok(false);
            }
        }
        let mut buf = [0u8; 4096];
        let mut position = start;
        for chunk in bytes.value.chunks(buf.len()) {
            let stored = &mut buf[..chunk.len()];
            self.db.read_at(position, stored)?;
            if stored != chunk {
                return Ok(false);
            }
            position += chunk.len() as i64;
        }
        Ok(true)
    }

    /// The number of items in a collection, or bytes in a byte array.
    pub fn count(&self) -> Result<i64> {
        let slot = self.slot()?;
        match slot.tag {
            Tag::None => Ok(0),
            Tag::ArrayList => Ok(self.db.read_array_list_header(slot.value)?.size),
            Tag::LinkedArrayList | Tag::SortedMap | Tag::SortedSet => {
                Ok(self.db.read_btree_header(slot.value)?.size)
            }
            Tag::Bytes | Tag::CountedHashMap | Tag::CountedHashSet => self.db.read_i64_at(slot.value),
            Tag::ShortBytes => Ok(short_bytes_value(slot).1 as i64),
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// Iterates over a collection. Map and set iterators yield cursors to
    /// key-value pairs (see [`ReadCursor::read_key_value_pair`]).
    ///
    /// Iterators don't copy shared nodes, so their cursors are read-only.
    pub fn iter(&self) -> Result<CursorIterator<'a, C>> {
        CursorIterator::new(self)
    }
}

/// Cursors to the key and value of a key-value pair.
pub struct ReadKvPairCursor<'a, C: Core> {
    pub value_cursor: ReadCursor<'a, C>,
    pub key_cursor: ReadCursor<'a, C>,
    pub hash: Vec<u8>,
}

// CursorReader

/// Reads a byte array incrementally. Implements [`io::Read`] and
/// [`io::Seek`].
pub struct CursorReader<'a, C: Core> {
    db: &'a Database<C>,
    size: u64,
    start_position: u64,
    relative_position: u64,
    // the value of short bytes, which live in their slot
    inline: Option<[u8; 8]>,
}

impl<C: Core> CursorReader<'_, C> {
    /// The length of the byte array.
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Fills `buf`, or returns [`Error::EndOfStream`] if there aren't
    /// enough bytes left.
    pub fn read_fully(&mut self, buf: &mut [u8]) -> Result<()> {
        if self.size < self.relative_position || self.size - self.relative_position < buf.len() as u64 {
            return Err(Error::EndOfStream);
        }
        let start = self.start_position + self.relative_position;
        match &self.inline {
            Some(inline) => buf.copy_from_slice(&inline[start as usize..start as usize + buf.len()]),
            None => self.db.read_at(start as i64, buf)?,
        }
        self.relative_position += buf.len() as u64;
        Ok(())
    }

    pub fn read_u8(&mut self) -> Result<u8> {
        let mut buf = [0u8; 1];
        self.read_fully(&mut buf)?;
        Ok(buf[0])
    }

    pub fn read_i16(&mut self) -> Result<i16> {
        let mut buf = [0u8; 2];
        self.read_fully(&mut buf)?;
        Ok(i16::from_be_bytes(buf))
    }

    pub fn read_i32(&mut self) -> Result<i32> {
        let mut buf = [0u8; 4];
        self.read_fully(&mut buf)?;
        Ok(i32::from_be_bytes(buf))
    }

    pub fn read_i64(&mut self) -> Result<i64> {
        let mut buf = [0u8; 8];
        self.read_fully(&mut buf)?;
        Ok(i64::from_be_bytes(buf))
    }

    /// Moves to `position`, relative to the start of the byte array.
    pub fn seek_to(&mut self, position: u64) -> Result<()> {
        if position > self.size {
            return Err(Error::InvalidOffset);
        }
        self.relative_position = position;
        Ok(())
    }

    /// Reads the rest of the byte array.
    pub fn read_all(&mut self) -> Result<Vec<u8>> {
        let mut buf = vec![0u8; self.size.saturating_sub(self.relative_position) as usize];
        self.read_fully(&mut buf)?;
        Ok(buf)
    }
}

impl<C: Core> io::Read for CursorReader<'_, C> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.size < self.relative_position {
            return Err(Error::EndOfStream.into());
        }
        let read_size = (buf.len() as u64).min(self.size - self.relative_position) as usize;
        if read_size == 0 {
            return Ok(0);
        }
        self.read_fully(&mut buf[..read_size])?;
        Ok(read_size)
    }
}

impl<C: Core> io::Seek for CursorReader<'_, C> {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        let position = match pos {
            io::SeekFrom::Start(n) => Some(n),
            io::SeekFrom::End(n) => self.size.checked_add_signed(n),
            io::SeekFrom::Current(n) => self.relative_position.checked_add_signed(n),
        };
        let position = position.ok_or_else(|| io::Error::from(Error::InvalidOffset))?;
        self.seek_to(position)?;
        Ok(position)
    }
}

// CursorIterator - stack-based tree traversal

#[derive(Clone, Copy)]
struct IterLevel {
    position: i64,
    block: [Slot; SLOT_COUNT],
    index: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum IterKind {
    Empty,
    // a fixed number of items in an array list or b-tree
    Counted,
    // hash maps and sets, which are walked until the stack is empty
    Map,
}

/// Iterates over the items of a collection, yielding read-only cursors.
pub struct CursorIterator<'a, C: Core> {
    db: &'a Database<C>,
    kind: IterKind,
    size: i64,
    index: i64,
    stack: Vec<IterLevel>,
    // skips a b-tree node's kind+num header, or 0 for the radix trie
    node_offset: i64,
    // for array lists, the stack depth of the leaf blocks. every slot in them
    // is an item, even an empty one, so they are counted even when empty.
    // otherwise, empty slots past the end of a list that was sliced and then
    // appended to without being written would be followed by stale items.
    leaf_depth: Option<usize>,
    done: bool,
}

/// Resolves a possibly-negative start index against `size` to a 0-based
/// rank. Negatives count from the end (-1 is the last entry); anything out
/// of range returns `None` (yield nothing).
fn resolve_start_index(index: i64, size: i64) -> Option<i64> {
    let resolved = if index < 0 { index + size } else { index };
    (0..size).contains(&resolved).then_some(resolved)
}

impl<'a, C: Core> CursorIterator<'a, C> {
    fn empty(db: &'a Database<C>) -> CursorIterator<'a, C> {
        CursorIterator {
            db,
            kind: IterKind::Empty,
            size: 0,
            index: 0,
            stack: Vec::new(),
            node_offset: 0,
            leaf_depth: None,
            done: true,
        }
    }

    fn level(&self, position: i64) -> Result<IterLevel> {
        Ok(IterLevel { position, block: self.db.read_index_block(position)?, index: 0 })
    }

    pub(crate) fn new(cursor: &ReadCursor<'a, C>) -> Result<CursorIterator<'a, C>> {
        let cursor = cursor.resolved_cursor()?;
        let db = cursor.db;
        let slot = cursor.slot_ptr.slot;
        let mut it = CursorIterator::empty(db);
        match slot.tag {
            Tag::None => {}
            Tag::ArrayList => {
                let header = db.read_array_list_header(slot.value)?;
                it.kind = IterKind::Counted;
                it.size = header.size;
                it.stack = vec![it.level(header.ptr)?];
                it.leaf_depth = Some(array_list_shift(header.size - 1) as usize + 1);
            }
            Tag::LinkedArrayList | Tag::SortedMap | Tag::SortedSet => {
                // backed by a b-tree: read the header, then walk from the root
                // node's value/child slots (skipping its kind+num header)
                let header = db.read_btree_header(slot.value)?;
                it.kind = IterKind::Counted;
                it.size = header.size;
                it.node_offset = BTREE_NODE_HEADER_SIZE as i64;
                it.stack = vec![it.level(header.root_ptr + BTREE_NODE_HEADER_SIZE as i64)?];
            }
            Tag::HashMap | Tag::HashSet => {
                it.kind = IterKind::Map;
                it.stack = vec![it.level(slot.value)?];
            }
            Tag::CountedHashMap | Tag::CountedHashSet => {
                it.kind = IterKind::Map;
                it.stack = vec![it.level(slot.value + 8)?];
            }
            _ => return Err(Error::UnexpectedTag),
        }
        it.done = it.kind == IterKind::Empty;
        Ok(it)
    }

    // starts a counted iterator at `index` with a stack from a seek
    fn seeked(db: &'a Database<C>, size: i64, index: i64, node_offset: i64, stack: Vec<IterLevel>) -> Self {
        CursorIterator { db, kind: IterKind::Counted, size, index, stack, node_offset, leaf_depth: None, done: false }
    }

    /// An array list iterator that starts at `start_index`, descending the
    /// radix trie straight to it. Negatives count from the end; out of
    /// range (or an unwritten list) yields nothing.
    pub(crate) fn array_list_from(cursor: &ReadCursor<'a, C>, start_index: i64) -> Result<Self> {
        let cursor = cursor.resolved_cursor()?;
        let db = cursor.db;
        let slot = cursor.slot_ptr.slot;
        match slot.tag {
            Tag::None => return Ok(CursorIterator::empty(db)),
            Tag::ArrayList => {}
            _ => return Err(Error::UnexpectedTag),
        }
        let header = db.read_array_list_header(slot.value)?;
        let Some(idx) = resolve_start_index(start_index, header.size) else {
            return Ok(CursorIterator::empty(db));
        };
        let mut shift = array_list_shift(header.size - 1);
        // descend the radix trie, pushing one level per tier with its index
        // set to that tier's child slot
        let mut stack = Vec::new();
        let mut pos = header.ptr;
        loop {
            let block = db.read_index_block(pos)?;
            let i = ((idx >> (shift as u32 * BIT_COUNT)) & MASK) as usize;
            stack.push(IterLevel { position: pos, block, index: i });
            if shift == 0 {
                break;
            }
            // every tier above the leaf is a populated index slot for any
            // index < size, so this child always exists
            pos = block[i].value;
            shift -= 1;
        }
        let leaf_depth = stack.len();
        let mut it = CursorIterator::seeked(db, header.size, idx, 0, stack);
        it.leaf_depth = Some(leaf_depth);
        Ok(it)
    }

    /// A linked array list iterator that starts at `start_index`.
    pub(crate) fn linked_array_list_from(cursor: &ReadCursor<'a, C>, start_index: i64) -> Result<Self> {
        let cursor = cursor.resolved_cursor()?;
        let db = cursor.db;
        let slot = cursor.slot_ptr.slot;
        match slot.tag {
            Tag::None => return Ok(CursorIterator::empty(db)),
            Tag::LinkedArrayList => {}
            _ => return Err(Error::UnexpectedTag),
        }
        let header = db.read_btree_header(slot.value)?;
        let Some(idx) = resolve_start_index(start_index, header.size) else {
            return Ok(CursorIterator::empty(db));
        };
        let mut stack = Vec::new();
        let mut node_ptr = header.root_ptr;
        let mut rem = idx;
        loop {
            let node = db.read_btree_node(node_ptr)?;
            let position = node_ptr + BTREE_NODE_HEADER_SIZE as i64;
            if node.kind == BTreeNodeKind::Leaf {
                stack.push(IterLevel { position, block: node.values, index: check_rank(rem, node.num, false)? });
                break;
            }
            let mut i = 0;
            while i + 1 < node.num && rem >= node.counts[i] {
                rem -= node.counts[i];
                i += 1;
            }
            stack.push(IterLevel { position, block: node.children, index: i });
            node_ptr = node.children[i].value;
        }
        Ok(CursorIterator::seeked(db, header.size, idx, BTREE_NODE_HEADER_SIZE as i64, stack))
    }

    fn sorted_root(cursor: &ReadCursor<'a, C>) -> Result<Option<(i64, i64)>> {
        let slot = cursor.slot_ptr.slot;
        match slot.tag {
            Tag::None => Ok(None),
            Tag::SortedMap | Tag::SortedSet => {
                let header = cursor.db.read_btree_header(slot.value)?;
                Ok(Some((header.root_ptr, header.size)))
            }
            _ => Err(Error::UnexpectedTag),
        }
    }

    fn levels(path: crate::sorted::NodePath) -> Vec<IterLevel> {
        path.into_iter().map(|(position, block, index)| IterLevel { position, block, index }).collect()
    }

    /// A sorted map iterator that starts at the entry with rank
    /// `start_index`. Negatives count from the end.
    pub(crate) fn sorted_from_index(cursor: &ReadCursor<'a, C>, start_index: i64) -> Result<Self> {
        let cursor = cursor.resolved_cursor()?;
        let db = cursor.db;
        let Some((root_ptr, size)) = Self::sorted_root(&cursor)? else {
            // an unwritten map is none (like iter()): yield nothing
            return Ok(CursorIterator::empty(db));
        };
        let Some(idx) = resolve_start_index(start_index, size) else {
            return Ok(CursorIterator::empty(db));
        };
        let stack = Self::levels(db.sorted_path_from_index(root_ptr, idx)?);
        Ok(CursorIterator::seeked(db, size, idx, BTREE_NODE_HEADER_SIZE as i64, stack))
    }

    /// A sorted map iterator that starts at the first entry with a key >=
    /// `start_key`.
    pub(crate) fn sorted_from_key(cursor: &ReadCursor<'a, C>, start_key: &[u8]) -> Result<Self> {
        let cursor = cursor.resolved_cursor()?;
        let db = cursor.db;
        let Some((root_ptr, size)) = Self::sorted_root(&cursor)? else {
            return Ok(CursorIterator::empty(db));
        };
        let (path, before) = db.sorted_path_from_key(root_ptr, start_key)?;
        Ok(CursorIterator::seeked(db, size, before, BTREE_NODE_HEADER_SIZE as i64, Self::levels(path)))
    }

    // the next slot, or None once the stack is exhausted. empty slots are
    // skipped, except in array list leaf blocks.
    fn next_internal(&mut self) -> Result<Option<SlotPointer>> {
        while let Some(level) = self.stack.last_mut() {
            if level.index >= level.block.len() {
                self.stack.pop();
                if let Some(parent) = self.stack.last_mut() {
                    parent.index += 1;
                }
                continue;
            }

            let next_slot = level.block[level.index];
            if next_slot.tag == Tag::Index {
                // node_offset skips a b-tree node's kind+num header
                let next_pos = next_slot.value + self.node_offset;
                let level = self.level(next_pos)?;
                self.stack.push(level);
                continue;
            }

            level.index += 1;
            if !next_slot.is_empty() || self.leaf_depth == Some(self.stack.len()) {
                let level = self.stack.last().expect("checked above");
                let position = level.position + ((level.index - 1) * SLOT_LENGTH) as i64;
                return Ok(Some(SlotPointer::new(Some(position), next_slot)));
            }
        }
        Ok(None)
    }
}

impl<'a, C: Core> Iterator for CursorIterator<'a, C> {
    type Item = Result<ReadCursor<'a, C>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        loop {
            if self.kind == IterKind::Counted {
                if self.index >= self.size {
                    self.done = true;
                    return None;
                }
                self.index += 1;
            }
            match self.next_internal() {
                Err(err) => {
                    self.done = true;
                    return Some(Err(err));
                }
                // an empty array list item counts toward the size, but has no value
                Ok(Some(slot_ptr)) if slot_ptr.slot.is_empty() => {}
                Ok(Some(slot_ptr)) => return Some(Ok(ReadCursor::new(slot_ptr, self.db))),
                Ok(None) => {
                    self.done = true;
                    return None;
                }
            }
        }
    }
}

// WriteCursor

/// A pointer to a slot that can be written to.
///
/// Writes through the root cursor are transactions. Writes through any
/// other cursor must happen inside a transaction, such as in the function
/// given to [`WriteArrayList::append_context`](crate::WriteArrayList::append_context)
/// or [`Database::run_context`].
pub struct WriteCursor<'a, C: Core> {
    pub(crate) read: ReadCursor<'a, C>,
    transaction: Option<u64>,
    // writes through this cursor copy any data written before this
    // position, even within the transaction (see freeze)
    pub(crate) frozen_at: i64,
}

impl<C: Core> Clone for WriteCursor<'_, C> {
    fn clone(&self) -> Self {
        WriteCursor { read: self.read.clone(), transaction: self.transaction, frozen_at: self.frozen_at }
    }
}

impl<'a, C: Core> Deref for WriteCursor<'a, C> {
    type Target = ReadCursor<'a, C>;

    fn deref(&self) -> &ReadCursor<'a, C> {
        &self.read
    }
}

impl<C: Core> std::fmt::Debug for WriteCursor<'_, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WriteCursor")
            .field("slot_ptr", &self.read.slot_ptr)
            .field("frozen_at", &self.frozen_at)
            .finish_non_exhaustive()
    }
}

/// Discards an unfinished write's data when dropped, unless disarmed.
struct TruncateOnFailure<'a, C: Core> {
    db: &'a Database<C>,
    failed: bool,
}

impl<C: Core> Drop for TruncateOnFailure<'_, C> {
    fn drop(&mut self) {
        // only truncate when an error or panic escapes the outer write. a
        // nested callback's caller may still commit its work.
        if self.failed && self.db.tx_start.get().is_none() {
            let _ = self.db.truncate();
        }
    }
}

/// Ends a transaction when dropped.
struct EndTransaction<'a, C: Core>(Option<&'a Database<C>>);

impl<C: Core> Drop for EndTransaction<'_, C> {
    fn drop(&mut self) {
        if let Some(db) = self.0 {
            db.transaction.set(None);
        }
    }
}

impl<'a, C: Core> WriteCursor<'a, C> {
    pub(crate) fn new(slot_ptr: SlotPointer, db: &'a Database<C>) -> WriteCursor<'a, C> {
        let transaction = if slot_ptr.position.is_some() && !is_root(&slot_ptr) {
            db.transaction_id()
        } else {
            None
        };
        WriteCursor { read: ReadCursor::new(slot_ptr, db), transaction, frozen_at: 0 }
    }

    /// A read-only copy of this cursor.
    pub fn read_cursor(&self) -> ReadCursor<'a, C> {
        self.read.clone()
    }

    pub fn slot_ptr(&self) -> SlotPointer {
        self.read.slot_ptr
    }

    // require the active transaction and a writable slot
    pub(crate) fn check_writable(&self) -> Result<()> {
        if let Some(transaction) = self.transaction
            && Some(transaction) != self.read.db.transaction_id()
        {
            return Err(Error::ExpiredTransaction);
        }
        // writes below the root must run inside a transaction
        if !is_root(&self.read.slot_ptr) && self.transaction.is_none() {
            return Err(Error::ExpectedTxStart);
        }
        self.read.db.check_frozen_slot(&self.read.slot_ptr)
    }

    // a collection made by a write through the root cursor outside a
    // transaction would belong to a transaction that has already ended, so
    // it could never be written to
    pub(crate) fn check_in_transaction(&self) -> Result<()> {
        if is_root(&self.read.slot_ptr) && self.read.db.transaction.get().is_none() {
            return Err(Error::ExpectedTxStart);
        }
        Ok(())
    }

    // reload because an earlier write may have moved what the slot points to
    pub(crate) fn reload_slot(&mut self) -> Result<()> {
        if self.transaction.is_some()
            && let Some(position) = self.read.slot_ptr.position
        {
            let slot = self.read.db.read_slot_at(position)?;
            self.read.slot_ptr = self.read.slot_ptr.with_slot(slot);
        }
        Ok(())
    }

    /// Follows `path`, creating anything along it that doesn't exist, and
    /// returns a cursor to where it ends.
    pub fn write_path(&mut self, path: &[PathPart<'_>]) -> Result<WriteCursor<'a, C>> {
        self.write_path_inner(path, None)
    }

    /// Like [`WriteCursor::write_path`], then runs `f` with a cursor to
    /// where the path ends. If `f` fails, a transaction started by this
    /// write is discarded.
    pub fn write_path_context(
        &mut self,
        path: &[PathPart<'_>],
        f: impl FnOnce(&mut WriteCursor<'a, C>) -> Result<()>,
    ) -> Result<WriteCursor<'a, C>> {
        self.write_path_inner(path, Some(Box::new(f)))
    }

    fn write_path_inner(&mut self, path: &[PathPart<'_>], ctx: Option<ContextFn<'_, 'a, C>>) -> Result<WriteCursor<'a, C>> {
        let db = self.read.db;
        self.check_writable()?;
        let has_parts = !path.is_empty() || ctx.is_some();
        // nested top-level writes could commit before the outer transaction ends
        if db.transaction.get().is_some() && is_root(&self.read.slot_ptr) && has_parts {
            return Err(Error::NestedTopLevelWrite);
        }
        let starts_transaction = db.transaction.get().is_none() && is_root(&self.read.slot_ptr);
        // declared before the truncate guard, so it is dropped after it:
        // truncating needs to see the transaction's freeze point
        let _end_transaction = EndTransaction(starts_transaction.then(|| {
            db.begin_transaction();
            db
        }));
        let mut guard = TruncateOnFailure { db, failed: true };

        self.reload_slot()?;
        let mut ctx = ctx;
        let slot_ptr = db.read_slot_pointer(WriteMode::ReadWrite, path, 0, self.read.slot_ptr, self.frozen_at, &mut ctx)?;
        guard.failed = false;
        if db.tx_start.get().is_none() {
            db.core().sync()?;
        }
        self.reload_slot()?;
        let mut cursor = WriteCursor::new(slot_ptr, db);
        cursor.frozen_at = self.frozen_at;
        cursor.reload_slot()?;
        Ok(cursor)
    }

    /// Makes writes through this cursor, and cursors made from it
    /// afterward, copy what the transaction wrote so far instead of
    /// changing it in place. Call it after pointing this slot at data still
    /// referred to elsewhere, and before wrapping the cursor in a
    /// collection. Unlike [`Database::freeze`], other cursors keep writing
    /// in place.
    pub fn freeze(&mut self) -> Result<()> {
        if self.read.db.tx_start.get().is_none() {
            return Err(Error::ExpectedTxStart);
        }
        self.frozen_at = self.read.db.len()?;
        Ok(())
    }

    /// Writes `data` to the slot.
    pub fn write<'d>(&mut self, data: impl Into<Data<'d>>) -> Result<()> {
        let data = data.into();
        let cursor = self.write_path(&[PathPart::WriteData(&data)])?;
        self.read.slot_ptr = cursor.read.slot_ptr;
        Ok(())
    }

    /// Writes `data` only if the slot is empty.
    pub fn write_if_empty<'d>(&mut self, data: impl Into<Data<'d>>) -> Result<()> {
        self.check_writable()?;
        if self.read.resolved()?.slot.is_empty() {
            return self.write(data);
        }
        Ok(())
    }

    /// Writes `data` only if it differs from what the slot holds (see
    /// [`ReadCursor::equals`]), and returns whether it wrote. If it's the
    /// same, nothing at all is written.
    pub fn write_if_changed<'d>(&mut self, data: impl Into<Data<'d>>) -> Result<bool> {
        let data = data.into();
        self.check_writable()?;
        self.reload_slot()?;
        if self.read.equals_data(&data)? {
            return Ok(false);
        }
        self.write(data)?;
        Ok(true)
    }

    /// For a cursor to a key-value pair, writable cursors to the key and
    /// the value.
    pub fn read_key_value_pair(&self) -> Result<WriteKvPairCursor<'a, C>> {
        let kv = self.read.read_key_value_pair()?;
        let wrap = |read| WriteCursor { read, transaction: self.transaction, frozen_at: self.frozen_at };
        Ok(WriteKvPairCursor { value_cursor: wrap(kv.value_cursor), key_cursor: wrap(kv.key_cursor), hash: kv.hash })
    }

    /// An incremental writer for a byte array. Call
    /// [`CursorWriter::finish`] when done, or nothing is written to the
    /// slot.
    pub fn writer(&mut self) -> Result<CursorWriter<'_, 'a, C>> {
        self.check_writable()?;
        // bytes are written to the root with write, which runs inside a
        // transaction
        if is_root(&self.read.slot_ptr) {
            return Err(Error::CursorNotWriteable);
        }
        let db = self.read.db;
        if db.tx_start.get().is_none() {
            return Err(Error::ExpectedTxStart);
        }
        let ptr_pos = db.append(&0i64.to_be_bytes())?;
        let start_position = db.len()?;
        Ok(CursorWriter {
            parent: self,
            size: 0,
            slot: Slot::new(ptr_pos, Tag::Bytes),
            start_position,
            relative_position: 0,
            format_tag: None,
        })
    }
}

/// Writable cursors to the key and value of a key-value pair.
pub struct WriteKvPairCursor<'a, C: Core> {
    pub value_cursor: WriteCursor<'a, C>,
    pub key_cursor: WriteCursor<'a, C>,
    pub hash: Vec<u8>,
}

// CursorWriter

/// Writes a byte array incrementally. Implements [`io::Write`].
pub struct CursorWriter<'w, 'a, C: Core> {
    parent: &'w mut WriteCursor<'a, C>,
    size: i64,
    pub(crate) slot: Slot,
    start_position: i64,
    relative_position: i64,
    /// The format tag to store with the byte array. Set it before calling
    /// [`CursorWriter::finish`].
    pub format_tag: Option<[u8; 2]>,
}

impl<C: Core> CursorWriter<'_, '_, C> {
    /// The slot of the byte array. The cursor's slot is set to it by
    /// [`CursorWriter::finish`].
    pub fn slot(&self) -> Slot {
        self.slot
    }

    /// The number of bytes written so far.
    pub fn size(&self) -> u64 {
        self.size as u64
    }

    // validate the parent cursor and reject writes to frozen bytes
    fn check_writable(&self) -> Result<()> {
        self.parent.check_writable()?;
        let db = self.parent.read.db;
        if db.tx_start.get().is_none() {
            return Err(Error::ExpectedTxStart);
        }
        if let Some(frozen_at) = db.transaction.get().and_then(|t| t.frozen_at)
            && self.slot.value < frozen_at
        {
            return Err(Error::FrozenBytes);
        }
        Ok(())
    }

    fn write_bytes(&mut self, buf: &[u8]) -> Result<()> {
        self.check_writable()?;
        if self.size < self.relative_position {
            return Err(Error::EndOfStream);
        }
        let db = self.parent.read.db;
        let new_position = self.relative_position + buf.len() as i64;

        // another allocation may now follow this byte array.
        // extending it would overwrite that allocation.
        if new_position > self.size && db.len()? != self.start_position + self.size {
            return Err(Error::UnexpectedWriterPosition);
        }

        db.write_at(self.start_position + self.relative_position, buf)?;
        self.relative_position = new_position;
        self.size = self.size.max(self.relative_position);
        Ok(())
    }

    /// Moves to `position`, relative to the start of the byte array. It
    /// can't move past the bytes written so far.
    pub fn seek_to(&mut self, position: u64) {
        // compare as u64, so a huge position can't wrap around to a negative
        // one and point before the byte array
        if position <= self.size as u64 {
            self.relative_position = position as i64;
        }
    }

    /// Writes the byte array's length and format tag, and points the slot
    /// at it.
    pub fn finish(&mut self) -> Result<()> {
        self.check_writable()?;
        let db = self.parent.read.db;
        if let Some(format_tag) = self.format_tag {
            self.slot = self.slot.with_full(true);
            let format_tag_pos = db.len()?;
            if self.start_position + self.size != format_tag_pos {
                return Err(Error::UnexpectedWriterPosition);
            }
            db.write_at(format_tag_pos, &format_tag)?;
        }

        db.write_i64_at(self.slot.value, self.size)?;

        let position = self.parent.read.slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
        db.write_slot_at(position, self.slot)?;

        self.parent.read.slot_ptr = self.parent.read.slot_ptr.with_slot(self.slot);
        if db.tx_start.get().is_none() {
            db.core().sync()?;
        }
        Ok(())
    }
}

impl<C: Core> io::Write for CursorWriter<'_, '_, C> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_bytes(buf)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
