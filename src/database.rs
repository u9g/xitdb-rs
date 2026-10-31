use std::cell::{Cell, RefCell, RefMut};
use std::io;

use crate::compact::{Compactor, OffsetMap};
use crate::core::Core;
use crate::cursor::WriteCursor;
use crate::data::Data;
use crate::error::{Error, Result};
use crate::format::*;
use crate::hasher::Hasher;
use crate::path::{HashMapGetTarget, PathPart, WriteMode, hash_map_tag, sorted_map_tag};
use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};

/// A function run inside a write, with a cursor to the slot the path led to.
pub(crate) type ContextFn<'f, 'a, C> =
    Box<dyn FnOnce(&mut WriteCursor<'a, C>) -> Result<()> + 'f>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Transaction {
    pub id: u64,
    pub root_position: Option<i64>,
    // the copy of the root slot that the transaction works on
    pub scratch_position: Option<i64>,
    pub frozen_at: Option<i64>,
}

impl Transaction {
    // whether position is the transaction's root, which stays writable after freezing
    fn is_root_position(&self, position: Option<i64>) -> bool {
        position.is_some() && position == self.root_position
    }

    // whether position is the copy of the root slot that the transaction works on
    fn is_scratch_position(&self, position: Option<i64>) -> bool {
        position.is_some() && position == self.scratch_position
    }
}

pub(crate) struct HashMapGetResult {
    pub slot_ptr: SlotPointer,
    pub is_empty: bool,
}

/// An immutable database.
///
/// Every transaction efficiently creates a new "copy" of the data, and past
/// copies can still be read from. A `Database` is not thread safe; each
/// thread should open its own instance (reads never block writes, so this
/// works even while another instance is writing).
pub struct Database<C: Core> {
    core: RefCell<C>,
    hasher: Hasher,
    header: Cell<Header>,
    pub(crate) tx_start: Cell<Option<i64>>,
    pub(crate) transaction: Cell<Option<Transaction>>,
    next_transaction_id: Cell<u64>,
}

impl<C: Core> std::fmt::Debug for Database<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Database")
            .field("header", &self.header.get())
            .field("tx_start", &self.tx_start.get())
            .finish_non_exhaustive()
    }
}

/// Resets a cell to `None` when dropped, like a Go `defer`.
struct ResetOnDrop<'a, T: Copy>(&'a Cell<Option<T>>);

impl<T: Copy> Drop for ResetOnDrop<'_, T> {
    fn drop(&mut self) {
        self.0.set(None);
    }
}

pub(crate) fn is_root(slot_ptr: &SlotPointer) -> bool {
    slot_ptr.position == Some(ROOT_HEADER_START)
}

/// Resolves a possibly-negative index against `size`, or returns
/// [`Error::KeyNotFound`] if it's out of range.
fn resolve_index(index: i64, size: i64) -> Result<i64> {
    if index >= size || index < -size {
        return Err(Error::KeyNotFound);
    }
    Ok(if index < 0 { size + index } else { index })
}

/// The nibble of the big-endian hash at `offset` nibbles from its least
/// significant end.
fn hash_nibble(hash: &[u8], offset: usize) -> usize {
    if offset / 2 >= hash.len() {
        return 0;
    }
    let byte = hash[hash.len() - 1 - offset / 2];
    (if offset % 2 == 0 { byte & 0xf } else { byte >> 4 }) as usize
}

fn random_u64() -> Result<u64> {
    getrandom::u64().map_err(|err| Error::Io(io::Error::other(err.to_string())))
}

impl<C: Core> Database<C> {
    /// Opens the database in `core`, initializing it if the core is empty.
    pub fn new(core: C, hasher: Hasher) -> Result<Database<C>> {
        let db = Database {
            core: RefCell::new(core),
            header: Cell::new(Header {
                file_id: 0,
                hash_id: 0,
                hash_size: 0,
                version: VERSION,
                magic_number: MAGIC_NUMBER,
            }),
            hasher,
            tx_start: Cell::new(None),
            transaction: Cell::new(None),
            next_transaction_id: Cell::new(1),
        };

        db.seek(0)?;
        if db.len()? == 0 {
            let file_id = match db.hasher.file_id {
                0 => random_u64()?,
                file_id => file_id,
            };
            let header = Header {
                file_id,
                hash_id: db.hasher.id,
                hash_size: u16::try_from(db.hasher.hash_size()).map_err(|_| Error::InvalidHashSize)?,
                version: VERSION,
                magic_number: MAGIC_NUMBER,
            };
            db.header.set(header);
            db.write_bytes(&header.to_bytes())?;
            // write the root header and commit an empty root, so the
            // file ends with a trailer like after any transaction
            db.write_bytes(&RootHeader { file_size: 0, root: Slot::default() }.to_bytes())?;
            // the first commit's ID is 0, so a new database's bytes only
            // depend on its file ID
            db.commit_root(Slot::default(), 0)?;
            db.core().sync()?;
        } else {
            let header = db.read_and_validate_header()?;
            db.header.set(header);
            db.committed_size()?;
        }

        Ok(db)
    }

    /// The database header.
    pub fn header(&self) -> Header {
        self.header.get()
    }

    pub fn hasher(&self) -> &Hasher {
        &self.hasher
    }

    /// Hashes `data` with the database's hasher.
    pub fn digest(&self, data: &[u8]) -> Vec<u8> {
        self.hasher.digest(data)
    }

    /// Borrows the underlying core. Don't hold on to it while using
    /// cursors, or they will panic.
    pub fn core(&self) -> RefMut<'_, C> {
        self.core.borrow_mut()
    }

    pub fn into_core(self) -> C {
        self.core.into_inner()
    }

    // i/o helpers. each borrows the core only for the duration of the call,
    // so they can be used while user callbacks are running.

    pub(crate) fn seek(&self, pos: i64) -> Result<()> {
        let pos = u64::try_from(pos).map_err(|_| Error::InvalidOffset)?;
        Ok(self.core().seek_to(pos)?)
    }

    pub(crate) fn len(&self) -> Result<i64> {
        Ok(self.core().length()? as i64)
    }

    pub(crate) fn read_bytes(&self, buf: &mut [u8]) -> Result<()> {
        Ok(self.core().read(buf)?)
    }

    pub(crate) fn write_bytes(&self, buf: &[u8]) -> Result<()> {
        Ok(self.core().write(buf)?)
    }

    pub(crate) fn read_at(&self, pos: i64, buf: &mut [u8]) -> Result<()> {
        self.seek(pos)?;
        self.read_bytes(buf)
    }

    pub(crate) fn write_at(&self, pos: i64, buf: &[u8]) -> Result<()> {
        self.seek(pos)?;
        self.write_bytes(buf)
    }

    /// Writes `buf` at the end and returns its position.
    pub(crate) fn append(&self, buf: &[u8]) -> Result<i64> {
        let pos = self.len()?;
        self.write_at(pos, buf)?;
        Ok(pos)
    }

    /// Validates the length of a byte array read from disk before a buffer
    /// is allocated for it, so corrupt data can't cause a huge allocation.
    /// Small lengths aren't checked against the end of the database, which
    /// would cost a syscall on some cores; reading them fails anyway if
    /// they run past the end.
    pub(crate) fn checked_len(&self, pos: i64, len: i64) -> Result<usize> {
        const UNCHECKED_LEN: i64 = 1 << 16;
        if len < 0 {
            return Err(Error::ExpectedUnsignedLong);
        }
        if len > UNCHECKED_LEN && pos.checked_add(len).is_none_or(|end| end > self.len().unwrap_or(0)) {
            return Err(Error::InvalidDatabase);
        }
        usize::try_from(len).map_err(|_| Error::InvalidDatabase)
    }

    pub(crate) fn read_i64_at(&self, pos: i64) -> Result<i64> {
        let mut buf = [0u8; 8];
        self.read_at(pos, &mut buf)?;
        Ok(i64::from_be_bytes(buf))
    }

    pub(crate) fn write_i64_at(&self, pos: i64, value: i64) -> Result<()> {
        self.write_at(pos, &value.to_be_bytes())
    }

    pub(crate) fn read_slot_at(&self, pos: i64) -> Result<Slot> {
        let mut buf = [0u8; SLOT_LENGTH];
        self.read_at(pos, &mut buf)?;
        Slot::from_bytes(&buf)
    }

    pub(crate) fn write_slot_at(&self, pos: i64, slot: Slot) -> Result<()> {
        self.write_at(pos, &slot.to_bytes())
    }

    pub(crate) fn read_index_block(&self, pos: i64) -> Result<[Slot; SLOT_COUNT]> {
        let mut buf = [0u8; INDEX_BLOCK_SIZE];
        self.read_at(pos, &mut buf)?;
        decode_slots(&buf)
    }

    pub(crate) fn read_array_list_header(&self, pos: i64) -> Result<ArrayListHeader> {
        let mut buf = [0u8; ARRAY_LIST_HEADER_LENGTH];
        self.read_at(pos, &mut buf)?;
        ArrayListHeader::from_bytes(&buf)
    }

    pub(crate) fn read_btree_header(&self, pos: i64) -> Result<BTreeHeader> {
        let mut buf = [0u8; BTREE_HEADER_LENGTH];
        self.read_at(pos, &mut buf)?;
        BTreeHeader::from_bytes(&buf)
    }

    pub(crate) fn hash_size(&self) -> usize {
        self.header.get().hash_size as usize
    }

    fn read_and_validate_header(&self) -> Result<Header> {
        self.seek(0)?;
        let header = Header::read(&mut *self.core())?;
        header.validate()?;
        if header.hash_size as usize != self.hasher.hash_size() {
            return Err(Error::InvalidHashSize);
        }
        Ok(header)
    }

    /// A cursor to the root of the database. Writes through it are
    /// transactions.
    pub fn root_cursor(&self) -> WriteCursor<'_, C> {
        // the cursor only holds a snapshot of the root slot, and every
        // operation that starts at it reads the root again. if this read
        // fails, the cursor looks empty and the next operation returns the error.
        let root = self.read_root_slot().unwrap_or_default();
        WriteCursor::new(SlotPointer::new(Some(ROOT_HEADER_START), root), self)
    }

    /// Runs `f` with a write cursor to the root in a single transaction,
    /// discarding everything it wrote if it returns an error. Use it to
    /// group writes to a root that isn't an array list, such as a hash map.
    /// For an array list root, [`WriteArrayList::append_context`](crate::WriteArrayList::append_context)
    /// does the same.
    pub fn run_context<'a>(
        &'a self,
        f: impl FnOnce(&mut WriteCursor<'a, C>) -> Result<()>,
    ) -> Result<()> {
        self.root_cursor().write_path_context(&[], f).map(|_| ())
    }

    /// Makes all writes in the current transaction treat the data written
    /// so far as immutable, so they copy it instead of changing it.
    pub fn freeze(&self) -> Result<()> {
        let (Some(mut active), Some(_)) = (self.transaction.get(), self.tx_start.get()) else {
            return Err(Error::ExpectedTxStart);
        };
        let length = self.len()?;
        self.tx_start.set(Some(length));
        active.frozen_at = Some(length);
        self.transaction.set(Some(active));
        Ok(())
    }

    pub(crate) fn begin_transaction(&self) -> u64 {
        let id = self.next_transaction_id.get();
        self.next_transaction_id.set(id + 1);
        self.transaction.set(Some(Transaction {
            id,
            root_position: None,
            scratch_position: None,
            frozen_at: None,
        }));
        id
    }

    pub(crate) fn transaction_id(&self) -> Option<u64> {
        self.transaction.get().map(|t| t.id)
    }

    // replication

    /// This database's [`ReplicaState`].
    pub fn replica_state(&self) -> Result<ReplicaState> {
        let committed_size = self.committed_size()?;
        let trailer = self.read_root_trailer(committed_size)?;
        Ok(ReplicaState { committed_size, checksum: trailer.checksum })
    }

    /// Where to start sending committed bytes to a replica in `state`.
    /// That's its committed size if its bytes are a prefix of this
    /// database, or 0 if it must be replaced, because it's a replica of
    /// another file or it has diverged from this one.
    pub fn replication_start(&self, state: ReplicaState) -> Result<i64> {
        let committed_size = self.committed_size()?;
        if state.committed_size > committed_size {
            return Ok(0);
        }
        match self.read_root_trailer(state.committed_size) {
            Ok(trailer) if trailer.checksum == state.checksum => Ok(state.committed_size),
            Ok(_) | Err(Error::InvalidDatabase | Error::UnexpectedTag) => Ok(0),
            Err(err) => Err(err),
        }
    }

    /// Writes the committed bytes from `start` up to `end` to `w`. `start`
    /// is usually from [`Database::replication_start`], and `end` can't be
    /// past [`Database::committed_size`]. Committed bytes never change
    /// except for the root header, so when `start` is 0, a root header
    /// matching `end` is written, making the bytes a complete database by
    /// themselves.
    pub fn read_committed(&self, start: i64, end: i64, w: &mut impl io::Write) -> Result<()> {
        let committed_size = self.committed_size()?;
        if start < 0 || start > end || end > committed_size {
            return Err(Error::InvalidRange);
        }
        if start > 0 && start < ROOT_HEADER_END {
            return Err(Error::InvalidRange);
        }
        if start == 0 {
            let trailer = self.read_root_trailer(end)?;
            self.stream_bytes(w, 0, ROOT_HEADER_START)?;
            w.write_all(&RootHeader { file_size: end, root: trailer.root }.to_bytes())?;
            return self.stream_bytes(w, ROOT_HEADER_END, end - ROOT_HEADER_END);
        }
        self.stream_bytes(w, start, end - start)
    }

    // writes length bytes, starting at start, to w
    fn stream_bytes(&self, w: &mut impl io::Write, start: i64, mut length: i64) -> Result<()> {
        self.seek(start)?;
        let mut buf = vec![0u8; length.clamp(0, 4096) as usize];
        while length > 0 {
            let chunk = length.min(buf.len() as i64) as usize;
            self.read_bytes(&mut buf[..chunk])?;
            w.write_all(&buf[..chunk])?;
            length -= chunk as i64;
        }
        Ok(())
    }

    /// Writes `length` bytes from `r` at `start` and commits them. They
    /// must be the bytes from [`Database::read_committed`], so they end with
    /// a trailer. When `start` is 0, this database is replaced by them;
    /// otherwise `start` must be this database's committed size.
    pub fn apply_replicated(&self, start: i64, r: &mut impl io::Read, length: i64) -> Result<()> {
        if start == 0 {
            self.core().set_length(0)?;
        } else {
            if start != self.committed_size()? {
                return Err(Error::InvalidRange);
            }
            // discard anything past the committed bytes, such as the remains of an interrupted sync
            self.truncate()?;
        }

        self.seek(start)?;
        let mut buf = vec![0u8; length.clamp(0, 4096) as usize];
        let mut remaining = length;
        while remaining > 0 {
            let chunk = remaining.min(buf.len() as i64) as usize;
            r.read_exact(&mut buf[..chunk])?;
            self.write_bytes(&buf[..chunk])?;
            remaining -= chunk as i64;
        }

        if start == 0 {
            // the bytes are a different database, with its own header
            self.core().sync()?;
            let header = self.read_and_validate_header()?;
            self.header.set(header);
            self.committed_size()?;
        } else if length > 0 {
            // the bytes must end with a trailer. update the root header to match it.
            let trailer = self.read_root_trailer(start + length)?;
            self.core().sync()?;
            self.write_root_header(trailer.root)?;
            self.core().sync()?;
        }
        Ok(())
    }

    // compaction

    /// Copies the data reachable from the latest copy (moment) of this
    /// database into a new database in `target_core`, so it no longer
    /// contains the history. If the root is an array list, its last moment
    /// becomes the only moment of the new one.
    ///
    /// `offset_map` is reset and then records where each copied object
    /// lives, so shared references and cycles stay shared. The target must
    /// be a new or empty database, or this returns [`Error::TargetNotEmpty`].
    pub fn compact<T: Core>(
        &self,
        target_core: T,
        offset_map: &mut dyn OffsetMap,
    ) -> Result<Database<T>> {
        // cached offsets only apply to this compaction's target
        offset_map.reset()?;
        let mut hasher = self.hasher.clone();
        hasher.id = self.header.get().hash_id;
        hasher.file_id = 0;
        let target = Database::new(target_core, hasher)?;

        // the target must be a new or empty database, because compaction
        // writes to it with ordinary transactions.
        if !target.read_root_slot()?.is_empty() {
            return Err(Error::TargetNotEmpty);
        }

        let source_root = self.read_root_slot()?;
        // an empty root compacts to a new database. a root explicitly
        // set to null isn't empty, so it is remapped below.
        if source_root.is_empty() {
            return Ok(target);
        }

        // the target is written as one ordinary transaction, so it is
        // committed and fsynced like any other. the remap must run inside
        // the transaction, because starting one truncates the target.
        let remap = |slot: Slot| {
            let target = &target;
            move |cursor: &mut WriteCursor<'_, T>| -> Result<()> {
                let mut compactor = Compactor {
                    source: self,
                    target,
                    hash_size: self.hash_size(),
                    offset_map,
                };
                let remapped = compactor.remap_slot(slot)?;
                cursor.write(Data::Slot(remapped))
            }
        };

        match source_root.tag {
            Tag::ArrayList => {
                // an array list root is a history, and its latest moment
                // becomes the only moment of a new one
                let last_moment = self.root_cursor().read_path_slot(&[PathPart::ArrayListGet(-1)])?;
                if let Some(last_moment) = last_moment.filter(|slot| !slot.is_empty()) {
                    target.root_cursor().write_path_context(
                        &[PathPart::ArrayListInit, PathPart::ArrayListAppend],
                        remap(last_moment),
                    )?;
                }
            }
            // any other root is remapped whole
            _ => target.run_context(remap(source_root))?,
        }

        Ok(target)
    }

    // committed size

    /// The number of bytes that belong to committed transactions. They
    /// never change except for the root header (see
    /// [`Database::read_committed`]).
    pub fn committed_size(&self) -> Result<i64> {
        let header = self.read_root_header()?;
        let minimum_size = ROOT_HEADER_END + ROOT_TRAILER_LENGTH as i64;
        if header.file_size < minimum_size {
            return Err(Error::InvalidDatabase);
        }
        if self.len()? < header.file_size {
            return Err(Error::TruncatedDatabase);
        }
        // the committed bytes must end with a trailer matching the header
        let trailer = self.read_root_trailer(header.file_size)?;
        if trailer.root != header.root {
            return Err(Error::InvalidDatabase);
        }
        Ok(header.file_size)
    }

    pub(crate) fn truncate(&self) -> Result<()> {
        let committed_size = self.committed_size()?;
        if let Some(frozen_at) = self.transaction.get().and_then(|t| t.frozen_at)
            && frozen_at > committed_size
        {
            // retain frozen bytes without publishing the failed transaction.
            // discard what follows the frozen bytes, then commit the current
            // root again after them, so they end with a trailer
            if self.len()? > frozen_at {
                self.core().set_length(frozen_at as u64)?;
            }
            let root = self.read_root_slot()?;
            self.commit_root(root, random_u64()?)?;
            self.core().sync()?;
            return Ok(());
        }
        if self.len()? > committed_size {
            self.core().set_length(committed_size as u64)?;
        }
        Ok(())
    }

    pub(crate) fn read_root_header(&self) -> Result<RootHeader> {
        let mut buf = [0u8; ROOT_HEADER_LENGTH];
        self.read_at(ROOT_HEADER_START, &mut buf)?;
        RootHeader::from_bytes(&buf)
    }

    // the most recently committed root slot
    pub(crate) fn read_root_slot(&self) -> Result<Slot> {
        Ok(self.read_root_header()?.root)
    }

    // the trailer that ends at end
    pub(crate) fn read_root_trailer(&self, end: i64) -> Result<RootTrailer> {
        if end < ROOT_TRAILER_LENGTH as i64 {
            return Err(Error::InvalidDatabase);
        }
        let trailer_pos = end - ROOT_TRAILER_LENGTH as i64;
        let mut buf = [0u8; ROOT_TRAILER_LENGTH];
        self.read_at(trailer_pos, &mut buf)?;
        // check the checksum before decoding the root, because a corrupt
        // trailer can hold an unknown tag
        let checksum = read_u64(&buf[SLOT_LENGTH + 8..]);
        let commit_id = read_u64(&buf[SLOT_LENGTH..SLOT_LENGTH + 8]);
        let root_bytes: [u8; SLOT_LENGTH] = buf[..SLOT_LENGTH].try_into().unwrap();
        let expected = crate::crc64::checksum(&{
            let mut data = [0u8; 24 + SLOT_LENGTH];
            data[0..8].copy_from_slice(&self.header.get().file_id.to_be_bytes());
            data[8..16].copy_from_slice(&trailer_pos.to_be_bytes());
            data[16..16 + SLOT_LENGTH].copy_from_slice(&root_bytes);
            data[16 + SLOT_LENGTH..].copy_from_slice(&commit_id.to_be_bytes());
            data
        });
        if checksum != expected {
            return Err(Error::InvalidDatabase);
        }
        RootTrailer::from_bytes(&buf)
    }

    // completes a transaction by appending a trailer for root and updating
    // the root header. callers must sync afterwards to make the header
    // itself durable.
    pub(crate) fn commit_root(&self, root: Slot, commit_id: u64) -> Result<()> {
        let trailer_pos = self.len()?;
        let trailer = RootTrailer::new(self.header.get().file_id, trailer_pos, root, commit_id);
        self.write_at(trailer_pos, &trailer.to_bytes())?;

        // flush and fsync before updating the header, because updating
        // the header is what completes the transaction. without the
        // fsync, the OS could persist the header before the data it
        // points to, so a crash could commit a transaction whose data
        // never reached disk.
        self.core().sync()?;

        self.write_root_header(root)
    }

    // points the root header at root, which must be in the trailer that ends
    // the file.
    fn write_root_header(&self, root: Slot) -> Result<()> {
        let file_size = self.len()?;
        self.write_at(ROOT_HEADER_START, &RootHeader { file_size, root }.to_bytes())
    }

    // whether the data at ptr predates this transaction, or the writing
    // cursor's freeze point, so it must be copied before it is modified.
    // writes only happen inside a transaction.
    pub(crate) fn is_old(&self, ptr: i64, frozen_at: i64) -> Result<bool> {
        let tx_start = self.tx_start.get().ok_or(Error::ExpectedTxStart)?;
        Ok(ptr < tx_start.max(frozen_at))
    }

    // copies an index block to the end unless it was made in this transaction
    fn copy_index_block_if_old(&self, ptr: i64, frozen_at: i64) -> Result<i64> {
        if !self.is_old(ptr, frozen_at)? {
            return Ok(ptr);
        }
        let mut block = [0u8; INDEX_BLOCK_SIZE];
        self.read_at(ptr, &mut block)?;
        self.append(&block)
    }

    fn check_hash<'h>(&self, hash: &'h [u8]) -> Result<&'h [u8]> {
        if hash.len() != self.hash_size() {
            return Err(Error::InvalidHashSize);
        }
        Ok(hash)
    }

    // reject writes into frozen data; the current transaction's root slot remains writable
    pub(crate) fn check_frozen_slot(&self, slot_ptr: &SlotPointer) -> Result<()> {
        if let Some(active) = self.transaction.get()
            && let (Some(frozen_at), Some(position)) = (active.frozen_at, slot_ptr.position)
            && position < frozen_at
            && !active.is_root_position(slot_ptr.position)
        {
            return Err(Error::FrozenSlot);
        }
        Ok(())
    }

    // copy frozen collection storage before mutation to preserve existing readers
    fn copy_collection_if_frozen(
        &self,
        slot_ptr: SlotPointer,
        init: PathPart<'_>,
        frozen_at: i64,
    ) -> Result<SlotPointer> {
        if let Some(tx_frozen_at) = self.transaction.get().and_then(|t| t.frozen_at)
            && slot_ptr.slot.value < tx_frozen_at
        {
            return self.read_part(init, WriteMode::ReadWrite, &[init], 0, slot_ptr, frozen_at, &mut None);
        }
        Ok(slot_ptr)
    }

    // the central path-traversal method. `ctx`, if any, runs at the end of
    // the path, as if it were its last part.
    pub(crate) fn read_slot_pointer<'a>(
        &'a self,
        write_mode: WriteMode,
        path: &[PathPart<'_>],
        path_i: usize,
        slot_ptr: SlotPointer,
        frozen_at: i64,
        ctx: &mut Option<ContextFn<'_, 'a, C>>,
    ) -> Result<SlotPointer> {
        if path_i == path.len() && ctx.is_none() {
            if write_mode == WriteMode::ReadOnly && slot_ptr.slot.is_empty() {
                return Err(Error::KeyNotFound);
            }
            return Ok(slot_ptr);
        }
        if write_mode == WriteMode::ReadWrite {
            self.check_frozen_slot(&slot_ptr)?;
        }

        // every write that starts at the root is a transaction
        if is_root(&slot_ptr) {
            return self.read_root_slot_pointer(write_mode, path, path_i, frozen_at, ctx);
        }

        match path.get(path_i) {
            Some(&part) => self.read_part(part, write_mode, path, path_i, slot_ptr, frozen_at, ctx),
            None => {
                let f = ctx.take().expect("checked above");
                if write_mode == WriteMode::ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let mut cursor = WriteCursor::new(slot_ptr, self);
                cursor.frozen_at = frozen_at;
                f(&mut cursor)?;
                Ok(cursor.slot_ptr)
            }
        }
    }

    fn read_root_slot_pointer<'a>(
        &'a self,
        write_mode: WriteMode,
        path: &[PathPart<'_>],
        path_i: usize,
        frozen_at: i64,
        ctx: &mut Option<ContextFn<'_, 'a, C>>,
    ) -> Result<SlotPointer> {
        let root = self.read_root_slot()?;

        // the position of a read path doesn't matter, but it must not be
        // ROOT_HEADER_START or this would recurse forever
        if write_mode == WriteMode::ReadOnly {
            return self.read_slot_pointer(write_mode, path, path_i, SlotPointer::new(None, root), frozen_at, ctx);
        }

        // initializing an initialized root is free, so a wrapper like
        // WriteArrayList can hold a root cursor without a transaction. like
        // starting one, it discards data left by an unfinished transaction.
        // (write_path rejects root writes inside a transaction, so none is
        // open here.)
        if ctx.is_none()
            && path.len() - path_i == 1
            && root.tag != Tag::None
            && path[path_i].init_tag() == Some(root.tag)
        {
            self.truncate()?;
            return Ok(SlotPointer::new(Some(ROOT_HEADER_START), root));
        }

        // discard data left by an unfinished transaction after a crash
        self.truncate()?;
        let scratch_pos = self.len()?;
        self.tx_start.set(Some(scratch_pos));
        let _reset_tx_start = ResetOnDrop(&self.tx_start);
        // the copy is the transaction's root, so it stays writable after freezing
        if let Some(mut active) = self.transaction.get() {
            active.root_position = Some(scratch_pos);
            active.scratch_position = Some(scratch_pos);
            self.transaction.set(Some(active));
        }

        // the transaction works on a copy of the root slot
        self.write_slot_at(scratch_pos, root)?;
        let mut root_ptr = SlotPointer::new(Some(scratch_pos), root);

        // every collection expects its init part to copy its header or root
        // block into the transaction before anything writes to it. the root
        // has no enclosing init part, so run one here.
        if let Some(init) = PathPart::init_for(root.tag) {
            root_ptr = self.read_slot_pointer(write_mode, &[init], 0, root_ptr, frozen_at, &mut None)?;
        }

        let mut result = self.read_slot_pointer(write_mode, path, path_i, root_ptr, frozen_at, ctx)?;

        // the copy now holds the new root, so commit it
        let next_root = self.read_slot_at(scratch_pos)?;
        self.commit_root(next_root, random_u64()?)?;

        // a path that ends at the root (such as an init or a write) returns
        // a root cursor, so it can be used for later transactions
        if result.position == Some(scratch_pos) {
            result = SlotPointer::new(Some(ROOT_HEADER_START), next_root);
        }
        Ok(result)
    }

    #[allow(clippy::too_many_arguments)]
    fn read_part<'a>(
        &'a self,
        part: PathPart<'_>,
        write_mode: WriteMode,
        path: &[PathPart<'_>],
        path_i: usize,
        slot_ptr: SlotPointer,
        frozen_at: i64,
        ctx: &mut Option<ContextFn<'_, 'a, C>>,
    ) -> Result<SlotPointer> {
        use WriteMode::*;

        let next = |slot_ptr: SlotPointer, ctx: &mut Option<ContextFn<'_, 'a, C>>| {
            self.read_slot_pointer(write_mode, path, path_i + 1, slot_ptr, frozen_at, ctx)
        };

        match part {
            PathPart::ArrayListInit => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let array_list_start = match slot_ptr.slot.tag {
                    Tag::None => {
                        let start = self.len()?;
                        let header = ArrayListHeader {
                            ptr: start + ARRAY_LIST_HEADER_LENGTH as i64,
                            size: 0,
                        };
                        self.write_at(start, &header.to_bytes())?;
                        self.write_bytes(&[0u8; INDEX_BLOCK_SIZE])?;
                        start
                    }
                    Tag::ArrayList => {
                        let mut start = slot_ptr.slot.value;
                        // copy it to the end unless it was made in this transaction
                        if self.is_old(start, frozen_at)? {
                            let header = self.read_array_list_header(start)?;
                            let mut block = [0u8; INDEX_BLOCK_SIZE];
                            self.read_at(header.ptr, &mut block)?;
                            let new_start = self.len()?;
                            let header = ArrayListHeader {
                                ptr: new_start + ARRAY_LIST_HEADER_LENGTH as i64,
                                size: header.size,
                            };
                            self.write_at(new_start, &header.to_bytes())?;
                            self.write_bytes(&block)?;
                            start = new_start;
                        }
                        start
                    }
                    _ => return Err(Error::UnexpectedTag),
                };
                let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(array_list_start, Tag::ArrayList));
                self.write_slot_at(position, next_slot_ptr.slot)?;
                next(next_slot_ptr, ctx)
            }

            PathPart::ArrayListGet(index) => {
                match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::ArrayList => {}
                    _ => return Err(Error::UnexpectedTag),
                }
                let mut slot_ptr = slot_ptr;
                if write_mode == ReadWrite {
                    slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::ArrayListInit, frozen_at)?;
                }
                let header = self.read_array_list_header(slot_ptr.slot.value)?;
                let key = resolve_index(index, header.size)?;
                let shift = array_list_shift(header.size - 1);
                let final_slot_ptr = self.read_array_list_slot(header.ptr, key, shift, write_mode, frozen_at)?;
                next(final_slot_ptr, ctx)
            }

            PathPart::ArrayListAppend => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                if slot_ptr.slot.tag != Tag::ArrayList {
                    return Err(Error::UnexpectedTag);
                }
                let slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::ArrayListInit, frozen_at)?;
                let start = slot_ptr.slot.value;
                let orig_header = self.read_array_list_header(start)?;
                let (header, appended) = self.read_array_list_slot_append(orig_header, write_mode, frozen_at)?;
                // update the header before callbacks can freeze it
                self.write_at(start, &header.to_bytes())?;
                // the appended moment becomes the transaction's root, so it
                // stays writable after freezing. the top-level history is the
                // list held by the copy of the root slot.
                if let Some(mut active) = self.transaction.get()
                    && active.is_scratch_position(slot_ptr.position)
                {
                    active.root_position = appended.position;
                    self.transaction.set(Some(active));
                }
                next(appended, ctx)
            }

            PathPart::ArrayListSlice(size) => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                if slot_ptr.slot.tag != Tag::ArrayList {
                    return Err(Error::UnexpectedTag);
                }
                let slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::ArrayListInit, frozen_at)?;
                let start = slot_ptr.slot.value;
                let orig_header = self.read_array_list_header(start)?;
                let slice_header = self.read_array_list_slice(orig_header, size, frozen_at)?;
                // update the header before callbacks can freeze it
                self.write_at(start, &slice_header.to_bytes())?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListInit => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let header_ptr = match slot_ptr.slot.tag {
                    Tag::None => {
                        // create an empty tree: a single empty leaf plus a header
                        let root_ptr = self.write_btree_node(&BTreeNode::empty(BTreeNodeKind::Leaf, 0))?;
                        self.append(&BTreeHeader { root_ptr, size: 0 }.to_bytes())?
                    }
                    Tag::LinkedArrayList => {
                        // copy the header into this transaction unless it was made
                        // in it, so past moments still pointing at the old header
                        // are unaffected. b-tree nodes are copied on write, so
                        // only the header needs copying.
                        self.copy_header_if_old(slot_ptr.slot.value, frozen_at)?
                    }
                    _ => return Err(Error::UnexpectedTag),
                };
                let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(header_ptr, Tag::LinkedArrayList));
                self.write_slot_at(position, next_slot_ptr.slot)?;
                next(next_slot_ptr, ctx)
            }

            PathPart::LinkedArrayListGet(index) => {
                match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::LinkedArrayList => {}
                    _ => return Err(Error::UnexpectedTag),
                }
                let mut slot_ptr = slot_ptr;
                if write_mode == ReadWrite {
                    slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::LinkedArrayListInit, frozen_at)?;
                }
                let header_ptr = slot_ptr.slot.value;
                let header = self.read_btree_header(header_ptr)?;
                let rank = resolve_index(index, header.size)?;

                if write_mode == ReadOnly {
                    let final_slot_ptr = self.read_btree_slot(header.root_ptr, rank)?;
                    return next(final_slot_ptr, ctx);
                }

                // path-copy down to the value slot so the write is persistent
                let write_slot = self.btree_get_for_write(header.root_ptr, rank, frozen_at)?;
                // update the header before callbacks can freeze it
                if write_slot.node_ptr != header.root_ptr {
                    let new_header = BTreeHeader { root_ptr: write_slot.node_ptr, size: header.size };
                    self.write_at(header_ptr, &new_header.to_bytes())?;
                }
                next(SlotPointer::new(Some(write_slot.value_position), write_slot.slot), ctx)
            }

            PathPart::LinkedArrayListAppend => {
                let (slot_ptr, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                let _ = slot_ptr;
                let result = self.btree_insert(header.root_ptr, header.size, frozen_at)?;
                let new_root_ptr = self.btree_make_root(result.join)?;
                // update the header before filling in the value, so that a
                // failure in the rest of the path leaves the tree and header
                // consistent
                let new_header = BTreeHeader { root_ptr: new_root_ptr, size: header.size + 1 };
                self.write_at(header_ptr, &new_header.to_bytes())?;
                // fill in the value via the rest of the path
                next(SlotPointer::new(Some(result.value_position), Slot::default()), ctx)
            }

            PathPart::LinkedArrayListSlice { offset, size } => {
                let (slot_ptr, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                // bounds-checked without overflow (offset + size could wrap)
                if offset < 0 || size < 0 || offset > header.size || size > header.size - offset {
                    return Err(Error::KeyNotFound);
                }
                // slice = drop [0, offset) then keep [0, size) of what's left
                let after_offset = self.btree_split(header.root_ptr, offset)?;
                let sliced = self.btree_split(after_offset.1, size)?;
                // update the header before recursing into the rest of the
                // path, so that a failure there leaves the tree and header
                // consistent
                self.write_at(header_ptr, &BTreeHeader { root_ptr: sliced.0, size }.to_bytes())?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListConcat(list) => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                if slot_ptr.slot.tag != Tag::LinkedArrayList || list.tag != Tag::LinkedArrayList {
                    return Err(Error::UnexpectedTag);
                }
                let (slot_ptr, header_ptr, header_a) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                let header_b = self.read_btree_header(list.value)?;
                // the join result shares subtrees with both operands (and the
                // second operand stays live), so freeze everything created so
                // far: later in-place mutations will then copy those nodes
                // instead of overwriting a node that is still referenced
                // elsewhere.
                self.tx_start.set(Some(self.len()?));
                let new_root_ptr = self.btree_join(header_a.root_ptr, header_b.root_ptr)?;
                // update the header before recursing into the rest of the
                // path, so that a failure there leaves the tree and header
                // consistent
                let new_header = BTreeHeader { root_ptr: new_root_ptr, size: header_a.size + header_b.size };
                self.write_at(header_ptr, &new_header.to_bytes())?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListInsert(index) => {
                let (_, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                let rank = resolve_index(index, header.size)?;
                let result = self.btree_insert(header.root_ptr, rank, frozen_at)?;
                let new_root_ptr = self.btree_make_root(result.join)?;
                // update the header before filling in the value, so that a
                // failure in the rest of the path leaves the tree and header
                // consistent
                let new_header = BTreeHeader { root_ptr: new_root_ptr, size: header.size + 1 };
                self.write_at(header_ptr, &new_header.to_bytes())?;
                next(SlotPointer::new(Some(result.value_position), Slot::default()), ctx)
            }

            PathPart::LinkedArrayListRemove(index) => {
                let (slot_ptr, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                let rank = resolve_index(index, header.size)?;
                let new_root_ptr = if header.size == 1 {
                    self.btree_new_root()?
                } else {
                    let mut root = self.btree_remove(header.root_ptr, rank, frozen_at)?;
                    let mut new_root_ptr = self.btree_write_node(&root, header.root_ptr, frozen_at)?;
                    // a root left with one child is replaced by it
                    while root.kind == BTreeNodeKind::Branch && root.num == 1 {
                        new_root_ptr = root.children[0].value;
                        root = self.read_btree_node(new_root_ptr)?;
                    }
                    new_root_ptr
                };
                // update the header before recursing into the rest of the
                // path, so that a failure there leaves the tree and header
                // consistent
                let new_header = BTreeHeader { root_ptr: new_root_ptr, size: header.size - 1 };
                self.write_at(header_ptr, &new_header.to_bytes())?;
                next(slot_ptr, ctx)
            }

            PathPart::HashMapInit { counted, set } => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let tag = hash_map_tag(counted, set);
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let map_start = match slot_ptr.slot.tag {
                    Tag::None => {
                        let map_start = self.len()?;
                        self.seek(map_start)?;
                        if counted {
                            self.write_bytes(&0i64.to_be_bytes())?;
                        }
                        self.write_bytes(&[0u8; INDEX_BLOCK_SIZE])?;
                        map_start
                    }
                    Tag::HashMap | Tag::HashSet | Tag::CountedHashMap | Tag::CountedHashSet => {
                        let is_counted = matches!(slot_ptr.slot.tag, Tag::CountedHashMap | Tag::CountedHashSet);
                        if counted != is_counted {
                            return Err(Error::UnexpectedTag);
                        }
                        let mut map_start = slot_ptr.slot.value;
                        // copy it to the end unless it was made in this transaction
                        if self.is_old(map_start, frozen_at)? {
                            let len = INDEX_BLOCK_SIZE + if counted { 8 } else { 0 };
                            let mut buf = vec![0u8; len];
                            self.read_at(map_start, &mut buf)?;
                            map_start = self.append(&buf)?;
                        }
                        map_start
                    }
                    _ => return Err(Error::UnexpectedTag),
                };
                let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(map_start, tag));
                self.write_slot_at(position, next_slot_ptr.slot)?;
                next(next_slot_ptr, ctx)
            }

            PathPart::HashMapGet(target) => {
                let (counted, set) = match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::HashMap => (false, false),
                    Tag::HashSet => (false, true),
                    Tag::CountedHashMap => (true, false),
                    Tag::CountedHashSet => (true, true),
                    _ => return Err(Error::UnexpectedTag),
                };
                let mut slot_ptr = slot_ptr;
                if write_mode == ReadWrite {
                    slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::HashMapInit { counted, set }, frozen_at)?;
                }
                let index_pos = slot_ptr.slot.value + if counted { 8 } else { 0 };
                let hash = self.check_hash(target.hash())?;
                let res = self.read_map_slot(index_pos, hash, 0, write_mode, target, frozen_at)?;
                if write_mode == ReadWrite && counted && res.is_empty {
                    let count = self.read_i64_at(slot_ptr.slot.value)?;
                    self.write_i64_at(slot_ptr.slot.value, count.wrapping_add(1))?;
                }
                next(res.slot_ptr, ctx)
            }

            PathPart::HashMapRemove(hash) => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let (counted, set) = match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::HashMap => (false, false),
                    Tag::HashSet => (false, true),
                    Tag::CountedHashMap => (true, false),
                    Tag::CountedHashSet => (true, true),
                    _ => return Err(Error::UnexpectedTag),
                };
                let slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::HashMapInit { counted, set }, frozen_at)?;
                let index_pos = slot_ptr.slot.value + if counted { 8 } else { 0 };
                let hash = self.check_hash(hash)?;
                let key_found = match self.remove_map_slot(index_pos, hash, 0, frozen_at) {
                    Ok(_) => true,
                    Err(Error::KeyNotFound) => false,
                    Err(err) => return Err(err),
                };
                if !key_found {
                    return Err(Error::KeyNotFound);
                }
                if counted {
                    let count = self.read_i64_at(slot_ptr.slot.value)?;
                    self.write_i64_at(slot_ptr.slot.value, count.wrapping_sub(1))?;
                }
                Ok(slot_ptr)
            }

            PathPart::SortedMapInit { set } => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let tag = sorted_map_tag(set);
                let header_ptr = match slot_ptr.slot.tag {
                    Tag::None => {
                        let root_ptr = self.write_sorted_node(&SortedNode::empty(BTreeNodeKind::Leaf, 0))?;
                        self.append(&BTreeHeader { root_ptr, size: 0 }.to_bytes())?
                    }
                    Tag::SortedMap | Tag::SortedSet => {
                        if slot_ptr.slot.tag != tag {
                            return Err(Error::UnexpectedTag);
                        }
                        // copy the header into this transaction unless it was made in it
                        self.copy_header_if_old(slot_ptr.slot.value, frozen_at)?
                    }
                    _ => return Err(Error::UnexpectedTag),
                };
                let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(header_ptr, tag));
                self.write_slot_at(position, next_slot_ptr.slot)?;
                next(next_slot_ptr, ctx)
            }

            PathPart::SortedMapGet(target) => {
                let set = match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::SortedMap => false,
                    Tag::SortedSet => true,
                    _ => return Err(Error::UnexpectedTag),
                };
                let key = target.key();
                let mut slot_ptr = slot_ptr;
                if write_mode == ReadWrite {
                    slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::SortedMapInit { set }, frozen_at)?;
                }
                let header_ptr = slot_ptr.slot.value;
                let header = self.read_btree_header(header_ptr)?;

                if write_mode == ReadOnly {
                    let found = self.sorted_get(header.root_ptr, key)?.ok_or(Error::KeyNotFound)?;
                    let target_slot = self.sorted_target_slot(found.slot, target)?;
                    return next(target_slot, ctx);
                }

                let result = self.sorted_put(header.root_ptr, key, frozen_at)?;
                let new_root_ptr = self.sorted_grow_root(&result)?;
                // update the header before filling in the value, so that a
                // failure in the rest of the path leaves the tree and header
                // consistent (the entry exists with an empty value) rather
                // than inserted-but-uncounted
                let size = header.size + i64::from(result.added);
                self.write_at(header_ptr, &BTreeHeader { root_ptr: new_root_ptr, size }.to_bytes())?;
                let target_slot = self.sorted_target_slot(result.kv_slot, target)?;
                next(target_slot, ctx)
            }

            PathPart::SortedMapGetIndex(index) => {
                if write_mode == ReadWrite {
                    return Err(Error::WriteNotAllowed);
                }
                match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::SortedMap | Tag::SortedSet => {}
                    _ => return Err(Error::UnexpectedTag),
                }
                let header = self.read_btree_header(slot_ptr.slot.value)?;
                let rank = resolve_index(index, header.size)?;
                let found = self.sorted_get_by_index(header.root_ptr, rank)?;
                // return the entry so the caller can read key and value
                next(SlotPointer::new(Some(found.position), found.slot), ctx)
            }

            PathPart::SortedMapRemove(key) => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let set = match slot_ptr.slot.tag {
                    Tag::None => return Err(Error::KeyNotFound),
                    Tag::SortedMap => false,
                    Tag::SortedSet => true,
                    _ => return Err(Error::UnexpectedTag),
                };
                let slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::SortedMapInit { set }, frozen_at)?;
                let header_ptr = slot_ptr.slot.value;
                let header = self.read_btree_header(header_ptr)?;
                let (node_ptr, found) = self.sorted_remove(header.root_ptr, key, frozen_at)?;
                if !found {
                    return Err(Error::KeyNotFound);
                }
                self.write_at(header_ptr, &BTreeHeader { root_ptr: node_ptr, size: header.size - 1 }.to_bytes())?;
                Ok(slot_ptr)
            }

            PathPart::WriteData(data) => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let mut slot = match data {
                    Data::None => Slot::default(),
                    Data::Slot(slot) => *slot,
                    Data::Uint(value) => Slot::new(*value as i64, Tag::Uint),
                    Data::Int(value) => Slot::new(*value, Tag::Int),
                    Data::Float(value) => Slot::new(value.to_bits() as i64, Tag::Float),
                    Data::Bytes(bytes) if bytes.is_short() => {
                        let mut buf = [0u8; 8];
                        buf[..bytes.value.len()].copy_from_slice(&bytes.value);
                        if let Some(format_tag) = bytes.format_tag {
                            buf[6..].copy_from_slice(&format_tag);
                        }
                        Slot::new(i64::from_be_bytes(buf), Tag::ShortBytes).with_full(bytes.format_tag.is_some())
                    }
                    Data::Bytes(bytes) => {
                        let mut cursor = WriteCursor::new(slot_ptr, self);
                        let mut writer = cursor.writer()?;
                        writer.format_tag = bytes.format_tag;
                        io::Write::write_all(&mut writer, &bytes.value)?;
                        writer.finish()?;
                        writer.slot
                    }
                };
                if slot.tag == Tag::None {
                    slot = slot.with_full(true);
                }
                self.write_slot_at(position, slot)?;
                next(SlotPointer::new(slot_ptr.position, slot), ctx)
            }
        }
    }

    // validates a linked array list for a write and copies it if frozen,
    // returning it with its header position and header
    fn linked_array_list_for_write(
        &self,
        write_mode: WriteMode,
        slot_ptr: SlotPointer,
        frozen_at: i64,
    ) -> Result<(SlotPointer, i64, BTreeHeader)> {
        if write_mode == WriteMode::ReadOnly {
            return Err(Error::WriteNotAllowed);
        }
        if slot_ptr.slot.tag != Tag::LinkedArrayList {
            return Err(Error::UnexpectedTag);
        }
        let slot_ptr = self.copy_collection_if_frozen(slot_ptr, PathPart::LinkedArrayListInit, frozen_at)?;
        let header_ptr = slot_ptr.slot.value;
        let header = self.read_btree_header(header_ptr)?;
        Ok((slot_ptr, header_ptr, header))
    }

    // copies a b-tree header to the end unless it was made in this transaction
    fn copy_header_if_old(&self, header_ptr: i64, frozen_at: i64) -> Result<i64> {
        if !self.is_old(header_ptr, frozen_at)? {
            return Ok(header_ptr);
        }
        let mut buf = [0u8; BTREE_HEADER_LENGTH];
        self.read_at(header_ptr, &mut buf)?;
        self.append(&buf)
    }

    // hash map

    fn read_map_slot(
        &self,
        index_pos: i64,
        key_hash: &[u8],
        key_offset: usize,
        write_mode: WriteMode,
        target: HashMapGetTarget<'_>,
        frozen_at: i64,
    ) -> Result<HashMapGetResult> {
        let max_offset = self.hash_size() * 8 / BIT_COUNT as usize;
        if key_offset > max_offset {
            return Err(Error::KeyOffsetExceeded);
        }

        let i = hash_nibble(key_hash, key_offset);
        let slot_pos = index_pos + (SLOT_LENGTH * i) as i64;
        let slot = self.read_slot_at(slot_pos)?;
        let ptr = slot.value;

        // the slot pointer that the target asks for, given the entry's
        // slot and where its kv pair is
        let target_slot_ptr = |slot: Slot, kv_pos: i64, kv: &KeyValuePair| {
            let key_slot_pos = kv_pos + self.hash_size() as i64;
            let value_slot_pos = key_slot_pos + SLOT_LENGTH as i64;
            match target {
                HashMapGetTarget::KvPair(_) => SlotPointer::new(Some(slot_pos), slot),
                HashMapGetTarget::Key(_) => SlotPointer::new(Some(key_slot_pos), kv.key_slot),
                HashMapGetTarget::Value(_) => SlotPointer::new(Some(value_slot_pos), kv.value_slot),
            }
        };

        match slot.tag {
            Tag::None => match write_mode {
                WriteMode::ReadOnly => Err(Error::KeyNotFound),
                WriteMode::ReadWrite => {
                    // write hash and key/val slots
                    let kv = KeyValuePair {
                        value_slot: Slot::default(),
                        key_slot: Slot::default(),
                        hash: key_hash.to_vec(),
                    };
                    let hash_pos = self.append(&kv.to_bytes())?;
                    // point slot to hash pos
                    let next_slot = Slot::new(hash_pos, Tag::KvPair);
                    self.write_slot_at(slot_pos, next_slot)?;
                    Ok(HashMapGetResult { slot_ptr: target_slot_ptr(next_slot, hash_pos, &kv), is_empty: true })
                }
            },

            Tag::Index => {
                let mut next_ptr = ptr;
                if write_mode == WriteMode::ReadWrite {
                    next_ptr = self.copy_index_block_if_old(ptr, frozen_at)?;
                    if next_ptr != ptr {
                        // make slot point to the copied block
                        self.write_slot_at(slot_pos, Slot::new(next_ptr, Tag::Index))?;
                    }
                }
                self.read_map_slot(next_ptr, key_hash, key_offset + 1, write_mode, target, frozen_at)
            }

            Tag::KvPair => {
                let mut buf = vec![0u8; key_value_pair_length(self.hash_size())];
                self.read_at(ptr, &mut buf)?;
                let kv = KeyValuePair::from_bytes(&buf, self.hash_size())?;

                if kv.hash == key_hash {
                    if write_mode == WriteMode::ReadWrite && self.is_old(ptr, frozen_at)? {
                        let hash_pos = self.append(&kv.to_bytes())?;
                        let next_slot = Slot::new(hash_pos, Tag::KvPair);
                        self.write_slot_at(slot_pos, next_slot)?;
                        return Ok(HashMapGetResult {
                            slot_ptr: target_slot_ptr(next_slot, hash_pos, &kv),
                            is_empty: false,
                        });
                    }
                    return Ok(HashMapGetResult { slot_ptr: target_slot_ptr(slot, ptr, &kv), is_empty: false });
                }

                // hash collision - different keys
                match write_mode {
                    WriteMode::ReadOnly => Err(Error::KeyNotFound),
                    WriteMode::ReadWrite => {
                        if key_offset + 1 >= max_offset {
                            return Err(Error::KeyOffsetExceeded);
                        }
                        let next_i = hash_nibble(&kv.hash, key_offset + 1);
                        let next_index_pos = self.append(&[0u8; INDEX_BLOCK_SIZE])?;
                        self.write_slot_at(next_index_pos + (SLOT_LENGTH * next_i) as i64, slot)?;
                        let res = self.read_map_slot(next_index_pos, key_hash, key_offset + 1, write_mode, target, frozen_at)?;
                        self.write_slot_at(slot_pos, Slot::new(next_index_pos, Tag::Index))?;
                        Ok(res)
                    }
                }
            }

            _ => Err(Error::UnexpectedTag),
        }
    }

    fn remove_map_slot(&self, index_pos: i64, key_hash: &[u8], key_offset: usize, frozen_at: i64) -> Result<Slot> {
        if key_offset > self.hash_size() * 8 / BIT_COUNT as usize {
            return Err(Error::KeyOffsetExceeded);
        }

        // read block
        let mut slot_block = self.read_index_block(index_pos)?;
        let i = hash_nibble(key_hash, key_offset);
        let slot_pos = index_pos + (SLOT_LENGTH * i) as i64;
        let slot = slot_block[i];

        let next_slot = match slot.tag {
            Tag::None => return Err(Error::KeyNotFound),
            Tag::Index => self.remove_map_slot(slot.value, key_hash, key_offset + 1, frozen_at)?,
            Tag::KvPair => {
                let mut buf = vec![0u8; key_value_pair_length(self.hash_size())];
                self.read_at(slot.value, &mut buf)?;
                let kv = KeyValuePair::from_bytes(&buf, self.hash_size())?;
                if kv.hash != key_hash {
                    return Err(Error::KeyNotFound);
                }
                Slot::default()
            }
            _ => return Err(Error::UnexpectedTag),
        };

        // if we're the root node, just write the new slot and finish
        if key_offset == 0 {
            self.write_slot_at(slot_pos, next_slot)?;
            return Ok(Slot::new(index_pos, Tag::Index));
        }

        // get slot to return if there is only one used slot in this index block
        slot_block[i] = next_slot;
        let mut slot_to_return = Some(Slot::default());
        for block_slot in slot_block {
            if block_slot.tag == Tag::None {
                continue;
            }
            if let Some(existing) = slot_to_return
                && existing.tag != Tag::None
            {
                slot_to_return = None;
                break;
            }
            slot_to_return = Some(block_slot);
        }
        if let Some(slot_to_return) = slot_to_return
            && matches!(slot_to_return.tag, Tag::None | Tag::KvPair)
        {
            return Ok(slot_to_return);
        }

        // there was more than one used slot, or a single INDEX slot,
        // so we must keep this index block. update the slot in it,
        // copying the block first unless it belongs to this transaction.
        let next_index_pos = self.copy_index_block_if_old(index_pos, frozen_at)?;
        self.write_slot_at(next_index_pos + (SLOT_LENGTH * i) as i64, next_slot)?;
        Ok(Slot::new(next_index_pos, Tag::Index))
    }

    // array list

    fn read_array_list_slot_append(
        &self,
        header: ArrayListHeader,
        write_mode: WriteMode,
        frozen_at: i64,
    ) -> Result<(ArrayListHeader, SlotPointer)> {
        let mut index_pos = header.ptr;
        let key = header.size;

        let prev_shift = array_list_shift(key - 1);
        let next_shift = array_list_shift(key);

        if prev_shift != next_shift {
            // root overflow
            let next_index_pos = self.append(&[0u8; INDEX_BLOCK_SIZE])?;
            self.write_slot_at(next_index_pos, Slot::new(index_pos, Tag::Index))?;
            index_pos = next_index_pos;
        }

        let slot_ptr = self.read_array_list_slot(index_pos, key, next_shift, write_mode, frozen_at)?;
        // clear values left by a rollback or slice
        let slot_ptr = slot_ptr.with_slot(Slot::default());
        let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
        self.write_slot_at(position, slot_ptr.slot)?;
        Ok((ArrayListHeader { ptr: index_pos, size: header.size + 1 }, slot_ptr))
    }

    fn read_array_list_slot(
        &self,
        index_pos: i64,
        key: i64,
        shift: u8,
        write_mode: WriteMode,
        frozen_at: i64,
    ) -> Result<SlotPointer> {
        if shift >= MAX_BRANCH_LENGTH {
            return Err(Error::MaxShiftExceeded);
        }

        let i = (key >> (shift as u32 * BIT_COUNT)) & MASK;
        let slot_pos = index_pos + SLOT_LENGTH as i64 * i;
        let slot = self.read_slot_at(slot_pos)?;

        if shift == 0 {
            return Ok(SlotPointer::new(Some(slot_pos), slot));
        }

        match slot.tag {
            Tag::None => match write_mode {
                WriteMode::ReadOnly => Err(Error::KeyNotFound),
                WriteMode::ReadWrite => {
                    let next_index_pos = self.append(&[0u8; INDEX_BLOCK_SIZE])?;
                    self.write_slot_at(slot_pos, Slot::new(next_index_pos, Tag::Index))?;
                    self.read_array_list_slot(next_index_pos, key, shift - 1, write_mode, frozen_at)
                }
            },
            Tag::Index => {
                let ptr = slot.value;
                let mut next_ptr = ptr;
                if write_mode == WriteMode::ReadWrite {
                    next_ptr = self.copy_index_block_if_old(ptr, frozen_at)?;
                    if next_ptr != ptr {
                        // make slot point to the copied block
                        self.write_slot_at(slot_pos, Slot::new(next_ptr, Tag::Index))?;
                    }
                }
                self.read_array_list_slot(next_ptr, key, shift - 1, write_mode, frozen_at)
            }
            _ => Err(Error::UnexpectedTag),
        }
    }

    fn read_array_list_slice(&self, header: ArrayListHeader, size: i64, frozen_at: i64) -> Result<ArrayListHeader> {
        if size > header.size || size < 0 {
            return Err(Error::KeyNotFound);
        }

        let prev_shift = array_list_shift(header.size - 1);
        let next_shift = array_list_shift(size - 1);

        if prev_shift == next_shift {
            return Ok(ArrayListHeader { ptr: header.ptr, size });
        }

        let mut shift = prev_shift;
        let mut index_pos = header.ptr;
        while shift > next_shift {
            index_pos = self.read_slot_at(index_pos)?.value;
            shift -= 1;
        }
        // the new root may still belong to a past moment. unlike child
        // nodes, root nodes are written directly, so copy it now.
        let index_pos = self.copy_index_block_if_old(index_pos, frozen_at)?;
        Ok(ArrayListHeader { ptr: index_pos, size })
    }
}
