use std::cell::{Cell, RefCell, RefMut};
use std::io;

use crate::compact::{Compactor, OffsetMap};
use crate::core::{Core, DynCore};
#[cfg(feature = "sha1")]
use crate::core::{CoreBufferedFile, CoreMemory};
use crate::cursor::WriteCursor;
use crate::data::{Data, Encoded};
use crate::error::{Error, Result};
use vstd::prelude::*;
use crate::format::*;
use crate::hasher::Hasher;
use crate::path::{HashMapGetTarget, PathPart, WriteMode, hash_map_tag, sorted_map_tag};
use crate::slot::{Slot, SlotPointer, Tag};
use crate::map_store::MapTarget;
use crate::store::{DbStore, IoSink, IoSource};

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
    // where the current transaction started: everything before it is
    // committed. tx_start can move past it (freezing, concatenation), but
    // this doesn't.
    pub(crate) tx_floor: Cell<Option<i64>>,
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

verus! {

/// Resolves a possibly-negative index against `size`, or returns
/// [`Error::KeyNotFound`] if it's out of range.
fn resolve_index(index: i64, size: i64) -> (r: Result<i64>)
    ensures
        r is Err <==> !(-size <= index < size),
        r matches Ok(i) ==> 0 <= i < size && i == if index < 0 { size + index } else { index as int },
{
    if size < 0 {
        return Err(Error::KeyNotFound);
    }
    if index >= size || index < -size {
        return Err(Error::KeyNotFound);
    }
    Ok(if index < 0 { size + index } else { index })
}

} // verus!

fn random_u64() -> Result<u64> {
    getrandom::u64().map_err(|err| Error::Io(io::Error::other(err.to_string())))
}

#[cfg(feature = "sha1")]
impl Database<CoreBufferedFile> {
    /// Opens the database file at `path` with [`CoreBufferedFile::open`] and
    /// [`Hasher::sha1`], creating and initializing it if it doesn't exist.
    ///
    /// The file isn't locked. When writing from multiple processes, hold an
    /// exclusive lock on a separate lock file before calling this, since it
    /// may initialize the file; see [`CoreBufferedFile::open`]. For another
    /// hasher, use `Database::new(CoreBufferedFile::open(path)?, hasher)`.
    pub fn open(path: impl AsRef<std::path::Path>) -> Result<Database<CoreBufferedFile>> {
        Database::new(CoreBufferedFile::open(path)?, Hasher::sha1())
    }

    /// Opens the existing database file at `path` for reading only, with
    /// [`CoreBufferedFile::open_read_only`] and [`Hasher::sha1`]. This is
    /// how to read a database that another process is writing to, and it
    /// needs no lock. It never initializes the file, so an empty file fails
    /// with [`Error::InvalidDatabase`]. Writes fail with [`Error::Io`].
    pub fn open_read_only(path: impl AsRef<std::path::Path>) -> Result<Database<CoreBufferedFile>> {
        let mut core = CoreBufferedFile::open_read_only(path)?;
        if core.length()? == 0 {
            return Err(Error::InvalidDatabase);
        }
        Database::new(core, Hasher::sha1())
    }
}

#[cfg(feature = "sha1")]
impl Database<CoreMemory> {
    /// Creates an empty in-memory database with [`Hasher::sha1`].
    pub fn in_memory() -> Result<Database<CoreMemory>> {
        Database::new(CoreMemory::new(), Hasher::sha1())
    }
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
            tx_floor: Cell::new(None),
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
            // write the header and the root header and commit an empty
            // root, so the file ends with a trailer like after any
            // transaction. verified in commit_store.rs
            crate::commit_store::init_file(&mut DbStore::new(&db), header)?;
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

    /// Consumes the database and calls [`Core::finish`] on its core,
    /// returning any error from writing out buffered data. Dropping a
    /// [`CoreBufferedFile`](crate::CoreBufferedFile) also writes out its
    /// buffer, but ignores errors.
    pub fn close(self) -> Result<()> {
        Ok(self.into_core().finish()?)
    }

    /// Boxes the core, so databases with different cores have the same
    /// type, such as a file in production and memory in tests:
    ///
    /// ```
    /// use xitdb::*;
    ///
    /// # fn main() -> xitdb::Result<()> {
    /// # let path = std::env::temp_dir().join("xitdb-into-dyn-doctest.db");
    /// # let in_production = false;
    /// let db: Database<DynCore> = if in_production {
    ///     Database::open(&path)?.into_dyn()
    /// } else {
    ///     Database::in_memory()?.into_dyn()
    /// };
    /// db.close()?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn into_dyn(self) -> Database<DynCore>
    where
        C: Send + 'static,
    {
        Database {
            core: RefCell::new(Box::new(self.core.into_inner())),
            hasher: self.hasher,
            header: self.header,
            tx_start: self.tx_start,
            transaction: self.transaction,
            next_transaction_id: self.next_transaction_id,
        }
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

    pub(crate) fn read_i64_at(&self, pos: i64) -> Result<i64> {
        let mut buf = [0u8; 8];
        self.read_at(pos, &mut buf)?;
        Ok(i64::from_be_bytes(buf))
    }

    pub(crate) fn read_slot_at(&self, pos: i64) -> Result<Slot> {
        crate::array_list_store::read_slot_at(&mut DbStore::new(self), pos)
    }

    pub(crate) fn read_array_list_header(&self, pos: i64) -> Result<ArrayListHeader> {
        crate::path_store::read_array_list_header(&mut DbStore::new(self), pos)
    }

    pub(crate) fn read_btree_header(&self, pos: i64) -> Result<BTreeHeader> {
        crate::path_store::read_btree_header(&mut DbStore::new(self), pos)
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
        // verified in commit_store.rs
        crate::commit_store::replica_state(&mut DbStore::new(self), self.header.get().file_id)
    }

    /// Where to start sending committed bytes to a replica in `state`.
    /// That's its committed size if its bytes are a prefix of this
    /// database, or 0 if it must be replaced, because it's a replica of
    /// another file or it has diverged from this one.
    pub fn replication_start(&self, state: ReplicaState) -> Result<i64> {
        // verified in commit_store.rs
        crate::commit_store::replication_start(&mut DbStore::new(self), self.header.get().file_id, state)
    }

    /// Writes the committed bytes from `start` up to `end` to `w`. `start`
    /// is usually from [`Database::replication_start`], and `end` can't be
    /// past [`Database::committed_size`]. Committed bytes never change
    /// except for the root header, so when `start` is 0, a root header
    /// matching `end` is written, making the bytes a complete database by
    /// themselves.
    pub fn read_committed(&self, start: i64, end: i64, w: &mut impl io::Write) -> Result<()> {
        // verified in commit_store.rs
        let mut sink = IoSink::new(w);
        crate::commit_store::read_committed(&mut DbStore::new(self), &mut sink, start, end, self.header.get().file_id)
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

        // verified in commit_store.rs
        let mut source = IoSource::new(r);
        crate::commit_store::write_replicated(&mut DbStore::new(self), &mut source, start, length)?;

        if start == 0 {
            // the bytes are a different database, with its own header
            self.core().sync()?;
            let header = self.read_and_validate_header()?;
            self.header.set(header);
            self.committed_size()?;
        } else if length > 0 {
            // the bytes must end with a trailer. update the root header to match it.
            crate::commit_store::finish_replicated(&mut DbStore::new(self), start, length, self.header.get().file_id)?;
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
        // verified in commit_store.rs
        crate::commit_store::committed_size(&mut DbStore::new(self), self.header.get().file_id)
    }

    pub(crate) fn truncate(&self) -> Result<()> {
        // verified in commit_store.rs
        let file_id = self.header.get().file_id;
        let committed_size = self.committed_size()?;
        if let Some(frozen_at) = self.transaction.get().and_then(|t| t.frozen_at)
            && frozen_at > committed_size
        {
            // retain frozen bytes without publishing the failed transaction
            return crate::commit_store::truncate_to_frozen(&mut DbStore::new(self), frozen_at, random_u64()?, file_id);
        }
        crate::commit_store::truncate_to_committed(&mut DbStore::new(self), committed_size)
    }

    pub(crate) fn read_root_header(&self) -> Result<RootHeader> {
        crate::commit_store::read_root_header(&mut DbStore::new(self))
    }

    // the most recently committed root slot
    pub(crate) fn read_root_slot(&self) -> Result<Slot> {
        Ok(self.read_root_header()?.root)
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

    // copy frozen or committed collection storage before mutation to
    // preserve existing readers. a path can reach a collection without its
    // init part (such as through a copied hash map), and a collection from a
    // past transaction must not change in place.
    fn copy_collection_if_frozen(
        &self,
        slot_ptr: SlotPointer,
        init: PathPart<'_>,
        frozen_at: i64,
    ) -> Result<SlotPointer> {
        let frozen = self.transaction.get().and_then(|t| t.frozen_at).is_some_and(|f| slot_ptr.slot.value < f);
        let committed = self.tx_floor.get().is_some_and(|floor| slot_ptr.slot.value < floor);
        if frozen || committed {
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
        self.tx_floor.set(Some(scratch_pos));
        let _reset_tx_floor = ResetOnDrop(&self.tx_floor);
        // the copy is the transaction's root, so it stays writable after freezing
        if let Some(mut active) = self.transaction.get() {
            active.root_position = Some(scratch_pos);
            active.scratch_position = Some(scratch_pos);
            self.transaction.set(Some(active));
        }

        // the transaction works on a copy of the root slot, appended.
        // verified in commit_store.rs
        let scratch_pos = crate::commit_store::begin_transaction(&mut DbStore::new(self), root)?;
        let mut root_ptr = SlotPointer::new(Some(scratch_pos), root);

        // every collection expects its init part to copy its header or root
        // block into the transaction before anything writes to it. the root
        // has no enclosing init part, so run one here.
        if let Some(init) = PathPart::init_for(root.tag) {
            root_ptr = self.read_slot_pointer(write_mode, &[init], 0, root_ptr, frozen_at, &mut None)?;
        }

        let mut result = self.read_slot_pointer(write_mode, path, path_i, root_ptr, frozen_at, ctx)?;

        // the copy now holds the new root, so commit it. verified in
        // commit_store.rs
        let commit_id = random_u64()?;
        let next_root = crate::commit_store::finish_transaction(
            &mut DbStore::new(self),
            scratch_pos,
            commit_id,
            self.header.get().file_id,
        )?;

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
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let next_slot_ptr =
                    crate::path_store::array_list_init(&mut DbStore::new(self), position, slot_ptr.slot, limit, copy_at)?;
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
                // update the header before callbacks can freeze it. verified
                // in path_store.rs
                let limit = self.write_limit(frozen_at)?;
                crate::path_store::write_array_list_header(&mut DbStore::new(self), start, header, limit)?;
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
                // update the header before callbacks can freeze it. verified
                // in path_store.rs
                let limit = self.write_limit(frozen_at)?;
                crate::path_store::write_array_list_header(&mut DbStore::new(self), start, slice_header, limit)?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListInit => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let next_slot_ptr =
                    crate::path_store::linked_array_list_init(&mut DbStore::new(self), position, slot_ptr.slot, limit, copy_at)?;
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

// path-copy down to the value slot so the write is persistent,
                // updating the header before callbacks can freeze it.
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let slot_ptr =
                    crate::path_store::linked_get_for_write(&mut DbStore::new(self), header_ptr, header, rank, limit, copy_at)?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListAppend => {
                let (_, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                // the header is updated before the value is filled in via the
                // rest of the path. verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let slot_ptr =
                    crate::path_store::linked_insert(&mut DbStore::new(self), header_ptr, header, header.size, limit, copy_at)?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListSlice { offset, size } => {
                let (slot_ptr, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                // the header is updated before recursing into the rest of the
                // path. verified in path_store.rs
                let limit = self.write_limit(frozen_at)?;
                crate::path_store::linked_slice(&mut DbStore::new(self), header_ptr, header, offset, size, limit)?;
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
                // the header is updated before recursing into the rest of the
                // path. verified in path_store.rs
                let limit = self.write_limit(frozen_at)?;
                crate::path_store::linked_concat(&mut DbStore::new(self), header_ptr, header_a, header_b, limit)?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListInsert(index) => {
                let (_, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                let rank = resolve_index(index, header.size)?;
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let slot_ptr = crate::path_store::linked_insert(&mut DbStore::new(self), header_ptr, header, rank, limit, copy_at)?;
                next(slot_ptr, ctx)
            }

            PathPart::LinkedArrayListRemove(index) => {
                let (slot_ptr, header_ptr, header) = self.linked_array_list_for_write(write_mode, slot_ptr, frozen_at)?;
                let rank = resolve_index(index, header.size)?;
                // the header is updated before recursing into the rest of the
                // path. verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                crate::path_store::linked_remove(&mut DbStore::new(self), header_ptr, header, rank, limit, copy_at)?;
                next(slot_ptr, ctx)
            }

            PathPart::HashMapInit { counted, set } => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let tag = hash_map_tag(counted, set);
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let next_slot_ptr =
                    crate::path_store::hash_map_init(&mut DbStore::new(self), position, slot_ptr.slot, counted, tag, limit, copy_at)?;
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
                let index_pos = crate::path_store::map_index_pos(slot_ptr.slot.value, counted)?;
                let hash = self.check_hash(target.hash())?;
                let res = self.read_map_slot(index_pos, hash, 0, write_mode, target, frozen_at)?;
                if write_mode == ReadWrite && counted && res.is_empty {
                    // verified in path_store.rs
                    let limit = self.write_limit(frozen_at)?;
                    crate::path_store::update_map_count(&mut DbStore::new(self), slot_ptr.slot.value, true, limit)?;
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
                let index_pos = crate::path_store::map_index_pos(slot_ptr.slot.value, counted)?;
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
                    // verified in path_store.rs
                    let limit = self.write_limit(frozen_at)?;
                    crate::path_store::update_map_count(&mut DbStore::new(self), slot_ptr.slot.value, false, limit)?;
                }
                Ok(slot_ptr)
            }

            PathPart::SortedMapInit { set } => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let tag = sorted_map_tag(set);
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let next_slot_ptr =
                    crate::path_store::sorted_map_init(&mut DbStore::new(self), position, slot_ptr.slot, tag, limit, copy_at)?;
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

                // the entry for the key, inserted if new, with the header
                // updated before the value is filled in. verified in
                // path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                let kv_slot = crate::path_store::sorted_get_for_write(
                    &mut DbStore::new(self),
                    header_ptr,
                    header,
                    key,
                    limit,
                    copy_at,
                    self.hash_size(),
                )?;
                let target_slot = self.sorted_target_slot(kv_slot, target)?;
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
                // verified in path_store.rs
                let (limit, copy_at) = self.write_bounds(frozen_at)?;
                crate::path_store::sorted_remove_key(&mut DbStore::new(self), header_ptr, header, key, limit, copy_at, self.hash_size())?;
                Ok(slot_ptr)
            }

            PathPart::WriteData(data) => {
                if write_mode == ReadOnly {
                    return Err(Error::WriteNotAllowed);
                }
                let position = slot_ptr.position.ok_or(Error::CursorNotWriteable)?;
                let slot = match data.encode() {
                    Encoded::Inline(slot) => slot,
                    Encoded::Long(bytes) => {
                        let mut cursor = WriteCursor::new(slot_ptr, self);
                        let mut writer = cursor.writer()?;
                        writer.format_tag = bytes.format_tag;
                        io::Write::write_all(&mut writer, &bytes.value)?;
                        writer.finish()?;
                        writer.slot
                    }
                };
                // verified in path_store.rs
                let limit = self.write_limit(frozen_at)?;
                crate::path_store::write_data_slot(&mut DbStore::new(self), position, slot, limit)?;
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
    // the bounds of a write: nothing before the transaction's start may
    // change (the verified guarantee), and what a path reaches before
    // max(tx_start, frozen_at) is copied rather than changed in place. a
    // collection's own header or root block, once in the transaction, is
    // still written in place after a freeze. writes only happen inside a
    // transaction.
    fn write_bounds(&self, frozen_at: i64) -> Result<(i64, i64)> {
        self.tx_bounds(frozen_at).ok_or(Error::ExpectedTxStart)
    }

    fn tx_bounds(&self, frozen_at: i64) -> Option<(i64, i64)> {
        Some((self.tx_floor.get()?, self.tx_start.get()?.max(frozen_at)))
    }

    // the bound below which nothing changes: the transaction's start
    fn write_limit(&self, frozen_at: i64) -> Result<i64> {
        Ok(self.write_bounds(frozen_at)?.0)
    }

    // hash map

    // verified in map_store.rs
    fn read_map_slot(
        &self,
        index_pos: i64,
        key_hash: &[u8],
        key_offset: usize,
        write_mode: WriteMode,
        target: HashMapGetTarget<'_>,
        frozen_at: i64,
    ) -> Result<HashMapGetResult> {
        let bounds = self.tx_bounds(frozen_at);
        let (limit, copy_at) = (bounds.map(|b| b.0), bounds.map_or(0, |b| b.1));
        let target = match target {
            HashMapGetTarget::KvPair(_) => MapTarget::KvPair,
            HashMapGetTarget::Key(_) => MapTarget::Key,
            HashMapGetTarget::Value(_) => MapTarget::Value,
        };
        let write = write_mode == WriteMode::ReadWrite;
        let res = crate::map_store::read_map_slot_checked(
            &mut DbStore::new(self),
            index_pos,
            key_hash,
            key_offset,
            write,
            target,
            limit,
            copy_at,
            self.hash_size(),
        )?;
        Ok(HashMapGetResult { slot_ptr: res.slot_ptr, is_empty: res.is_empty })
    }

    // verified in map_store.rs
    fn remove_map_slot(&self, index_pos: i64, key_hash: &[u8], key_offset: usize, frozen_at: i64) -> Result<Slot> {
        let bounds = self.tx_bounds(frozen_at);
        let (limit, copy_at) = (bounds.map(|b| b.0), bounds.map_or(0, |b| b.1));
        crate::map_store::remove_map_slot_checked(&mut DbStore::new(self), index_pos, key_hash, key_offset, limit, copy_at, self.hash_size())
    }

    // array list

    // verified in array_list_store.rs
    fn read_array_list_slot_append(
        &self,
        header: ArrayListHeader,
        _write_mode: WriteMode,
        frozen_at: i64,
    ) -> Result<(ArrayListHeader, SlotPointer)> {
        let bounds = self.tx_bounds(frozen_at);
        let (limit, copy_at) = (bounds.map(|b| b.0), bounds.map_or(0, |b| b.1));
        crate::array_list_store::read_array_list_slot_append(&mut DbStore::new(self), header, limit, copy_at)
    }

    // verified in array_list_store.rs
    fn read_array_list_slot(
        &self,
        index_pos: i64,
        key: i64,
        shift: u8,
        write_mode: WriteMode,
        frozen_at: i64,
    ) -> Result<SlotPointer> {
        let bounds = self.tx_bounds(frozen_at);
        let (limit, copy_at) = (bounds.map(|b| b.0), bounds.map_or(0, |b| b.1));
        let write = write_mode == WriteMode::ReadWrite;
        crate::array_list_store::read_array_list_slot_checked(&mut DbStore::new(self), index_pos, key, shift, write, limit, copy_at)
    }

    // verified in array_list_store.rs
    fn read_array_list_slice(&self, header: ArrayListHeader, size: i64, frozen_at: i64) -> Result<ArrayListHeader> {
        let bounds = self.tx_bounds(frozen_at);
        let (limit, copy_at) = (bounds.map(|b| b.0), bounds.map_or(0, |b| b.1));
        crate::array_list_store::read_array_list_slice(&mut DbStore::new(self), header, size, limit, copy_at)
    }
}
