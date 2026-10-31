//! A database whose root is a history of hash map moments.

use crate::collections::{ReadArrayList, ReadHashMap, WriteArrayList, WriteHashMap};
use crate::core::Core;
use crate::cursor::ReadCursor;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::format::INDEX_BLOCK_SIZE;
use crate::slot::{Slot, SlotPointer, Tag};

/// A database whose root is an array list of hash maps, each one a
/// "moment": a copy of the data as of one transaction. This is the layout
/// recommended in the README, and the other implementations read and write
/// it the same way.
///
/// Each [`History::transact`] appends a copy of the latest moment and
/// changes it, so every past moment stays readable with
/// [`History::moment`].
///
/// ```
/// use xitdb::{CoreMemory, Database, Hasher, History};
///
/// # fn main() -> xitdb::Result<()> {
/// let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
/// let history = History::new(&db)?;
///
/// history.transact(|moment| moment.put("foo", "bar"))?;
///
/// let foo = history.latest()?.get_cursor("foo")?.unwrap().read_bytes(Some(1024))?;
/// assert_eq!(foo, b"bar");
/// # Ok(())
/// # }
/// ```
pub struct History<'a, C: Core> {
    db: &'a Database<C>,
}

impl<C: Core> Clone for History<'_, C> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<C: Core> Copy for History<'_, C> {}

impl<C: Core> std::fmt::Debug for History<'_, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("History").field("db", self.db).finish()
    }
}

impl<'a, C: Core> History<'a, C> {
    /// Opens the history at the root of `db`, initializing an empty one if
    /// the database is empty. Returns [`Error::UnexpectedTag`] if the root
    /// is something other than an array list.
    pub fn new(db: &'a Database<C>) -> Result<Self> {
        WriteArrayList::new(&mut db.root_cursor())?;
        Ok(History { db })
    }

    pub fn database(&self) -> &'a Database<C> {
        self.db
    }

    /// The array list of moments, as of the latest transaction.
    pub fn moments(&self) -> Result<ReadArrayList<'a, C>> {
        ReadArrayList::new(self.db.root_cursor())
    }

    /// The number of moments, which is the number of transactions that
    /// changed something.
    pub fn count(&self) -> Result<i64> {
        self.moments()?.count()
    }

    /// The moment at `index`, or `None` if it's out of range. Negative
    /// indexes count from the end.
    pub fn moment(&self, index: i64) -> Result<Option<ReadHashMap<'a, C>>> {
        self.moments()?.get_cursor(index)?.map(ReadHashMap::new).transpose()
    }

    /// The latest moment. If there are no moments yet, this is an empty
    /// map, so reads work the same on a new database: every lookup returns
    /// `None` and iterating yields nothing. Use [`History::moment`] with
    /// `-1` to tell the two apart.
    ///
    /// The map is a snapshot: later transactions don't change it.
    pub fn latest(&self) -> Result<ReadHashMap<'a, C>> {
        match self.moment(-1)? {
            Some(moment) => Ok(moment),
            None => ReadHashMap::new(ReadCursor::new(SlotPointer::new(None, Slot::default()), self.db)),
        }
    }

    /// Runs `f` on a copy of the latest moment (an empty map if there are
    /// none) and appends the result as a new moment, in one transaction.
    /// Reads inside `f` see its own writes. Returns what `f` returns.
    ///
    /// If `f` returns an error, nothing is committed and its error is
    /// returned. `E` can be any error type that xitdb's errors convert
    /// into, so `f` can abort with an error of the application's own.
    ///
    /// If the moment is unchanged at the end of `f`, nothing is committed
    /// either, so the history doesn't grow. See
    /// [`History::transact_with_status`] for what counts as unchanged.
    pub fn transact<T, E: From<Error>>(
        &self,
        f: impl FnOnce(&mut WriteHashMap<'a, C>) -> Result<T, E>,
    ) -> Result<T, E> {
        self.transact_with_status(f).map(|(value, _)| value)
    }

    /// Like [`History::transact`], but also returns whether a moment was
    /// committed.
    ///
    /// The moment counts as unchanged if, at the end of `f`, its top-level
    /// index block is byte-for-byte the same as the previous moment's (or
    /// is empty, if there was none). This costs two small reads, and it
    /// never mistakes a change for no change: data from earlier
    /// transactions is never changed in place, so any write below the top
    /// level gives the top level a new pointer. It's exact when `f` makes
    /// no writes, but not in general. Most writes count as a change even
    /// if they leave the same contents, because they copy what they write
    /// to: putting a value that's already there usually commits a new
    /// moment, so compare before writing to avoid that. A write that's
    /// undone before `f` returns, such as a put followed by a remove of the
    /// same key, can leave the top level identical, and then counts as
    /// unchanged.
    pub fn transact_with_status<T, E: From<Error>>(
        &self,
        f: impl FnOnce(&mut WriteHashMap<'a, C>) -> Result<T, E>,
    ) -> Result<(T, bool), E> {
        let db = self.db;
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;
        let last = history.get_slot(-1)?;

        // returning an error from the callback is the only way to discard
        // the transaction, so these carry the outcome out of it
        let mut output: Option<Result<T, E>> = None;
        let mut unchanged = false;
        let result = history.append_context(last, |cursor| {
            let before = index_block(db, cursor.slot_ptr().slot)?;
            let mut moment = WriteHashMap::new(cursor)?;
            let position = moment.write_cursor().slot_ptr().position.ok_or(Error::CursorNotWriteable)?;
            let failed = {
                let result = f(&mut moment);
                let failed = result.is_err();
                output = Some(result);
                failed
            };
            if failed {
                return Err(Error::WriteNotAllowed);
            }
            let after = index_block(db, db.read_slot_at(position)?)?;
            if before.is_some() && before == after {
                unchanged = true;
                return Err(Error::WriteNotAllowed);
            }
            Ok(())
        });

        match (result, output) {
            (_, Some(Err(err))) => Err(err),
            (Ok(()), Some(Ok(value))) => Ok((value, true)),
            (Err(_), Some(Ok(value))) if unchanged => Ok((value, false)),
            (Err(err), _) => Err(err.into()),
            (Ok(()), None) => unreachable!("the callback ran"),
        }
    }
}

/// The top-level index block of a moment, or `None` if it isn't a hash
/// map, so it can't be compared.
fn index_block<C: Core>(db: &Database<C>, slot: Slot) -> Result<Option<[u8; INDEX_BLOCK_SIZE]>> {
    let mut block = [0u8; INDEX_BLOCK_SIZE];
    match slot.tag {
        // an empty slot is the same as an empty map
        Tag::None => {}
        Tag::HashMap => db.read_at(slot.value, &mut block)?,
        _ => return Ok(None),
    }
    Ok(Some(block))
}
