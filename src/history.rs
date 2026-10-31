//! A database whose root is a history of hash map moments.

use std::io;

use crate::collections::{ReadArrayList, ReadHashMap, WriteHashMap};
use crate::core::Core;
use crate::cursor::{ReadCursor, WriteCursor};
use crate::data::Data;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::format::INDEX_BLOCK_SIZE;
use crate::path::PathPart;
use crate::slot::{Slot, SlotPointer, Tag};

/// A database whose root is an array list of hash maps, each one a
/// "moment": a copy of the data as of one transaction. This is the layout
/// recommended in the README, and the other implementations read and write
/// it the same way. Every moment must be a plain hash map, not a counted
/// map or a set; otherwise [`History::new`] and [`History::transact`]
/// return [`Error::UnexpectedTag`].
///
/// Each [`History::transact`] appends a copy of the latest moment and
/// changes it, so every past moment stays readable with
/// [`History::moment`].
///
/// ```
/// use xitdb::{Database, History};
///
/// # fn main() -> xitdb::Result<()> {
/// let db = Database::in_memory()?;
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
    /// Opens the history at the root of `db`. An empty database is an empty
    /// history, which the first [`History::transact`] initializes. Returns
    /// [`Error::UnexpectedTag`] if the root is something other than an array
    /// list, or its latest moment is something other than a hash map.
    ///
    /// Opening a history never writes, so it works on a database opened with
    /// [`Database::open_read_only`].
    pub fn new(db: &'a Database<C>) -> Result<Self> {
        let list = ReadArrayList::new(db.root_cursor())?;
        check_moment(list.get_slot(-1)?.unwrap_or_default())?;
        Ok(History { db })
    }

    pub fn database(&self) -> &'a Database<C> {
        self.db
    }

    /// The array list of moments, as of the latest transaction.
    pub fn moments(&self) -> Result<ReadArrayList<'a, C>> {
        ReadArrayList::new(self.db.root_cursor())
    }

    /// The number of moments. Each [`History::transact`] that commits adds
    /// one, but so does anything else that appends to the root list.
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
    ///
    /// The latest moment is read inside the transaction, so a commit made
    /// just before through another [`Database`] on the same file is never
    /// lost.
    ///
    /// The moment may be discarded when `f` returns, so neither `T` nor `E`
    /// can borrow from it. To keep something from it, read it into an
    /// owned value, or read it from [`History::latest`] afterwards:
    ///
    /// ```compile_fail
    /// # use xitdb::*;
    /// # let db = Database::in_memory().unwrap();
    /// # let history = History::new(&db).unwrap();
    /// let moment = history.transact(|moment| ReadHashMap::new(moment.cursor().clone()));
    /// ```
    pub fn transact<T, E: From<Error>>(
        &self,
        f: impl for<'t> FnOnce(&mut WriteHashMap<'t, C>) -> Result<T, E>,
    ) -> Result<T, E> {
        self.transact_with_status(f).map(|(value, _)| value)
    }

    /// Like [`History::transact`], but also returns whether a moment was
    /// committed.
    ///
    /// The moment counts as unchanged if, at the end of `f`, its top-level
    /// index block is byte-for-byte the same as the previous moment's (or
    /// is empty, if there was none). This costs one small read before `f`
    /// and one after, and it never mistakes a change for no change: data
    /// from earlier transactions is never changed in place, so any write
    /// below the top level gives the top level a new pointer. It's exact
    /// when `f` makes no writes, but not in general. Most writes count as a
    /// change even if they leave the same contents, because they copy what
    /// they write to: putting a value that's already there usually commits
    /// a new moment, so use [`WriteHashMap::put_if_changed`] or
    /// [`WriteHashMap::put_path_if_changed`], which write nothing then. A write
    /// that's undone before `f` returns, such as a put followed by a remove
    /// of the same key, can leave the top level identical, and then counts
    /// as unchanged.
    pub fn transact_with_status<T, E: From<Error>>(
        &self,
        f: impl for<'t> FnOnce(&mut WriteHashMap<'t, C>) -> Result<T, E>,
    ) -> Result<(T, bool), E> {
        // the callback can only discard the transaction by failing, so its
        // outcome is carried out here, and the error it fails with is unused
        let mut outcome = None;
        let result = self.db.root_cursor().write_path_context(&[PathPart::ArrayListInit], |list| {
            let next = append_moment(self.db, list, f).unwrap_or_else(|err| Outcome::Failed(err.into()));
            let commit = matches!(next, Outcome::Committed(_));
            outcome = Some(next);
            if commit { Ok(()) } else { Err(Error::Io(io::Error::other("history transaction discarded"))) }
        });

        match outcome {
            Some(Outcome::Failed(err)) => Err(err),
            Some(Outcome::Unchanged(value)) => Ok((value, false)),
            Some(Outcome::Committed(value)) => result.map(|_| (value, true)).map_err(E::from),
            None => Err(result.expect_err("the callback runs unless the write fails first").into()),
        }
    }
}

/// How a transaction ended.
enum Outcome<T, E> {
    Failed(E),
    Unchanged(T),
    Committed(T),
}

/// Appends a copy of the last moment in `list` and runs `f` on it.
/// xitdb's errors are returned as `Err`, and `f`'s as [`Outcome::Failed`].
fn append_moment<C: Core, T, E>(
    db: &Database<C>,
    list: &mut WriteCursor<'_, C>,
    f: impl for<'t> FnOnce(&mut WriteHashMap<'t, C>) -> Result<T, E>,
) -> Result<Outcome<T, E>> {
    // read in this transaction, so it's the latest committed moment
    let last = list.read_path_slot(&[PathPart::ArrayListGet(-1)])?.unwrap_or_default();
    check_moment(last)?;
    let before = index_block(db, last)?;

    let data = Data::from(last);
    let mut cursor = list.write_path(&[PathPart::ArrayListAppend, PathPart::WriteData(&data)])?;
    let mut moment = WriteHashMap::new(&mut cursor)?;
    let position = moment.write_cursor().slot_ptr().position.ok_or(Error::CursorNotWriteable)?;
    let value = match f(&mut moment) {
        Ok(value) => value,
        Err(err) => return Ok(Outcome::Failed(err)),
    };

    // f could have replaced the moment with something that isn't a map
    let after = db.read_slot_at(position)?;
    if after.tag == Tag::HashMap && index_block(db, after)? == before {
        Ok(Outcome::Unchanged(value))
    } else {
        Ok(Outcome::Committed(value))
    }
}

/// Returns [`Error::UnexpectedTag`] unless a moment is a hash map or empty.
fn check_moment(slot: Slot) -> Result<()> {
    match slot.tag {
        Tag::None | Tag::HashMap => Ok(()),
        _ => Err(Error::UnexpectedTag),
    }
}

/// The top-level index block of a moment that passed [`check_moment`]. An
/// empty moment is the same as an empty map.
fn index_block<C: Core>(db: &Database<C>, moment: Slot) -> Result<[u8; INDEX_BLOCK_SIZE]> {
    let mut block = [0u8; INDEX_BLOCK_SIZE];
    if moment.tag == Tag::HashMap {
        db.read_at(moment.value, &mut block)?;
    }
    Ok(block)
}
