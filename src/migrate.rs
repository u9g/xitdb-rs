//! Versioned layouts for a [`History`], changed by ordered migrations.

use std::fmt;

use crate::collections::WriteHashMap;
use crate::core::Core;
use crate::error::{Error, Result};
use crate::history::History;

/// The key in each moment where [`History::migrate`] records the layout
/// version, as a `Uint`, unless [`Migrations::with_key`] picks another.
/// A moment without it is at version 0.
pub const LAYOUT_VERSION_KEY: &str = "xitdb/layout-version";

/// One step from the previous layout version to `version`: `run` changes
/// the moment, for example by renaming a key or reshaping its values.
///
/// `run` is a plain function, so it can't capture anything, and a generic
/// one works for any core:
///
/// ```
/// use xitdb::{Core, Migration, WriteHashMap};
///
/// fn add_tags<C: Core>(moment: &mut WriteHashMap<'_, C>) -> xitdb::Result<()> {
///     moment.put_set("tags")?;
///     Ok(())
/// }
///
/// let migration: Migration<xitdb::CoreMemory> = Migration { version: 1, name: "add tags", run: add_tags };
/// ```
pub struct Migration<C: Core, E = Error> {
    /// The layout version after this migration. Versions start at 1, since
    /// 0 is the version of a moment that has never been migrated.
    pub version: u64,
    /// A name for logs, returned in [`Migrated::ran`].
    pub name: &'static str,
    /// Changes the moment from the previous version's layout to this one's.
    /// Reads see the writes of earlier migrations in the same run.
    pub run: fn(&mut WriteHashMap<'_, C>) -> Result<(), E>,
}

impl<C: Core, E> Clone for Migration<C, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<C: Core, E> Copy for Migration<C, E> {}

impl<C: Core, E> fmt::Debug for Migration<C, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Migration").field("version", &self.version).field("name", &self.name).finish()
    }
}

/// An ordered list of [`Migration`]s, checked when it's made, and the key
/// the layout version is recorded under. Run it with [`History::migrate`],
/// and check it from a reader with [`History::check_version`].
pub struct Migrations<C: Core, E = Error> {
    list: Vec<Migration<C, E>>,
    key: &'static str,
}

impl<C: Core, E> Migrations<C, E> {
    /// Checks that the versions start above 0 and strictly increase, so
    /// there are no duplicates, and returns
    /// [`Error::MigrationOutOfOrder`] for the first one that doesn't. The
    /// list must already be in order: it's never sorted, since a list out
    /// of order is more likely a mistake than a request.
    pub fn new(migrations: impl IntoIterator<Item = Migration<C, E>>) -> Result<Self> {
        let list: Vec<_> = migrations.into_iter().collect();
        let mut previous = 0;
        for migration in &list {
            if migration.version <= previous {
                return Err(Error::MigrationOutOfOrder { version: migration.version, previous });
            }
            previous = migration.version;
        }
        Ok(Migrations { list, key: LAYOUT_VERSION_KEY })
    }

    /// Records the layout version under `key` instead of
    /// [`LAYOUT_VERSION_KEY`]. Changing the key of an existing database
    /// makes it look unmigrated, so pick it once.
    pub fn with_key(mut self, key: &'static str) -> Self {
        self.key = key;
        self
    }

    /// The key the layout version is recorded under.
    pub fn key(&self) -> &'static str {
        self.key
    }

    /// The newest version, which [`History::migrate`] brings the moment
    /// to, or 0 if there are no migrations.
    pub fn latest(&self) -> u64 {
        self.list.last().map_or(0, |migration| migration.version)
    }

    /// The migrations, in order.
    pub fn as_slice(&self) -> &[Migration<C, E>] {
        &self.list
    }

    /// The migrations newer than `version`.
    fn pending(&self, version: u64) -> &[Migration<C, E>] {
        let start = self.list.partition_point(|migration| migration.version <= version);
        &self.list[start..]
    }
}

impl<C: Core, E> fmt::Debug for Migrations<C, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Migrations").field("list", &self.list).field("key", &self.key).finish()
    }
}

/// What [`History::migrate`] did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Migrated {
    /// The layout version before migrating.
    pub from: u64,
    /// The layout version after migrating. It's the same as `from` if
    /// nothing ran.
    pub to: u64,
    /// The names of the migrations that ran, in order.
    pub ran: Vec<&'static str>,
}

impl<C: Core> History<'_, C> {
    /// The layout version recorded in the latest moment under
    /// [`LAYOUT_VERSION_KEY`], or 0 if there is none, as on a new database.
    /// Returns [`Error::UnexpectedTag`] if the value there isn't a `Uint`.
    /// For a custom key, read it with `history.latest()?.get_uint(key)`.
    ///
    /// Like [`History::latest`], this never writes, so it works on a
    /// database opened with
    /// [`Database::open_read_only`](crate::Database::open_read_only).
    pub fn version(&self) -> Result<u64> {
        Ok(self.latest()?.get_uint(LAYOUT_VERSION_KEY)?.unwrap_or(0))
    }

    /// Brings the latest moment to the newest layout version: runs each
    /// migration newer than the recorded version, in order, then records
    /// the newest version, all in one [`History::transact`]. Returns the
    /// versions before and after and the names of the migrations that ran.
    ///
    /// If a migration returns an error, nothing is committed, so the moment
    /// and its version stay exactly as they were, and that error is
    /// returned. If the recorded version is newer than every migration,
    /// so the data was written by newer code, it returns
    /// [`Error::LayoutTooNew`] and changes nothing. If there's nothing to
    /// run, nothing is committed.
    ///
    /// The version is read inside the transaction, so with one writer at a
    /// time (see the README on locking), each migration runs exactly once.
    pub fn migrate<E: From<Error>>(&self, migrations: &Migrations<C, E>) -> Result<Migrated, E> {
        let known = migrations.latest();
        self.transact(|moment| {
            let from = moment.get_uint(migrations.key)?.unwrap_or(0);
            if from > known {
                return Err(Error::LayoutTooNew { found: from, known }.into());
            }
            let pending = migrations.pending(from);
            for migration in pending {
                (migration.run)(moment)?;
            }
            if !pending.is_empty() {
                moment.put(migrations.key, known)?;
            }
            let ran = pending.iter().map(|migration| migration.name).collect();
            Ok(Migrated { from, to: from.max(known), ran })
        })
    }

    /// Checks, without writing, that the latest moment is at exactly the
    /// newest version of `migrations`, and returns it. This is for readers,
    /// which shouldn't migrate: it returns [`Error::LayoutTooNew`] if the
    /// data was written by newer code, and [`Error::LayoutTooOld`] if the
    /// writer hasn't migrated it yet.
    pub fn check_version<E>(&self, migrations: &Migrations<C, E>) -> Result<u64> {
        let found = self.latest()?.get_uint(migrations.key)?.unwrap_or(0);
        let known = migrations.latest();
        if found > known {
            Err(Error::LayoutTooNew { found, known })
        } else if found < known {
            Err(Error::LayoutTooOld { found, expected: known })
        } else {
            Ok(found)
        }
    }
}
