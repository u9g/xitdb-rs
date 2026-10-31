//! Versioned layouts for a [`History`], changed by ordered migrations.

use std::fmt;

use crate::collections::{ReadHashMap, WriteHashMap};
use crate::core::Core;
use crate::error::{Error, Result};
use crate::history::History;
use crate::slot::Tag;

/// The key in each moment where [`History::migrate`] records the layout
/// version, as a `Uint`, unless [`Migrations::with_key`] picks another.
/// A moment without it is at version 0. A non-negative `Int` there, as
/// another implementation might write, is read as the same version.
pub const LAYOUT_VERSION_KEY: &str = "xitdb/layout-version";

/// A migration's function.
type Run<C, E> = Box<dyn Fn(&mut WriteHashMap<'_, C>) -> Result<(), E> + Send + Sync>;

/// One step from the previous layout version to `version`: a function
/// that changes the moment, for example by renaming a key or reshaping its
/// values. It's made with [`Migration::new`], from a function or a closure,
/// which can capture configuration such as a default value:
///
/// ```
/// use xitdb::{Core, Migration, WriteHashMap};
///
/// fn add_tags<C: Core>(moment: &mut WriteHashMap<'_, C>) -> xitdb::Result<()> {
///     moment.put_set("tags")?;
///     Ok(())
/// }
///
/// let default_limit = 10u64;
/// let migrations: Vec<Migration<xitdb::CoreMemory>> = vec![
///     Migration::new(1, "add tags", add_tags),
///     Migration::new(2, "add limit", move |moment| moment.put("limit", default_limit)),
/// ];
/// ```
pub struct Migration<C: Core, E = Error> {
    /// The layout version after this migration. Versions start at 1, since
    /// 0 is the version of a moment that has never been migrated.
    pub version: u64,
    /// A name for logs, returned in [`Migrated::ran`].
    pub name: &'static str,
    run: Run<C, E>,
}

impl<C: Core, E> Migration<C, E> {
    /// A migration to `version`. `run` changes the moment from the previous
    /// version's layout to this one's. Its reads see the writes of earlier
    /// migrations in the same run.
    ///
    /// `run` is boxed, so it must be `'static`. A function that's generic
    /// over the core, such as `add_tags::<C>`, is only `'static` if `C` is,
    /// so code that builds migrations for any core needs `C: Core + 'static`.
    /// Every core in this crate is `'static`.
    pub fn new(
        version: u64,
        name: &'static str,
        run: impl Fn(&mut WriteHashMap<'_, C>) -> Result<(), E> + Send + Sync + 'static,
    ) -> Self {
        Migration { version, name, run: Box::new(run) }
    }
}

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

    /// The migrations newer than `version`, or an error unless `version` is
    /// 0 or one of the migrations' versions: [`Error::LayoutTooNew`] if it's
    /// newer than all of them, and [`Error::UnknownLayoutVersion`] if it
    /// falls between them.
    fn pending(&self, version: u64) -> Result<&[Migration<C, E>]> {
        if version > self.latest() {
            return Err(Error::LayoutTooNew { found: version, known: self.latest() });
        }
        let start = self.list.partition_point(|migration| migration.version <= version);
        if version != 0 && (start == 0 || self.list[start - 1].version != version) {
            return Err(Error::UnknownLayoutVersion { found: version });
        }
        Ok(&self.list[start..])
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
    /// The layout version recorded in the latest moment under the key of
    /// `migrations`, or 0 if there is none, as on a new database. This
    /// doesn't check it against the migrations; see
    /// [`History::check_version`] for that.
    ///
    /// The version is a `Uint`, or a non-negative `Int`. Anything else is an
    /// [`Error::UnexpectedTag`], and a negative `Int` is an
    /// [`Error::ExpectedUnsignedLong`].
    ///
    /// Like [`History::latest`], this never writes, so it works on a
    /// database opened with
    /// [`Database::open_read_only`](crate::Database::open_read_only).
    pub fn version<E>(&self, migrations: &Migrations<C, E>) -> Result<u64> {
        recorded_version(&self.latest()?, migrations.key)
    }

    /// Brings the latest moment to the newest layout version: runs each
    /// migration newer than the recorded version, in order, then records
    /// the newest version, all in one [`History::transact`]. Returns the
    /// versions before and after and the names of the migrations that ran.
    ///
    /// If a migration returns an error, nothing is committed, so the moment
    /// and its version stay exactly as they were, and that error is
    /// returned. If nothing is pending, nothing is committed.
    ///
    /// The recorded version must be 0 or the version of one of the
    /// migrations; otherwise nothing runs. If it's newer than every
    /// migration, so the data was written by newer code, this returns
    /// [`Error::LayoutTooNew`]. If it's between them, so the data was
    /// written by code with a migration this list doesn't have, it returns
    /// [`Error::UnknownLayoutVersion`].
    ///
    /// The version is read inside the transaction, so with one writer at a
    /// time (see the locking rules under "Initializing a Database" in the
    /// README), each
    /// migration runs exactly once.
    pub fn migrate<E: From<Error>>(&self, migrations: &Migrations<C, E>) -> Result<Migrated, E> {
        self.transact(|moment| {
            let from = recorded_version(moment, migrations.key)?;
            let pending = migrations.pending(from)?;
            for migration in pending {
                (migration.run)(moment)?;
            }
            if !pending.is_empty() {
                moment.put(migrations.key, migrations.latest())?;
            }
            let ran = pending.iter().map(|migration| migration.name).collect();
            Ok(Migrated { from, to: migrations.latest(), ran })
        })
    }

    /// Checks, without writing, that the latest moment is at exactly the
    /// newest version of `migrations`, and returns it. This is for readers,
    /// which shouldn't migrate: it returns [`Error::LayoutTooNew`] if the
    /// data was written by newer code, [`Error::UnknownLayoutVersion`] if
    /// its version isn't one of the migrations', and
    /// [`Error::LayoutTooOld`] if the writer hasn't migrated it yet.
    pub fn check_version<E>(&self, migrations: &Migrations<C, E>) -> Result<u64> {
        let found = self.version(migrations)?;
        if migrations.pending(found)?.is_empty() {
            Ok(found)
        } else {
            Err(Error::LayoutTooOld { found, expected: migrations.latest() })
        }
    }
}

/// The layout version recorded in `moment` under `key`. A missing or empty
/// value is version 0.
fn recorded_version<C: Core>(moment: &ReadHashMap<'_, C>, key: &str) -> Result<u64> {
    let Some(cursor) = moment.get_cursor(key)? else {
        return Ok(0);
    };
    match cursor.slot()?.tag {
        Tag::None => Ok(0),
        Tag::Int => u64::try_from(cursor.read_int()?).map_err(|_| Error::ExpectedUnsignedLong),
        _ => cursor.read_uint(),
    }
}
