//! Compaction: copying the data reachable from the latest moment into a
//! new database.

use std::collections::HashMap;
use std::ffi::OsString;
use std::fs::{self, File, OpenOptions};
use std::path::{Path, PathBuf};

use crate::core::Core;
use crate::database::Database;
use crate::error::Result;
use crate::slot::Slot;
use crate::store::DbStore;

/// Maps source offsets to target offsets during compaction.
///
/// Mappings must remain available until reset to preserve sharing and
/// cycles. Each map requires exclusive use during compaction.
pub trait OffsetMap {
    /// Clears mappings from the previous compaction.
    fn reset(&mut self) -> Result<()>;
    /// Returns the target offset, if the source offset is present.
    fn get(&mut self, source_offset: i64) -> Result<Option<i64>>;
    /// Records where the source object was copied.
    fn put(&mut self, source_offset: i64, target_offset: i64) -> Result<()>;
}

/// Stores compaction offsets in memory.
///
/// It grows with the number of live objects copied; use a
/// [`FileOffsetMap`](crate::FileOffsetMap) to keep them on disk instead.
pub type MemoryOffsetMap = HashMap<i64, i64>;

impl OffsetMap for HashMap<i64, i64> {
    fn reset(&mut self) -> Result<()> {
        self.clear();
        Ok(())
    }

    fn get(&mut self, source_offset: i64) -> Result<Option<i64>> {
        Ok(HashMap::get(self, &source_offset).copied())
    }

    fn put(&mut self, source_offset: i64, target_offset: i64) -> Result<()> {
        self.insert(source_offset, target_offset);
        Ok(())
    }
}

impl<C: Core> Database<C> {
    /// Compacts the database file at `path` in place, and makes `self` the
    /// compacted database.
    ///
    /// `self` must be the database opened from `path`. The compacted copy is
    /// written to a new temporary file next to it,
    /// `<path>.compacting-<random>`, and renamed over `path`, so `path` holds
    /// either the original or the complete compacted database, even after a
    /// crash. `open` wraps a file in a core (for example,
    /// `CoreBufferedFile::new`, or `|file| Box::new(CoreBufferedFile::new(file)) as DynCore`
    /// for a [`DynCore`](crate::DynCore)); it is called for the new file, and for the
    /// original again if the rename fails. `offset_map` is used as in
    /// [`Database::compact`]. `self` keeps its hasher.
    ///
    /// The original file is never lost:
    ///
    /// * If compaction fails, the temporary file is removed and `self` is
    ///   unchanged.
    /// * If the rename fails, the original is reopened as `self`, the
    ///   temporary file is removed, and the rename's error is returned.
    /// * If the rename fails and the original can't be reopened either,
    ///   `self` stays on the compacted copy, and this returns
    ///   [`Error::CompactFileReopenFailed`] with its path. Don't delete
    ///   that file. Calling `compact_file` again with the original `path`
    ///   retries the replacement, after which the old copy can be deleted.
    /// * On Unix, the parent directory is synced after the rename. If that
    ///   fails, the error is returned, but `path` and `self` are already the
    ///   compacted database.
    ///
    /// The file is replaced, not rewritten:
    ///
    /// * Other `Database`s with the file open keep reading the old file, so
    ///   they must reopen `path` to see the compacted one. A writer in
    ///   another process would keep committing to the old file, and those
    ///   commits would be lost, so hold the exclusive lock on the separate
    ///   lock file (see [`CoreBufferedFile::open`](crate::CoreBufferedFile::open))
    ///   across the compaction, and have other writers reopen `path` after
    ///   taking it.
    /// * Symlinks in `path` are resolved first, so the real file is
    ///   replaced, but other hard links to it keep the old file.
    /// * The new file gets the original's permission bits, but not its
    ///   owner or group (it is owned by the current user).
    pub fn compact_file(
        &mut self,
        path: impl AsRef<Path>,
        offset_map: &mut dyn OffsetMap,
        mut open: impl FnMut(File) -> C,
    ) -> Result<()> {
        let path = fs::canonicalize(path)?;
        let path = path.as_path();
        let temp_path = compacting_path(path)?;
        let hasher = self.hasher().clone();

        let compacted = (|| {
            // a new file, so a compaction never truncates a file in use
            let file = OpenOptions::new().read(true).write(true).create_new(true).open(&temp_path)?;
            fs::set_permissions(&temp_path, fs::metadata(path)?.permissions())?;
            // compact commits and syncs the target, and reopening it with
            // the caller's hasher keeps that hasher for later writes
            let core = self.compact(open(file), offset_map)?.into_core();
            Database::new(core, hasher.clone())
        })();
        let compacted = match compacted {
            Ok(compacted) => compacted,
            Err(err) => {
                let _ = fs::remove_file(&temp_path);
                return Err(err);
            }
        };

        // close the original before replacing it. the compacted copy stays
        // open, and its handle follows the file through the rename.
        drop(std::mem::replace(self, compacted));

        if let Err(rename_error) = fs::rename(&temp_path, path) {
            let reopened = (|| {
                let file = OpenOptions::new().read(true).write(true).open(path)?;
                Database::new(open(file), hasher)
            })();
            return match reopened {
                Ok(reopened) => {
                    drop(std::mem::replace(self, reopened));
                    let _ = fs::remove_file(&temp_path);
                    Err(rename_error.into())
                }
                Err(reopen_error) => Err(Error::CompactFileReopenFailed {
                    temp_path,
                    rename_error,
                    reopen_error: Box::new(reopen_error),
                }),
            };
        }

        sync_parent_dir(path)
    }
}

/// `<path>.compacting-<random>`, the temporary file used by
/// [`Database::compact_file`].
fn compacting_path(path: &Path) -> Result<PathBuf> {
    let random = getrandom::u64().map_err(|err| Error::Io(std::io::Error::other(err.to_string())))?;
    let mut name = OsString::from(path.as_os_str());
    name.push(format!(".compacting-{random:016x}"));
    Ok(PathBuf::from(name))
}

/// Makes a rename in `path`'s directory durable. On Unix, a rename is only
/// durable once its directory is synced; std can't sync a directory on
/// other platforms.
#[cfg(unix)]
fn sync_parent_dir(path: &Path) -> Result<()> {
    // the path is canonical, so it has a parent unless it is a root
    if let Some(parent) = path.parent() {
        File::open(parent)?.sync_all()?;
    }
    Ok(())
}

#[cfg(not(unix))]
fn sync_parent_dir(_path: &Path) -> Result<()> {
    Ok(())
}

pub(crate) struct Compactor<'s, 't, 'm, S: Core, T: Core> {
    pub source: &'s Database<S>,
    pub target: &'t Database<T>,
    pub hash_size: usize,
    pub offset_map: &'m mut dyn OffsetMap,
}

impl<S: Core, T: Core> Compactor<'_, '_, '_, S, T> {
    // verified in compact_store.rs
    pub(crate) fn remap_slot(&mut self, slot: Slot) -> Result<Slot> {
        let mut map = MapAdapter { map: &mut *self.offset_map };
        crate::compact_store::compact_slot(
            &mut DbStore::new(self.source),
            &mut DbStore::new(self.target),
            &mut map,
            slot,
            self.hash_size,
        )
    }
}

/// An [`OffsetMap`] as the verified compaction uses it.
struct MapAdapter<'m> {
    map: &'m mut dyn OffsetMap,
}

impl crate::compact_store::OffsetMapping for MapAdapter<'_> {
    fn get(&mut self, source_offset: i64) -> Result<Option<i64>> {
        self.map.get(source_offset)
    }

    fn put(&mut self, source_offset: i64, target_offset: i64) -> Result<()> {
        self.map.put(source_offset, target_offset)
    }
}
