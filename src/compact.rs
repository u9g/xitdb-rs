//! Compaction: copying the data reachable from the latest moment into a
//! new database.

use std::collections::HashMap;
use std::ffi::OsString;
use std::fs::{self, File, OpenOptions};
use std::path::{Path, PathBuf};

use crate::core::Core;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::{SLOT_LENGTH, Slot, Tag};

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
    /// `CoreBufferedFile::new`); it is called for the new file, and for the
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
    ///   commits would be lost, so hold the exclusive write lock across the
    ///   compaction, and have other writers reopen `path` after taking it.
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

#[derive(Clone, Copy)]
enum Populate {
    Index,
    ArrayList,
    BTree,
    HashMap { counted: bool },
    KvPair(Tag),
    SortedMap,
    BTreeLeaf { num: u8 },
    BTreeBranch { num: u8 },
    SortedLeaf { num: u8 },
    SortedBranch { num: u8 },
}

impl<S: Core, T: Core> Compactor<'_, '_, '_, S, T> {
    fn reserve_block(&self, size: usize) -> Result<i64> {
        self.target.append(&vec![0u8; size])
    }

    fn visit_object(&mut self, source_offset: i64, size: usize, populate: Populate) -> Result<i64> {
        if let Some(target_offset) = self.offset_map.get(source_offset)? {
            return Ok(target_offset);
        }
        let target_offset = self.reserve_block(size)?;
        self.offset_map.put(source_offset, target_offset)?;
        self.populate(populate, source_offset, target_offset)?;
        Ok(target_offset)
    }

    fn populate(&mut self, populate: Populate, source_offset: i64, target_offset: i64) -> Result<()> {
        match populate {
            Populate::Index => self.populate_index(source_offset, target_offset),
            Populate::ArrayList => self.populate_array_list(source_offset, target_offset),
            Populate::BTree => self.populate_btree(source_offset, target_offset, false),
            Populate::SortedMap => self.populate_btree(source_offset, target_offset, true),
            Populate::HashMap { counted } => self.populate_hash_map(source_offset, target_offset, counted),
            Populate::KvPair(tag) => self.populate_kv_pair(source_offset, target_offset, tag),
            Populate::BTreeLeaf { num } | Populate::SortedLeaf { num } => {
                self.populate_leaf(source_offset, target_offset, num)
            }
            Populate::BTreeBranch { num } => self.populate_branch(source_offset, target_offset, num, false),
            Populate::SortedBranch { num } => self.populate_branch(source_offset, target_offset, num, true),
        }
    }

    pub(crate) fn remap_slot(&mut self, slot: Slot) -> Result<Slot> {
        let new_offset = match slot.tag {
            Tag::None | Tag::Uint | Tag::Int | Tag::Float | Tag::ShortBytes => return Ok(slot),
            Tag::Bytes => self.remap_bytes(slot)?,
            Tag::Index => self.visit_object(slot.value, INDEX_BLOCK_SIZE, Populate::Index)?,
            Tag::ArrayList => self.visit_object(slot.value, ARRAY_LIST_HEADER_LENGTH, Populate::ArrayList)?,
            Tag::LinkedArrayList => self.visit_object(slot.value, BTREE_HEADER_LENGTH, Populate::BTree)?,
            Tag::HashMap | Tag::HashSet => {
                self.visit_object(slot.value, INDEX_BLOCK_SIZE, Populate::HashMap { counted: false })?
            }
            Tag::CountedHashMap | Tag::CountedHashSet => {
                self.visit_object(slot.value, INDEX_BLOCK_SIZE + 8, Populate::HashMap { counted: true })?
            }
            Tag::KvPair => {
                let size = key_value_pair_length(self.hash_size);
                self.visit_object(slot.value, size, Populate::KvPair(Tag::KvPair))?
            }
            Tag::SortedKvPair => {
                self.visit_object(slot.value, SORTED_KEY_VALUE_PAIR_LENGTH, Populate::KvPair(Tag::SortedKvPair))?
            }
            Tag::SortedMap | Tag::SortedSet => {
                self.visit_object(slot.value, BTREE_HEADER_LENGTH, Populate::SortedMap)?
            }
        };
        Ok(Slot { value: new_offset, tag: slot.tag, full: slot.full })
    }

    fn remap_bytes(&mut self, slot: Slot) -> Result<i64> {
        if let Some(target_offset) = self.offset_map.get(slot.value)? {
            return Ok(target_offset);
        }

        let length = self.source.read_i64_at(slot.value)?;
        let format_tag_size = if slot.full { 2 } else { 0 };
        let mut remaining = length + format_tag_size;

        let new_offset = self.target.append(&length.to_be_bytes())?;
        let mut buf = vec![0u8; remaining.clamp(0, 4096) as usize];
        while remaining > 0 {
            let chunk = remaining.min(buf.len() as i64) as usize;
            // the target is appended to, so it is written at its end each time
            self.source.read_bytes(&mut buf[..chunk])?;
            self.target.write_bytes(&buf[..chunk])?;
            remaining -= chunk as i64;
        }

        self.offset_map.put(slot.value, new_offset)?;
        Ok(new_offset)
    }

    fn remap_slots(&mut self, slots: &[Slot]) -> Result<Vec<Slot>> {
        slots.iter().map(|&slot| self.remap_slot(slot)).collect()
    }

    fn populate_index(&mut self, source_offset: i64, target_offset: i64) -> Result<()> {
        let block = self.source.read_index_block(source_offset)?;
        let remapped = self.remap_slots(&block)?;
        let mut buf = Vec::with_capacity(INDEX_BLOCK_SIZE);
        encode_slots(&mut buf, &remapped);
        self.target.write_at(target_offset, &buf)
    }

    fn remap_array_list_index(&mut self, source_offset: i64, size: i64, shift: u8) -> Result<i64> {
        let child_size = 1i64 << (shift as u32 * BIT_COUNT);

        // full blocks can use the normal cache. partial blocks may be shared
        // by lists with different sizes, so copy them separately and leave
        // the slots beyond the size empty.
        if child_size <= i64::MAX / SLOT_COUNT as i64 && size == child_size * SLOT_COUNT as i64 {
            return Ok(self.remap_slot(Slot::new(source_offset, Tag::Index))?.value);
        }

        let target_offset = self.reserve_block(INDEX_BLOCK_SIZE)?;
        let block = self.source.read_index_block(source_offset)?;
        let mut remapped_block = [Slot::default(); SLOT_COUNT];
        let mut remaining = size;
        for (i, &child_slot) in block.iter().enumerate() {
            if remaining <= 0 {
                break;
            }
            let count = remaining.min(child_size);
            remapped_block[i] = if shift == 0 {
                self.remap_slot(child_slot)?
            } else {
                if child_slot.tag != Tag::Index {
                    return Err(Error::UnexpectedTag);
                }
                let value = self.remap_array_list_index(child_slot.value, count, shift - 1)?;
                Slot { value, ..child_slot }
            };
            remaining -= count;
        }

        let mut buf = Vec::with_capacity(INDEX_BLOCK_SIZE);
        encode_slots(&mut buf, &remapped_block);
        self.target.write_at(target_offset, &buf)?;
        Ok(target_offset)
    }

    fn populate_array_list(&mut self, source_offset: i64, target_offset: i64) -> Result<()> {
        let header = self.source.read_array_list_header(source_offset)?;
        let shift = array_list_shift(header.size - 1);
        let ptr = self.remap_array_list_index(header.ptr, header.size, shift)?;
        self.target.write_at(target_offset, &ArrayListHeader { ptr, size: header.size }.to_bytes())
    }

    fn populate_btree(&mut self, source_offset: i64, target_offset: i64, sorted: bool) -> Result<()> {
        let header = self.source.read_btree_header(source_offset)?;
        let root_ptr = self.remap_node(header.root_ptr, sorted)?;
        self.target.write_at(target_offset, &BTreeHeader { root_ptr, size: header.size }.to_bytes())
    }

    fn remap_node(&mut self, node_offset: i64, sorted: bool) -> Result<i64> {
        if let Some(mapped) = self.offset_map.get(node_offset)? {
            return Ok(mapped);
        }
        let mut header = [0u8; BTREE_NODE_HEADER_SIZE];
        self.source.read_at(node_offset, &mut header)?;
        let (kind, num) = decode_node_header(&header)?;
        let num = num as u8;
        let (size, populate) = match (kind, sorted) {
            (BTreeNodeKind::Leaf, false) => (BTREE_LEAF_BLOCK_SIZE, Populate::BTreeLeaf { num }),
            (BTreeNodeKind::Branch, false) => (BTREE_BRANCH_BLOCK_SIZE, Populate::BTreeBranch { num }),
            (BTreeNodeKind::Leaf, true) => (SORTED_LEAF_BLOCK_SIZE, Populate::SortedLeaf { num }),
            (BTreeNodeKind::Branch, true) => (SORTED_BRANCH_BLOCK_SIZE, Populate::SortedBranch { num }),
        };
        self.visit_object(node_offset, size, populate)
    }

    // leaves of both kinds of b-tree are a header followed by slots that are
    // remapped like any other
    fn populate_leaf(&mut self, source_offset: i64, target_offset: i64, num: u8) -> Result<()> {
        let mut body = [0u8; SLOT_LENGTH * BTREE_SLOT_COUNT];
        self.source.read_at(source_offset + BTREE_NODE_HEADER_SIZE as i64, &mut body)?;
        let slots = self.remap_slots(&decode_slots(&body)?)?;
        let mut buf = Vec::with_capacity(BTREE_LEAF_BLOCK_SIZE);
        buf.extend_from_slice(&[BTreeNodeKind::Leaf as u8, num]);
        encode_slots(&mut buf, &slots);
        self.target.write_at(target_offset, &buf)
    }

    fn populate_branch(&mut self, source_offset: i64, target_offset: i64, num: u8, sorted: bool) -> Result<()> {
        let slot_blocks = if sorted { 2 } else { 1 };
        let mut body = vec![0u8; (SLOT_LENGTH * slot_blocks + 8) * BTREE_SLOT_COUNT];
        self.source.read_at(source_offset + BTREE_NODE_HEADER_SIZE as i64, &mut body)?;

        let mut children = decode_slots(&body)?;
        for child in &mut children {
            // non-index children are copied verbatim
            if child.tag == Tag::Index {
                child.value = self.remap_node(child.value, sorted)?;
            }
        }
        let separators = if sorted {
            Some(self.remap_slots(&decode_slots(&body[SLOT_LENGTH * BTREE_SLOT_COUNT..])?)?)
        } else {
            None
        };
        let counts = decode_counts(&body[SLOT_LENGTH * slot_blocks * BTREE_SLOT_COUNT..]);

        let mut buf = Vec::with_capacity(BTREE_NODE_HEADER_SIZE + body.len());
        buf.extend_from_slice(&[BTreeNodeKind::Branch as u8, num]);
        encode_slots(&mut buf, &children);
        if let Some(separators) = separators {
            encode_slots(&mut buf, &separators);
        }
        encode_counts(&mut buf, &counts);
        self.target.write_at(target_offset, &buf)
    }

    fn populate_hash_map(&mut self, source_offset: i64, target_offset: i64, counted: bool) -> Result<()> {
        let (count, index_offset) = if counted {
            (Some(self.source.read_i64_at(source_offset)?), source_offset + 8)
        } else {
            (None, source_offset)
        };
        let block = self.source.read_index_block(index_offset)?;
        let remapped = self.remap_slots(&block)?;

        let mut buf = Vec::with_capacity(8 + INDEX_BLOCK_SIZE);
        if let Some(count) = count {
            buf.extend_from_slice(&count.to_be_bytes());
        }
        encode_slots(&mut buf, &remapped);
        self.target.write_at(target_offset, &buf)
    }

    fn populate_kv_pair(&mut self, source_offset: i64, target_offset: i64, tag: Tag) -> Result<()> {
        let mut kv = self.source.read_kv_pair(Slot::new(source_offset, tag))?;
        // remap the key and value slots, and write the pair in the same form
        kv.key_slot = self.remap_slot(kv.key_slot)?;
        kv.value_slot = self.remap_slot(kv.value_slot)?;
        self.target.write_at(target_offset, &kv.encode(tag)?)
    }
}
