//! Corrupt files whose pointers form a cycle make every walk fail with an
//! error. Verus proves the walks finish; these check the error.

use crate::btree::index_slot;
use crate::compact_store::{OffsetMapping, compact_slot};
use crate::error::{Error, Result};
use crate::format::{BTreeNode, BTreeNodeKind, SortedNode};
use crate::slot::{Slot, Tag};
use crate::store::{DbStore, Store, append, walk_bound};
use crate::{CoreMemory, Database, Hasher};

fn db() -> Database<CoreMemory> {
    Database::new(CoreMemory::new(), Hasher::sha1()).unwrap()
}

/// Appends a b-tree branch whose only child is itself.
fn cyclic_branch(s: &mut impl Store) -> i64 {
    let pos = s.len().unwrap();
    let mut node = BTreeNode::empty(BTreeNodeKind::Branch, 1);
    node.children[0] = index_slot(pos);
    node.counts[0] = 1;
    append(s, &node.to_bytes()).unwrap()
}

/// Appends an index block whose first slot points at itself.
fn cyclic_index(s: &mut impl Store) -> i64 {
    let pos = s.len().unwrap();
    let mut block = Vec::new();
    block.extend_from_slice(&Slot::new(pos, Tag::Index).to_bytes());
    for _ in 1..crate::format::SLOT_COUNT {
        block.extend_from_slice(&Slot::new(0, Tag::None).to_bytes());
    }
    append(s, &block).unwrap()
}

#[test]
fn cyclic_btree_reads_fail() {
    let db = db();
    let s = &mut DbStore::new(&db);
    let root = cyclic_branch(s);
    assert!(matches!(crate::btree_io::read_btree_slot(s, root, 0), Err(Error::InvalidBTreeNode)));
    assert!(matches!(crate::btree_join::btree_height(s, root), Err(Error::InvalidBTreeNode)));
    let header = crate::format::BTreeHeader { root_ptr: root, size: 1 };
    assert!(matches!(crate::iter_store::linked_array_list_seek(s, header, 0), Err(Error::InvalidBTreeNode)));
}

#[test]
fn cyclic_btree_writes_fail() {
    let db = db();
    let s = &mut DbStore::new(&db);
    let root = cyclic_branch(s);
    let fuel = walk_bound(s, crate::format::BTREE_BRANCH_BLOCK_SIZE as u64).unwrap();
    assert!(matches!(crate::btree_io::btree_insert(s, root, 0, None, fuel), Err(Error::InvalidBTreeNode)));
    let fuel = walk_bound(s, crate::format::BTREE_BRANCH_BLOCK_SIZE as u64).unwrap();
    assert!(matches!(crate::btree_io::btree_get_for_write(s, root, 0, None, fuel), Err(Error::InvalidBTreeNode)));
    let fuel = walk_bound(s, crate::format::BTREE_BRANCH_BLOCK_SIZE as u64).unwrap();
    assert!(matches!(crate::btree_io::btree_remove(s, root, 0, None, fuel), Err(Error::InvalidBTreeNode)));
    let fuel = walk_bound(s, crate::format::BTREE_BRANCH_BLOCK_SIZE as u64).unwrap();
    assert!(matches!(crate::btree_join::btree_split(s, root, 0, fuel), Err(Error::InvalidBTreeNode)));
}

#[test]
fn cyclic_sorted_map_fails() {
    let db = db();
    let s = &mut DbStore::new(&db);
    let pos = s.len().unwrap();
    let mut node = SortedNode::empty(BTreeNodeKind::Branch, 1);
    node.children[0] = index_slot(pos);
    node.counts[0] = 1;
    let root = append(s, &node.to_bytes()).unwrap();
    use crate::sorted_store::*;
    assert!(matches!(sorted_get_by_index(s, root, 0), Err(Error::InvalidBTreeNode)));
    assert!(matches!(sorted_path_from_index(s, root, 0), Err(Error::InvalidBTreeNode)));
}

#[test]
fn cyclic_hash_map_iteration_fails() {
    let db = db();
    let s = &mut DbStore::new(&db);
    let pos = cyclic_index(s);
    let mut st = crate::iter_store::new_state(s, Slot::new(pos, Tag::HashMap)).unwrap();
    assert!(matches!(crate::iter_store::next_internal(s, &mut st), Err(Error::InvalidDatabase)));
}

/// An offset map that forgets everything, so compaction can't stop at an
/// object it has already copied.
struct Forgetful;

impl OffsetMapping for Forgetful {
    fn get(&mut self, _: i64) -> Result<Option<i64>> {
        Ok(None)
    }
    fn put(&mut self, _: i64, _: i64) -> Result<()> {
        Ok(())
    }
}

#[test]
fn cyclic_compaction_fails() {
    let source = db();
    let target = db();
    let src = &mut DbStore::new(&source);
    let pos = cyclic_index(src);
    let tgt = &mut DbStore::new(&target);
    let r = compact_slot(src, tgt, &mut Forgetful, Slot::new(pos, Tag::HashMap), 20);
    assert!(matches!(r, Err(Error::InvalidDatabase)));
}
