//! The count-augmented B+tree behind sorted maps and sorted sets.


use crate::core::Core;
use crate::database::Database;
use crate::error::Result;
use crate::format::*;
use crate::path::SortedMapGetTarget;
#[allow(unused_imports)]
use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};
use crate::sorted_store::{self, SortedTarget};
use crate::store::DbStore;
use vstd::prelude::*;

verus! {

/// The new right sibling produced when a node splits.
#[derive(Debug, Clone, Copy)]
pub struct SortedSplit {
    pub node_ptr: i64,
    pub count: i64,
    pub separator: Slot,
}

/// Insert/replace result: the entry whose value to write, whether a new
/// entry was added (vs replacing), and the new right sibling if this node
/// split.
#[derive(Debug, Clone, Copy)]
pub struct SortedInsertResult {
    pub node_ptr: i64,
    pub count: i64,
    pub kv_slot: Slot,
    pub added: bool,
    pub split: Option<SortedSplit>,
}

/// The levels of a descent through a tree: each node's slot block, where
/// its slots start, and the index of the slot the descent took.
pub type NodePath = Vec<(i64, [Slot; SLOT_COUNT], usize)>;

#[derive(Debug, Clone, Copy)]
pub struct SortedSlot {
    pub slot: Slot,
    pub position: i64,
}

} // verus!

verus! {

pub(crate) fn leaf(entries: &[Slot]) -> (r: SortedNode)
    requires
        entries@.len() <= BTREE_SLOT_COUNT,
    ensures
        r.kind == BTreeNodeKind::Leaf,
        r.num == entries@.len(),
        r.entries@.subrange(0, r.num as int) == entries@,
{
    let mut node = SortedNode::empty(BTreeNodeKind::Leaf, entries.len());
    let mut j: usize = 0;
    while j < entries.len()
        invariant
            entries@.len() <= BTREE_SLOT_COUNT,
            j <= entries@.len(),
            node.kind == BTreeNodeKind::Leaf,
            node.num == entries@.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] node.entries@[k] == entries@[k],
        decreases entries.len() - j,
    {
        node.entries[j] = entries[j];
        j += 1;
    }
    assert(node.entries@.subrange(0, node.num as int) =~= entries@);
    node
}

pub(crate) fn branch(children: &[Slot], separators: &[Slot], counts: &[i64]) -> (r: SortedNode)
    requires
        children@.len() <= BTREE_SLOT_COUNT,
        separators@.len() == children@.len(),
        counts@.len() == children@.len(),
    ensures
        r.kind == BTreeNodeKind::Branch,
        r.num == children@.len(),
        r.children@.subrange(0, r.num as int) == children@,
        r.separators@.subrange(0, r.num as int) == separators@,
        r.counts@.subrange(0, r.num as int) == counts@,
{
    let mut node = SortedNode::empty(BTreeNodeKind::Branch, children.len());
    let mut j: usize = 0;
    while j < children.len()
        invariant
            children@.len() <= BTREE_SLOT_COUNT,
            separators@.len() == children@.len(),
            counts@.len() == children@.len(),
            j <= children@.len(),
            node.kind == BTreeNodeKind::Branch,
            node.num == children@.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] node.children@[k] == children@[k],
            forall|k: int| 0 <= k < j ==> #[trigger] node.separators@[k] == separators@[k],
            forall|k: int| 0 <= k < j ==> #[trigger] node.counts@[k] == counts@[k],
        decreases children.len() - j,
    {
        node.children[j] = children[j];
        node.separators[j] = separators[j];
        node.counts[j] = counts[j];
        j += 1;
    }
    assert(node.children@.subrange(0, node.num as int) =~= children@);
    assert(node.separators@.subrange(0, node.num as int) =~= separators@);
    assert(node.counts@.subrange(0, node.num as int) =~= counts@);
    node
}

/// Decodes a short bytes slot's inline value: its big-endian bytes, and
/// the length up to the first zero byte.
pub(crate) fn short_bytes_value(slot: Slot) -> (r: ([u8; 8], usize))
    ensures
        r.0@ == crate::bytes::u64_be_spec(crate::bytes::i2u(slot.value)),
        r.1 <= (if slot.full { 6usize } else { 8usize }),
        forall|i: int| 0 <= i < r.1 ==> #[trigger] r.0@[i] != 0,
        r.1 < (if slot.full { 6usize } else { 8usize }) ==> r.0@[r.1 as int] == 0,
{
    let buf = crate::bytes::u64_to_be_bytes(slot.value as u64);
    let total: usize = if slot.full { 6 } else { 8 };
    let mut len: usize = 0;
    while len < total && buf[len] != 0
        invariant
            len <= total <= 8,
            forall|i: int| 0 <= i < len ==> #[trigger] buf@[i] != 0,
        decreases total - len,
    {
        len += 1;
    }
    (buf, len)
}

} // verus!

// the database methods below forward to the verified versions in
// sorted_store.rs
impl<C: Core> Database<C> {
    fn limit(&self, frozen_at: i64) -> Option<i64> {
        self.tx_start.get().map(|tx_start| tx_start.max(frozen_at))
    }

    pub(crate) fn write_sorted_node(&self, node: &SortedNode) -> Result<i64> {
        sorted_store::write_sorted_node(&mut DbStore::new(self), node)
    }

    pub(crate) fn read_kv_pair(&self, kv_slot: Slot) -> Result<KeyValuePair> {
        sorted_store::read_kv_pair(&mut DbStore::new(self), kv_slot, self.hash_size())
    }

    // where the key slot is in a KvPair or SortedKvPair entry. the value slot follows it.
    pub(crate) fn kv_key_offset(&self, tag: Tag) -> i64 {
        sorted_store::kv_key_offset(tag, self.hash_size())
    }

    // descend by key to the matching leaf entry, or None
    pub(crate) fn sorted_get(&self, root_ptr: i64, key: &[u8]) -> Result<Option<SortedSlot>> {
        sorted_store::sorted_get(&mut DbStore::new(self), root_ptr, key, self.hash_size())
    }

    // descend by rank to the leaf entry at the given 0-based index
    pub(crate) fn sorted_get_by_index(&self, root_ptr: i64, rank: i64) -> Result<SortedSlot> {
        sorted_store::sorted_get_by_index(&mut DbStore::new(self), root_ptr, rank)
    }

    // number of keys strictly less than key (the inverse of get_by_index)
    pub(crate) fn sorted_rank(&self, root_ptr: i64, key: &[u8]) -> Result<i64> {
        sorted_store::sorted_rank(&mut DbStore::new(self), root_ptr, key, self.hash_size())
    }

    /// Descends to the first entry with a key >= `key`, returning the path
    /// of (node position, block, index) levels and the number of entries
    /// before it.
    pub(crate) fn sorted_path_from_key(&self, root_ptr: i64, key: &[u8]) -> Result<(NodePath, i64)> {
        sorted_store::sorted_path_from_key(&mut DbStore::new(self), root_ptr, key, self.hash_size())
    }

    /// Descends to the entry at `rank`, returning the path of (node
    /// position, block, index) levels.
    pub(crate) fn sorted_path_from_index(&self, root_ptr: i64, rank: i64) -> Result<NodePath> {
        sorted_store::sorted_path_from_index(&mut DbStore::new(self), root_ptr, rank)
    }

    // insert key (or locate it for replacement) within the subtree at
    // node_ptr, path-copying nodes and maintaining separators + counts. the
    // caller writes the value of the returned entry.
    pub(crate) fn sorted_put(&self, node_ptr: i64, key: &[u8], frozen_at: i64) -> Result<SortedInsertResult> {
        sorted_store::sorted_put(&mut DbStore::new(self), node_ptr, key, self.limit(frozen_at), self.hash_size())
    }

    // remove key from the subtree at node_ptr, path-copying nodes and
    // decrementing counts. an emptied leaf is left in place. returns the new
    // node pointer and whether the key was found.
    pub(crate) fn sorted_remove(&self, node_ptr: i64, key: &[u8], frozen_at: i64) -> Result<(i64, bool)> {
        sorted_store::sorted_remove(&mut DbStore::new(self), node_ptr, key, self.limit(frozen_at), self.hash_size())
    }

    pub(crate) fn sorted_grow_root(&self, result: &SortedInsertResult) -> Result<i64> {
        sorted_store::sorted_grow_root(&mut DbStore::new(self), result)
    }

    // turn a located/inserted entry into the slot for the requested target.
    // only the value is writeable (that is how put works); the key and the
    // entry pointer are immutable, so they are returned with no writeable
    // position.
    pub(crate) fn sorted_target_slot(&self, kv_slot: Slot, target: SortedMapGetTarget<'_>) -> Result<SlotPointer> {
        let target = match target {
            SortedMapGetTarget::KvPair(_) => SortedTarget::KvPair,
            SortedMapGetTarget::Key(_) => SortedTarget::Key,
            SortedMapGetTarget::Value(_) => SortedTarget::Value,
        };
        sorted_store::sorted_target_slot(&mut DbStore::new(self), kv_slot, target, self.hash_size())
    }
}
