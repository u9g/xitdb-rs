//! The count-augmented B+tree behind sorted maps and sorted sets.

use std::cmp::Ordering;

use crate::core::Core;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::format::*;
use crate::path::SortedMapGetTarget;
use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};
use vstd::prelude::*;

/// The new right sibling produced when a node splits.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SortedSplit {
    pub node_ptr: i64,
    pub count: i64,
    pub separator: Slot,
}

/// Insert/replace result: the entry whose value to write, whether a new
/// entry was added (vs replacing), and the new right sibling if this node
/// split.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SortedInsertResult {
    pub node_ptr: i64,
    pub count: i64,
    pub kv_slot: Slot,
    pub added: bool,
    pub split: Option<SortedSplit>,
}

/// The levels of a descent through a tree: each node's slot block, where
/// its slots start, and the index of the slot the descent took.
pub(crate) type NodePath = Vec<(i64, [Slot; SLOT_COUNT], usize)>;

#[derive(Debug, Clone, Copy)]
pub(crate) struct SortedSlot {
    pub slot: Slot,
    pub position: i64,
}

verus! {

fn index_slot(ptr: i64) -> (r: Slot)
    ensures
        r == (Slot { value: ptr, tag: Tag::Index, full: false }),
{
    Slot::new(ptr, Tag::Index)
}

} // verus!

fn entry_position(node_ptr: i64, i: usize) -> i64 {
    node_ptr + (BTREE_NODE_HEADER_SIZE + i * SLOT_LENGTH) as i64
}

verus! {

fn leaf(entries: &[Slot]) -> (r: SortedNode)
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

fn branch(children: &[Slot], separators: &[Slot], counts: &[i64]) -> (r: SortedNode)
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

impl<C: Core> Database<C> {
    pub(crate) fn read_sorted_node(&self, ptr: i64) -> Result<SortedNode> {
        let mut header = [0u8; BTREE_NODE_HEADER_SIZE];
        self.read_at(ptr, &mut header)?;
        let (kind, num) = decode_node_header(&header)?;
        let mut node = SortedNode::empty(kind, num);
        match kind {
            BTreeNodeKind::Leaf => {
                let mut body = [0u8; SLOT_LENGTH * BTREE_SLOT_COUNT];
                self.read_bytes(&mut body)?;
                node.entries = decode_slots(&body)?;
            }
            BTreeNodeKind::Branch => {
                let mut body = [0u8; (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT];
                self.read_bytes(&mut body)?;
                let separators_offset = SLOT_LENGTH * BTREE_SLOT_COUNT;
                let counts_offset = SLOT_LENGTH * 2 * BTREE_SLOT_COUNT;
                node.children = decode_slots(&body)?;
                node.separators = decode_slots(&body[separators_offset..])?;
                node.counts = decode_counts(&body[counts_offset..])?;
            }
        }
        Ok(node)
    }

    pub(crate) fn write_sorted_node(&self, node: &SortedNode) -> Result<i64> {
        self.append(&node.to_bytes())
    }

    // reuse old_ptr's position in place when it belongs to this transaction
    // (mirrors btree_write_node)
    fn sorted_write_node(&self, node: &SortedNode, old_ptr: i64, frozen_at: i64) -> Result<i64> {
        if self.btree_reusable(old_ptr, frozen_at) {
            self.write_at(old_ptr, &node.to_bytes())?;
            return Ok(old_ptr);
        }
        self.write_sorted_node(node)
    }

    pub(crate) fn read_kv_pair(&self, kv_slot: Slot) -> Result<KeyValuePair> {
        let hash_size = self.hash_size();
        let mut buf = vec![0u8; KeyValuePair::encoded_len(kv_slot.tag, hash_size)?];
        self.read_at(kv_slot.value, &mut buf)?;
        KeyValuePair::decode(&buf, kv_slot.tag, hash_size)
    }

    // writes a KvPair or SortedKvPair entry at the end and returns its slot
    fn write_kv_pair(&self, tag: Tag, kv: &KeyValuePair) -> Result<Slot> {
        let pos = self.append(&kv.encode(tag)?)?;
        Ok(Slot::new(pos, tag))
    }

    // where the key slot is in a KvPair or SortedKvPair entry. the value slot follows it.
    pub(crate) fn kv_key_offset(&self, tag: Tag) -> i64 {
        if tag == Tag::KvPair { self.hash_size() as i64 } else { 0 }
    }

    // lexicographic comparison of the byte key stored at key_slot (a bytes
    // or short_bytes slot) against the in-memory target
    fn compare_key(&self, key_slot: Slot, target: &[u8]) -> Result<Ordering> {
        match key_slot.tag {
            Tag::ShortBytes => {
                let (buf, len) = short_bytes_value(key_slot);
                Ok(buf[..len].cmp(target))
            }
            Tag::Bytes => {
                let len = self.read_i64_at(key_slot.value)?;
                let len = self.checked_len(key_slot.value + 8, len)?;
                let mut key = vec![0u8; len];
                self.read_bytes(&mut key)?;
                Ok(key.as_slice().cmp(target))
            }
            _ => Err(Error::UnexpectedTag),
        }
    }

    fn compare_entry_key(&self, entry: Slot, target: &[u8]) -> Result<Ordering> {
        let kv = self.read_kv_pair(entry)?;
        self.compare_key(kv.key_slot, target)
    }

    // the child of a branch whose subtree holds key, and the number of keys
    // in the children before it
    fn child_for_key(&self, node: &SortedNode, key: &[u8]) -> Result<(usize, i64)> {
        let mut i = 0;
        let mut before = 0i64;
        while i + 1 < node.num && self.compare_key(node.separators[i + 1], key)? != Ordering::Greater {
            before = before.wrapping_add(node.counts[i]);
            i += 1;
        }
        Ok((i, before))
    }

    // the child of a branch that holds `rank`, and the rank within it
    fn child_for_rank(node: &SortedNode, rank: i64) -> (usize, i64) {
        let mut i = 0;
        let mut rem = rank;
        while i + 1 < node.num && rem >= node.counts[i] {
            rem -= node.counts[i];
            i += 1;
        }
        (i, rem)
    }

    // descend by key to the matching leaf entry, or None
    pub(crate) fn sorted_get(&self, root_ptr: i64, key: &[u8]) -> Result<Option<SortedSlot>> {
        let mut node_ptr = root_ptr;
        loop {
            let node = self.read_sorted_node(node_ptr)?;
            if node.kind == BTreeNodeKind::Leaf {
                for (i, &entry) in node.entries[..node.num].iter().enumerate() {
                    match self.compare_entry_key(entry, key)? {
                        Ordering::Equal => {
                            return Ok(Some(SortedSlot { slot: entry, position: entry_position(node_ptr, i) }));
                        }
                        Ordering::Greater => return Ok(None),
                        Ordering::Less => {}
                    }
                }
                return Ok(None);
            }
            let (i, _) = self.child_for_key(&node, key)?;
            node_ptr = node.children[i].value;
        }
    }

    // descend by rank to the leaf entry at the given 0-based index
    pub(crate) fn sorted_get_by_index(&self, root_ptr: i64, rank: i64) -> Result<SortedSlot> {
        let mut node_ptr = root_ptr;
        let mut rem = rank;
        loop {
            let node = self.read_sorted_node(node_ptr)?;
            if node.kind == BTreeNodeKind::Leaf {
                let i = check_rank(rem, node.num, false)?;
                return Ok(SortedSlot { slot: node.entries[i], position: entry_position(node_ptr, i) });
            }
            let (i, next_rem) = Self::child_for_rank(&node, rem);
            rem = next_rem;
            node_ptr = node.children[i].value;
        }
    }

    // number of keys strictly less than key (the inverse of get_by_index)
    pub(crate) fn sorted_rank(&self, root_ptr: i64, key: &[u8]) -> Result<i64> {
        let mut node_ptr = root_ptr;
        let mut rank = 0;
        loop {
            let node = self.read_sorted_node(node_ptr)?;
            if node.kind == BTreeNodeKind::Leaf {
                for &entry in &node.entries[..node.num] {
                    if self.compare_entry_key(entry, key)? != Ordering::Less {
                        break;
                    }
                    rank += 1;
                }
                return Ok(rank);
            }
            let (i, before) = self.child_for_key(&node, key)?;
            rank += before;
            node_ptr = node.children[i].value;
        }
    }

    /// Descends to the first entry with a key >= `key`, returning the path
    /// of (node position, block, index) levels and the number of entries
    /// before it.
    pub(crate) fn sorted_path_from_key(
        &self,
        root_ptr: i64,
        key: &[u8],
    ) -> Result<(NodePath, i64)> {
        let mut stack = Vec::new();
        let mut node_ptr = root_ptr;
        let mut before = 0;
        loop {
            let node = self.read_sorted_node(node_ptr)?;
            let position = node_ptr + BTREE_NODE_HEADER_SIZE as i64;
            if node.kind == BTreeNodeKind::Leaf {
                let mut li = node.num;
                for (j, &entry) in node.entries[..node.num].iter().enumerate() {
                    if self.compare_entry_key(entry, key)? != Ordering::Less {
                        li = j;
                        break;
                    }
                }
                before += li as i64;
                stack.push((position, node.entries, li));
                return Ok((stack, before));
            }
            let (i, child_before) = self.child_for_key(&node, key)?;
            before += child_before;
            stack.push((position, node.children, i));
            node_ptr = node.children[i].value;
        }
    }

    /// Descends to the entry at `rank`, returning the path of (node
    /// position, block, index) levels.
    pub(crate) fn sorted_path_from_index(
        &self,
        root_ptr: i64,
        rank: i64,
    ) -> Result<NodePath> {
        let mut stack = Vec::new();
        let mut node_ptr = root_ptr;
        let mut rem = rank;
        loop {
            let node = self.read_sorted_node(node_ptr)?;
            let position = node_ptr + BTREE_NODE_HEADER_SIZE as i64;
            if node.kind == BTreeNodeKind::Leaf {
                stack.push((position, node.entries, check_rank(rem, node.num, false)?));
                return Ok(stack);
            }
            let (i, next_rem) = Self::child_for_rank(&node, rem);
            rem = next_rem;
            stack.push((position, node.children, i));
            node_ptr = node.children[i].value;
        }
    }

    // write a byte key as a short_bytes (inline, <=8 bytes, no interior zero)
    // or external bytes slot
    fn write_key(&self, key: &[u8]) -> Result<Slot> {
        if key.len() <= 8 && !key.contains(&0) {
            let mut value = [0u8; 8];
            value[..key.len()].copy_from_slice(key);
            return Ok(Slot::new(i64::from_be_bytes(value), Tag::ShortBytes));
        }
        let mut buf = Vec::with_capacity(8 + key.len());
        buf.extend_from_slice(&(key.len() as i64).to_be_bytes());
        buf.extend_from_slice(key);
        let pos = self.append(&buf)?;
        Ok(Slot::new(pos, Tag::Bytes))
    }

    // materialize a new leaf entry: write the key bytes and a key-value pair
    // with an empty value (the caller fills it in). navigation is by key
    // bytes, so the entry has no hash.
    fn sorted_new_entry(&self, key: &[u8]) -> Result<Slot> {
        let key_slot = self.write_key(key)?;
        let kv = KeyValuePair { value_slot: Slot::default(), key_slot, hash: Vec::new() };
        self.write_kv_pair(Tag::SortedKvPair, &kv)
    }

    // insert key (or locate it for replacement) within the subtree at
    // node_ptr, path-copying nodes and maintaining separators + counts. the
    // caller writes the value of the returned entry.
    pub(crate) fn sorted_put(&self, node_ptr: i64, key: &[u8], frozen_at: i64) -> Result<SortedInsertResult> {
        let node = self.read_sorted_node(node_ptr)?;
        match node.kind {
            BTreeNodeKind::Leaf => {
                let mut idx = node.num;
                let mut found = false;
                for (i, &entry) in node.entries[..node.num].iter().enumerate() {
                    match self.compare_entry_key(entry, key)? {
                        Ordering::Equal => {
                            idx = i;
                            found = true;
                            break;
                        }
                        Ordering::Greater => {
                            idx = i;
                            break;
                        }
                        Ordering::Less => {}
                    }
                }

                if found {
                    // replace: return a writable value slot, copy-on-writing the
                    // kv_pair if it belongs to a past moment
                    let mut leaf = node;
                    let mut kv_slot = node.entries[idx];
                    if !self.btree_reusable(kv_slot.value, frozen_at) {
                        let kv = self.read_kv_pair(kv_slot)?;
                        kv_slot = self.write_kv_pair(kv_slot.tag, &kv)?;
                        leaf.entries[idx] = kv_slot;
                    }
                    let ptr = self.sorted_write_node(&leaf, node_ptr, frozen_at)?;
                    return Ok(SortedInsertResult {
                        node_ptr: ptr,
                        count: node.num as i64,
                        kv_slot,
                        added: false,
                        split: None,
                    });
                }

                // insert a new entry at idx
                let entry = self.sorted_new_entry(key)?;
                let mut entries = node.entries[..node.num].to_vec();
                entries.insert(idx, entry);
                let total = entries.len();

                if total <= BTREE_SLOT_COUNT {
                    let ptr = self.sorted_write_node(&leaf(&entries), node_ptr, frozen_at)?;
                    return Ok(SortedInsertResult {
                        node_ptr: ptr,
                        count: total as i64,
                        kv_slot: entry,
                        added: true,
                        split: None,
                    });
                }

                // overflow: split into two leaves; the new sibling's separator is
                // the key of its first entry
                let left_n = BTREE_SPLIT_COUNT;
                let separator = self.read_kv_pair(entries[left_n])?.key_slot;
                let left_ptr = self.sorted_write_node(&leaf(&entries[..left_n]), node_ptr, frozen_at)?;
                let right_ptr = self.write_sorted_node(&leaf(&entries[left_n..]))?;
                Ok(SortedInsertResult {
                    node_ptr: left_ptr,
                    count: left_n as i64,
                    kv_slot: entry,
                    added: true,
                    split: Some(SortedSplit { node_ptr: right_ptr, count: (total - left_n) as i64, separator }),
                })
            }
            BTreeNodeKind::Branch => {
                let (i, _) = self.child_for_key(&node, key)?;
                let child = self.sorted_put(node.children[i].value, key, frozen_at)?;

                let mut children = node.children[..node.num].to_vec();
                let mut separators = node.separators[..node.num].to_vec();
                let mut counts = node.counts[..node.num].to_vec();
                children[i] = index_slot(child.node_ptr);
                counts[i] = child.count;
                if let Some(split) = child.split {
                    children.insert(i + 1, index_slot(split.node_ptr));
                    separators.insert(i + 1, split.separator);
                    counts.insert(i + 1, split.count);
                }
                let total = children.len();

                if total <= BTREE_SLOT_COUNT {
                    let node = branch(&children, &separators, &counts);
                    let ptr = self.sorted_write_node(&node, node_ptr, frozen_at)?;
                    return Ok(SortedInsertResult {
                        node_ptr: ptr,
                        count: node.subtree_count(),
                        kv_slot: child.kv_slot,
                        added: child.added,
                        split: None,
                    });
                }

                // overflow: split into two branches; the new sibling's separator
                // is the smallest key of its first child (separators[left_n] of
                // the combined)
                let left_n = BTREE_SPLIT_COUNT;
                let left = branch(&children[..left_n], &separators[..left_n], &counts[..left_n]);
                let right = branch(&children[left_n..], &separators[left_n..], &counts[left_n..]);
                let separator = separators[left_n];
                let left_ptr = self.sorted_write_node(&left, node_ptr, frozen_at)?;
                let right_ptr = self.write_sorted_node(&right)?;
                Ok(SortedInsertResult {
                    node_ptr: left_ptr,
                    count: left.subtree_count(),
                    kv_slot: child.kv_slot,
                    added: child.added,
                    split: Some(SortedSplit { node_ptr: right_ptr, count: right.subtree_count(), separator }),
                })
            }
        }
    }

    // remove key from the subtree at node_ptr, path-copying nodes and
    // decrementing counts. an emptied leaf is left in place. returns the new
    // node pointer and whether the key was found.
    pub(crate) fn sorted_remove(&self, node_ptr: i64, key: &[u8], frozen_at: i64) -> Result<(i64, bool)> {
        let node = self.read_sorted_node(node_ptr)?;
        match node.kind {
            BTreeNodeKind::Leaf => {
                let mut idx = None;
                for (i, &entry) in node.entries[..node.num].iter().enumerate() {
                    match self.compare_entry_key(entry, key)? {
                        Ordering::Equal => {
                            idx = Some(i);
                            break;
                        }
                        Ordering::Greater => break,
                        Ordering::Less => {}
                    }
                }
                let Some(idx) = idx else {
                    return Ok((node_ptr, false));
                };
                let mut entries = node.entries[..node.num].to_vec();
                entries.remove(idx);
                let ptr = self.sorted_write_node(&leaf(&entries), node_ptr, frozen_at)?;
                Ok((ptr, true))
            }
            BTreeNodeKind::Branch => {
                let (i, _) = self.child_for_key(&node, key)?;
                let (child_ptr, found) = self.sorted_remove(node.children[i].value, key, frozen_at)?;
                if !found {
                    return Ok((node_ptr, false));
                }
                let mut branch = node;
                branch.children[i] = index_slot(child_ptr);
                branch.counts[i] -= 1;
                let ptr = self.sorted_write_node(&branch, node_ptr, frozen_at)?;
                Ok((ptr, true))
            }
        }
    }

    pub(crate) fn sorted_grow_root(&self, result: &SortedInsertResult) -> Result<i64> {
        match result.split {
            Some(split) => {
                let mut root = SortedNode::empty(BTreeNodeKind::Branch, 2);
                root.children[0] = index_slot(result.node_ptr);
                root.children[1] = index_slot(split.node_ptr);
                root.separators[1] = split.separator; // separators[0] is an unused sentinel
                root.counts[0] = result.count;
                root.counts[1] = split.count;
                self.write_sorted_node(&root)
            }
            None => Ok(result.node_ptr),
        }
    }

    // turn a located/inserted entry into the slot for the requested target.
    // only the value is writeable (that is how put works); the key and the
    // entry pointer are immutable, so they are returned with no writeable
    // position.
    pub(crate) fn sorted_target_slot(&self, kv_slot: Slot, target: SortedMapGetTarget<'_>) -> Result<SlotPointer> {
        let kv = self.read_kv_pair(kv_slot)?;
        Ok(match target {
            SortedMapGetTarget::KvPair(_) => SlotPointer::new(None, kv_slot),
            SortedMapGetTarget::Key(_) => SlotPointer::new(None, kv.key_slot),
            SortedMapGetTarget::Value(_) => {
                let pos = kv_slot.value + self.kv_key_offset(kv_slot.tag) + SLOT_LENGTH as i64;
                SlotPointer::new(Some(pos), kv.value_slot)
            }
        })
    }
}
