//! The sorted map B+tree over a [`Store`] (`src/sorted.rs`'s database
//! methods), checked by Verus.
//!
//! Reads leave the file unchanged. Writes change nothing before `limit`
//! (the crate's `max(tx_start, frozen_at)`): a node is written in place only
//! from `limit` on and appended otherwise, and the entry `sorted_put`
//! returns for its value to be written is at or after `limit`. Every
//! offset computation is checked, so corrupt pointers and counts fail with
//! an error instead of overflowing.

use std::cmp::Ordering;

#[allow(unused_imports)]
use crate::array_list_store::*;
#[allow(unused_imports)]
use crate::btree_io::*;
#[allow(unused_imports)]
use crate::btree_join::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::sorted::{NodePath, SortedInsertResult, SortedSlot, SortedSplit, short_bytes_value};
use crate::store::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Which part of a sorted map entry `sorted_target_slot` returns.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SortedTarget {
    KvPair,
    Key,
    Value,
}

pub open spec fn writes_ok(f: Seq<u8>, g: Seq<u8>, limit: Option<i64>) -> bool {
    tx_ok(f, g, limit)
}

proof fn lemma_grows_tx(f: Seq<u8>, g: Seq<u8>, limit: Option<i64>)
    requires
        grows(f, g),
        limit is Some ==> 0 <= limit.unwrap() <= f.len(),
    ensures
        tx_ok(f, g, limit),
{
    if limit is Some {
        let l = limit.unwrap() as int;
        assert(g.subrange(0, l) =~= f.subrange(0, l));
    }
}

proof fn lemma_tx_trans(f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, limit: Option<i64>)
    requires
        tx_ok(f, g, limit),
        tx_ok(g, h, limit),
    ensures
        tx_ok(f, h, limit),
{
    if limit is Some {
        lemma_kept_trans(f, g, h, limit.unwrap() as int);
    }
}

fn zero_vec(n: usize) -> (r: Vec<u8>)
    ensures
        r@.len() == n,
{
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r@.len() == i,
        decreases n - i,
    {
        r.push(0);
        i += 1;
    }
    r
}

/// Lexicographic comparison of byte strings, as `<[u8]>::cmp`.
fn lex_cmp(a: &[u8], b: &[u8]) -> (r: Ordering) {
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        invariant
            i <= a@.len(),
            i <= b@.len(),
        decreases a.len() - i,
    {
        if a[i] < b[i] {
            return Ordering::Less;
        }
        if a[i] > b[i] {
            return Ordering::Greater;
        }
        i += 1;
    }
    if a.len() < b.len() {
        Ordering::Less
    } else if a.len() > b.len() {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

fn is_greater(o: Ordering) -> (r: bool)
    ensures
        r == (o == Ordering::Greater),
{
    matches!(o, Ordering::Greater)
}

fn is_less(o: Ordering) -> (r: bool)
    ensures
        r == (o == Ordering::Less),
{
    matches!(o, Ordering::Less)
}

/// `read_sorted_node`.
pub fn read_sorted_node<S: Store>(s: &mut S, ptr: i64) -> (r: Result<SortedNode>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().num <= BTREE_SLOT_COUNT,
        r is Ok ==> forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] r.unwrap().counts[i] >= 0,
{
    let mut header = [0u8; BTREE_NODE_HEADER_SIZE];
    s.read_at(ptr, &mut header)?;
    let (kind, num) = decode_node_header(&header)?;
    let mut node = SortedNode::empty(kind, num);
    let body_pos = match ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    match kind {
        BTreeNodeKind::Leaf => {
            let mut body = [0u8; SLOT_LENGTH * BTREE_SLOT_COUNT];
            s.read_at(body_pos, &mut body)?;
            node.entries = decode_slots(&body)?;
        },
        BTreeNodeKind::Branch => {
            let mut body = [0u8; (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT];
            s.read_at(body_pos, &mut body)?;
            let separators_offset = SLOT_LENGTH * BTREE_SLOT_COUNT;
            let counts_offset = SLOT_LENGTH * 2 * BTREE_SLOT_COUNT;
            node.children = decode_slots(&body)?;
            node.separators = decode_slots(slice_subrange(body.as_slice(), separators_offset, counts_offset))?;
            node.counts = decode_counts(slice_subrange(body.as_slice(), counts_offset, (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT))?;
        },
    }
    Ok(node)
}

/// `write_sorted_node`: appended.
pub fn write_sorted_node<S: Store>(s: &mut S, node: &SortedNode) -> (r: Result<i64>)
    ensures
        r is Ok ==> r.unwrap() == old(s).file().len() && grows(old(s).file(), final(s).file()),
{
    let bytes = node.to_bytes();
    let p = append(s, bytes.as_slice())?;
    proof {
        assert(s.file().subrange(0, old(s).file().len() as int) =~= old(s).file());
    }
    Ok(p)
}

/// `sorted_write_node`: in place at `old_ptr` if that is at or after
/// `limit`, appended otherwise.
pub fn sorted_write_node<S: Store>(s: &mut S, node: &SortedNode, old_ptr: i64, limit: Option<i64>) -> (r: Result<i64>)
    requires
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        (r is Ok && limit is Some) ==> r.unwrap() >= limit.unwrap(),
{
    let reusable = match limit {
        Some(l) => old_ptr >= l,
        None => false,
    };
    if reusable {
        let ghost f = s.file();
        let bytes = node.to_bytes();
        s.write_at(old_ptr, bytes.as_slice())?;
        proof {
            lemma_overwrite_keeps(f, old_ptr as int, bytes@, limit.unwrap() as int);
        }
        return Ok(old_ptr);
    }
    let p = write_sorted_node(s, node)?;
    proof {
        lemma_grows_tx(old(s).file(), s.file(), limit);
    }
    Ok(p)
}

/// `read_kv_pair`.
pub fn read_kv_pair<S: Store>(s: &mut S, kv_slot: Slot, hash_size: usize) -> (r: Result<KeyValuePair>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
{
    let len = KeyValuePair::encoded_len(kv_slot.tag, hash_size)?;
    let mut buf = zero_vec(len);
    s.read_at(kv_slot.value, buf.as_mut_slice())?;
    KeyValuePair::decode(buf.as_slice(), kv_slot.tag, hash_size)
}

/// `write_kv_pair`: the entry, appended.
pub fn write_kv_pair<S: Store>(s: &mut S, tag: Tag, kv: &KeyValuePair) -> (r: Result<Slot>)
    ensures
        r is Ok ==> r.unwrap().value == old(s).file().len() && grows(old(s).file(), final(s).file()),
{
    let bytes = kv.encode(tag)?;
    let pos = append(s, bytes.as_slice())?;
    proof {
        assert(s.file().subrange(0, old(s).file().len() as int) =~= old(s).file());
    }
    Ok(Slot::new(pos, tag))
}

/// `kv_key_offset`: where the key slot is in an entry.
pub fn kv_key_offset(tag: Tag, hash_size: usize) -> (r: i64)
    requires
        hash_size <= 0xffff,
    ensures
        0 <= r <= 0xffff,
{
    if matches!(tag, Tag::KvPair) { hash_size as i64 } else { 0 }
}

/// `checked_len`: a byte array's length, read from disk, checked before a
/// buffer is allocated for it.
pub fn checked_len<S: Store>(s: &mut S, pos: i64, len: i64) -> (r: Result<usize>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap() == len,
{
    if len < 0 {
        return Err(Error::ExpectedUnsignedLong);
    }
    if len > 0x1_0000 {
        let end = match pos.checked_add(len) {
            Some(e) => e,
            None => return Err(Error::InvalidDatabase),
        };
        let file_len = match s.len() {
            Ok(n) => n,
            Err(_) => 0,
        };
        if end > file_len {
            return Err(Error::InvalidDatabase);
        }
    }
    if len as u64 > usize::MAX as u64 {
        return Err(Error::InvalidDatabase);
    }
    Ok(len as usize)
}

/// `compare_key`: the byte key in `key_slot` against `target`.
pub fn compare_key<S: Store>(s: &mut S, key_slot: Slot, target: &[u8]) -> (r: Result<Ordering>)
    ensures
        final(s).file() == old(s).file(),
{
    match key_slot.tag {
        Tag::ShortBytes => {
            let (buf, len) = short_bytes_value(key_slot);
            Ok(lex_cmp(slice_subrange(buf.as_slice(), 0, len), target))
        },
        Tag::Bytes => {
            let mut lbuf = [0u8; 8];
            s.read_at(key_slot.value, &mut lbuf)?;
            let len = read_i64(&lbuf);
            let start = match key_slot.value.checked_add(8) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let len = checked_len(s, start, len)?;
            let mut key = zero_vec(len);
            s.read_at(start, key.as_mut_slice())?;
            Ok(lex_cmp(key.as_slice(), target))
        },
        _ => Err(Error::UnexpectedTag),
    }
}

pub fn compare_entry_key<S: Store>(s: &mut S, entry: Slot, target: &[u8], hash_size: usize) -> (r: Result<Ordering>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
{
    let kv = read_kv_pair(s, entry, hash_size)?;
    compare_key(s, kv.key_slot, target)
}

/// `child_for_key`: the child of a branch whose subtree holds `key`, and
/// the number of entries before it.
pub fn child_for_key<S: Store>(s: &mut S, node: &SortedNode, key: &[u8]) -> (r: Result<(usize, i64)>)
    requires
        node.num <= BTREE_SLOT_COUNT,
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().0 < node.num || (node.num == 0 && r.unwrap().0 == 0),
{
    let mut i: usize = 0;
    let mut before = 0i64;
    while i + 1 < node.num
        invariant
            i < node.num || (node.num == 0 && i == 0),
            node.num <= BTREE_SLOT_COUNT,
            s.file() == old(s).file(),
        decreases node.num - i,
    {
        let c = compare_key(s, node.separators[i + 1], key)?;
        if is_greater(c) {
            break;
        }
        before = before.wrapping_add(node.counts[i]);
        i += 1;
    }
    Ok((i, before))
}

/// `child_for_rank`: the child holding `rank`, and the rank within it.
pub fn child_for_rank(node: &SortedNode, rank: i64) -> (r: (usize, i64))
    requires
        node.num <= BTREE_SLOT_COUNT,
        forall|j: int| 0 <= j < BTREE_SLOT_COUNT ==> #[trigger] node.counts[j] >= 0,
    ensures
        r.0 < node.num || (node.num == 0 && r.0 == 0),
{
    let mut i: usize = 0;
    let mut rem = rank;
    while i + 1 < node.num && rem >= node.counts[i]
        invariant
            i < node.num || (node.num == 0 && i == 0),
            node.num <= BTREE_SLOT_COUNT,
            forall|j: int| 0 <= j < BTREE_SLOT_COUNT ==> #[trigger] node.counts[j] >= 0,
        decreases node.num - i,
    {
        rem -= node.counts[i];
        i += 1;
    }
    (i, rem)
}

fn entry_position(node_ptr: i64, i: usize) -> (r: Result<i64>)
    requires
        i <= BTREE_SLOT_COUNT,
    ensures
        r is Ok ==> r.unwrap() == node_ptr + 2 + 9 * i,
{
    match node_ptr.checked_add((BTREE_NODE_HEADER_SIZE + i * SLOT_LENGTH) as i64) {
        Some(p) => Ok(p),
        None => Err(Error::InvalidOffset),
    }
}

/// `sorted_get`: the entry with `key`, if any.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_get<S: Store>(s: &mut S, root_ptr: i64, key: &[u8], hash_size: usize) -> (r: Result<Option<SortedSlot>>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
{
    let mut node_ptr = root_ptr;
    loop
        invariant
            s.file() == old(s).file(),
            hash_size <= 0xffff,
    {
        let node = read_sorted_node(s, node_ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let mut i: usize = 0;
            while i < node.num
                invariant
                    i <= node.num <= BTREE_SLOT_COUNT,
                    s.file() == old(s).file(),
                    hash_size <= 0xffff,
                decreases node.num - i,
            {
                let entry = node.entries[i];
                let c = compare_entry_key(s, entry, key, hash_size)?;
                match c {
                    Ordering::Equal => {
                        let position = entry_position(node_ptr, i)?;
                        return Ok(Some(SortedSlot { slot: entry, position }));
                    },
                    Ordering::Greater => return Ok(None),
                    Ordering::Less => {},
                }
                i += 1;
            }
            return Ok(None);
        }
        let (i, _) = child_for_key(s, &node, key)?;
        node_ptr = node.children[i].value;
    }
}

/// `sorted_get_by_index`: the entry at `rank`.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_get_by_index<S: Store>(s: &mut S, root_ptr: i64, rank: i64) -> (r: Result<SortedSlot>)
    ensures
        final(s).file() == old(s).file(),
{
    let mut node_ptr = root_ptr;
    let mut rem = rank;
    loop
        invariant
            s.file() == old(s).file(),
    {
        let node = read_sorted_node(s, node_ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let i = check_rank(rem, node.num, false)?;
            let position = entry_position(node_ptr, i)?;
            return Ok(SortedSlot { slot: node.entries[i], position });
        }
        let (i, next_rem) = child_for_rank(&node, rem);
        rem = next_rem;
        node_ptr = node.children[i].value;
    }
}

/// `sorted_rank`: the number of keys below `key`.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_rank<S: Store>(s: &mut S, root_ptr: i64, key: &[u8], hash_size: usize) -> (r: Result<i64>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
{
    let mut node_ptr = root_ptr;
    let mut rank: i64 = 0;
    loop
        invariant
            s.file() == old(s).file(),
            hash_size <= 0xffff,
    {
        let node = read_sorted_node(s, node_ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let mut i: usize = 0;
            while i < node.num
                invariant
                    i <= node.num <= BTREE_SLOT_COUNT,
                    s.file() == old(s).file(),
                    hash_size <= 0xffff,
                decreases node.num - i,
            {
                let c = compare_entry_key(s, node.entries[i], key, hash_size)?;
                if !is_less(c) {
                    break;
                }
                rank = match rank.checked_add(1) {
                    Some(r) => r,
                    None => return Err(Error::InvalidBTreeNode),
                };
                i += 1;
            }
            return Ok(rank);
        }
        let (i, before) = child_for_key(s, &node, key)?;
        rank = match rank.checked_add(before) {
            Some(r) => r,
            None => return Err(Error::InvalidBTreeNode),
        };
        node_ptr = node.children[i].value;
    }
}

/// `sorted_path_from_key`: the path to the first entry with a key at
/// least `key`, and the number of entries before it.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_path_from_key<S: Store>(s: &mut S, root_ptr: i64, key: &[u8], hash_size: usize) -> (r: Result<(NodePath, i64)>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
{
    let mut stack: NodePath = Vec::new();
    let mut node_ptr = root_ptr;
    let mut before: i64 = 0;
    loop
        invariant
            s.file() == old(s).file(),
            hash_size <= 0xffff,
    {
        let node = read_sorted_node(s, node_ptr)?;
        let position = match node_ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let mut li = node.num;
            let mut j: usize = 0;
            while j < node.num
                invariant
                    j <= node.num <= BTREE_SLOT_COUNT,
                    li <= node.num,
                    s.file() == old(s).file(),
                    hash_size <= 0xffff,
                decreases node.num - j,
            {
                let c = compare_entry_key(s, node.entries[j], key, hash_size)?;
                if !is_less(c) {
                    li = j;
                    break;
                }
                j += 1;
            }
            before = match before.checked_add(li as i64) {
                Some(b) => b,
                None => return Err(Error::InvalidBTreeNode),
            };
            stack.push((position, node.entries, li));
            return Ok((stack, before));
        }
        let (i, child_before) = child_for_key(s, &node, key)?;
        before = match before.checked_add(child_before) {
            Some(b) => b,
            None => return Err(Error::InvalidBTreeNode),
        };
        stack.push((position, node.children, i));
        node_ptr = node.children[i].value;
    }
}

/// `sorted_path_from_index`: the path to the entry at `rank`.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_path_from_index<S: Store>(s: &mut S, root_ptr: i64, rank: i64) -> (r: Result<NodePath>)
    ensures
        final(s).file() == old(s).file(),
{
    let mut stack: NodePath = Vec::new();
    let mut node_ptr = root_ptr;
    let mut rem = rank;
    loop
        invariant
            s.file() == old(s).file(),
    {
        let node = read_sorted_node(s, node_ptr)?;
        let position = match node_ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let i = check_rank(rem, node.num, false)?;
            stack.push((position, node.entries, i));
            return Ok(stack);
        }
        let (i, next_rem) = child_for_rank(&node, rem);
        rem = next_rem;
        stack.push((position, node.children, i));
        node_ptr = node.children[i].value;
    }
}

/// `write_key`: a short key inline, or a longer one appended.
pub fn write_key<S: Store>(s: &mut S, key: &[u8]) -> (r: Result<Slot>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    let mut short = key.len() <= 8;
    let mut j: usize = 0;
    while short && j < key.len()
        invariant
            j <= key@.len(),
            short ==> key@.len() <= 8,
        decreases key.len() - j,
    {
        if key[j] == 0 {
            short = false;
        }
        j += 1;
    }
    if short {
        let mut value = [0u8; 8];
        let mut k: usize = 0;
        while k < key.len()
            invariant
                k <= key@.len() <= 8,
            decreases key.len() - k,
        {
            value[k] = key[k];
            k += 1;
        }
        proof {
            lemma_grows_refl(s.file());
        }
        return Ok(Slot::new(crate::bytes::u64_from_be_bytes(value.as_slice()) as i64, Tag::ShortBytes));
    }
    if key.len() as u64 > i64::MAX as u64 {
        return Err(Error::StreamTooLong);
    }
    let mut buf = Vec::new();
    let len = crate::bytes::u64_to_be_bytes(key.len() as u64);
    let mut k: usize = 0;
    while k < 8
        invariant
            k <= 8,
        decreases 8 - k,
    {
        buf.push(len[k]);
        k += 1;
    }
    let mut k: usize = 0;
    while k < key.len()
        invariant
            k <= key@.len(),
        decreases key.len() - k,
    {
        buf.push(key[k]);
        k += 1;
    }
    let pos = append(s, buf.as_slice())?;
    proof {
        assert(s.file().subrange(0, old(s).file().len() as int) =~= old(s).file());
    }
    Ok(Slot::new(pos, Tag::Bytes))
}

/// `sorted_new_entry`: a new entry for `key` with an empty value.
pub fn sorted_new_entry<S: Store>(s: &mut S, key: &[u8]) -> (r: Result<Slot>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
        r is Ok ==> r.unwrap().value >= old(s).file().len(),
{
    let key_slot = write_key(s, key)?;
    let ghost f1 = s.file();
    let kv = KeyValuePair { value_slot: Slot::new(0, Tag::None), key_slot, hash: Vec::new() };
    let r = write_kv_pair(s, Tag::SortedKvPair, &kv)?;
    proof {
        lemma_grows_trans(old(s).file(), f1, s.file());
    }
    Ok(r)
}

fn entries_vec(a: &[Slot; BTREE_SLOT_COUNT], n: usize) -> (r: Vec<Slot>)
    requires
        n <= BTREE_SLOT_COUNT,
    ensures
        r@.len() == n,
{
    let mut r = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n <= BTREE_SLOT_COUNT,
            r@.len() == j,
        decreases n - j,
    {
        r.push(a[j]);
        j += 1;
    }
    r
}

fn counts_vec(a: &[i64; BTREE_SLOT_COUNT], n: usize) -> (r: Vec<i64>)
    requires
        n <= BTREE_SLOT_COUNT,
    ensures
        r@.len() == n,
{
    let mut r = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n <= BTREE_SLOT_COUNT,
            r@.len() == j,
        decreases n - j,
    {
        r.push(a[j]);
        j += 1;
    }
    r
}

/// `sorted_put`: inserts `key` (or finds it) under the node at
/// `node_ptr`, copying committed nodes. The caller writes the value of the
/// returned entry.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_put<S: Store>(s: &mut S, node_ptr: i64, key: &[u8], limit: Option<i64>, hash_size: usize) -> (r: Result<SortedInsertResult>)
    requires
        hash_size <= 0xffff,
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        (r is Ok && limit is Some) ==> r.unwrap().kv_slot.value >= limit.unwrap() && r.unwrap().node_ptr >= limit.unwrap(),
{
    let node = read_sorted_node(s, node_ptr)?;
    let ghost f0 = s.file();
    match node.kind {
        BTreeNodeKind::Leaf => {
            let mut idx = node.num;
            let mut found = false;
            let mut i: usize = 0;
            while i < node.num
                invariant
                    i <= node.num <= BTREE_SLOT_COUNT,
                    idx <= node.num,
                    s.file() == f0,
                    hash_size <= 0xffff,
                decreases node.num - i,
            {
                let c = compare_entry_key(s, node.entries[i], key, hash_size)?;
                match c {
                    Ordering::Equal => {
                        idx = i;
                        found = true;
                        break;
                    },
                    Ordering::Greater => {
                        idx = i;
                        break;
                    },
                    Ordering::Less => {},
                }
                i += 1;
            }

            if found && idx < node.num {
                // replace: return a writable value slot, copying the entry if
                // it belongs to a past moment
                let mut leaf = node;
                let mut kv_slot = node.entries[idx];
                let reusable = match limit {
                    Some(l) => kv_slot.value >= l,
                    None => false,
                };
                let ghost f1 = s.file();
                if !reusable {
                    let kv = read_kv_pair(s, kv_slot, hash_size)?;
                    kv_slot = write_kv_pair(s, kv_slot.tag, &kv)?;
                    leaf.entries[idx] = kv_slot;
                    proof {
                        lemma_grows_tx(f1, s.file(), limit);
                    }
                } else {
                    proof {
                        lemma_grows_refl(f1);
                        lemma_grows_tx(f1, s.file(), limit);
                    }
                }
                let ghost f2 = s.file();
                let ptr = sorted_write_node(s, &leaf, node_ptr, limit)?;
                proof {
                    lemma_tx_trans(f1, f2, s.file(), limit);
                }
                return Ok(SortedInsertResult { node_ptr: ptr, count: node.num as i64, kv_slot, added: false, split: None });
            }

            // insert a new entry at idx
            let ghost f1 = s.file();
            let entry = sorted_new_entry(s, key)?;
            proof {
                lemma_grows_tx(f1, s.file(), limit);
            }
            let ghost f2 = s.file();
            let mut entries = entries_vec(&node.entries, node.num);
            entries.insert(idx, entry);
            let total = entries.len();

            if total <= BTREE_SLOT_COUNT {
                let ptr = sorted_write_node(s, &crate::sorted::leaf(entries.as_slice()), node_ptr, limit)?;
                proof {
                    lemma_tx_trans(f1, f2, s.file(), limit);
                }
                return Ok(SortedInsertResult { node_ptr: ptr, count: total as i64, kv_slot: entry, added: true, split: None });
            }

            // overflow: split into two leaves; the new sibling's separator is
            // the key of its first entry
            let left_n = BTREE_SPLIT_COUNT;
            let separator = read_kv_pair(s, entries[left_n], hash_size)?.key_slot;
            let left_ptr = sorted_write_node(s, &crate::sorted::leaf(slice_subrange(entries.as_slice(), 0, left_n)), node_ptr, limit)?;
            let ghost f3 = s.file();
            let right_ptr = write_sorted_node(s, &crate::sorted::leaf(slice_subrange(entries.as_slice(), left_n, total)))?;
            proof {
                lemma_tx_trans(f1, f2, f3, limit);
                lemma_grows_tx(f3, s.file(), limit);
                lemma_tx_trans(f1, f3, s.file(), limit);
            }
            Ok(SortedInsertResult {
                node_ptr: left_ptr,
                count: left_n as i64,
                kv_slot: entry,
                added: true,
                split: Some(SortedSplit { node_ptr: right_ptr, count: (total - left_n) as i64, separator }),
            })
        },
        BTreeNodeKind::Branch => {
            let (i, _) = child_for_key(s, &node, key)?;
            if node.num == 0 {
                return Err(Error::InvalidBTreeNode);
            }
            let child = sorted_put(s, node.children[i].value, key, limit, hash_size)?;
            let ghost f1 = s.file();

            let mut children = entries_vec(&node.children, node.num);
            let mut separators = entries_vec(&node.separators, node.num);
            let mut counts = counts_vec(&node.counts, node.num);
            children.set(i, Slot::new(child.node_ptr, Tag::Index));
            counts.set(i, child.count);
            if let Some(split) = child.split {
                children.insert(i + 1, Slot::new(split.node_ptr, Tag::Index));
                separators.insert(i + 1, split.separator);
                counts.insert(i + 1, split.count);
            }
            let total = children.len();

            if total <= BTREE_SLOT_COUNT {
                let node2 = crate::sorted::branch(children.as_slice(), separators.as_slice(), counts.as_slice());
                let ptr = sorted_write_node(s, &node2, node_ptr, limit)?;
                proof {
                    lemma_tx_trans(f0, f1, s.file(), limit);
                }
                return Ok(SortedInsertResult {
                    node_ptr: ptr,
                    count: node2.subtree_count(),
                    kv_slot: child.kv_slot,
                    added: child.added,
                    split: None,
                });
            }

            // overflow: split into two branches; the new sibling's separator
            // is the smallest key of its first child
            let left_n = BTREE_SPLIT_COUNT;
            let left = crate::sorted::branch(
                slice_subrange(children.as_slice(), 0, left_n),
                slice_subrange(separators.as_slice(), 0, left_n),
                slice_subrange(counts.as_slice(), 0, left_n),
            );
            let right = crate::sorted::branch(
                slice_subrange(children.as_slice(), left_n, total),
                slice_subrange(separators.as_slice(), left_n, total),
                slice_subrange(counts.as_slice(), left_n, total),
            );
            let separator = separators[left_n];
            let left_ptr = sorted_write_node(s, &left, node_ptr, limit)?;
            let ghost f2 = s.file();
            let right_ptr = write_sorted_node(s, &right)?;
            proof {
                lemma_tx_trans(f0, f1, f2, limit);
                lemma_grows_tx(f2, s.file(), limit);
                lemma_tx_trans(f0, f2, s.file(), limit);
            }
            Ok(SortedInsertResult {
                node_ptr: left_ptr,
                count: left.subtree_count(),
                kv_slot: child.kv_slot,
                added: child.added,
                split: Some(SortedSplit { node_ptr: right_ptr, count: right.subtree_count(), separator }),
            })
        },
    }
}

/// `sorted_remove`: removes `key` under the node at `node_ptr`, copying
/// committed nodes; an emptied leaf is left in place.
#[verifier::exec_allows_no_decreases_clause]
pub fn sorted_remove<S: Store>(s: &mut S, node_ptr: i64, key: &[u8], limit: Option<i64>, hash_size: usize) -> (r: Result<(i64, bool)>)
    requires
        hash_size <= 0xffff,
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
{
    let node = read_sorted_node(s, node_ptr)?;
    let ghost f0 = s.file();
    match node.kind {
        BTreeNodeKind::Leaf => {
            let mut idx: Option<usize> = None;
            let mut i: usize = 0;
            while i < node.num
                invariant
                    i <= node.num <= BTREE_SLOT_COUNT,
                    idx is Some ==> idx.unwrap() < node.num,
                    s.file() == f0,
                    hash_size <= 0xffff,
                decreases node.num - i,
            {
                let c = compare_entry_key(s, node.entries[i], key, hash_size)?;
                match c {
                    Ordering::Equal => {
                        idx = Some(i);
                        break;
                    },
                    Ordering::Greater => break,
                    Ordering::Less => {},
                }
                i += 1;
            }
            let idx = match idx {
                Some(i) => i,
                None => {
                    proof {
                        lemma_grows_refl(f0);
                        lemma_grows_tx(f0, s.file(), limit);
                    }
                    return Ok((node_ptr, false));
                },
            };
            let mut entries = entries_vec(&node.entries, node.num);
            entries.remove(idx);
            let ptr = sorted_write_node(s, &crate::sorted::leaf(entries.as_slice()), node_ptr, limit)?;
            Ok((ptr, true))
        },
        BTreeNodeKind::Branch => {
            let (i, _) = child_for_key(s, &node, key)?;
            if node.num == 0 {
                return Err(Error::InvalidBTreeNode);
            }
            let (child_ptr, found) = sorted_remove(s, node.children[i].value, key, limit, hash_size)?;
            if !found {
                return Ok((node_ptr, false));
            }
            let ghost f1 = s.file();
            let mut branch = node;
            branch.children[i] = Slot::new(child_ptr, Tag::Index);
            branch.counts[i] = match branch.counts[i].checked_sub(1) {
                Some(c) => c,
                None => return Err(Error::InvalidBTreeNode),
            };
            let ptr = sorted_write_node(s, &branch, node_ptr, limit)?;
            proof {
                lemma_tx_trans(f0, f1, s.file(), limit);
            }
            Ok((ptr, true))
        },
    }
}

/// `sorted_grow_root`: a root that split gets a new parent.
pub fn sorted_grow_root<S: Store>(s: &mut S, result: &SortedInsertResult) -> (r: Result<i64>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    match result.split {
        Some(split) => {
            let mut root = SortedNode::empty(BTreeNodeKind::Branch, 2);
            root.children[0] = Slot::new(result.node_ptr, Tag::Index);
            root.children[1] = Slot::new(split.node_ptr, Tag::Index);
            root.separators[1] = split.separator; // separators[0] is an unused sentinel
            root.counts[0] = result.count;
            root.counts[1] = split.count;
            write_sorted_node(s, &root)
        },
        None => {
            proof {
                lemma_grows_refl(s.file());
            }
            Ok(result.node_ptr)
        },
    }
}

/// `sorted_target_slot`: the slot the target asks for. Only the value is
/// writeable, at its position in the entry.
pub fn sorted_target_slot<S: Store>(s: &mut S, kv_slot: Slot, target: SortedTarget, hash_size: usize) -> (r: Result<SlotPointer>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
        (r is Ok && target == SortedTarget::Value) ==> r.unwrap().position is Some && r.unwrap().position.unwrap() >= kv_slot.value,
        (r is Ok && target != SortedTarget::Value) ==> r.unwrap().position is None,
{
    let kv = read_kv_pair(s, kv_slot, hash_size)?;
    Ok(match target {
        SortedTarget::KvPair => SlotPointer::new(None, kv_slot),
        SortedTarget::Key => SlotPointer::new(None, kv.key_slot),
        SortedTarget::Value => {
            let off = kv_key_offset(kv_slot.tag, hash_size);
            let pos = match kv_slot.value.checked_add(off) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let pos = match pos.checked_add(SLOT_LENGTH as i64) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            SlotPointer::new(Some(pos), kv.value_slot)
        },
    })
}

} // verus!
