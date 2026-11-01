//! The sorted map B+tree over a [`Store`] (`src/sorted.rs`'s database
//! methods), checked by Verus.
//!
//! Reads leave the file unchanged. Writes change nothing before `limit`
//! (where the transaction started): a node is written in place only from
//! `copy_at` on, which is at least `limit`, and appended otherwise, and the
//! entry `sorted_put` returns for its value to be written is at or after
//! `limit`. Every offset computation is checked, so corrupt pointers and
//! counts fail with an error instead of overflowing.

use std::cmp::Ordering;

#[allow(unused_imports)]
use crate::array_list_store::*;
#[allow(unused_imports)]
use crate::btree_io::*;
#[allow(unused_imports)]
use crate::btree_join::*;
#[allow(unused_imports)]
use crate::bytes::*;
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
/// Byte strings in lexicographic order, from index `i`.
pub open spec fn lex_spec(a: Seq<u8>, b: Seq<u8>, i: int) -> Ordering
    decreases a.len() - i,
{
    if 0 <= i && i < a.len() && i < b.len() {
        if a[i] < b[i] {
            Ordering::Less
        } else if a[i] > b[i] {
            Ordering::Greater
        } else {
            lex_spec(a, b, i + 1)
        }
    } else if a.len() < b.len() {
        Ordering::Less
    } else if a.len() > b.len() {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

fn lex_cmp(a: &[u8], b: &[u8]) -> (r: Ordering)
    ensures
        r == lex_spec(a@, b@, 0),
{
    let mut i: usize = 0;
    while i < a.len() && i < b.len()
        invariant
            i <= a@.len(),
            i <= b@.len(),
            lex_spec(a@, b@, i as int) == lex_spec(a@, b@, 0),
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
/// `n` is the sorted node encoded at `ptr`, as far as the descents read
/// it: the header, a leaf's entries, a branch's children, separators and
/// counts.
pub open spec fn snode_at(f: Seq<u8>, ptr: int, n: SortedNode) -> bool {
    &&& 0 <= ptr
    &&& ptr + BTREE_NODE_HEADER_SIZE <= f.len()
    &&& f[ptr] == kind_byte_spec(n.kind)
    &&& f[ptr + 1] == n.num
    &&& n.num <= BTREE_SLOT_COUNT
    &&& match n.kind {
        BTreeNodeKind::Leaf => forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] slot_at(f, ptr + 2 + 9 * i, n.entries[i]),
        BTreeNodeKind::Branch => {
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] slot_at(f, ptr + 2 + 9 * i, n.children[i])
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] slot_at(f, ptr + 146 + 9 * i, n.separators[i])
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] n.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 290 + 8 * i, ptr + 298 + 8 * i)))
            &&& ptr + 290 + 128 <= f.len()
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] n.counts[i] >= 0
        },
    }
}

/// The entry at `rank` under the node at `ptr`, descending at most
/// `depth` levels, over the bytes: the position of its slot and the slot.
pub open spec fn sorted_read(f: Seq<u8>, ptr: int, rank: int, depth: nat) -> Option<(int, Slot)>
    decreases depth,
{
    if depth == 0 {
        None
    } else if exists|n: SortedNode| snode_at(f, ptr, n) {
        let n = choose|n: SortedNode| snode_at(f, ptr, n);
        match n.kind {
            BTreeNodeKind::Leaf => if 0 <= rank < n.num {
                Some((ptr + 2 + 9 * rank, n.entries[rank]))
            } else {
                None
            },
            BTreeNodeKind::Branch => if n.num >= 1 {
                let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
                sorted_read(f, n.children[i].value as int, rem, (depth - 1) as nat)
            } else {
                None
            },
        }
    } else {
        None
    }
}

/// A node's encoding determines everything the descent reads.
pub proof fn lemma_snode_unique(f: Seq<u8>, ptr: int, a: SortedNode, b: SortedNode)
    requires
        snode_at(f, ptr, a),
        snode_at(f, ptr, b),
    ensures
        a.kind == b.kind,
        a.num == b.num,
        a.kind == BTreeNodeKind::Leaf ==> a.entries@ == b.entries@,
        a.kind == BTreeNodeKind::Branch ==> a.children@ == b.children@ && a.counts@ == b.counts@ && a.separators@ == b.separators@,
{
    match (a.kind, b.kind) {
        (BTreeNodeKind::Leaf, BTreeNodeKind::Leaf) => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.entries@[i] == b.entries@[i] by {
                assert(slot_at(f, ptr + 2 + 9 * i, a.entries[i]));
                assert(slot_at(f, ptr + 2 + 9 * i, b.entries[i]));
                lemma_slot_encode_injective(a.entries[i], b.entries[i]);
            }
            assert(a.entries@ =~= b.entries@);
        },
        (BTreeNodeKind::Branch, BTreeNodeKind::Branch) => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.children@[i] == b.children@[i] by {
                assert(slot_at(f, ptr + 2 + 9 * i, a.children[i]));
                assert(slot_at(f, ptr + 2 + 9 * i, b.children[i]));
                lemma_slot_encode_injective(a.children[i], b.children[i]);
            }
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.counts@[i] == b.counts@[i] by {
                assert(a.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 290 + 8 * i, ptr + 298 + 8 * i))));
                assert(b.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 290 + 8 * i, ptr + 298 + 8 * i))));
            }
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.separators@[i] == b.separators@[i] by {
                assert(slot_at(f, ptr + 146 + 9 * i, a.separators[i]));
                assert(slot_at(f, ptr + 146 + 9 * i, b.separators[i]));
                lemma_slot_encode_injective(a.separators[i], b.separators[i]);
            }
            assert(a.children@ =~= b.children@);
            assert(a.counts@ =~= b.counts@);
            assert(a.separators@ =~= b.separators@);
        },
        _ => {},
    }
}

/// One level of the descent, for the node the code read.
proof fn lemma_sorted_read_step(f: Seq<u8>, ptr: int, rank: int, depth: nat, n: SortedNode)
    requires
        snode_at(f, ptr, n),
        depth >= 1,
    ensures
        n.kind == BTreeNodeKind::Leaf ==> sorted_read(f, ptr, rank, depth) == if 0 <= rank < n.num {
            Some((ptr + 2 + 9 * rank, n.entries[rank]))
        } else {
            None
        },
        (n.kind == BTreeNodeKind::Branch && n.num >= 1) ==> sorted_read(f, ptr, rank, depth) == {
            let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
            sorted_read(f, n.children[i].value as int, rem, (depth - 1) as nat)
        },
{
    let c = choose|m: SortedNode| snode_at(f, ptr, m);
    lemma_snode_unique(f, ptr, n, c);
    if n.kind == BTreeNodeKind::Leaf && 0 <= rank < n.num {
        assert(c.entries@[rank] == n.entries@[rank]);
    }
    if n.kind == BTreeNodeKind::Branch && n.num >= 1 {
        let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
        assert(crate::btree::cfr(c.counts@, c.num as int, 0, rank, false) == (i, rem));
        crate::btree::lemma_cfr_range(n.counts@, n.num as int, 0, rank, false);
        assert(c.children@[i] == n.children@[i]);
    }
}

/// The bytes of a key stored in `slot`: inline, or a byte array.
pub open spec fn stored_key(f: Seq<u8>, slot: Slot) -> Option<Seq<u8>> {
    if slot.tag == Tag::ShortBytes {
        Some(crate::sorted::short_key(slot))
    } else if slot.tag == Tag::Bytes {
        let v = slot.value as int;
        let len = u2i(be_u64_spec(f.subrange(v, v + 8)));
        if 0 <= v && v + 8 <= f.len() && 0 <= len && v + 8 + len <= f.len() {
            Some(f.subrange(v + 8, v + 8 + len))
        } else {
            None
        }
    } else {
        None
    }
}

/// Where an entry's key slot is: after the hash in a hash map pair, first
/// in a sorted map pair.
pub open spec fn entry_key_pos(entry: Slot, hash_size: int) -> int {
    entry.value as int + if entry.tag == Tag::KvPair { hash_size } else { 0 }
}

/// The key of the entry `entry` points at.
pub open spec fn entry_key(f: Seq<u8>, entry: Slot, hash_size: int) -> Option<Seq<u8>> {
    if entry.tag == Tag::KvPair || entry.tag == Tag::SortedKvPair {
        match slot_spec(f, entry_key_pos(entry, hash_size)) {
            Some(ks) => stored_key(f, ks),
            None => None,
        }
    } else {
        None
    }
}

/// The child of a branch that `key` belongs under: the last one whose
/// separator is at most `key`, from `i` on.
pub open spec fn ck_index(f: Seq<u8>, n: SortedNode, i: int, key: Seq<u8>) -> Option<int>
    decreases n.num - i,
{
    if 0 <= i && i + 1 < n.num {
        match stored_key(f, n.separators[i + 1]) {
            Some(k) => if lex_spec(k, key, 0) == Ordering::Greater {
                Some(i)
            } else {
                ck_index(f, n, i + 1, key)
            },
            None => None,
        }
    } else {
        Some(i)
    }
}

/// A leaf's entry for `key`, scanning from `i`: `Some(None)` if it isn't
/// there, `None` if a key can't be read.
pub open spec fn leaf_find(f: Seq<u8>, n: SortedNode, ptr: int, i: int, key: Seq<u8>, hash_size: int) -> Option<Option<(int, Slot)>>
    decreases n.num - i,
{
    if 0 <= i < n.num {
        match entry_key(f, n.entries[i], hash_size) {
            Some(k) => {
                let c = lex_spec(k, key, 0);
                if c == Ordering::Equal {
                    Some(Some((ptr + 2 + 9 * i, n.entries[i])))
                } else if c == Ordering::Greater {
                    Some(None)
                } else {
                    leaf_find(f, n, ptr, i + 1, key, hash_size)
                }
            },
            None => None,
        }
    } else {
        Some(None)
    }
}

/// The entry for `key` under the node at `ptr`, descending at most
/// `depth` levels, over the bytes.
pub open spec fn sorted_find(f: Seq<u8>, ptr: int, key: Seq<u8>, hash_size: int, depth: nat) -> Option<Option<(int, Slot)>>
    decreases depth,
{
    if depth == 0 {
        None
    } else if exists|n: SortedNode| snode_at(f, ptr, n) {
        let n = choose|n: SortedNode| snode_at(f, ptr, n);
        match n.kind {
            BTreeNodeKind::Leaf => leaf_find(f, n, ptr, 0, key, hash_size),
            BTreeNodeKind::Branch => if n.num >= 1 {
                match ck_index(f, n, 0, key) {
                    Some(i) => sorted_find(f, n.children[i].value as int, key, hash_size, (depth - 1) as nat),
                    None => None,
                }
            } else {
                None
            },
        }
    } else {
        None
    }
}

pub proof fn lemma_ck_index_ext(f: Seq<u8>, a: SortedNode, b: SortedNode, i: int, key: Seq<u8>)
    requires
        a.num == b.num,
        a.num <= BTREE_SLOT_COUNT,
        a.separators@ == b.separators@,
    ensures
        ck_index(f, a, i, key) == ck_index(f, b, i, key),
    decreases a.num - i,
{
    if 0 <= i && i + 1 < a.num {
        assert(a.separators[i + 1] == a.separators@[i + 1]);
        assert(b.separators[i + 1] == b.separators@[i + 1]);
        lemma_ck_index_ext(f, a, b, i + 1, key);
    }
}

pub proof fn lemma_leaf_find_ext(f: Seq<u8>, a: SortedNode, b: SortedNode, ptr: int, i: int, key: Seq<u8>, hash_size: int)
    requires
        a.num == b.num,
        a.num <= BTREE_SLOT_COUNT,
        a.entries@ == b.entries@,
    ensures
        leaf_find(f, a, ptr, i, key, hash_size) == leaf_find(f, b, ptr, i, key, hash_size),
    decreases a.num - i,
{
    if 0 <= i < a.num {
        assert(a.entries[i] == a.entries@[i]);
        assert(b.entries[i] == b.entries@[i]);
        lemma_leaf_find_ext(f, a, b, ptr, i + 1, key, hash_size);
    }
}

/// One level of the descent by key, for the node the code read.
proof fn lemma_sorted_find_step(f: Seq<u8>, ptr: int, key: Seq<u8>, hash_size: int, depth: nat, n: SortedNode)
    requires
        snode_at(f, ptr, n),
        depth >= 1,
    ensures
        n.kind == BTreeNodeKind::Leaf ==> sorted_find(f, ptr, key, hash_size, depth) == leaf_find(f, n, ptr, 0, key, hash_size),
        (n.kind == BTreeNodeKind::Branch && n.num >= 1) ==> sorted_find(f, ptr, key, hash_size, depth) == match ck_index(f, n, 0, key) {
            Some(i) => sorted_find(f, n.children[i].value as int, key, hash_size, (depth - 1) as nat),
            None => None,
        },
{
    let c = choose|m: SortedNode| snode_at(f, ptr, m);
    lemma_snode_unique(f, ptr, n, c);
    if n.kind == BTreeNodeKind::Leaf {
        lemma_leaf_find_ext(f, n, c, ptr, 0, key, hash_size);
    }
    if n.kind == BTreeNodeKind::Branch && n.num >= 1 {
        lemma_ck_index_ext(f, n, c, 0, key);
        if let Some(i) = ck_index(f, n, 0, key) {
            lemma_ck_index_range(f, n, 0, key);
            assert(c.children@[i] == n.children@[i]);
        }
    }
}

proof fn lemma_ck_index_range(f: Seq<u8>, n: SortedNode, i: int, key: Seq<u8>)
    requires
        0 <= i < n.num,
    ensures
        ck_index(f, n, i, key) matches Some(j) ==> i <= j < n.num,
    decreases n.num - i,
{
    if i + 1 < n.num {
        lemma_ck_index_range(f, n, i + 1, key);
    }
}

pub fn read_sorted_node<S: Store>(s: &mut S, ptr: i64) -> (r: Result<SortedNode>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().num <= BTREE_SLOT_COUNT,
        r is Ok ==> forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] r.unwrap().counts[i] >= 0,
        r is Ok ==> snode_at(old(s).file(), ptr as int, r.unwrap()),
{
    let mut header = [0u8; BTREE_NODE_HEADER_SIZE];
    s.read_at(ptr, &mut header)?;
    let (kind, num) = decode_node_header(&header)?;
    let mut node = SortedNode::empty(kind, num);
    let body_pos = match ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let ghost f = s.file();
    match kind {
        BTreeNodeKind::Leaf => {
            let mut body = [0u8; SLOT_LENGTH * BTREE_SLOT_COUNT];
            s.read_at(body_pos, &mut body)?;
            node.entries = decode_slots(&body)?;
            proof {
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(f, ptr + 2 + 9 * i, node.entries[i]) by {
                    assert(f.subrange(ptr + 2 + 9 * i, ptr + 2 + 9 * i + 9) =~= body@.subrange(i * 9, i * 9 + 9));
                }
            }
        },
        BTreeNodeKind::Branch => {
            let mut body = [0u8; (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT];
            s.read_at(body_pos, &mut body)?;
            let separators_offset = SLOT_LENGTH * BTREE_SLOT_COUNT;
            let counts_offset = SLOT_LENGTH * 2 * BTREE_SLOT_COUNT;
            node.children = decode_slots(&body)?;
            node.separators = decode_slots(slice_subrange(body.as_slice(), separators_offset, counts_offset))?;
            node.counts = decode_counts(slice_subrange(body.as_slice(), counts_offset, (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT))?;
            proof {
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(f, ptr + 2 + 9 * i, node.children[i]) by {
                    assert(f.subrange(ptr + 2 + 9 * i, ptr + 2 + 9 * i + 9) =~= body@.subrange(i * 9, i * 9 + 9));
                }
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(f, ptr + 146 + 9 * i, node.separators[i]) by {
                    assert(f.subrange(ptr + 146 + 9 * i, ptr + 146 + 9 * i + 9) =~= body@.subrange(144, 288).subrange(i * 9, i * 9 + 9));
                }
                let cb = body@.subrange(288, 416);
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] node.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 290 + 8 * i, ptr + 298 + 8 * i))) by {
                    assert(f.subrange(ptr + 290 + 8 * i, ptr + 298 + 8 * i) =~= cb.subrange(i * 8, i * 8 + 8));
                }
            }
        },
    }
    proof {
        assert(header@[0] == f[ptr as int] && header@[1] == f[ptr + 1]);
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
pub fn sorted_write_node<S: Store>(s: &mut S, node: &SortedNode, old_ptr: i64, limit: Option<i64>, copy_at: i64) -> (r: Result<i64>)
    requires
        limit is Some ==> limit.unwrap() <= copy_at,
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        (r is Ok && limit is Some) ==> r.unwrap() >= limit.unwrap(),
{
    let reusable = match limit {
        Some(_) => old_ptr >= copy_at,
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
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> (kv_slot.tag == Tag::KvPair || kv_slot.tag == Tag::SortedKvPair)
            && slot_at(old(s).file(), entry_key_pos(kv_slot, hash_size as int), r.unwrap().key_slot),
{
    if hash_size > 0xffff {
        return Err(Error::InvalidHashSize);
    }
    let len = KeyValuePair::encoded_len(kv_slot.tag, hash_size)?;
    let mut buf = zero_vec(len);
    let ghost f = s.file();
    s.read_at(kv_slot.value, buf.as_mut_slice())?;
    let r = KeyValuePair::decode(buf.as_slice(), kv_slot.tag, hash_size);
    proof {
        if let Ok(kv) = &r {
            let v = kv_slot.value as int;
            if kv_slot.tag == Tag::KvPair {
                let h = hash_size as int;
                assert(kv_encode_spec(*kv).subrange(h, h + 9) =~= slot_encode_spec(kv.key_slot));
                assert(buf@.subrange(h, h + 9) =~= buf@.subrange(0, h + 18).subrange(h, h + 9));
                assert(f.subrange(v + h, v + h + 9) =~= buf@.subrange(h, h + 9));
            } else {
                assert(sorted_kv_encode_spec(*kv).subrange(0, 9) =~= slot_encode_spec(kv.key_slot));
                assert(buf@.subrange(0, 9) =~= buf@.subrange(0, 18).subrange(0, 9));
                assert(f.subrange(v, v + 9) =~= buf@.subrange(0, 9));
            }
        }
    }
    r
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
pub fn kv_key_offset(tag: Tag, hash_size: u16) -> (r: i64)
    ensures
        0 <= r <= 0xffff,
        r == (if tag == Tag::KvPair { hash_size as int } else { 0 }),
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
        r is Ok ==> (stored_key(old(s).file(), key_slot) matches Some(k) && r.unwrap() == lex_spec(k, target@, 0)),
{
    match key_slot.tag {
        Tag::ShortBytes => {
            let (buf, len) = short_bytes_value(key_slot);
            Ok(lex_cmp(slice_subrange(buf.as_slice(), 0, len), target))
        },
        Tag::Bytes => {
            let ghost f = s.file();
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
            proof {
                let v = key_slot.value as int;
                assert(lbuf@.subrange(0, 8) =~= f.subrange(v, v + 8));
                assert(key@ =~= f.subrange(v + 8, v + 8 + len));
            }
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
        r is Ok ==> (entry_key(old(s).file(), entry, hash_size as int) matches Some(k) && r.unwrap() == lex_spec(k, target@, 0)),
{
    let kv = read_kv_pair(s, entry, hash_size)?;
    proof {
        lemma_slot_spec(s.file(), entry_key_pos(entry, hash_size as int), kv.key_slot);
    }
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
        r is Ok ==> ck_index(old(s).file(), *node, 0, key@) == Some(r.unwrap().0 as int),
{
    let mut i: usize = 0;
    let mut before = 0i64;
    while i + 1 < node.num
        invariant
            i < node.num || (node.num == 0 && i == 0),
            node.num <= BTREE_SLOT_COUNT,
            s.file() == old(s).file(),
            ck_index(old(s).file(), *node, i as int, key@) == ck_index(old(s).file(), *node, 0, key@),
        ensures
            ck_index(old(s).file(), *node, 0, key@) == Some(i as int),
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
        node.num >= 1 ==> (r.0 as int, r.1 as int) == crate::btree::cfr(node.counts@, node.num as int, 0, rank as int, false),
{
    let mut i: usize = 0;
    let mut rem = rank;
    while i + 1 < node.num && rem >= node.counts[i]
        invariant
            i < node.num || (node.num == 0 && i == 0),
            node.num <= BTREE_SLOT_COUNT,
            forall|j: int| 0 <= j < BTREE_SLOT_COUNT ==> #[trigger] node.counts[j] >= 0,
            node.num >= 1 ==> crate::btree::cfr(node.counts@, node.num as int, i as int, rem as int, false)
                == crate::btree::cfr(node.counts@, node.num as int, 0, rank as int, false),
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
pub fn sorted_get<S: Store>(s: &mut S, root_ptr: i64, key: &[u8], hash_size: usize) -> (r: Result<Option<SortedSlot>>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> exists|d: nat| #[trigger] sorted_find(old(s).file(), root_ptr as int, key@, hash_size as int, d) == Some(
            match r.unwrap() {
                Some(ss) => Some((ss.position as int, ss.slot)),
                None => None,
            },
        ),
{
    if hash_size > 0xffff {
        return Err(Error::InvalidHashSize);
    }
    let mut node_ptr = root_ptr;
    let mut fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f = s.file();
    let ghost h = hash_size as int;
    let ghost mut k: nat = 0;
    loop
        invariant
            s.file() == f,
            f == old(s).file(),
            hash_size <= 0xffff,
            h == hash_size as int,
            forall|d: nat| #[trigger] sorted_find(f, node_ptr as int, key@, h, d) is Some ==> sorted_find(f, root_ptr as int, key@, h, d + k)
                == sorted_find(f, node_ptr as int, key@, h, d),
        decreases fuel,
    {
        if fuel == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        fuel = fuel - 1;
        let node = read_sorted_node(s, node_ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            proof {
                lemma_sorted_find_step(f, node_ptr as int, key@, h, 1, node);
            }
            let mut i: usize = 0;
            while i < node.num
                invariant
                    i <= node.num <= BTREE_SLOT_COUNT,
                    s.file() == f,
                    f == old(s).file(),
                    hash_size <= 0xffff,
                    h == hash_size as int,
                    leaf_find(f, node, node_ptr as int, i as int, key@, h) == leaf_find(f, node, node_ptr as int, 0, key@, h),
                    sorted_find(f, node_ptr as int, key@, h, 1) == leaf_find(f, node, node_ptr as int, 0, key@, h),
                    forall|d: nat| #[trigger] sorted_find(f, node_ptr as int, key@, h, d) is Some ==> sorted_find(f, root_ptr as int, key@, h, d + k)
                        == sorted_find(f, node_ptr as int, key@, h, d),
                decreases node.num - i,
            {
                let entry = node.entries[i];
                let c = compare_entry_key(s, entry, key, hash_size)?;
                match c {
                    Ordering::Equal => {
                        let position = entry_position(node_ptr, i)?;
                        proof {
                            assert(sorted_find(f, root_ptr as int, key@, h, 1 + k) == Some(Some((position as int, entry))));
                        }
                        return Ok(Some(SortedSlot { slot: entry, position }));
                    },
                    Ordering::Greater => {
                        proof {
                            assert(sorted_find(f, root_ptr as int, key@, h, 1 + k) == Some(None::<(int, Slot)>));
                        }
                        return Ok(None);
                    },
                    Ordering::Less => {},
                }
                i += 1;
            }
            proof {
                assert(sorted_find(f, root_ptr as int, key@, h, 1 + k) == Some(None::<(int, Slot)>));
            }
            return Ok(None);
        }
        // a branch without children is corrupt
        if node.num == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        let (i, _) = child_for_key(s, &node, key)?;
        let ghost old_ptr = node_ptr;
        node_ptr = node.children[i].value;
        proof {
            assert forall|d: nat| #[trigger] sorted_find(f, node_ptr as int, key@, h, d) is Some implies sorted_find(f, root_ptr as int, key@, h, d + k + 1)
                == sorted_find(f, node_ptr as int, key@, h, d) by {
                lemma_sorted_find_step(f, old_ptr as int, key@, h, d + 1, node);
                assert(((d + 1) - 1) as nat == d);
            }
            k = k + 1;
        }
    }
}

/// `sorted_get_by_index`: the entry at `rank`.
pub fn sorted_get_by_index<S: Store>(s: &mut S, root_ptr: i64, rank: i64) -> (r: Result<SortedSlot>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> exists|d: nat| #[trigger] sorted_read(old(s).file(), root_ptr as int, rank as int, d)
            == Some((r.unwrap().position as int, r.unwrap().slot)),
{
    let mut node_ptr = root_ptr;
    let mut rem = rank;
    let mut fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f = s.file();
    let ghost mut k: nat = 0;
    loop
        invariant
            s.file() == f,
            f == old(s).file(),
            forall|d: nat| #[trigger] sorted_read(f, node_ptr as int, rem as int, d) is Some ==> sorted_read(f, root_ptr as int, rank as int, d + k)
                == sorted_read(f, node_ptr as int, rem as int, d),
        decreases fuel,
    {
        if fuel == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        fuel = fuel - 1;
        let node = read_sorted_node(s, node_ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let i = check_rank(rem, node.num, false)?;
            let position = entry_position(node_ptr, i)?;
            proof {
                lemma_sorted_read_step(f, node_ptr as int, rem as int, 1, node);
                assert(sorted_read(f, root_ptr as int, rank as int, 1 + k) == Some((position as int, node.entries[i as int])));
            }
            return Ok(SortedSlot { slot: node.entries[i], position });
        }
        // a branch without children is corrupt
        if node.num == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        let (i, next_rem) = child_for_rank(&node, rem);
        let ghost old_ptr = node_ptr;
        let ghost old_rem = rem;
        rem = next_rem;
        node_ptr = node.children[i].value;
        proof {
            assert forall|d: nat| #[trigger] sorted_read(f, node_ptr as int, rem as int, d) is Some implies sorted_read(f, root_ptr as int, rank as int, d + k + 1)
                == sorted_read(f, node_ptr as int, rem as int, d) by {
                lemma_sorted_read_step(f, old_ptr as int, old_rem as int, d + 1, node);
                assert(((d + 1) - 1) as nat == d);
            }
            k = k + 1;
        }
    }
}

/// `sorted_rank`: the number of keys below `key`.
pub fn sorted_rank<S: Store>(s: &mut S, root_ptr: i64, key: &[u8], hash_size: usize) -> (r: Result<i64>)
    ensures
        final(s).file() == old(s).file(),
{
    if hash_size > 0xffff {
        return Err(Error::InvalidHashSize);
    }
    let mut node_ptr = root_ptr;
    let mut rank: i64 = 0;
    let mut fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    loop
        invariant
            s.file() == old(s).file(),
            hash_size <= 0xffff,
        decreases fuel,
    {
        if fuel == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        fuel = fuel - 1;
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
pub fn sorted_path_from_key<S: Store>(s: &mut S, root_ptr: i64, key: &[u8], hash_size: usize) -> (r: Result<(NodePath, i64)>)
    ensures
        final(s).file() == old(s).file(),
{
    if hash_size > 0xffff {
        return Err(Error::InvalidHashSize);
    }
    let mut stack: NodePath = Vec::new();
    let mut node_ptr = root_ptr;
    let mut before: i64 = 0;
    let mut fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    loop
        invariant
            s.file() == old(s).file(),
            hash_size <= 0xffff,
        decreases fuel,
    {
        if fuel == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        fuel = fuel - 1;
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
pub fn sorted_path_from_index<S: Store>(s: &mut S, root_ptr: i64, rank: i64) -> (r: Result<NodePath>)
    ensures
        final(s).file() == old(s).file(),
{
    let mut stack: NodePath = Vec::new();
    let mut node_ptr = root_ptr;
    let mut rem = rank;
    let mut fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    loop
        invariant
            s.file() == old(s).file(),
        decreases fuel,
    {
        if fuel == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        fuel = fuel - 1;
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
pub fn sorted_put<S: Store>(s: &mut S, node_ptr: i64, key: &[u8], limit: Option<i64>, copy_at: i64, hash_size: usize, fuel: u64) -> (r: Result<SortedInsertResult>)
    requires
        limit is Some ==> limit.unwrap() <= copy_at,
        hash_size <= 0xffff,
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        (r is Ok && limit is Some) ==> r.unwrap().kv_slot.value >= limit.unwrap() && r.unwrap().node_ptr >= limit.unwrap(),
    decreases fuel,
{
    if fuel == 0 {
        return Err(Error::InvalidBTreeNode);
    }
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
                    Some(_) => kv_slot.value >= copy_at,
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
                let ptr = sorted_write_node(s, &leaf, node_ptr, limit, copy_at)?;
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
                let ptr = sorted_write_node(s, &crate::sorted::leaf(entries.as_slice()), node_ptr, limit, copy_at)?;
                proof {
                    lemma_tx_trans(f1, f2, s.file(), limit);
                }
                return Ok(SortedInsertResult { node_ptr: ptr, count: total as i64, kv_slot: entry, added: true, split: None });
            }

            // overflow: split into two leaves; the new sibling's separator is
            // the key of its first entry
            let left_n = BTREE_SPLIT_COUNT;
            let separator = read_kv_pair(s, entries[left_n], hash_size)?.key_slot;
            let left_ptr = sorted_write_node(s, &crate::sorted::leaf(slice_subrange(entries.as_slice(), 0, left_n)), node_ptr, limit, copy_at)?;
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
            let child = sorted_put(s, node.children[i].value, key, limit, copy_at, hash_size, fuel - 1)?;
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
                let ptr = sorted_write_node(s, &node2, node_ptr, limit, copy_at)?;
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
            let left_ptr = sorted_write_node(s, &left, node_ptr, limit, copy_at)?;
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
pub fn sorted_remove<S: Store>(s: &mut S, node_ptr: i64, key: &[u8], limit: Option<i64>, copy_at: i64, hash_size: usize, fuel: u64) -> (r: Result<(i64, bool)>)
    requires
        limit is Some ==> limit.unwrap() <= copy_at,
        hash_size <= 0xffff,
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
    decreases fuel,
{
    if fuel == 0 {
        return Err(Error::InvalidBTreeNode);
    }
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
            let ptr = sorted_write_node(s, &crate::sorted::leaf(entries.as_slice()), node_ptr, limit, copy_at)?;
            Ok((ptr, true))
        },
        BTreeNodeKind::Branch => {
            let (i, _) = child_for_key(s, &node, key)?;
            if node.num == 0 {
                return Err(Error::InvalidBTreeNode);
            }
            let (child_ptr, found) = sorted_remove(s, node.children[i].value, key, limit, copy_at, hash_size, fuel - 1)?;
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
            let ptr = sorted_write_node(s, &branch, node_ptr, limit, copy_at)?;
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
    ensures
        final(s).file() == old(s).file(),
        (r is Ok && target == SortedTarget::Value) ==> r.unwrap().position is Some && r.unwrap().position.unwrap() >= kv_slot.value,
        (r is Ok && target != SortedTarget::Value) ==> r.unwrap().position is None,
{
    if hash_size > 0xffff {
        return Err(Error::InvalidHashSize);
    }
    let kv = read_kv_pair(s, kv_slot, hash_size)?;
    Ok(match target {
        SortedTarget::KvPair => SlotPointer::new(None, kv_slot),
        SortedTarget::Key => SlotPointer::new(None, kv.key_slot),
        SortedTarget::Value => {
            let off = kv_key_offset(kv_slot.tag, hash_size as u16);
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
