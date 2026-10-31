//! The hash map of `src/database.rs` (`read_map_slot` and
//! `remove_map_slot`), as a model over an append-only store.
//!
//! A hash map is a tree of index blocks of 16 slots. Each slot is empty,
//! points to a key/value pair, or points to a child index block. The slot a
//! key goes in at depth `d` is nibble `d` of its hash, counting from the
//! least significant end.
//!
//! The store is the database file: index blocks and key/value pairs live at
//! positions, new ones are appended at `next`, and positions before
//! `frozen` (`frozen_at` in the crate) belong to committed transactions and
//! must never change. Positions from `frozen` on belong to the current
//! transaction and are written in place, so the model has to show that no
//! two places in the tree share a mutable block, or a write through one
//! would change the other.
//!
//! Positions are abstract (one per block or pair instead of byte offsets)
//! and values are opaque, which is all the algorithms depend on.
//!
//! The main results:
//!
//! * [`lemma_put`]: inserting into a well-formed map never fails (in
//!   particular `KeyOffsetExceeded` is unreachable), keeps it well-formed,
//!   and gives the map `old.insert(hash, value)`.
//! * [`lemma_remove`]: removing succeeds exactly when the key is present,
//!   keeps the map well-formed, and gives `old.remove(hash)`.
//! * Both only write positions from `frozen` on, so every map committed
//!   before the transaction reads the same as before
//!   ([`lemma_snapshot_unchanged`]).

use vstd::prelude::*;

verus! {

// nibbles

/// `hash_nibble`: nibble `offset` of the big-endian hash, counting from its
/// least significant end, or 0 past the end of the hash.
pub open spec fn nibble(h: Seq<u8>, offset: int) -> int {
    if offset < 0 || offset / 2 >= h.len() {
        0
    } else {
        let byte = h[h.len() - 1 - offset / 2];
        if offset % 2 == 0 {
            (byte & 0xfu8) as int
        } else {
            (byte >> 4u8) as int
        }
    }
}

proof fn lemma_nibble_bits(b: u8)
    by (bit_vector)
    ensures
        b & 0xfu8 < 16,
        b >> 4u8 < 16,
{
}

proof fn lemma_nibbles_determine_byte(a: u8, b: u8)
    by (bit_vector)
    requires
        a & 0xfu8 == b & 0xfu8,
        a >> 4u8 == b >> 4u8,
    ensures
        a == b,
{
}

pub proof fn lemma_nibble_range(h: Seq<u8>, offset: int)
    ensures
        0 <= nibble(h, offset) < 16,
{
    if !(offset < 0 || offset / 2 >= h.len()) {
        lemma_nibble_bits(h[h.len() - 1 - offset / 2]);
    }
}

/// Two different hashes of length `len` differ in one of their first
/// `2 * len` nibbles, which is the `max_offset` the crate allows.
pub proof fn lemma_distinct_hashes_differ_in_nibble(a: Seq<u8>, b: Seq<u8>, len: int)
    requires
        a.len() == len,
        b.len() == len,
        a != b,
    ensures
        exists|j: int| 0 <= j < 2 * len && nibble(a, j) != nibble(b, j),
{
    if forall|j: int| 0 <= j < 2 * len ==> nibble(a, j) == nibble(b, j) {
        assert forall|k: int| 0 <= k < len implies a[k] == b[k] by {
            let j = 2 * (len - 1 - k);
            assert(nibble(a, j) == nibble(b, j));
            assert(nibble(a, j + 1) == nibble(b, j + 1));
            assert(j / 2 == len - 1 - k);
            assert((j + 1) / 2 == len - 1 - k);
            lemma_nibbles_determine_byte(a[k], b[k]);
        }
        assert(a =~= b);
    }
}

/// `hash_nibble`, executable.
pub fn hash_nibble(hash: &[u8], offset: usize) -> (r: usize)
    ensures
        r == nibble(hash@, offset as int),
        r < 16,
{
    if offset / 2 >= hash.len() {
        return 0;
    }
    let byte = hash[hash.len() - 1 - offset / 2];
    proof {
        lemma_nibble_bits(byte);
    }
    (if offset % 2 == 0 {
        byte & 0xf
    } else {
        byte >> 4
    }) as usize
}

// the store

pub enum Ptr {
    Empty,
    Index(int),
    Kv(int),
}

pub struct KvPair {
    pub hash: Seq<u8>,
    pub value: int,
}

pub struct Store {
    pub blocks: Map<int, Seq<Ptr>>,
    pub kvs: Map<int, KvPair>,
    /// Where the next append goes: the length of the file.
    pub next: int,
}

pub open spec fn store_ok(s: Store, frozen: int) -> bool {
    &&& 0 <= frozen <= s.next
    &&& forall|x: int| #[trigger]
        s.blocks.contains_key(x) ==> 0 <= x < s.next && s.blocks[x].len() == 16
    &&& forall|x: int| #[trigger]
        s.kvs.contains_key(x) ==> 0 <= x < s.next && !s.blocks.contains_key(x)
}

pub open spec fn empty_block() -> Seq<Ptr> {
    Seq::new(16, |i: int| Ptr::Empty)
}

pub open spec fn write_slot(s: Store, pos: int, i: int, p: Ptr) -> Store {
    Store { blocks: s.blocks.insert(pos, s.blocks[pos].update(i, p)), ..s }
}

/// Appends an index block.
pub open spec fn append_block(s: Store, b: Seq<Ptr>) -> Store {
    Store { blocks: s.blocks.insert(s.next, b), next: s.next + 1, ..s }
}

/// Appends a key/value pair.
pub open spec fn append_kv(s: Store, kv: KvPair) -> Store {
    Store { kvs: s.kvs.insert(s.next, kv), next: s.next + 1, ..s }
}

/// Position `x` reads the same in both stores.
pub open spec fn agree(s: Store, t: Store, x: int) -> bool {
    &&& s.blocks.contains_key(x) == t.blocks.contains_key(x)
    &&& s.blocks.contains_key(x) ==> s.blocks[x] == t.blocks[x]
    &&& s.kvs.contains_key(x) == t.kvs.contains_key(x)
    &&& s.kvs.contains_key(x) ==> s.kvs[x] == t.kvs[x]
}

// footprints: every position a block reaches

pub open spec fn in_fp(s: Store, pos: int, d: int, len: int, x: int) -> bool
    decreases 2 * len - d, 1int,
{
    x == pos || (0 <= d < 2 * len && s.blocks.contains_key(pos) && exists|i: int|
        0 <= i < 16 && in_fp_child(s, #[trigger] s.blocks[pos][i], d + 1, len, x))
}

/// `in_fp` for what a slot points to; `d` is the depth of the child.
pub open spec fn in_fp_child(s: Store, p: Ptr, d: int, len: int, x: int) -> bool
    decreases 2 * len - d + 1, 0int,
{
    match p {
        Ptr::Empty => false,
        Ptr::Kv(q) => x == q,
        Ptr::Index(q) => d <= 2 * len && in_fp(s, q, d, len, x),
    }
}

pub open spec fn ptr_pos(p: Ptr) -> int {
    match p {
        Ptr::Empty => -1,
        Ptr::Kv(q) => q,
        Ptr::Index(q) => q,
    }
}

// well-formedness

/// The pair at `q` belongs at the end of `path`: its hash has the store's
/// hash length and its first nibbles are `path`.
pub open spec fn kv_ok(s: Store, q: int, path: Seq<int>, len: int) -> bool {
    &&& s.kvs.contains_key(q)
    &&& s.kvs[q].hash.len() == len
    &&& forall|j: int| 0 <= j < path.len() ==> nibble(s.kvs[q].hash, j) == path[j]
}

/// The index block at `pos`, at depth `d` (the crate's `key_offset`) and
/// reached through the nibbles `path`, is a well-formed hash map.
pub open spec fn wf(s: Store, pos: int, d: int, path: Seq<int>, frozen: int, len: int) -> bool
    decreases 2 * len - d, 1int,
{
    &&& 0 <= d < 2 * len
    &&& path.len() == d
    &&& s.blocks.contains_key(pos)
    &&& s.blocks[pos].len() == 16
    &&& forall|i: int|
        0 <= i < 16 ==> child_wf(s, #[trigger] s.blocks[pos][i], d + 1, path.push(i), frozen, len)
    // committed blocks only point to committed data
    &&& pos < frozen ==> forall|i: int| 0 <= i < 16 ==> ptr_pos(#[trigger] s.blocks[pos][i]) < frozen
    // a block of this transaction is reachable only once
    &&& pos >= frozen ==> forall|i: int|
        0 <= i < 16 ==> !in_fp_child(s, #[trigger] s.blocks[pos][i], d + 1, len, pos)
    &&& pos >= frozen ==> forall|i: int, j: int, x: int|
        0 <= i < 16 && 0 <= j < 16 && i != j && #[trigger] in_fp_child(
            s,
            s.blocks[pos][i],
            d + 1,
            len,
            x,
        ) && #[trigger] in_fp_child(s, s.blocks[pos][j], d + 1, len, x) ==> x < frozen
}

/// A slot of a block at depth `d - 1` and path `path.drop_last()` is
/// well-formed.
pub open spec fn child_wf(s: Store, p: Ptr, d: int, path: Seq<int>, frozen: int, len: int) -> bool
    decreases 2 * len - d + 1, 0int,
{
    match p {
        Ptr::Empty => true,
        Ptr::Kv(q) => kv_ok(s, q, path, len),
        Ptr::Index(q) => d <= 2 * len && wf(s, q, d, path, frozen, len),
    }
}

/// The hash follows `path`.
pub open spec fn follows(h: Seq<u8>, path: Seq<int>) -> bool {
    forall|j: int| 0 <= j < path.len() ==> nibble(h, j) == path[j]
}

// lookups

/// `read_map_slot` in `WriteMode::ReadOnly`: the value for `h`, if any.
pub open spec fn lookup(s: Store, pos: int, h: Seq<u8>, d: int, len: int) -> Option<int>
    decreases 2 * len + 1 - d, 1int,
{
    if !(0 <= d <= 2 * len) || !s.blocks.contains_key(pos) {
        None
    } else {
        lookup_child(s, s.blocks[pos][nibble(h, d)], h, d + 1, len)
    }
}

pub open spec fn lookup_child(s: Store, p: Ptr, h: Seq<u8>, d: int, len: int) -> Option<int>
    decreases 2 * len + 2 - d, 0int,
{
    match p {
        Ptr::Empty => None,
        Ptr::Index(q) => if d <= 2 * len + 1 {
            lookup(s, q, h, d, len)
        } else {
            None
        },
        Ptr::Kv(q) => if s.kvs.contains_key(q) && s.kvs[q].hash == h {
            Some(s.kvs[q].value)
        } else {
            None
        },
    }
}

/// The map a hash map holds.
pub open spec fn contents(s: Store, root: int, len: int) -> IMap<Seq<u8>, int> {
    IMap::new(
        |h: Seq<u8>| h.len() == len && lookup(s, root, h, 0, len) is Some,
        |h: Seq<u8>| lookup(s, root, h, 0, len).unwrap(),
    )
}

// basic facts

/// Everything a well-formed block reaches is stored, and below `next`.
pub proof fn lemma_fp_stored(s: Store, pos: int, d: int, path: Seq<int>, frozen: int, len: int, x: int)
    requires
        store_ok(s, frozen),
        wf(s, pos, d, path, frozen, len),
        in_fp(s, pos, d, len, x),
    ensures
        s.blocks.contains_key(x) || s.kvs.contains_key(x),
        0 <= x < s.next,
    decreases 2 * len - d,
{
    if x != pos {
        assert(0 <= d < 2 * len);
        let i = choose|i: int| 0 <= i < 16 && in_fp_child(s, #[trigger] s.blocks[pos][i], d + 1, len, x);
        assert(0 <= i < 16);
        assert(child_wf(s, s.blocks[pos][i], d + 1, path.push(i), frozen, len));
        match s.blocks[pos][i] {
            Ptr::Index(q) => {
                lemma_fp_stored(s, q, d + 1, path.push(i), frozen, len, x);
            },
            _ => {},
        }
    }
}

/// A committed block only reaches committed data.
pub proof fn lemma_fp_frozen(s: Store, pos: int, d: int, path: Seq<int>, frozen: int, len: int, x: int)
    requires
        wf(s, pos, d, path, frozen, len),
        pos < frozen,
        in_fp(s, pos, d, len, x),
    ensures
        x < frozen,
    decreases 2 * len - d,
{
    if x != pos {
        let i = choose|i: int| 0 <= i < 16 && in_fp_child(s, #[trigger] s.blocks[pos][i], d + 1, len, x);
        assert(child_wf(s, s.blocks[pos][i], d + 1, path.push(i), frozen, len));
        assert(ptr_pos(s.blocks[pos][i]) < frozen);
        match s.blocks[pos][i] {
            Ptr::Index(q) => {
                lemma_fp_frozen(s, q, d + 1, path.push(i), frozen, len, x);
            },
            _ => {},
        }
    }
}

pub proof fn lemma_fp_child_stored(s: Store, p: Ptr, d: int, path: Seq<int>, frozen: int, len: int, x: int)
    requires
        store_ok(s, frozen),
        child_wf(s, p, d, path, frozen, len),
        in_fp_child(s, p, d, len, x),
    ensures
        0 <= x < s.next,
{
    if let Ptr::Index(q) = p {
        lemma_fp_stored(s, q, d, path, frozen, len, x);
    }
}

/// The frame lemma: a block reads the same in any store that agrees with
/// this one on everything the block reaches.
pub proof fn lemma_frame(s: Store, t: Store, pos: int, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        wf(s, pos, d, path, frozen, len),
        forall|x: int| in_fp(s, pos, d, len, x) ==> #[trigger] agree(s, t, x),
    ensures
        wf(t, pos, d, path, frozen, len),
        forall|x: int| #[trigger] in_fp(t, pos, d, len, x) == in_fp(s, pos, d, len, x),
        forall|h: Seq<u8>| #[trigger] lookup(t, pos, h, d, len) == lookup(s, pos, h, d, len),
    decreases 2 * len - d, 1int,
{
    assert(agree(s, t, pos));
    assert(t.blocks[pos] == s.blocks[pos]);
    assert forall|i: int| 0 <= i < 16 implies {
        &&& child_wf(t, #[trigger] s.blocks[pos][i], d + 1, path.push(i), frozen, len)
        &&& forall|x: int| #[trigger]
            in_fp_child(t, s.blocks[pos][i], d + 1, len, x) == in_fp_child(s, s.blocks[pos][i], d + 1, len, x)
        &&& forall|h: Seq<u8>| #[trigger]
            lookup_child(t, s.blocks[pos][i], h, d + 1, len) == lookup_child(s, s.blocks[pos][i], h, d + 1, len)
    } by {
        assert(child_wf(s, s.blocks[pos][i], d + 1, path.push(i), frozen, len));
        assert forall|x: int| in_fp_child(s, s.blocks[pos][i], d + 1, len, x) implies #[trigger] agree(s, t, x) by {
            assert(in_fp(s, pos, d, len, x));
        }
        lemma_frame_child(s, t, s.blocks[pos][i], d + 1, path.push(i), frozen, len);
    }
    assert forall|x: int| #[trigger] in_fp(t, pos, d, len, x) == in_fp(s, pos, d, len, x) by {
        if in_fp(s, pos, d, len, x) && x != pos {
            let i = choose|i: int| 0 <= i < 16 && in_fp_child(s, #[trigger] s.blocks[pos][i], d + 1, len, x);
            assert(in_fp_child(t, t.blocks[pos][i], d + 1, len, x));
        }
        if in_fp(t, pos, d, len, x) && x != pos {
            let i = choose|i: int| 0 <= i < 16 && in_fp_child(t, #[trigger] t.blocks[pos][i], d + 1, len, x);
            assert(in_fp_child(s, s.blocks[pos][i], d + 1, len, x));
        }
    }
    assert forall|h: Seq<u8>| #[trigger] lookup(t, pos, h, d, len) == lookup(s, pos, h, d, len) by {
        lemma_nibble_range(h, d);
        let i = nibble(h, d);
        assert(lookup_child(t, s.blocks[pos][i], h, d + 1, len) == lookup_child(s, s.blocks[pos][i], h, d + 1, len));
    }
}

pub proof fn lemma_frame_child(s: Store, t: Store, p: Ptr, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        child_wf(s, p, d, path, frozen, len),
        forall|x: int| in_fp_child(s, p, d, len, x) ==> #[trigger] agree(s, t, x),
    ensures
        child_wf(t, p, d, path, frozen, len),
        forall|x: int| #[trigger] in_fp_child(t, p, d, len, x) == in_fp_child(s, p, d, len, x),
        forall|h: Seq<u8>| #[trigger] lookup_child(t, p, h, d, len) == lookup_child(s, p, h, d, len),
    decreases 2 * len - d + 1, 0int,
{
    match p {
        Ptr::Empty => {},
        Ptr::Kv(q) => {
            assert(in_fp_child(s, p, d, len, q));
            assert(agree(s, t, q));
        },
        Ptr::Index(q) => {
            assert forall|x: int| in_fp(s, q, d, len, x) implies #[trigger] agree(s, t, x) by {
                assert(in_fp_child(s, p, d, len, x));
            }
            lemma_frame(s, t, q, d, path, frozen, len);
            assert forall|x: int| #[trigger] in_fp_child(t, p, d, len, x) == in_fp_child(s, p, d, len, x) by {
                assert(in_fp(t, q, d, len, x) == in_fp(s, q, d, len, x));
            }
            assert forall|h: Seq<u8>| #[trigger] lookup_child(t, p, h, d, len) == lookup_child(s, p, h, d, len) by {
                assert(lookup(t, q, h, d, len) == lookup(s, q, h, d, len));
            }
        },
    }
}

/// A hash that doesn't follow a block's path isn't in it.
pub proof fn lemma_lookup_off_path(s: Store, pos: int, h: Seq<u8>, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        wf(s, pos, d, path, frozen, len),
        !follows(h, path),
    ensures
        lookup(s, pos, h, d, len) is None,
    decreases 2 * len - d,
{
    let i = nibble(h, d);
    lemma_nibble_range(h, d);
    let p = s.blocks[pos][i];
    assert(child_wf(s, p, d + 1, path.push(i), frozen, len));
    assert(!follows(h, path.push(i))) by {
        let j = choose|j: int| 0 <= j < path.len() && nibble(h, j) != path[j];
        assert(path.push(i)[j] == path[j]);
    }
    match p {
        Ptr::Index(q) => {
            lemma_lookup_off_path(s, q, h, d + 1, path.push(i), frozen, len);
        },
        Ptr::Kv(q) => {
            if s.kvs[q].hash == h {
                let j = choose|j: int| 0 <= j < path.push(i).len() && nibble(h, j) != path.push(i)[j];
                assert(nibble(s.kvs[q].hash, j) == path.push(i)[j]);
            }
        },
        Ptr::Empty => {},
    }
}

// insertion

/// `read_map_slot` in `WriteMode::ReadWrite` for the hash `h`, followed by
/// writing `v` into the key/value pair it returns. `None` is an error
/// (`KeyOffsetExceeded`); `Some(t)` is the store afterwards.
pub open spec fn put(s: Store, pos: int, h: Seq<u8>, v: int, d: int, frozen: int, len: int) -> Option<Store>
    decreases 2 * len + 1 - d,
{
    if !(0 <= d <= 2 * len) {
        None
    } else {
        let i = nibble(h, d);
        let kv = KvPair { hash: h, value: v };
        match s.blocks[pos][i] {
            Ptr::Empty => Some(write_slot(append_kv(s, kv), pos, i, Ptr::Kv(s.next))),
            Ptr::Index(q) => if q < frozen {
                // copy_index_block_if_old, then point the slot at the copy
                let s2 = write_slot(append_block(s, s.blocks[q]), pos, i, Ptr::Index(s.next));
                put(s2, s.next, h, v, d + 1, frozen, len)
            } else {
                put(s, q, h, v, d + 1, frozen, len)
            },
            Ptr::Kv(q) => if s.kvs[q].hash == h {
                if q < frozen {
                    Some(write_slot(append_kv(s, kv), pos, i, Ptr::Kv(s.next)))
                } else {
                    Some(Store { kvs: s.kvs.insert(q, kv), ..s })
                }
            } else if d + 1 >= 2 * len {
                None
            } else {
                // hash collision: move the pair into a new block one level down
                let n = s.next;
                let b = empty_block().update(nibble(s.kvs[q].hash, d + 1), Ptr::Kv(q));
                match put(append_block(s, b), n, h, v, d + 1, frozen, len) {
                    Some(s2) => Some(write_slot(s2, pos, i, Ptr::Index(n))),
                    None => None,
                }
            },
        }
    }
}

/// What a write to a mutable block may change: positions it reaches that
/// belong to this transaction, and new positions.
pub open spec fn frame_ok(s: Store, t: Store, pos: int, d: int, frozen: int, len: int) -> bool {
    &&& t.next >= s.next
    &&& forall|x: int|
        0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) ==> #[trigger] agree(s, t, x)
    &&& forall|x: int| #[trigger] in_fp(t, pos, d, len, x) ==> in_fp(s, pos, d, len, x) || s.next <= x
}

/// A block whose slot `i` now holds `np` is still well-formed, if `np` is,
/// and the other slots read the same. The new block is either the old one
/// written in place, if it belongs to this transaction, or a copy appended
/// at `npos`.
proof fn lemma_rebuild(
    s: Store,
    t: Store,
    pos: int,
    npos: int,
    i: int,
    np: Ptr,
    d: int,
    path: Seq<int>,
    frozen: int,
    len: int,
)
    requires
        store_ok(s, frozen),
        wf(s, pos, d, path, frozen, len),
        (npos == pos && pos >= frozen) || (pos < frozen && npos >= s.next),
        0 <= i < 16,
        t.blocks.contains_key(npos),
        t.blocks[npos] == s.blocks[pos].update(i, np),
        forall|j: int, x: int|
            0 <= j < 16 && j != i && #[trigger] in_fp_child(s, s.blocks[pos][j], d + 1, len, x) ==> agree(s, t, x),
        child_wf(t, np, d + 1, path.push(i), frozen, len),
        !in_fp_child(t, np, d + 1, len, npos),
        forall|x: int| #[trigger]
            in_fp_child(t, np, d + 1, len, x) ==> in_fp_child(s, s.blocks[pos][i], d + 1, len, x) || s.next <= x,
    ensures
        wf(t, npos, d, path, frozen, len),
        forall|x: int| #[trigger] in_fp(t, npos, d, len, x) ==> in_fp(s, pos, d, len, x) || s.next <= x,
        forall|h: Seq<u8>| nibble(h, d) != i ==> #[trigger] lookup(t, npos, h, d, len) == lookup(s, pos, h, d, len),
        forall|h: Seq<u8>| nibble(h, d) == i ==> #[trigger] lookup(t, npos, h, d, len) == lookup_child(t, np, h, d + 1, len),
{
    let b = s.blocks[pos];
    let tb = t.blocks[npos];
    assert forall|j: int| 0 <= j < 16 && j != i implies {
        &&& child_wf(t, #[trigger] b[j], d + 1, path.push(j), frozen, len)
        &&& forall|x: int| #[trigger] in_fp_child(t, b[j], d + 1, len, x) == in_fp_child(s, b[j], d + 1, len, x)
        &&& forall|x: int| #[trigger] in_fp_child(s, b[j], d + 1, len, x) ==> 0 <= x < s.next && (pos < frozen ==> x < frozen)
        &&& forall|h: Seq<u8>| #[trigger] lookup_child(t, b[j], h, d + 1, len) == lookup_child(s, b[j], h, d + 1, len)
    } by {
        assert(child_wf(s, b[j], d + 1, path.push(j), frozen, len));
        lemma_frame_child(s, t, b[j], d + 1, path.push(j), frozen, len);
        assert forall|x: int| #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies 0 <= x < s.next && (pos < frozen ==> x < frozen) by {
            lemma_fp_child_stored(s, b[j], d + 1, path.push(j), frozen, len, x);
            if pos < frozen {
                assert(in_fp(s, pos, d, len, x));
                lemma_fp_frozen(s, pos, d, path, frozen, len, x);
            }
        }
    }
    assert forall|j: int| 0 <= j < 16 implies child_wf(t, #[trigger] tb[j], d + 1, path.push(j), frozen, len) by {
        if j != i {
            assert(tb[j] == b[j]);
        }
    }
    assert forall|j: int| 0 <= j < 16 implies !in_fp_child(t, #[trigger] tb[j], d + 1, len, npos) by {
        if j != i {
            assert(tb[j] == b[j]);
            if npos == pos {
                assert(!in_fp_child(s, b[j], d + 1, len, pos));
            }
        }
    }
    assert forall|j: int, k: int, x: int|
        0 <= j < 16 && 0 <= k < 16 && j != k && #[trigger] in_fp_child(t, tb[j], d + 1, len, x)
            && #[trigger] in_fp_child(t, tb[k], d + 1, len, x) implies x < frozen by {
        if j != i && k != i {
            assert(tb[j] == b[j] && tb[k] == b[k]);
            assert(in_fp_child(s, b[j], d + 1, len, x) && in_fp_child(s, b[k], d + 1, len, x));
        } else if j == i {
            assert(tb[k] == b[k]);
            assert(in_fp_child(s, b[k], d + 1, len, x));
            if pos >= frozen {
                assert(in_fp_child(s, b[i], d + 1, len, x));
            }
        } else {
            assert(tb[j] == b[j]);
            assert(in_fp_child(s, b[j], d + 1, len, x));
            if pos >= frozen {
                assert(in_fp_child(s, b[i], d + 1, len, x));
            }
        }
    }
    assert(wf(t, npos, d, path, frozen, len));
    assert forall|x: int| #[trigger] in_fp(t, npos, d, len, x) implies in_fp(s, pos, d, len, x) || s.next <= x by {
        if x != npos {
            let j = choose|j: int| 0 <= j < 16 && in_fp_child(t, #[trigger] t.blocks[npos][j], d + 1, len, x);
            if j != i {
                assert(tb[j] == b[j]);
                assert(in_fp_child(s, s.blocks[pos][j], d + 1, len, x));
            } else if !(s.next <= x) {
                assert(in_fp_child(s, s.blocks[pos][i], d + 1, len, x));
            }
        }
    }
    assert forall|h: Seq<u8>| nibble(h, d) != i implies #[trigger] lookup(t, npos, h, d, len) == lookup(s, pos, h, d, len) by {
        lemma_nibble_range(h, d);
        let j = nibble(h, d);
        assert(tb[j] == b[j]);
        assert(lookup_child(t, b[j], h, d + 1, len) == lookup_child(s, b[j], h, d + 1, len));
    }
}

/// Copying a committed block to a new position gives a block that reads
/// the same.
proof fn lemma_copy_frozen(s: Store, t: Store, q: int, n: int, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, q, d, path, frozen, len),
        q < frozen,
        n >= frozen,
        t.blocks.contains_key(n),
        t.blocks[n] == s.blocks[q],
        forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x),
    ensures
        wf(t, n, d, path, frozen, len),
        forall|x: int| #[trigger] in_fp(t, n, d, len, x) ==> x == n || (in_fp(s, q, d, len, x) && x < frozen),
        forall|h: Seq<u8>| #[trigger] lookup(t, n, h, d, len) == lookup(s, q, h, d, len),
{
    let b = s.blocks[q];
    assert forall|j: int| 0 <= j < 16 implies {
        &&& child_wf(t, #[trigger] b[j], d + 1, path.push(j), frozen, len)
        &&& forall|x: int| #[trigger] in_fp_child(t, b[j], d + 1, len, x) == in_fp_child(s, b[j], d + 1, len, x)
        &&& forall|x: int| #[trigger] in_fp_child(s, b[j], d + 1, len, x) ==> x < frozen && in_fp(s, q, d, len, x)
        &&& forall|h: Seq<u8>| #[trigger] lookup_child(t, b[j], h, d + 1, len) == lookup_child(s, b[j], h, d + 1, len)
    } by {
        assert(child_wf(s, b[j], d + 1, path.push(j), frozen, len));
        assert forall|x: int| #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies x < frozen && in_fp(s, q, d, len, x) by {
            assert(in_fp(s, q, d, len, x));
            lemma_fp_frozen(s, q, d, path, frozen, len, x);
        }
        assert forall|x: int| in_fp_child(s, b[j], d + 1, len, x) implies #[trigger] agree(s, t, x) by {
            lemma_fp_stored(s, q, d, path, frozen, len, x);
        }
        lemma_frame_child(s, t, b[j], d + 1, path.push(j), frozen, len);
    }
    assert forall|j: int, k: int, x: int|
        0 <= j < 16 && 0 <= k < 16 && j != k && #[trigger] in_fp_child(t, t.blocks[n][j], d + 1, len, x)
            && #[trigger] in_fp_child(t, t.blocks[n][k], d + 1, len, x) implies x < frozen by {
        assert(in_fp_child(s, b[j], d + 1, len, x));
    }
    assert forall|j: int| 0 <= j < 16 implies !in_fp_child(t, #[trigger] t.blocks[n][j], d + 1, len, n) by {
        if in_fp_child(s, b[j], d + 1, len, n) {
            assert(n < frozen);
        }
    }
    assert(wf(t, n, d, path, frozen, len));
    assert forall|x: int| #[trigger] in_fp(t, n, d, len, x) implies x == n || (in_fp(s, q, d, len, x) && x < frozen) by {
        if x != n {
            let j = choose|j: int| 0 <= j < 16 && in_fp_child(t, #[trigger] t.blocks[n][j], d + 1, len, x);
            assert(in_fp_child(s, b[j], d + 1, len, x));
        }
    }
    assert forall|h: Seq<u8>| #[trigger] lookup(t, n, h, d, len) == lookup(s, q, h, d, len) by {
        lemma_nibble_range(h, d);
        let j = nibble(h, d);
        assert(lookup_child(t, b[j], h, d + 1, len) == lookup_child(s, b[j], h, d + 1, len));
    }
}

proof fn lemma_agree_trans(s: Store, t: Store, u: Store, x: int)
    requires
        agree(s, t, x),
        agree(t, u, x),
    ensures
        agree(s, u, x),
{
}

/// Inserting into a mutable, well-formed block.
pub proof fn lemma_put(s: Store, pos: int, h: Seq<u8>, v: int, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, pos, d, path, frozen, len),
        pos >= frozen,
        h.len() == len,
        follows(h, path),
    ensures
        put(s, pos, h, v, d, frozen, len) is Some,
        ({
            let t = put(s, pos, h, v, d, frozen, len).unwrap();
            &&& store_ok(t, frozen)
            &&& wf(t, pos, d, path, frozen, len)
            &&& frame_ok(s, t, pos, d, frozen, len)
            &&& forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                Some(v)
            } else {
                lookup(s, pos, h2, d, len)
            }
        }),
    decreases 2 * len - d,
{
    let i = nibble(h, d);
    lemma_nibble_range(h, d);
    let b = s.blocks[pos];
    let kv = KvPair { hash: h, value: v };
    assert(child_wf(s, b[i], d + 1, path.push(i), frozen, len));
    assert(follows(h, path.push(i)));
    assert(forall|x: int| #[trigger] in_fp_child(s, b[i], d + 1, len, x) ==> in_fp(s, pos, d, len, x));
    assert(in_fp(s, pos, d, len, pos));
    // the siblings of slot i don't reach pos or anything mutable that slot i reaches
    assert forall|j: int, x: int|
        0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies
            x != pos && 0 <= x < s.next && (x < frozen || !in_fp_child(s, b[i], d + 1, len, x)) by {
        assert(child_wf(s, b[j], d + 1, path.push(j), frozen, len));
        lemma_fp_child_stored(s, b[j], d + 1, path.push(j), frozen, len, x);
    }
    match b[i] {
        Ptr::Empty => {
            let n = s.next;
            let t = write_slot(append_kv(s, kv), pos, i, Ptr::Kv(n));
            assert(put(s, pos, h, v, d, frozen, len) == Some(t));
            assert(child_wf(t, Ptr::Kv(n), d + 1, path.push(i), frozen, len));
            lemma_rebuild(s, t, pos, pos, i, Ptr::Kv(n), d, path, frozen, len);
            assert forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                Some(v)
            } else {
                lookup(s, pos, h2, d, len)
            } by {
                lemma_nibble_range(h2, d);
            }
        },
        Ptr::Kv(q) => {
            if s.kvs[q].hash == h {
                if q < frozen {
                    let n = s.next;
                    let t = write_slot(append_kv(s, kv), pos, i, Ptr::Kv(n));
                    assert(put(s, pos, h, v, d, frozen, len) == Some(t));
                    assert(child_wf(t, Ptr::Kv(n), d + 1, path.push(i), frozen, len));
                    lemma_rebuild(s, t, pos, pos, i, Ptr::Kv(n), d, path, frozen, len);
                    assert forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                        Some(v)
                    } else {
                        lookup(s, pos, h2, d, len)
                    } by {
                        lemma_nibble_range(h2, d);
                    }
                } else {
                    let t = Store { kvs: s.kvs.insert(q, kv), ..s };
                    assert(put(s, pos, h, v, d, frozen, len) == Some(t));
                    assert(in_fp_child(s, b[i], d + 1, len, q));
                    assert(b.update(i, Ptr::Kv(q)) =~= b);
                    lemma_rebuild(s, t, pos, pos, i, Ptr::Kv(q), d, path, frozen, len);
                    assert forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                        Some(v)
                    } else {
                        lookup(s, pos, h2, d, len)
                    } by {
                        lemma_nibble_range(h2, d);
                    }
                }
            } else {
                // the two hashes agree up to nibble d, and differ before 2 * len
                let kh = s.kvs[q].hash;
                lemma_distinct_hashes_differ_in_nibble(h, kh, len);
                let jd = choose|j: int| 0 <= j < 2 * len && nibble(h, j) != nibble(kh, j);
                assert(follows(kh, path.push(i)));
                if jd <= d {
                    assert(nibble(kh, jd) == path.push(i)[jd]);
                    assert(nibble(h, jd) == path.push(i)[jd]);
                }
                assert(d + 1 < 2 * len);
                let n = s.next;
                let k = nibble(kh, d + 1);
                lemma_nibble_range(kh, d + 1);
                let nb = empty_block().update(k, Ptr::Kv(q));
                let s1 = append_block(s, nb);
                // the new block is well-formed
                assert(kv_ok(s1, q, path.push(i).push(k), len)) by {
                    assert forall|j: int| 0 <= j < path.push(i).push(k).len() implies
                        nibble(s1.kvs[q].hash, j) == path.push(i).push(k)[j] by {
                        if j < d + 1 {
                            assert(path.push(i).push(k)[j] == path.push(i)[j]);
                        }
                    }
                }
                assert forall|j: int| 0 <= j < 16 implies child_wf(s1, #[trigger] s1.blocks[n][j], d + 2, path.push(i).push(j), frozen, len) by {
                    if j != k {
                        assert(s1.blocks[n][j] == Ptr::Empty);
                    }
                }
                assert forall|j: int, j2: int, x: int|
                    0 <= j < 16 && 0 <= j2 < 16 && j != j2 && #[trigger] in_fp_child(s1, s1.blocks[n][j], d + 2, len, x)
                        && #[trigger] in_fp_child(s1, s1.blocks[n][j2], d + 2, len, x) implies x < frozen by {
                    if j != k {
                        assert(s1.blocks[n][j] == Ptr::Empty);
                    } else {
                        assert(s1.blocks[n][j2] == Ptr::Empty);
                    }
                }
                assert forall|j: int| 0 <= j < 16 implies !in_fp_child(s1, #[trigger] s1.blocks[n][j], d + 2, len, n) by {
                    if j != k {
                        assert(s1.blocks[n][j] == Ptr::Empty);
                    }
                }
                assert(wf(s1, n, d + 1, path.push(i), frozen, len));
                assert(store_ok(s1, frozen));
                lemma_put(s1, n, h, v, d + 1, path.push(i), frozen, len);
                let s2 = put(s1, n, h, v, d + 1, frozen, len).unwrap();
                let t = write_slot(s2, pos, i, Ptr::Index(n));
                assert(put(s, pos, h, v, d, frozen, len) == Some(t));
                // what the new block reaches
                assert forall|x: int| #[trigger] in_fp(s1, n, d + 1, len, x) implies x == n || x == q by {
                    if x != n {
                        let j = choose|j: int| 0 <= j < 16 && in_fp_child(s1, #[trigger] s1.blocks[n][j], d + 2, len, x);
                        if j != k {
                            assert(s1.blocks[n][j] == Ptr::Empty);
                        }
                    }
                }
                assert(in_fp_child(s, b[i], d + 1, len, q));
                assert(!in_fp_child(s, b[i], d + 1, len, pos));
                assert(agree(s1, s2, pos));
                assert forall|x: int| in_fp(s2, n, d + 1, len, x) implies #[trigger] agree(s2, t, x) by {
                    if x == pos {
                        assert(in_fp(s1, n, d + 1, len, x) || s1.next <= x);
                    }
                }
                lemma_frame(s2, t, n, d + 1, path.push(i), frozen, len);
                assert(t.blocks[pos] == b.update(i, Ptr::Index(n)));
                assert forall|j: int, x: int|
                    0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies agree(s, t, x) by {
                    assert(agree(s, s1, x));
                    if !(x < frozen) {
                        assert(!in_fp(s1, n, d + 1, len, x));
                    }
                    assert(agree(s1, s2, x));
                    lemma_agree_trans(s, s1, s2, x);
                    lemma_agree_trans(s, s2, t, x);
                }
                assert forall|x: int| #[trigger] in_fp_child(t, Ptr::Index(n), d + 1, len, x) implies
                    in_fp_child(s, b[i], d + 1, len, x) || s.next <= x by {
                    assert(in_fp(t, n, d + 1, len, x));
                    assert(in_fp(s2, n, d + 1, len, x));
                    assert(in_fp(s1, n, d + 1, len, x) || s1.next <= x);
                }
                assert(!in_fp_child(t, Ptr::Index(n), d + 1, len, pos)) by {
                    if in_fp(t, n, d + 1, len, pos) {
                        assert(in_fp(s2, n, d + 1, len, pos));
                    }
                }
                lemma_rebuild(s, t, pos, pos, i, Ptr::Index(n), d, path, frozen, len);
                assert forall|x: int|
                    0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) implies #[trigger] agree(s, t, x) by {
                    assert(agree(s, s1, x));
                    if x == q {
                        assert(in_fp(s, pos, d, len, q));
                    }
                    assert(agree(s1, s2, x));
                    lemma_agree_trans(s, s1, s2, x);
                    lemma_agree_trans(s, s2, t, x);
                }
                assert forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                    Some(v)
                } else {
                    lookup(s, pos, h2, d, len)
                } by {
                    lemma_nibble_range(h2, d);
                    lemma_nibble_range(h2, d + 1);
                    if nibble(h2, d) == i {
                        assert(lookup(t, n, h2, d + 1, len) == lookup(s2, n, h2, d + 1, len));
                        if nibble(h2, d + 1) != k {
                            assert(s1.blocks[n][nibble(h2, d + 1)] == Ptr::Empty);
                        }
                    }
                }
            }
        },
        Ptr::Index(q) => {
            assert(wf(s, q, d + 1, path.push(i), frozen, len));
            if q < frozen {
                let n = s.next;
                let s1 = append_block(s, s.blocks[q]);
                let s2 = write_slot(s1, pos, i, Ptr::Index(n));
                assert forall|x: int| 0 <= x < frozen implies #[trigger] agree(s, s2, x) by {}
                lemma_copy_frozen(s, s2, q, n, d + 1, path.push(i), frozen, len);
                assert(store_ok(s2, frozen));
                lemma_put(s2, n, h, v, d + 1, path.push(i), frozen, len);
                let t = put(s2, n, h, v, d + 1, frozen, len).unwrap();
                assert(put(s, pos, h, v, d, frozen, len) == Some(t));
                assert(!in_fp(s2, n, d + 1, len, pos));
                assert(agree(s2, t, pos));
                assert(t.blocks[pos] == b.update(i, Ptr::Index(n)));
                assert forall|j: int, x: int|
                    0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies agree(s, t, x) by {
                    assert(agree(s, s2, x));
                    if !(x < frozen) {
                        assert(!in_fp(s2, n, d + 1, len, x));
                    }
                    assert(agree(s2, t, x));
                    lemma_agree_trans(s, s2, t, x);
                }
                assert forall|x: int| #[trigger] in_fp_child(t, Ptr::Index(n), d + 1, len, x) implies
                    in_fp_child(s, b[i], d + 1, len, x) || s.next <= x by {
                    assert(in_fp(t, n, d + 1, len, x));
                }
                assert(!in_fp_child(t, Ptr::Index(n), d + 1, len, pos)) by {
                    if in_fp(t, n, d + 1, len, pos) {
                        assert(in_fp(s2, n, d + 1, len, pos));
                    }
                }
                lemma_rebuild(s, t, pos, pos, i, Ptr::Index(n), d, path, frozen, len);
                assert forall|x: int|
                    0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) implies #[trigger] agree(s, t, x) by {
                    assert(agree(s, s2, x));
                    if !(x < frozen) {
                        assert(!in_fp(s2, n, d + 1, len, x));
                    }
                    assert(agree(s2, t, x));
                    lemma_agree_trans(s, s2, t, x);
                }
                assert forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                    Some(v)
                } else {
                    lookup(s, pos, h2, d, len)
                } by {
                    lemma_nibble_range(h2, d);
                    if nibble(h2, d) == i {
                        assert(lookup(t, pos, h2, d, len) == lookup_child(t, Ptr::Index(n), h2, d + 1, len));
                        assert(lookup_child(t, Ptr::Index(n), h2, d + 1, len) == lookup(t, n, h2, d + 1, len));
                        assert(lookup(s, pos, h2, d, len) == lookup_child(s, b[i], h2, d + 1, len));
                        assert(lookup_child(s, b[i], h2, d + 1, len) == lookup(s, q, h2, d + 1, len));
                        assert(lookup(s2, n, h2, d + 1, len) == lookup(s, q, h2, d + 1, len));
                    }
                }
            } else {
                lemma_put(s, q, h, v, d + 1, path.push(i), frozen, len);
                let t = put(s, q, h, v, d + 1, frozen, len).unwrap();
                assert(put(s, pos, h, v, d, frozen, len) == Some(t));
                assert(!in_fp(s, q, d + 1, len, pos));
                assert(agree(s, t, pos));
                assert(b.update(i, Ptr::Index(q)) =~= b);
                assert forall|j: int, x: int|
                    0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies agree(s, t, x) by {
                    if !(x < frozen) {
                        assert(!in_fp_child(s, b[i], d + 1, len, x));
                    }
                }
                assert forall|x: int| #[trigger] in_fp_child(t, Ptr::Index(q), d + 1, len, x) implies
                    in_fp_child(s, b[i], d + 1, len, x) || s.next <= x by {
                    assert(in_fp(t, q, d + 1, len, x));
                }
                assert(!in_fp_child(t, Ptr::Index(q), d + 1, len, pos)) by {
                    if in_fp(t, q, d + 1, len, pos) {
                        assert(in_fp(s, q, d + 1, len, pos) || s.next <= pos);
                    }
                }
                lemma_rebuild(s, t, pos, pos, i, Ptr::Index(q), d, path, frozen, len);
                assert forall|x: int|
                    0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) implies #[trigger] agree(s, t, x) by {
                    if !(x < frozen) {
                        assert(!in_fp_child(s, b[i], d + 1, len, x));
                    }
                }
                assert forall|h2: Seq<u8>| #[trigger] lookup(t, pos, h2, d, len) == if h2 == h {
                    Some(v)
                } else {
                    lookup(s, pos, h2, d, len)
                } by {
                    lemma_nibble_range(h2, d);
                    if nibble(h2, d) == i {
                        assert(lookup(t, pos, h2, d, len) == lookup_child(t, Ptr::Index(q), h2, d + 1, len));
                        assert(lookup_child(t, Ptr::Index(q), h2, d + 1, len) == lookup(t, q, h2, d + 1, len));
                        assert(lookup(s, pos, h2, d, len) == lookup_child(s, b[i], h2, d + 1, len));
                        assert(lookup_child(s, b[i], h2, d + 1, len) == lookup(s, q, h2, d + 1, len));
                    }
                }
            }
        },
    }
}

// removal

/// The loop in `remove_map_slot` that finds `slot_to_return`, after
/// looking at the first `k` slots: `Some(Empty)` while every slot is empty,
/// `Some(p)` while `p` is the only non-empty slot, and `None` (the loop's
/// `break`) once there are two.
pub open spec fn scan(b: Seq<Ptr>, k: int) -> Option<Ptr>
    decreases k,
{
    if k <= 0 {
        Some(Ptr::Empty)
    } else {
        let prev = scan(b, k - 1);
        if b[k - 1] is Empty {
            prev
        } else {
            match prev {
                Some(Ptr::Empty) => Some(b[k - 1]),
                _ => None,
            }
        }
    }
}

/// The slot `remove_map_slot` returns in place of a block, if it doesn't
/// keep the block: the block's only entry, if that is empty or a pair.
pub open spec fn collapse(b: Seq<Ptr>) -> Option<Ptr> {
    match scan(b, 16) {
        Some(p) => if p is Index {
            None
        } else {
            Some(p)
        },
        None => None,
    }
}

/// `remove_map_slot` after the slot `i` of the block at `pos` (whose
/// contents were `b`) has been updated to `ns` in the store `s1`.
pub open spec fn remove_finish(s1: Store, b: Seq<Ptr>, ns: Ptr, pos: int, i: int, d: int, frozen: int) -> (Store, Ptr) {
    if d == 0 {
        // the root block is written in place
        (write_slot(s1, pos, i, ns), Ptr::Index(pos))
    } else {
        match collapse(b.update(i, ns)) {
            Some(p) => (s1, p),
            None => if pos < frozen {
                // copy_index_block_if_old
                let n = s1.next;
                (write_slot(append_block(s1, s1.blocks[pos]), n, i, ns), Ptr::Index(n))
            } else {
                (write_slot(s1, pos, i, ns), Ptr::Index(pos))
            },
        }
    }
}

/// `remove_map_slot`: `None` is an error (`KeyNotFound`), and `Some((t, p))`
/// is the store afterwards and the slot that replaces the block.
pub open spec fn remove(s: Store, pos: int, h: Seq<u8>, d: int, frozen: int, len: int) -> Option<(Store, Ptr)>
    decreases 2 * len + 1 - d,
{
    if !(0 <= d <= 2 * len) {
        None
    } else {
        let b = s.blocks[pos];
        let i = nibble(h, d);
        let r = match b[i] {
            Ptr::Empty => None,
            Ptr::Index(q) => remove(s, q, h, d + 1, frozen, len),
            Ptr::Kv(q) => if s.kvs[q].hash == h {
                Some((s, Ptr::Empty))
            } else {
                None
            },
        };
        match r {
            None => None,
            Some((s1, ns)) => Some(remove_finish(s1, b, ns, pos, i, d, frozen)),
        }
    }
}

proof fn lemma_scan(b: Seq<Ptr>, k: int)
    requires
        0 <= k <= b.len(),
    ensures
        scan(b, k) == Some(Ptr::Empty) ==> forall|j: int| 0 <= j < k ==> #[trigger] b[j] is Empty,
        scan(b, k) is Some && !(scan(b, k).unwrap() is Empty) ==> exists|j: int|
            0 <= j < k && b[j] == scan(b, k).unwrap() && forall|j2: int|
                0 <= j2 < k && j2 != j ==> #[trigger] b[j2] is Empty,
    decreases k,
{
    if k > 0 {
        lemma_scan(b, k - 1);
        let prev = scan(b, k - 1);
        if !(b[k - 1] is Empty) && prev == Some(Ptr::Empty) {
            assert forall|j2: int| 0 <= j2 < k && j2 != k - 1 implies #[trigger] b[j2] is Empty by {}
        }
        if b[k - 1] is Empty && prev is Some && !(prev.unwrap() is Empty) {
            let j = choose|j: int|
                0 <= j < k - 1 && b[j] == prev.unwrap() && forall|j2: int|
                    0 <= j2 < k - 1 && j2 != j ==> #[trigger] b[j2] is Empty;
            assert forall|j2: int| 0 <= j2 < k && j2 != j implies #[trigger] b[j2] is Empty by {}
        }
    }
}

proof fn lemma_kv_ok_prefix(s: Store, q: int, path: Seq<int>, i: int, len: int)
    requires
        kv_ok(s, q, path.push(i), len),
    ensures
        kv_ok(s, q, path, len),
{
    assert forall|j: int| 0 <= j < path.len() implies nibble(s.kvs[q].hash, j) == path[j] by {
        assert(path.push(i)[j] == path[j]);
    }
}

/// What `remove` returns from a block.
pub open spec fn remove_ok(s: Store, t: Store, p: Ptr, pos: int, h: Seq<u8>, d: int, path: Seq<int>, frozen: int, len: int) -> bool {
    &&& store_ok(t, frozen)
    &&& t.next >= s.next
    &&& forall|x: int|
        0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) ==> #[trigger] agree(s, t, x)
    &&& child_wf(t, p, d, path, frozen, len)
    &&& forall|x: int| #[trigger] in_fp_child(t, p, d, len, x) ==> in_fp(s, pos, d, len, x) || s.next <= x
    &&& forall|h2: Seq<u8>| #[trigger] lookup_child(t, p, h2, d, len) == if h2 == h {
        None
    } else {
        lookup(s, pos, h2, d, len)
    }
}

proof fn lemma_remove_finish(s: Store, s1: Store, ns: Ptr, pos: int, h: Seq<u8>, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, pos, d, path, frozen, len),
        d == 0 ==> pos >= frozen,
        h.len() == len,
        store_ok(s1, frozen),
        s1.next >= s.next,
        ({
            let i = nibble(h, d);
            let b = s.blocks[pos];
            &&& forall|x: int|
                0 <= x < s.next && (x < frozen || !in_fp_child(s, b[i], d + 1, len, x)) ==> #[trigger] agree(s, s1, x)
            &&& child_wf(s1, ns, d + 1, path.push(i), frozen, len)
            &&& forall|x: int| #[trigger] in_fp_child(s1, ns, d + 1, len, x) ==> in_fp_child(s, b[i], d + 1, len, x) || s.next <= x
            &&& forall|h2: Seq<u8>| #[trigger] lookup_child(s1, ns, h2, d + 1, len) == if h2 == h {
                None
            } else {
                lookup_child(s, b[i], h2, d + 1, len)
            }
        }),
    ensures
        ({
            let (t, p) = remove_finish(s1, s.blocks[pos], ns, pos, nibble(h, d), d, frozen);
            &&& remove_ok(s, t, p, pos, h, d, path, frozen, len)
            &&& d == 0 ==> p == Ptr::Index(pos)
        }),
{
    let i = nibble(h, d);
    lemma_nibble_range(h, d);
    let b = s.blocks[pos];
    let b2 = b.update(i, ns);
    assert(child_wf(s, b[i], d + 1, path.push(i), frozen, len));
    assert(in_fp(s, pos, d, len, pos));
    assert(forall|j: int, x: int| 0 <= j < 16 && #[trigger] in_fp_child(s, b[j], d + 1, len, x) ==> in_fp(s, pos, d, len, x));
    // the siblings of slot i read the same in s1
    assert forall|j: int, x: int|
        0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies
            agree(s, s1, x) && (pos >= frozen ==> x != pos) && 0 <= x < s.next by {
        assert(child_wf(s, b[j], d + 1, path.push(j), frozen, len));
        lemma_fp_child_stored(s, b[j], d + 1, path.push(j), frozen, len, x);
        if pos < frozen {
            lemma_fp_frozen(s, pos, d, path, frozen, len, x);
        }
    }
    assert forall|j: int| 0 <= j < 16 && j != i implies {
        &&& child_wf(s1, #[trigger] b[j], d + 1, path.push(j), frozen, len)
        &&& forall|x: int| #[trigger] in_fp_child(s1, b[j], d + 1, len, x) == in_fp_child(s, b[j], d + 1, len, x)
        &&& forall|h2: Seq<u8>| #[trigger] lookup_child(s1, b[j], h2, d + 1, len) == lookup_child(s, b[j], h2, d + 1, len)
    } by {
        assert(child_wf(s, b[j], d + 1, path.push(j), frozen, len));
        lemma_frame_child(s, s1, b[j], d + 1, path.push(j), frozen, len);
    }
    // the block at pos is unchanged in s1
    if pos >= frozen {
        assert(!in_fp_child(s, b[i], d + 1, len, pos));
    }
    assert(agree(s, s1, pos));
    assert(s1.blocks[pos] == b);
    // reading through the updated block gives the map without h
    assert forall|h2: Seq<u8>| #[trigger] lookup_child(s1, b2[nibble(h2, d)], h2, d + 1, len) == if h2 == h {
        None
    } else {
        lookup(s, pos, h2, d, len)
    } by {
        lemma_nibble_range(h2, d);
        if nibble(h2, d) != i {
            assert(b2[nibble(h2, d)] == b[nibble(h2, d)]);
        }
    }
    let (t, p) = remove_finish(s1, b, ns, pos, i, d, frozen);
    let in_place = d == 0 || (collapse(b2) is None && pos >= frozen);
    if in_place {
        assert(t == write_slot(s1, pos, i, ns));
        assert(p == Ptr::Index(pos));
        assert forall|x: int| in_fp_child(s1, ns, d + 1, len, x) implies #[trigger] agree(s1, t, x) by {}
        lemma_frame_child(s1, t, ns, d + 1, path.push(i), frozen, len);
        assert forall|j: int, x: int|
            0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies agree(s, t, x) by {
            lemma_agree_trans(s, s1, t, x);
        }
        lemma_rebuild(s, t, pos, pos, i, ns, d, path, frozen, len);
        assert forall|x: int|
            0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) implies #[trigger] agree(s, t, x) by {
            if !(x < frozen) {
                assert(!in_fp_child(s, b[i], d + 1, len, x));
            }
            lemma_agree_trans(s, s1, t, x);
        }
        assert forall|h2: Seq<u8>| #[trigger] lookup_child(t, p, h2, d, len) == if h2 == h {
            None
        } else {
            lookup(s, pos, h2, d, len)
        } by {
            lemma_nibble_range(h2, d);
            assert(lookup_child(t, p, h2, d, len) == lookup(t, pos, h2, d, len));
            assert(lookup_child(s1, b2[nibble(h2, d)], h2, d + 1, len) == if h2 == h {
                None
            } else {
                lookup(s, pos, h2, d, len)
            });
        }
        assert forall|x: int| #[trigger] in_fp_child(t, p, d, len, x) implies in_fp(s, pos, d, len, x) || s.next <= x by {
            assert(in_fp(t, pos, d, len, x));
        }
    } else if collapse(b2) is None {
        // a committed block is copied before it's written
        let n = s1.next;
        assert(t == write_slot(append_block(s1, s1.blocks[pos]), n, i, ns));
        assert(p == Ptr::Index(n));
        assert forall|x: int| in_fp_child(s1, ns, d + 1, len, x) implies #[trigger] agree(s1, t, x) by {
            lemma_fp_child_stored(s1, ns, d + 1, path.push(i), frozen, len, x);
        }
        lemma_frame_child(s1, t, ns, d + 1, path.push(i), frozen, len);
        assert(!in_fp_child(t, ns, d + 1, len, n)) by {
            if in_fp_child(s1, ns, d + 1, len, n) {
                lemma_fp_child_stored(s1, ns, d + 1, path.push(i), frozen, len, n);
            }
        }
        assert forall|j: int, x: int|
            0 <= j < 16 && j != i && #[trigger] in_fp_child(s, b[j], d + 1, len, x) implies agree(s, t, x) by {
            lemma_agree_trans(s, s1, t, x);
        }
        lemma_rebuild(s, t, pos, n, i, ns, d, path, frozen, len);
        assert forall|x: int|
            0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) implies #[trigger] agree(s, t, x) by {
            if !(x < frozen) {
                assert(!in_fp_child(s, b[i], d + 1, len, x));
            }
            lemma_agree_trans(s, s1, t, x);
        }
        assert forall|h2: Seq<u8>| #[trigger] lookup_child(t, p, h2, d, len) == if h2 == h {
            None
        } else {
            lookup(s, pos, h2, d, len)
        } by {
            lemma_nibble_range(h2, d);
            assert(lookup_child(t, p, h2, d, len) == lookup(t, n, h2, d, len));
            assert(lookup_child(s1, b2[nibble(h2, d)], h2, d + 1, len) == if h2 == h {
                None
            } else {
                lookup(s, pos, h2, d, len)
            });
        }
        assert forall|x: int| #[trigger] in_fp_child(t, p, d, len, x) implies in_fp(s, pos, d, len, x) || s.next <= x by {
            assert(in_fp(t, n, d, len, x));
        }
    } else {
        // the block is replaced by its only entry
        assert(t == s1);
        lemma_scan(b2, 16);
        assert(scan(b2, 16) == Some(p));
        assert(!(p is Index));
        assert forall|x: int|
            0 <= x < s.next && (x < frozen || !in_fp(s, pos, d, len, x)) implies #[trigger] agree(s, t, x) by {
            if !(x < frozen) {
                assert(!in_fp_child(s, b[i], d + 1, len, x));
            }
        }
        if p is Empty {
            assert forall|h2: Seq<u8>| #[trigger] lookup_child(t, p, h2, d, len) == if h2 == h {
                None
            } else {
                lookup(s, pos, h2, d, len)
            } by {
                lemma_nibble_range(h2, d);
                assert(b2[nibble(h2, d)] is Empty);
                assert(lookup_child(s1, b2[nibble(h2, d)], h2, d + 1, len) == if h2 == h {
                    None
                } else {
                    lookup(s, pos, h2, d, len)
                });
            }
        } else {
            let q2 = p->Kv_0;
            let j = choose|j: int|
                0 <= j < 16 && b2[j] == p && forall|j2: int| 0 <= j2 < 16 && j2 != j ==> #[trigger] b2[j2] is Empty;
            // the pair belongs at slot j, so it belongs here too
            assert(kv_ok(s1, q2, path.push(j), len)) by {
                if j == i {
                    assert(child_wf(s1, ns, d + 1, path.push(i), frozen, len));
                } else {
                    assert(b[j] == p);
                    assert(child_wf(s, b[j], d + 1, path.push(j), frozen, len));
                    assert(in_fp_child(s, b[j], d + 1, len, q2));
                    assert(agree(s, s1, q2));
                }
            }
            lemma_kv_ok_prefix(s1, q2, path, j, len);
            assert(in_fp(s, pos, d, len, q2) || s.next <= q2) by {
                if j == i {
                    assert(in_fp_child(s1, ns, d + 1, len, q2));
                } else {
                    assert(b[j] == p);
                    assert(in_fp_child(s, b[j], d + 1, len, q2));
                }
            }
            assert forall|h2: Seq<u8>| #[trigger] lookup_child(t, p, h2, d, len) == if h2 == h {
                None
            } else {
                lookup(s, pos, h2, d, len)
            } by {
                lemma_nibble_range(h2, d);
                assert(lookup_child(s1, b2[nibble(h2, d)], h2, d + 1, len) == if h2 == h {
                    None
                } else {
                    lookup(s, pos, h2, d, len)
                });
                if nibble(h2, d) != j {
                    assert(b2[nibble(h2, d)] is Empty);
                    assert(nibble(s1.kvs[q2].hash, d) == path.push(j)[d]);
                }
            }
        }
    }
}

/// Removing from a well-formed block, which may be committed unless it is
/// the root.
pub proof fn lemma_remove(s: Store, pos: int, h: Seq<u8>, d: int, path: Seq<int>, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, pos, d, path, frozen, len),
        d == 0 ==> pos >= frozen,
        h.len() == len,
        follows(h, path),
    ensures
        remove(s, pos, h, d, frozen, len) is Some <==> lookup(s, pos, h, d, len) is Some,
        remove(s, pos, h, d, frozen, len) is Some ==> ({
            let (t, p) = remove(s, pos, h, d, frozen, len).unwrap();
            &&& remove_ok(s, t, p, pos, h, d, path, frozen, len)
            &&& d == 0 ==> p == Ptr::Index(pos)
        }),
    decreases 2 * len - d,
{
    let i = nibble(h, d);
    lemma_nibble_range(h, d);
    let b = s.blocks[pos];
    assert(child_wf(s, b[i], d + 1, path.push(i), frozen, len));
    assert(follows(h, path.push(i)));
    match b[i] {
        Ptr::Empty => {},
        Ptr::Kv(q) => {
            if s.kvs[q].hash == h {
                assert forall|h2: Seq<u8>| #[trigger] lookup_child(s, Ptr::Empty, h2, d + 1, len) == if h2 == h {
                    None
                } else {
                    lookup_child(s, b[i], h2, d + 1, len)
                } by {}
                lemma_remove_finish(s, s, Ptr::Empty, pos, h, d, path, frozen, len);
            }
        },
        Ptr::Index(q) => {
            lemma_remove(s, q, h, d + 1, path.push(i), frozen, len);
            if remove(s, q, h, d + 1, frozen, len) is Some {
                let (s1, ns) = remove(s, q, h, d + 1, frozen, len).unwrap();
                assert forall|x: int| #[trigger] in_fp_child(s, b[i], d + 1, len, x) == in_fp(s, q, d + 1, len, x) by {}
                assert forall|h2: Seq<u8>| #[trigger] lookup_child(s1, ns, h2, d + 1, len) == if h2 == h {
                    None
                } else {
                    lookup_child(s, b[i], h2, d + 1, len)
                } by {
                    assert(lookup_child(s, b[i], h2, d + 1, len) == lookup(s, q, h2, d + 1, len));
                }
                lemma_remove_finish(s, s1, ns, pos, h, d, path, frozen, len);
            }
        },
    }
}

// the hash map as a whole

/// Inserting into a hash map whose root block belongs to the current
/// transaction (the crate copies it first if it doesn't) never fails, and
/// gives the old map plus the new entry, without touching committed data.
pub proof fn theorem_put(s: Store, root: int, h: Seq<u8>, v: int, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, root, 0, Seq::empty(), frozen, len),
        root >= frozen,
        h.len() == len,
    ensures
        put(s, root, h, v, 0, frozen, len) is Some,
        ({
            let t = put(s, root, h, v, 0, frozen, len).unwrap();
            &&& store_ok(t, frozen)
            &&& wf(t, root, 0, Seq::empty(), frozen, len)
            &&& contents(t, root, len) == contents(s, root, len).insert(h, v)
            &&& forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x)
        }),
{
    lemma_put(s, root, h, v, 0, Seq::empty(), frozen, len);
    let t = put(s, root, h, v, 0, frozen, len).unwrap();
    assert(contents(t, root, len) =~= contents(s, root, len).insert(h, v));
}

/// Removing from a hash map fails exactly when the key isn't in it, and
/// otherwise gives the old map without the key, without touching committed
/// data.
pub proof fn theorem_remove(s: Store, root: int, h: Seq<u8>, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, root, 0, Seq::empty(), frozen, len),
        root >= frozen,
        h.len() == len,
    ensures
        remove(s, root, h, 0, frozen, len) is Some <==> contents(s, root, len).contains_key(h),
        remove(s, root, h, 0, frozen, len) is Some ==> ({
            let (t, p) = remove(s, root, h, 0, frozen, len).unwrap();
            &&& p == Ptr::Index(root)
            &&& store_ok(t, frozen)
            &&& wf(t, root, 0, Seq::empty(), frozen, len)
            &&& contents(t, root, len) == contents(s, root, len).remove(h)
            &&& forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x)
        }),
{
    lemma_remove(s, root, h, 0, Seq::empty(), frozen, len);
    if remove(s, root, h, 0, frozen, len) is Some {
        let (t, p) = remove(s, root, h, 0, frozen, len).unwrap();
        assert forall|h2: Seq<u8>| #[trigger] lookup(t, root, h2, 0, len) == if h2 == h {
            None
        } else {
            lookup(s, root, h2, 0, len)
        } by {
            assert(lookup_child(t, p, h2, 0, len) == lookup(t, root, h2, 0, len));
        }
        assert(contents(t, root, len) =~= contents(s, root, len).remove(h));
    }
}

/// Every hash map committed before a transaction (its root is below
/// `frozen`) reads the same in any store that kept the committed
/// positions, such as the store after any number of `put`s and `remove`s.
pub proof fn lemma_snapshot_unchanged(s: Store, t: Store, root: int, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        wf(s, root, 0, Seq::empty(), frozen, len),
        root < frozen,
        forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x),
    ensures
        wf(t, root, 0, Seq::empty(), frozen, len),
        contents(t, root, len) == contents(s, root, len),
{
    assert forall|x: int| in_fp(s, root, 0, len, x) implies #[trigger] agree(s, t, x) by {
        lemma_fp_frozen(s, root, 0, Seq::empty(), frozen, len, x);
        lemma_fp_stored(s, root, 0, Seq::empty(), frozen, len, x);
    }
    lemma_frame(s, t, root, 0, Seq::empty(), frozen, len);
    assert(contents(t, root, len) =~= contents(s, root, len));
}

/// An empty hash map, as `HashMapInit` writes it, is well-formed.
pub proof fn lemma_empty_map(s: Store, frozen: int, len: int)
    requires
        store_ok(s, frozen),
        len >= 1,
    ensures
        ({
            let t = append_block(s, empty_block());
            &&& store_ok(t, frozen)
            &&& wf(t, s.next, 0, Seq::empty(), frozen, len)
            &&& contents(t, s.next, len) == IMap::<Seq<u8>, int>::empty()
        }),
{
    let t = append_block(s, empty_block());
    let n = s.next;
    assert forall|j: int| 0 <= j < 16 implies child_wf(t, #[trigger] t.blocks[n][j], 1, Seq::<int>::empty().push(j), frozen, len) by {}
    assert(wf(t, n, 0, Seq::empty(), frozen, len));
    assert forall|h: Seq<u8>| #[trigger] lookup(t, n, h, 0, len) is None by {
        lemma_nibble_range(h, 0);
    }
    assert(contents(t, n, len) =~= IMap::<Seq<u8>, int>::empty());
}

} // verus!
