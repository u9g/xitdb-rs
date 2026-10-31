//! Old snapshots never change, checked by Verus.
//!
//! Every verified write keeps `tx_hdr_ok(f, g, limit)`: nothing before
//! `limit`, where the transaction started, changes apart from the root
//! header. This module proves what that means for readers. A read of an
//! array list, hash map or linked array list whose blocks all lie in
//! committed data (between the root header and `limit`) gives the same
//! result after the write as before it. Committed data only points at
//! committed data, so this holds for every read of a past moment, and by
//! induction for any sequence of writes.

#![allow(unused_imports)]

use crate::arith::*;
use crate::array_list_store::*;
use crate::btree_io::*;
use crate::bytes::*;
use crate::format::*;
use crate::map_store::*;
use crate::path_store::*;
use crate::slot::*;
use vstd::prelude::*;

verus! {

/// `f` and `g` agree before `upto`, except perhaps the root header.
pub open spec fn agree(f: Seq<u8>, g: Seq<u8>, upto: int) -> bool {
    &&& upto <= f.len()
    &&& upto <= g.len()
    &&& forall|i: int| 0 <= i < upto && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) ==> #[trigger] g[i] == f[i]
}

/// `n` bytes at `p` lie after the root header and before `upto`.
pub open spec fn fits(p: int, n: int, upto: int) -> bool {
    ROOT_HEADER_END <= p && p + n <= upto
}

/// A verified write's guarantee, for data before `limit`.
pub proof fn lemma_tx_agree(f: Seq<u8>, g: Seq<u8>, limit: int)
    requires
        tx_hdr_ok(f, g, limit),
        0 <= limit <= f.len(),
    ensures
        agree(f, g, limit),
{
}

pub proof fn lemma_agree_trans(f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, upto: int)
    requires
        agree(f, g, upto),
        agree(g, h, upto),
    ensures
        agree(f, h, upto),
{
    assert forall|i: int| 0 <= i < upto && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] h[i] == f[i] by {
        assert(g[i] == f[i]);
        assert(h[i] == g[i]);
    }
}

proof fn lemma_agree_symm(f: Seq<u8>, g: Seq<u8>, upto: int)
    requires
        agree(f, g, upto),
    ensures
        agree(g, f, upto),
{
    assert forall|i: int| 0 <= i < upto && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] f[i] == g[i] by {
        assert(g[i] == f[i]);
    }
}

proof fn lemma_agree_range(f: Seq<u8>, g: Seq<u8>, upto: int, p: int, n: int)
    requires
        agree(f, g, upto),
        fits(p, n, upto),
        n >= 0,
    ensures
        g.subrange(p, p + n) == f.subrange(p, p + n),
{
    assert forall|i: int| 0 <= i < n implies #[trigger] g.subrange(p, p + n)[i] == f.subrange(p, p + n)[i] by {
        assert(g[p + i] == f[p + i]);
    }
    assert(g.subrange(p, p + n) =~= f.subrange(p, p + n));
}

/// The slot at a committed position reads the same.
pub proof fn lemma_slot_frame(f: Seq<u8>, g: Seq<u8>, upto: int, p: int)
    requires
        agree(f, g, upto),
        fits(p, SLOT_LENGTH as int, upto),
    ensures
        slot_spec(g, p) == slot_spec(f, p),
{
    lemma_agree_range(f, g, upto, p, SLOT_LENGTH as int);
    if exists|s: Slot| slot_at(f, p, s) {
        let s = choose|s: Slot| slot_at(f, p, s);
        assert(slot_at(g, p, s));
        lemma_slot_spec(f, p, s);
        lemma_slot_spec(g, p, s);
    } else if exists|s: Slot| slot_at(g, p, s) {
        let s = choose|s: Slot| slot_at(g, p, s);
        assert(slot_at(f, p, s));
    }
}

/// The key/value pair at a committed position reads the same.
pub proof fn lemma_kv_frame(f: Seq<u8>, g: Seq<u8>, upto: int, p: int, hash_size: int)
    requires
        agree(f, g, upto),
        hash_size >= 0,
        fits(p, hash_size + 2 * SLOT_LENGTH, upto),
    ensures
        kv_spec(g, p, hash_size) == kv_spec(f, p, hash_size),
{
    lemma_agree_range(f, g, upto, p, hash_size + 2 * SLOT_LENGTH);
    if exists|kv: (Seq<u8>, Slot, Slot)| kv_at(f, p, hash_size, kv) {
        let kv = choose|kv: (Seq<u8>, Slot, Slot)| kv_at(f, p, hash_size, kv);
        assert(kv_at(g, p, hash_size, kv));
        lemma_kv_spec(f, p, hash_size, kv);
        lemma_kv_spec(g, p, hash_size, kv);
    } else if exists|kv: (Seq<u8>, Slot, Slot)| kv_at(g, p, hash_size, kv) {
        let kv = choose|kv: (Seq<u8>, Slot, Slot)| kv_at(g, p, hash_size, kv);
        assert(kv_at(f, p, hash_size, kv));
    }
}

// array lists

/// Every slot the array list walk reads lies in committed data.
pub open spec fn al_fits(f: Seq<u8>, upto: int, index_pos: int, key: int, shift: nat) -> bool
    decreases shift,
{
    if shift >= MAX_BRANCH_LENGTH {
        true
    } else {
        let slot_pos = index_pos + SLOT_LENGTH * digit(key, shift);
        &&& fits(slot_pos, SLOT_LENGTH as int, upto)
        &&& match slot_spec(f, slot_pos) {
            Some(s) => if shift != 0 && s.tag == Tag::Index {
                al_fits(f, upto, s.value as int, key, (shift - 1) as nat)
            } else {
                true
            },
            None => true,
        }
    }
}

/// An array list read in committed data gives the same result.
pub proof fn lemma_al_frame(f: Seq<u8>, g: Seq<u8>, upto: int, index_pos: int, key: int, shift: nat)
    requires
        agree(f, g, upto),
        al_fits(f, upto, index_pos, key, shift),
    ensures
        al_read(g, index_pos, key, shift) == al_read(f, index_pos, key, shift),
        al_fits(g, upto, index_pos, key, shift),
    decreases shift,
{
    if shift < MAX_BRANCH_LENGTH {
        let slot_pos = index_pos + SLOT_LENGTH * digit(key, shift);
        lemma_slot_frame(f, g, upto, slot_pos);
        if let Some(s) = slot_spec(f, slot_pos) {
            if shift != 0 && s.tag == Tag::Index {
                lemma_al_frame(f, g, upto, s.value as int, key, (shift - 1) as nat);
            }
        }
    }
}

// hash maps

/// Every slot and key/value pair the hash map walk reads lies in
/// committed data.
pub open spec fn map_fits(f: Seq<u8>, upto: int, index_pos: int, hash: Seq<u8>, offset: int, hash_size: int) -> bool
    decreases hash_size * 2 + 1 - offset,
{
    if offset > hash_size * 2 || offset < 0 {
        true
    } else {
        let slot_pos = index_pos + SLOT_LENGTH * nibble(hash, offset);
        &&& fits(slot_pos, SLOT_LENGTH as int, upto)
        &&& match slot_spec(f, slot_pos) {
            Some(slot) => if slot.tag == Tag::Index {
                map_fits(f, upto, slot.value as int, hash, offset + 1, hash_size)
            } else if slot.tag == Tag::KvPair {
                fits(slot.value as int, hash_size + 2 * SLOT_LENGTH, upto)
            } else {
                true
            },
            None => true,
        }
    }
}

/// A hash map read in committed data gives the same result.
pub proof fn lemma_map_frame(
    f: Seq<u8>,
    g: Seq<u8>,
    upto: int,
    index_pos: int,
    hash: Seq<u8>,
    offset: int,
    hash_size: int,
    target: MapTarget,
)
    requires
        agree(f, g, upto),
        hash_size >= 0,
        map_fits(f, upto, index_pos, hash, offset, hash_size),
    ensures
        map_read(g, index_pos, hash, offset, hash_size, target) == map_read(f, index_pos, hash, offset, hash_size, target),
        map_fits(g, upto, index_pos, hash, offset, hash_size),
    decreases hash_size * 2 + 1 - offset,
{
    if !(offset > hash_size * 2 || offset < 0) {
        let slot_pos = index_pos + SLOT_LENGTH * nibble(hash, offset);
        lemma_slot_frame(f, g, upto, slot_pos);
        if let Some(slot) = slot_spec(f, slot_pos) {
            if slot.tag == Tag::Index {
                lemma_map_frame(f, g, upto, slot.value as int, hash, offset + 1, hash_size, target);
            } else if slot.tag == Tag::KvPair {
                lemma_kv_frame(f, g, upto, slot.value as int, hash_size);
            }
        }
    }
}

// linked array lists

/// The bytes a node at `ptr` takes, by the kind byte there.
pub open spec fn bnode_size(f: Seq<u8>, ptr: int) -> int {
    if f[ptr] == kind_byte_spec(BTreeNodeKind::Leaf) { BTREE_LEAF_BLOCK_SIZE as int } else { BTREE_BRANCH_BLOCK_SIZE as int }
}

/// Every node the b-tree descent reads lies in committed data.
pub open spec fn btree_fits(f: Seq<u8>, upto: int, ptr: int, rank: int, depth: nat) -> bool
    decreases depth,
{
    if depth == 0 {
        true
    } else {
        &&& fits(ptr, BTREE_NODE_HEADER_SIZE as int, upto)
        &&& fits(ptr, bnode_size(f, ptr), upto)
        &&& (exists|n: BTreeNode| bnode_at(f, ptr, n)) ==> {
            let n = choose|n: BTreeNode| bnode_at(f, ptr, n);
            match n.kind {
                BTreeNodeKind::Leaf => true,
                BTreeNodeKind::Branch => n.num >= 1 ==> {
                    let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
                    btree_fits(f, upto, n.children[i].value as int, rem, (depth - 1) as nat)
                },
            }
        }
    }
}

proof fn lemma_kind_byte(a: BTreeNodeKind, b: BTreeNodeKind)
    requires
        kind_byte_spec(a) == kind_byte_spec(b),
    ensures
        a == b,
{
}

/// A node in committed data decodes the same in `g`.
proof fn lemma_bnode_frame(f: Seq<u8>, g: Seq<u8>, upto: int, ptr: int, n: BTreeNode)
    requires
        agree(f, g, upto),
        bnode_at(f, ptr, n),
        fits(ptr, if n.kind == BTreeNodeKind::Leaf { BTREE_LEAF_BLOCK_SIZE as int } else { BTREE_BRANCH_BLOCK_SIZE as int }, upto),
    ensures
        bnode_at(g, ptr, n),
{
    assert(g[ptr] == f[ptr]);
    assert(g[ptr + 1] == f[ptr + 1]);
    match n.kind {
        BTreeNodeKind::Leaf => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(g, ptr + 2 + 9 * i, n.values[i]) by {
                assert(slot_at(f, ptr + 2 + 9 * i, n.values[i]));
                lemma_agree_range(f, g, upto, ptr + 2 + 9 * i, SLOT_LENGTH as int);
            }
        },
        BTreeNodeKind::Branch => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(g, ptr + 2 + 9 * i, n.children[i]) by {
                assert(slot_at(f, ptr + 2 + 9 * i, n.children[i]));
                lemma_agree_range(f, g, upto, ptr + 2 + 9 * i, SLOT_LENGTH as int);
            }
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] n.counts[i] == u2i(be_u64_spec(g.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))) by {
                assert(n.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))));
                lemma_agree_range(f, g, upto, ptr + 146 + 8 * i, 8);
                assert(ptr + 154 + 8 * i == ptr + 146 + 8 * i + 8);
            }
        },
    }
}

/// Two decodings of the same node agree on everything the descent uses.
proof fn lemma_bnode_same(f: Seq<u8>, ptr: int, a: BTreeNode, b: BTreeNode)
    requires
        bnode_at(f, ptr, a),
        bnode_at(f, ptr, b),
    ensures
        a.kind == b.kind,
        a.num == b.num,
        a.kind == BTreeNodeKind::Leaf ==> a.values@ == b.values@,
        a.kind == BTreeNodeKind::Branch ==> a.children@ == b.children@ && a.counts@ == b.counts@,
{
    lemma_kind_byte(a.kind, b.kind);
    match a.kind {
        BTreeNodeKind::Leaf => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] a.values@[i] == b.values@[i] by {
                assert(slot_at(f, ptr + 2 + 9 * i, a.values[i]));
                assert(slot_at(f, ptr + 2 + 9 * i, b.values[i]));
                lemma_slot_encode_injective(a.values[i], b.values[i]);
            }
            assert(a.values@ =~= b.values@);
        },
        BTreeNodeKind::Branch => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] a.children@[i] == b.children@[i] by {
                assert(slot_at(f, ptr + 2 + 9 * i, a.children[i]));
                assert(slot_at(f, ptr + 2 + 9 * i, b.children[i]));
                lemma_slot_encode_injective(a.children[i], b.children[i]);
            }
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] a.counts@[i] == b.counts@[i] by {
                assert(a.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))));
                assert(b.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))));
            }
            assert(a.children@ =~= b.children@);
            assert(a.counts@ =~= b.counts@);
        },
    }
}

/// A linked array list read in committed data gives the same result.
pub proof fn lemma_btree_frame(f: Seq<u8>, g: Seq<u8>, upto: int, ptr: int, rank: int, depth: nat)
    requires
        agree(f, g, upto),
        btree_fits(f, upto, ptr, rank, depth),
    ensures
        btree_read(g, ptr, rank, depth) == btree_read(f, ptr, rank, depth),
        btree_fits(g, upto, ptr, rank, depth),
    decreases depth,
{
    if depth > 0 {
        assert(g[ptr] == f[ptr]);
        assert(bnode_size(g, ptr) == bnode_size(f, ptr));
        lemma_agree_symm(f, g, upto);
        let ef = exists|n: BTreeNode| bnode_at(f, ptr, n);
        let eg = exists|n: BTreeNode| bnode_at(g, ptr, n);
        if ef {
            let a = choose|n: BTreeNode| bnode_at(f, ptr, n);
            assert(a.kind == BTreeNodeKind::Leaf <==> f[ptr] == kind_byte_spec(BTreeNodeKind::Leaf)) by {
                if a.kind != BTreeNodeKind::Leaf {
                    assert(kind_byte_spec(a.kind) != kind_byte_spec(BTreeNodeKind::Leaf));
                }
            }
            lemma_bnode_frame(f, g, upto, ptr, a);
            assert(eg);
            let b = choose|n: BTreeNode| bnode_at(g, ptr, n);
            assert(b.kind == a.kind) by {
                lemma_kind_byte(a.kind, b.kind);
            }
            lemma_bnode_frame(g, f, upto, ptr, b);
            lemma_bnode_same(f, ptr, a, b);
            match a.kind {
                BTreeNodeKind::Leaf => {
                    if 0 <= rank < a.num {
                        assert(a.values[rank] == a.values@[rank]);
                        assert(b.values[rank] == b.values@[rank]);
                    }
                },
                BTreeNodeKind::Branch => {
                    if a.num >= 1 {
                        let (i, rem) = crate::btree::cfr(a.counts@, a.num as int, 0, rank, false);
                        assert(a.children[i] == a.children@[i]);
                        assert(b.children[i] == b.children@[i]);
                        lemma_btree_frame(f, g, upto, a.children[i].value as int, rem, (depth - 1) as nat);
                    }
                },
            }
        } else if eg {
            let b = choose|n: BTreeNode| bnode_at(g, ptr, n);
            assert(b.kind == BTreeNodeKind::Leaf <==> g[ptr] == kind_byte_spec(BTreeNodeKind::Leaf)) by {
                if b.kind != BTreeNodeKind::Leaf {
                    assert(kind_byte_spec(b.kind) != kind_byte_spec(BTreeNodeKind::Leaf));
                }
            }
            lemma_bnode_frame(g, f, upto, ptr, b);
        }
    }
}

// the theorem

/// Old snapshots never change. After a write that keeps
/// `tx_hdr_ok(f, g, limit)`, as every verified write does, any array list,
/// hash map or linked array list read whose blocks lie in committed data
/// gives the same result, and still lies in committed data, so this
/// extends to any sequence of writes.
pub proof fn theorem_snapshots_unchanged(f: Seq<u8>, g: Seq<u8>, limit: int)
    requires
        tx_hdr_ok(f, g, limit),
        0 <= limit <= f.len(),
    ensures
        forall|index_pos: int, key: int, shift: nat| #[trigger] al_fits(f, limit, index_pos, key, shift)
            ==> al_read(g, index_pos, key, shift) == al_read(f, index_pos, key, shift) && al_fits(g, limit, index_pos, key, shift),
        forall|index_pos: int, hash: Seq<u8>, offset: int, hash_size: int, target: MapTarget|
            map_fits(f, limit, index_pos, hash, offset, hash_size) && hash_size >= 0
            ==> map_read(g, index_pos, hash, offset, hash_size, target) == #[trigger] map_read(f, index_pos, hash, offset, hash_size, target)
                && map_fits(g, limit, index_pos, hash, offset, hash_size),
        forall|ptr: int, rank: int, depth: nat| #[trigger] btree_fits(f, limit, ptr, rank, depth)
            ==> btree_read(g, ptr, rank, depth) == btree_read(f, ptr, rank, depth) && btree_fits(g, limit, ptr, rank, depth),
{
    lemma_tx_agree(f, g, limit);
    assert forall|index_pos: int, key: int, shift: nat| #[trigger] al_fits(f, limit, index_pos, key, shift)
        implies al_read(g, index_pos, key, shift) == al_read(f, index_pos, key, shift) && al_fits(g, limit, index_pos, key, shift) by {
        lemma_al_frame(f, g, limit, index_pos, key, shift);
    }
    assert forall|index_pos: int, hash: Seq<u8>, offset: int, hash_size: int, target: MapTarget|
        map_fits(f, limit, index_pos, hash, offset, hash_size) && hash_size >= 0
        implies map_read(g, index_pos, hash, offset, hash_size, target) == #[trigger] map_read(f, index_pos, hash, offset, hash_size, target)
            && map_fits(g, limit, index_pos, hash, offset, hash_size) by {
        lemma_map_frame(f, g, limit, index_pos, hash, offset, hash_size, target);
    }
    assert forall|ptr: int, rank: int, depth: nat| #[trigger] btree_fits(f, limit, ptr, rank, depth)
        implies btree_read(g, ptr, rank, depth) == btree_read(f, ptr, rank, depth) && btree_fits(g, limit, ptr, rank, depth) by {
        lemma_btree_frame(f, g, limit, ptr, rank, depth);
    }
}

} // verus!
