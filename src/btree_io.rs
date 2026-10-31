//! B-tree nodes over a [`Store`], checked by Verus: reading a node
//! (`read_btree_node`), the copy-on-write node write (`btree_write_node`),
//! and the read-mode descent (`read_btree_slot`).
//!
//! A node is written in place only at or after `limit` (the crate's
//! `max(tx_start, frozen_at)`), and appended otherwise, so committed nodes
//! never change.

#[allow(unused_imports)]
use crate::array_list_store::*;
#[allow(unused_imports)]
use crate::bytes::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The linked array list node `node` is encoded at `ptr`.
pub open spec fn bnode_at(f: Seq<u8>, ptr: int, node: BTreeNode) -> bool {
    &&& 0 <= ptr
    &&& ptr + BTREE_NODE_HEADER_SIZE <= f.len()
    &&& f[ptr] == kind_byte_spec(node.kind)
    &&& f[ptr + 1] == node.num
    &&& node.num <= BTREE_SLOT_COUNT
    &&& match node.kind {
        BTreeNodeKind::Leaf => forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] slot_at(f, ptr + 2 + 9 * i, node.values[i]),
        BTreeNodeKind::Branch => {
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] slot_at(f, ptr + 2 + 9 * i, node.children[i])
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] node.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i)))
            &&& ptr + 146 + 128 <= f.len()
            &&& forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] node.counts[i] >= 0
        },
    }
}

/// `read_btree_node`: the node at `ptr`, with every count non-negative.
pub fn read_btree_node<S: Store>(s: &mut S, ptr: i64) -> (r: Result<BTreeNode>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> bnode_at(old(s).file(), ptr as int, r.unwrap()),
{
    let mut header = [0u8; BTREE_NODE_HEADER_SIZE];
    s.read_at(ptr, &mut header)?;
    let (kind, num) = decode_node_header(&header)?;
    let mut node = BTreeNode::empty(kind, num);
    let body_pos = match ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let ghost f = s.file();
    match kind {
        BTreeNodeKind::Leaf => {
            let mut body = [0u8; SLOT_LENGTH * BTREE_SLOT_COUNT];
            s.read_at(body_pos, &mut body)?;
            node.values = decode_slots(&body)?;
            proof {
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(f, ptr + 2 + 9 * i, node.values[i]) by {
                    assert(f.subrange(ptr + 2 + 9 * i, ptr + 2 + 9 * i + 9) =~= body@.subrange(i * 9, i * 9 + 9));
                }
            }
        },
        BTreeNodeKind::Branch => {
            let mut body = [0u8; (SLOT_LENGTH + 8) * BTREE_SLOT_COUNT];
            s.read_at(body_pos, &mut body)?;
            node.children = decode_slots(&body)?;
            node.counts = decode_counts(slice_subrange(body.as_slice(), SLOT_LENGTH * BTREE_SLOT_COUNT, (SLOT_LENGTH + 8) * BTREE_SLOT_COUNT))?;
            proof {
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] slot_at(f, ptr + 2 + 9 * i, node.children[i]) by {
                    assert(f.subrange(ptr + 2 + 9 * i, ptr + 2 + 9 * i + 9) =~= body@.subrange(i * 9, i * 9 + 9));
                }
                let cb = body@.subrange(144, 272);
                assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies #[trigger] node.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))) by {
                    assert(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i) =~= cb.subrange(i * 8, i * 8 + 8));
                }
            }
        },
    }
    proof {
        assert(header@[0] == f[ptr as int] && header@[1] == f[ptr + 1]);
    }
    Ok(node)
}

/// `btree_write_node`: the node is written in place at `old_ptr` if that
/// is at or after `limit`, and appended otherwise. Returns where it went.
pub fn btree_write_node<S: Store>(s: &mut S, node: &BTreeNode, old_ptr: i64, limit: Option<i64>) -> (r: Result<i64>)
    requires
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        (r is Ok && limit is Some) ==> r.unwrap() >= limit.unwrap() && kept_below(old(s).file(), final(s).file(), limit.unwrap() as int),
        (r is Ok && limit is None) ==> r.unwrap() == old(s).file().len() && final(s).file().subrange(0, old(s).file().len() as int) == old(s).file(),
{
    let reusable = match limit {
        Some(l) => old_ptr >= l,
        None => false,
    };
    let ghost f = s.file();
    let bytes = node.to_bytes();
    if reusable {
        s.write_at(old_ptr, bytes.as_slice())?;
        proof {
            lemma_overwrite_keeps(f, old_ptr as int, bytes@, limit.unwrap() as int);
        }
        return Ok(old_ptr);
    }
    let p = append(s, bytes.as_slice())?;
    proof {
        assert(s.file().subrange(0, f.len() as int) =~= f);
        if limit is Some {
            let l = limit.unwrap() as int;
            assert(s.file().subrange(0, l) =~= f.subrange(0, l));
        }
    }
    Ok(p)
}

/// The descent of `read_btree_slot` in at most `depth` levels: the
/// position of the value at `rank` and the slot there.
pub open spec fn btree_read(f: Seq<u8>, ptr: int, rank: int, depth: nat) -> Option<(int, Slot)>
    decreases depth,
{
    if depth == 0 {
        None
    } else if exists|n: BTreeNode| bnode_at(f, ptr, n) {
        let n = choose|n: BTreeNode| bnode_at(f, ptr, n);
        match n.kind {
            BTreeNodeKind::Leaf => if 0 <= rank < n.num {
                Some((ptr + 2 + 9 * rank, n.values[rank]))
            } else {
                None
            },
            BTreeNodeKind::Branch => if n.num >= 1 {
                let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
                btree_read(f, n.children[i].value as int, rem, (depth - 1) as nat)
            } else {
                None
            },
        }
    } else {
        None
    }
}

/// A node's encoding determines everything the descent reads.
pub proof fn lemma_bnode_unique(f: Seq<u8>, ptr: int, a: BTreeNode, b: BTreeNode)
    requires
        bnode_at(f, ptr, a),
        bnode_at(f, ptr, b),
    ensures
        a.kind == b.kind,
        a.num == b.num,
        a.kind == BTreeNodeKind::Leaf ==> a.values@ == b.values@,
        a.kind == BTreeNodeKind::Branch ==> a.children@ == b.children@ && a.counts@ == b.counts@,
{
    match (a.kind, b.kind) {
        (BTreeNodeKind::Leaf, BTreeNodeKind::Leaf) => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.values@[i] == b.values@[i] by {
                assert(slot_at(f, ptr + 2 + 9 * i, a.values[i]));
                assert(slot_at(f, ptr + 2 + 9 * i, b.values[i]));
                lemma_slot_encode_injective(a.values[i], b.values[i]);
            }
            assert(a.values@ =~= b.values@);
        },
        (BTreeNodeKind::Branch, BTreeNodeKind::Branch) => {
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.children@[i] == b.children@[i] by {
                assert(slot_at(f, ptr + 2 + 9 * i, a.children[i]));
                assert(slot_at(f, ptr + 2 + 9 * i, b.children[i]));
                lemma_slot_encode_injective(a.children[i], b.children[i]);
            }
            assert forall|i: int| 0 <= i < BTREE_SLOT_COUNT implies a.counts@[i] == b.counts@[i] by {
                assert(a.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))));
                assert(b.counts[i] == u2i(be_u64_spec(f.subrange(ptr + 146 + 8 * i, ptr + 154 + 8 * i))));
            }
            assert(a.children@ =~= b.children@);
            assert(a.counts@ =~= b.counts@);
        },
        _ => {},
    }
}

/// One level of the descent, for the node the code read.
proof fn lemma_btree_read_step(f: Seq<u8>, ptr: int, rank: int, depth: nat, n: BTreeNode)
    requires
        bnode_at(f, ptr, n),
        depth >= 1,
    ensures
        n.kind == BTreeNodeKind::Leaf ==> btree_read(f, ptr, rank, depth) == if 0 <= rank < n.num {
            Some((ptr + 2 + 9 * rank, n.values[rank]))
        } else {
            None
        },
        (n.kind == BTreeNodeKind::Branch && n.num >= 1) ==> btree_read(f, ptr, rank, depth) == {
            let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
            btree_read(f, n.children[i].value as int, rem, (depth - 1) as nat)
        },
{
    let c = choose|m: BTreeNode| bnode_at(f, ptr, m);
    lemma_bnode_unique(f, ptr, n, c);
    if n.kind == BTreeNodeKind::Leaf && 0 <= rank < n.num {
        assert(c.values@[rank] == n.values@[rank]);
    }
    if n.kind == BTreeNodeKind::Branch && n.num >= 1 {
        let (i, rem) = crate::btree::cfr(n.counts@, n.num as int, 0, rank, false);
        assert(crate::btree::cfr(c.counts@, c.num as int, 0, rank, false) == (i, rem));
        crate::btree::lemma_cfr_range(n.counts@, n.num as int, 0, rank, false);
        assert(c.children@[i] == n.children@[i]);
    }
}

/// `read_btree_slot`: the descent to the value at `rank`. A corrupt file
/// whose node pointers form a cycle makes it loop, so only what it returns
/// is proved, not that it returns.
#[verifier::exec_allows_no_decreases_clause]
pub fn read_btree_slot<S: Store>(s: &mut S, root_ptr: i64, rank: i64) -> (r: Result<SlotPointer>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().position is Some && exists|d: nat| #[trigger] btree_read(old(s).file(), root_ptr as int, rank as int, d)
            == Some((r.unwrap().position.unwrap() as int, r.unwrap().slot)),
{
    let ghost f = s.file();
    let mut node_ptr = root_ptr;
    let mut rem = rank;
    let ghost mut k: nat = 0;
    loop
        invariant
            s.file() == f,
            f == old(s).file(),
            forall|d: nat| #[trigger] btree_read(f, node_ptr as int, rem as int, d) is Some ==> btree_read(f, root_ptr as int, rank as int, d + k)
                == btree_read(f, node_ptr as int, rem as int, d),
    {
        let node = read_btree_node(s, node_ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let r = check_rank(rem, node.num, false)?;
            let pos = match node_ptr.checked_add((BTREE_NODE_HEADER_SIZE + r * SLOT_LENGTH) as i64) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            proof {
                lemma_btree_read_step(f, node_ptr as int, rem as int, 1, node);
                assert(btree_read(f, root_ptr as int, rank as int, 1 + k) == Some((pos as int, node.values[r as int])));
            }
            return Ok(SlotPointer::new(Some(pos), node.values[r]));
        }
        if node.num == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        let (i, next_rem) = crate::btree::child_for_rank_pub(&node, rem, false);
        let ghost old_ptr = node_ptr;
        let ghost old_rem = rem;
        rem = next_rem;
        node_ptr = node.children[i].value;
        proof {
            assert forall|d: nat| #[trigger] btree_read(f, node_ptr as int, rem as int, d) is Some implies btree_read(f, root_ptr as int, rank as int, d + k + 1)
                == btree_read(f, node_ptr as int, rem as int, d) by {
                lemma_btree_read_step(f, old_ptr as int, old_rem as int, d + 1, node);
                assert(((d + 1) - 1) as nat == d);
            }
            k = k + 1;
        }
    }
}

} // verus!
