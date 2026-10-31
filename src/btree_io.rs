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
use crate::btree::{InsertResult, JoinResult, NodeRef, WriteSlot};
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

// mutations

/// `write_btree_node`: the node, appended.
pub fn write_btree_node<S: Store>(s: &mut S, node: &BTreeNode) -> (r: Result<i64>)
    ensures
        r is Ok ==> r.unwrap() == old(s).file().len() && final(s).file().len() >= old(s).file().len()
            && final(s).file().subrange(0, old(s).file().len() as int) == old(s).file(),
{
    let bytes = node.to_bytes();
    let p = append(s, bytes.as_slice())?;
    proof {
        assert(s.file().subrange(0, old(s).file().len() as int) =~= old(s).file());
    }
    Ok(p)
}

proof fn lemma_append_keeps(f: Seq<u8>, g: Seq<u8>, limit: int)
    requires
        0 <= limit <= f.len(),
        g.len() >= f.len(),
        g.subrange(0, f.len() as int) == f,
    ensures
        kept_below(f, g, limit),
{
    assert(g.subrange(0, limit) =~= f.subrange(0, limit));
}

/// The position of value `rank` of the node at `ptr`.
pub fn value_position(ptr: i64, rank: usize) -> (r: Result<i64>)
    requires
        rank <= BTREE_SLOT_COUNT,
    ensures
        r is Ok ==> r.unwrap() == ptr + 2 + 9 * rank,
{
    match ptr.checked_add((BTREE_NODE_HEADER_SIZE + rank * SLOT_LENGTH) as i64) {
        Some(p) => Ok(p),
        None => Err(Error::InvalidOffset),
    }
}

/// What a write in a transaction guarantees: nothing before `limit`
/// changed.
pub open spec fn tx_ok(f: Seq<u8>, g: Seq<u8>, limit: Option<i64>) -> bool {
    limit is Some ==> kept_below(f, g, limit.unwrap() as int)
}

fn slots_to_vec(a: &[Slot; BTREE_SLOT_COUNT], from: usize, to: usize) -> (r: Vec<Slot>)
    requires
        from <= to <= BTREE_SLOT_COUNT,
    ensures
        r@ == a@.subrange(from as int, to as int),
{
    let mut r = Vec::new();
    let mut j = from;
    while j < to
        invariant
            from <= j <= to <= BTREE_SLOT_COUNT,
            r@ == a@.subrange(from as int, j as int),
        decreases to - j,
    {
        r.push(a[j]);
        j += 1;
        assert(r@ =~= a@.subrange(from as int, j as int));
    }
    r
}

fn counts_to_vec(a: &[i64; BTREE_SLOT_COUNT], to: usize) -> (r: Vec<i64>)
    requires
        to <= BTREE_SLOT_COUNT,
    ensures
        r@ == a@.subrange(0, to as int),
{
    let mut r = Vec::new();
    let mut j: usize = 0;
    while j < to
        invariant
            j <= to <= BTREE_SLOT_COUNT,
            r@ == a@.subrange(0, j as int),
        decreases to - j,
    {
        r.push(a[j]);
        j += 1;
        assert(r@ =~= a@.subrange(0, j as int));
    }
    r
}

/// `btree_insert`: a placeholder slot inserted at `rank` under the node at
/// `node_ptr`. A cyclic corrupt file makes it recurse without end, so only
/// what it returns is proved.
#[verifier::exec_allows_no_decreases_clause]
pub fn btree_insert<S: Store>(s: &mut S, node_ptr: i64, rank: i64, limit: Option<i64>) -> (r: Result<InsertResult>)
    requires
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        (r is Ok && limit is Some) ==> r.unwrap().value_position >= limit.unwrap() && r.unwrap().join.node_ptr >= limit.unwrap(),
{
    let node = read_btree_node(s, node_ptr)?;
    let ghost f0 = s.file();
    match node.kind {
        BTreeNodeKind::Leaf => {
            // build the entries with a placeholder spliced in at `rank`. the
            // placeholder is a NONE slot marked full so that, if the caller
            // never writes a value (e.g. append_cursor), iteration still
            // counts it as an element rather than skipping it as padding.
            let r = check_rank(rank, node.num, true)?;
            let mut vals = slots_to_vec(&node.values, 0, r);
            vals.push(Slot::new(0, Tag::None).with_full(true));
            let mut j = r;
            while j < node.num
                invariant
                    r <= j <= node.num <= BTREE_SLOT_COUNT,
                    vals@.len() == j + 1,
                decreases node.num - j,
            {
                vals.push(node.values[j]);
                j += 1;
            }
            let total = vals.len();

            if total <= BTREE_SLOT_COUNT {
                let ptr = btree_write_node(s, &crate::btree::leaf(vals.as_slice()), node_ptr, limit)?;
                let vp = value_position(ptr, r)?;
                return Ok(InsertResult { join: JoinResult { node_ptr: ptr, count: total as i64, split: None }, value_position: vp });
            }

            // overflow: split into two leaves (reuse this node for the left half)
            let left_n = BTREE_SPLIT_COUNT;
            let left_ptr = btree_write_node(s, &crate::btree::leaf(slice_subrange(vals.as_slice(), 0, left_n)), node_ptr, limit)?;
            let ghost f1 = s.file();
            let right_ptr = write_btree_node(s, &crate::btree::leaf(slice_subrange(vals.as_slice(), left_n, total)))?;
            proof {
                if limit is Some {
                    lemma_append_keeps(f1, s.file(), limit.unwrap() as int);
                    lemma_kept_trans(f0, f1, s.file(), limit.unwrap() as int);
                }
            }
            let vp = if r < left_n { value_position(left_ptr, r)? } else { value_position(right_ptr, r - left_n)? };
            Ok(InsertResult {
                join: JoinResult {
                    node_ptr: left_ptr,
                    count: left_n as i64,
                    split: Some(NodeRef { node_ptr: right_ptr, count: (total - left_n) as i64 }),
                },
                value_position: vp,
            })
        },
        BTreeNodeKind::Branch => {
            if node.num == 0 {
                return Err(Error::InvalidBTreeNode);
            }
            // pick the child that contains `rank`
            let (i, rem) = crate::btree::child_for_rank_pub(&node, rank, true);
            let child = btree_insert(s, node.children[i].value, rem, limit)?;
            let ghost f1 = s.file();

            // rebuild this branch with the (possibly split) child
            let mut children = slots_to_vec(&node.children, 0, node.num);
            let mut counts = counts_to_vec(&node.counts, node.num);
            children.set(i, crate::btree::index_slot(child.join.node_ptr));
            counts.set(i, child.join.count);
            if let Some(split) = child.join.split {
                children.insert(i + 1, crate::btree::index_slot(split.node_ptr));
                counts.insert(i + 1, split.count);
            }
            let total = children.len();

            if total <= BTREE_SLOT_COUNT {
                let node2 = crate::btree::branch(children.as_slice(), counts.as_slice());
                let ptr = btree_write_node(s, &node2, node_ptr, limit)?;
                proof {
                    if limit is Some {
                        lemma_kept_trans(f0, f1, s.file(), limit.unwrap() as int);
                    }
                }
                return Ok(InsertResult {
                    join: JoinResult { node_ptr: ptr, count: node2.subtree_count(), split: None },
                    value_position: child.value_position,
                });
            }

            // overflow: split into two branches (reuse this node for the left half)
            let left_n = BTREE_SPLIT_COUNT;
            let left = crate::btree::branch(slice_subrange(children.as_slice(), 0, left_n), slice_subrange(counts.as_slice(), 0, left_n));
            let right = crate::btree::branch(slice_subrange(children.as_slice(), left_n, total), slice_subrange(counts.as_slice(), left_n, total));
            let left_ptr = btree_write_node(s, &left, node_ptr, limit)?;
            let ghost f2 = s.file();
            let right_ptr = write_btree_node(s, &right)?;
            proof {
                if limit is Some {
                    let l = limit.unwrap() as int;
                    lemma_kept_trans(f0, f1, f2, l);
                    lemma_append_keeps(f2, s.file(), l);
                    lemma_kept_trans(f0, f2, s.file(), l);
                }
            }
            Ok(InsertResult {
                join: JoinResult {
                    node_ptr: left_ptr,
                    count: left.subtree_count(),
                    split: Some(NodeRef { node_ptr: right_ptr, count: right.subtree_count() }),
                },
                value_position: child.value_position,
            })
        },
    }
}

/// `btree_get_for_write`: the slot at `rank`, copying committed nodes on
/// the way so the returned position is writable.
#[verifier::exec_allows_no_decreases_clause]
pub fn btree_get_for_write<S: Store>(s: &mut S, node_ptr: i64, rank: i64, limit: Option<i64>) -> (r: Result<WriteSlot>)
    requires
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        (r is Ok && limit is Some) ==> r.unwrap().value_position >= limit.unwrap(),
        (r is Ok && limit is Some) ==> (r.unwrap().node_ptr == node_ptr || r.unwrap().node_ptr >= limit.unwrap()),
{
    let mut node = read_btree_node(s, node_ptr)?;
    let ghost f0 = s.file();
    if matches!(node.kind, BTreeNodeKind::Leaf) {
        let rank = check_rank(rank, node.num, false)?;
        let reusable = match limit {
            Some(l) => node_ptr >= l,
            None => false,
        };
        let mut new_ptr = node_ptr;
        if !reusable {
            new_ptr = write_btree_node(s, &node)?;
            proof {
                if limit is Some {
                    lemma_append_keeps(f0, s.file(), limit.unwrap() as int);
                }
            }
        }
        let vp = value_position(new_ptr, rank)?;
        return Ok(WriteSlot { node_ptr: new_ptr, value_position: vp, slot: node.values[rank] });
    }
    if node.num == 0 {
        return Err(Error::InvalidBTreeNode);
    }
    let (i, rem) = crate::btree::child_for_rank_pub(&node, rank, false);
    let child_ptr = node.children[i].value;
    let child = btree_get_for_write(s, child_ptr, rem, limit)?;
    // if the child stayed put, this branch is unchanged too
    if child.node_ptr == child_ptr {
        return Ok(WriteSlot { node_ptr, ..child });
    }
    let ghost f1 = s.file();
    node.children[i] = crate::btree::index_slot(child.node_ptr);
    let new_ptr = btree_write_node(s, &node, node_ptr, limit)?;
    proof {
        if limit is Some {
            lemma_kept_trans(f0, f1, s.file(), limit.unwrap() as int);
        }
    }
    Ok(WriteSlot { node_ptr: new_ptr, ..child })
}

fn same_kind(a: BTreeNodeKind, b: BTreeNodeKind) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (BTreeNodeKind::Leaf, BTreeNodeKind::Leaf) => true,
        (BTreeNodeKind::Branch, BTreeNodeKind::Branch) => true,
        _ => false,
    }
}

/// `btree_remove`: the node left after removing the value at `rank`, for
/// the caller to write. Emptied children are dropped and underfull ones
/// merged with a neighbor.
#[verifier::exec_allows_no_decreases_clause]
pub fn btree_remove<S: Store>(s: &mut S, node_ptr: i64, rank: i64, limit: Option<i64>) -> (r: Result<BTreeNode>)
    requires
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> tx_ok(old(s).file(), final(s).file(), limit),
        r is Ok ==> r.unwrap().num <= BTREE_SLOT_COUNT,
{
    let mut node = read_btree_node(s, node_ptr)?;
    let ghost f0 = s.file();
    match node.kind {
        BTreeNodeKind::Leaf => {
            let r = check_rank(rank, node.num, false)?;
            let mut j = r;
            while j + 1 < node.num
                invariant
                    r <= j < node.num <= BTREE_SLOT_COUNT,
                decreases node.num - j,
            {
                node.values[j] = node.values[j + 1];
                j += 1;
            }
            node.num = node.num - 1;
            node.values[node.num] = Slot::new(0, Tag::None);
        },
        BTreeNodeKind::Branch => {
            if node.num == 0 {
                return Err(Error::InvalidBTreeNode);
            }
            let (i0, rem) = crate::btree::child_for_rank_pub(&node, rank, false);
            let mut i = i0;
            let child_ptr = node.children[i].value;
            let mut child = btree_remove(s, child_ptr, rem, limit)?;
            let ghost f1 = s.file();
            if child.num == 0 {
                crate::btree::drop_child(&mut node, i);
                return Ok(node);
            }
            if child.num < BTREE_SPLIT_COUNT && node.num > 1 {
                // the pair is i and its right neighbor, or its left one if it is last
                let (first, neighbor_i) = if i + 1 >= node.num { (i - 1, i - 1) } else { (i, i + 1) };
                let neighbor = read_btree_node(s, node.children[neighbor_i].value)?;
                if child.num + neighbor.num <= BTREE_SLOT_COUNT && same_kind(child.kind, neighbor.kind) {
                    child = if first == i {
                        crate::btree::concat_nodes(&child, &neighbor)
                    } else {
                        crate::btree::concat_nodes(&neighbor, &child)
                    };
                    crate::btree::drop_child(&mut node, first + 1);
                    i = first;
                }
            }
            let ptr = btree_write_node(s, &child, child_ptr, limit)?;
            proof {
                if limit is Some {
                    lemma_kept_trans(f0, f1, s.file(), limit.unwrap() as int);
                }
            }
            node.children[i] = crate::btree::index_slot(ptr);
            node.counts[i] = child.subtree_count();
        },
    }
    Ok(node)
}

} // verus!
