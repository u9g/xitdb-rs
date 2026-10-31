//! Joining and splitting linked array list b-trees over a [`Store`]
//! (`btree_join` and `btree_split`, used by concatenation and slicing),
//! checked by Verus.
//!
//! These only ever append nodes: the file grows and every byte already in
//! it stays as it was ([`grows`]), so no committed data can change.

use crate::btree::{JoinResult, NodeRef, branch, index_slot, leaf, child_for_rank_pub};
use crate::btree_io::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// `g` is `f` with bytes appended.
pub open spec fn grows(f: Seq<u8>, g: Seq<u8>) -> bool {
    g.len() >= f.len() && g.subrange(0, f.len() as int) == f
}

pub proof fn lemma_grows_trans(f: Seq<u8>, g: Seq<u8>, h: Seq<u8>)
    requires
        grows(f, g),
        grows(g, h),
    ensures
        grows(f, h),
{
    assert(h.subrange(0, f.len() as int) =~= g.subrange(0, f.len() as int));
}

pub proof fn lemma_grows_refl(f: Seq<u8>)
    ensures
        grows(f, f),
{
    assert(f.subrange(0, f.len() as int) =~= f);
}

/// `btree_new_root`: an empty leaf, appended.
pub fn btree_new_root<S: Store>(s: &mut S) -> (r: Result<i64>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    write_btree_node(s, &BTreeNode::empty(BTreeNodeKind::Leaf, 0))
}

/// `btree_height`: the number of branch levels, following first children.
#[verifier::exec_allows_no_decreases_clause]
pub fn btree_height<S: Store>(s: &mut S, root_ptr: i64) -> (r: Result<usize>)
    ensures
        final(s).file() == old(s).file(),
{
    let mut ptr = root_ptr;
    let mut height: usize = 0;
    loop
        invariant
            s.file() == old(s).file(),
    {
        let node = read_btree_node(s, ptr)?;
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            return Ok(height);
        }
        if height == usize::MAX {
            return Err(Error::InvalidBTreeNode);
        }
        height += 1;
        ptr = node.children[0].value;
    }
}

/// `btree_make_root`: a root that split gets a new parent.
pub fn btree_make_root<S: Store>(s: &mut S, result: JoinResult) -> (r: Result<i64>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    match result.split {
        Some(split) => {
            let children = [index_slot(result.node_ptr), index_slot(split.node_ptr)];
            let counts = [result.count, split.count];
            let root = branch(&children, &counts);
            write_btree_node(s, &root)
        },
        None => {
            proof {
                lemma_grows_refl(s.file());
            }
            Ok(result.node_ptr)
        },
    }
}

/// `btree_assemble_leaf`: one leaf, or two halves.
pub fn btree_assemble_leaf<S: Store>(s: &mut S, vals: &[Slot]) -> (r: Result<JoinResult>)
    requires
        vals@.len() <= 2 * BTREE_SLOT_COUNT,
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    let total = vals.len();
    if total <= BTREE_SLOT_COUNT {
        let ptr = write_btree_node(s, &leaf(vals))?;
        return Ok(JoinResult { node_ptr: ptr, count: total as i64, split: None });
    }
    let left_n = total / 2;
    let ghost f0 = s.file();
    let left_ptr = write_btree_node(s, &leaf(slice_subrange(vals, 0, left_n)))?;
    let ghost f1 = s.file();
    let right_ptr = write_btree_node(s, &leaf(slice_subrange(vals, left_n, total)))?;
    proof {
        lemma_grows_trans(f0, f1, s.file());
    }
    Ok(JoinResult {
        node_ptr: left_ptr,
        count: left_n as i64,
        split: Some(NodeRef { node_ptr: right_ptr, count: (total - left_n) as i64 }),
    })
}

/// `btree_assemble_branch`: one branch, or two halves.
pub fn btree_assemble_branch<S: Store>(s: &mut S, children: &[Slot], counts: &[i64]) -> (r: Result<JoinResult>)
    requires
        children@.len() <= 2 * BTREE_SLOT_COUNT,
        counts@.len() == children@.len(),
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    let total = children.len();
    if total <= BTREE_SLOT_COUNT {
        let node = branch(children, counts);
        let ptr = write_btree_node(s, &node)?;
        return Ok(JoinResult { node_ptr: ptr, count: node.subtree_count(), split: None });
    }
    let left_n = total / 2;
    let left = branch(slice_subrange(children, 0, left_n), slice_subrange(counts, 0, left_n));
    let right = branch(slice_subrange(children, left_n, total), slice_subrange(counts, left_n, total));
    let ghost f0 = s.file();
    let left_ptr = write_btree_node(s, &left)?;
    let ghost f1 = s.file();
    let right_ptr = write_btree_node(s, &right)?;
    proof {
        lemma_grows_trans(f0, f1, s.file());
    }
    Ok(JoinResult {
        node_ptr: left_ptr,
        count: left.subtree_count(),
        split: Some(NodeRef { node_ptr: right_ptr, count: right.subtree_count() }),
    })
}

fn push_slots(v: &mut Vec<Slot>, a: &[Slot; BTREE_SLOT_COUNT], from: usize, to: usize)
    requires
        from <= to <= BTREE_SLOT_COUNT,
    ensures
        final(v)@.len() == old(v)@.len() + (to - from),
{
    let mut j = from;
    while j < to
        invariant
            from <= j <= to <= BTREE_SLOT_COUNT,
            v@.len() == old(v)@.len() + (j - from),
        decreases to - j,
    {
        v.push(a[j]);
        j += 1;
    }
}

fn push_counts(v: &mut Vec<i64>, a: &[i64; BTREE_SLOT_COUNT], from: usize, to: usize)
    requires
        from <= to <= BTREE_SLOT_COUNT,
    ensures
        final(v)@.len() == old(v)@.len() + (to - from),
{
    let mut j = from;
    while j < to
        invariant
            from <= j <= to <= BTREE_SLOT_COUNT,
            v@.len() == old(v)@.len() + (j - from),
        decreases to - j,
    {
        v.push(a[j]);
        j += 1;
    }
}

/// `btree_merge_nodes`: two nodes of equal height, `a` first, as one or
/// two nodes.
pub fn btree_merge_nodes<S: Store>(s: &mut S, a: &BTreeNode, b: &BTreeNode) -> (r: Result<JoinResult>)
    requires
        a.num <= BTREE_SLOT_COUNT,
        b.num <= BTREE_SLOT_COUNT,
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    if matches!(a.kind, BTreeNodeKind::Leaf) {
        let mut vals = Vec::new();
        push_slots(&mut vals, &a.values, 0, a.num);
        push_slots(&mut vals, &b.values, 0, b.num);
        return btree_assemble_leaf(s, vals.as_slice());
    }
    let mut children = Vec::new();
    push_slots(&mut children, &a.children, 0, a.num);
    push_slots(&mut children, &b.children, 0, b.num);
    let mut counts = Vec::new();
    push_counts(&mut counts, &a.counts, 0, a.num);
    push_counts(&mut counts, &b.counts, 0, b.num);
    btree_assemble_branch(s, children.as_slice(), counts.as_slice())
}

/// `btree_join_right`: `b` (shorter) joined into the rightmost spine of `a`.
pub fn btree_join_right<S: Store>(s: &mut S, a_ptr: i64, ha: usize, b_ptr: i64, hb: usize) -> (r: Result<JoinResult>)
    requires
        ha > hb,
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
    decreases ha,
{
    let a = read_btree_node(s, a_ptr)?;
    let ghost f0 = s.file();
    let last = match a.num.checked_sub(1) {
        Some(l) => l,
        None => return Err(Error::InvalidBTreeNode),
    };
    let sub = if ha - 1 == hb {
        let last_child = read_btree_node(s, a.children[last].value)?;
        let b = read_btree_node(s, b_ptr)?;
        btree_merge_nodes(s, &last_child, &b)?
    } else {
        btree_join_right(s, a.children[last].value, ha - 1, b_ptr, hb)?
    };
    let ghost f1 = s.file();

    let mut children = Vec::new();
    push_slots(&mut children, &a.children, 0, a.num);
    let mut counts = Vec::new();
    push_counts(&mut counts, &a.counts, 0, a.num);
    children.set(last, index_slot(sub.node_ptr));
    counts.set(last, sub.count);
    if let Some(split) = sub.split {
        children.push(index_slot(split.node_ptr));
        counts.push(split.count);
    }
    let r = btree_assemble_branch(s, children.as_slice(), counts.as_slice());
    proof {
        if r is Ok {
            lemma_grows_trans(f0, f1, s.file());
        }
    }
    r
}

/// `btree_join_left`: `a` (shorter) joined into the leftmost spine of `b`.
pub fn btree_join_left<S: Store>(s: &mut S, a_ptr: i64, ha: usize, b_ptr: i64, hb: usize) -> (r: Result<JoinResult>)
    requires
        hb > ha,
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
    decreases hb,
{
    let b = read_btree_node(s, b_ptr)?;
    let ghost f0 = s.file();
    if b.num == 0 {
        return Err(Error::InvalidBTreeNode);
    }
    let sub = if hb - 1 == ha {
        let a = read_btree_node(s, a_ptr)?;
        let first_child = read_btree_node(s, b.children[0].value)?;
        btree_merge_nodes(s, &a, &first_child)?
    } else {
        btree_join_left(s, a_ptr, ha, b.children[0].value, hb - 1)?
    };
    let ghost f1 = s.file();

    let mut children = Vec::new();
    children.push(index_slot(sub.node_ptr));
    let mut counts = Vec::new();
    counts.push(sub.count);
    if let Some(split) = sub.split {
        children.push(index_slot(split.node_ptr));
        counts.push(split.count);
    }
    push_slots(&mut children, &b.children, 1, b.num);
    push_counts(&mut counts, &b.counts, 1, b.num);
    let r = btree_assemble_branch(s, children.as_slice(), counts.as_slice());
    proof {
        if r is Ok {
            lemma_grows_trans(f0, f1, s.file());
        }
    }
    r
}

/// `btree_join`: the concatenation of two lists' trees.
pub fn btree_join<S: Store>(s: &mut S, root_a: i64, root_b: i64) -> (r: Result<i64>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    let ha = btree_height(s, root_a)?;
    let hb = btree_height(s, root_b)?;
    let ghost f0 = s.file();
    let result = if ha == hb {
        let a = read_btree_node(s, root_a)?;
        let b = read_btree_node(s, root_b)?;
        btree_merge_nodes(s, &a, &b)?
    } else if ha > hb {
        btree_join_right(s, root_a, ha, root_b, hb)?
    } else {
        btree_join_left(s, root_a, ha, root_b, hb)?
    };
    let ghost f1 = s.file();
    let r = btree_make_root(s, result);
    proof {
        if r is Ok {
            lemma_grows_trans(f0, f1, s.file());
            lemma_grows_refl(f0);
        }
    }
    r
}

/// `btree_subtree`: a run of sibling children as one tree.
fn btree_subtree<S: Store>(s: &mut S, children: &[Slot], counts: &[i64]) -> (r: Result<i64>)
    requires
        children@.len() <= BTREE_SLOT_COUNT,
        counts@.len() == children@.len(),
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    if children.len() == 0 {
        btree_new_root(s)
    } else if children.len() == 1 {
        proof {
            lemma_grows_refl(s.file());
        }
        Ok(children[0].value)
    } else {
        Ok(btree_assemble_branch(s, children, counts)?.node_ptr)
    }
}

/// `btree_split`: the roots of the values before and from `rank`.
#[verifier::exec_allows_no_decreases_clause]
pub fn btree_split<S: Store>(s: &mut S, root_ptr: i64, rank: i64) -> (r: Result<(i64, i64)>)
    ensures
        r is Ok ==> grows(old(s).file(), final(s).file()),
{
    let node = read_btree_node(s, root_ptr)?;
    let ghost f0 = s.file();
    if matches!(node.kind, BTreeNodeKind::Leaf) {
        let r = check_rank(rank, node.num, true)?;
        let left_ptr = write_btree_node(s, &leaf(slice_subrange(node.values.as_slice(), 0, r)))?;
        let ghost f1 = s.file();
        let right_ptr = write_btree_node(s, &leaf(slice_subrange(node.values.as_slice(), r, node.num)))?;
        proof {
            lemma_grows_trans(f0, f1, s.file());
        }
        return Ok((left_ptr, right_ptr));
    }
    if node.num == 0 {
        return Err(Error::InvalidBTreeNode);
    }
    let (i, rem) = child_for_rank_pub(&node, rank, true);
    let (child_left, child_right) = btree_split(s, node.children[i].value, rem)?;
    let ghost f1 = s.file();
    let left_sub = btree_subtree(s, slice_subrange(node.children.as_slice(), 0, i), slice_subrange(node.counts.as_slice(), 0, i))?;
    let ghost f2 = s.file();
    let right_sub = btree_subtree(
        s,
        slice_subrange(node.children.as_slice(), i + 1, node.num),
        slice_subrange(node.counts.as_slice(), i + 1, node.num),
    )?;
    let ghost f3 = s.file();
    let joined_left = btree_join(s, left_sub, child_left)?;
    let ghost f4 = s.file();
    let joined_right = btree_join(s, child_right, right_sub)?;
    proof {
        lemma_grows_trans(f0, f1, f2);
        lemma_grows_trans(f0, f2, f3);
        lemma_grows_trans(f0, f3, f4);
        lemma_grows_trans(f0, f4, s.file());
    }
    Ok((joined_left, joined_right))
}

} // verus!
