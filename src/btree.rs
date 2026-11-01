//! The count-augmented b-tree behind linked array lists.

use crate::core::Core;
use crate::database::Database;
use crate::error::Result;
use crate::format::*;
#[allow(unused_imports)]
use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};
use crate::store::DbStore;
use vstd::prelude::*;

verus! {

/// A node pointer plus the element count of its subtree (the right sibling
/// of a split).
#[derive(Debug, Clone, Copy)]
pub struct NodeRef {
    pub node_ptr: i64,
    pub count: i64,
}

/// A written node, plus its new right sibling if it overflowed.
#[derive(Debug, Clone, Copy)]
pub struct JoinResult {
    pub node_ptr: i64,
    pub count: i64,
    pub split: Option<NodeRef>,
}

#[derive(Debug, Clone, Copy)]
pub struct InsertResult {
    pub join: JoinResult,
    pub value_position: i64,
}

#[derive(Debug, Clone, Copy)]
pub struct WriteSlot {
    pub node_ptr: i64,
    pub value_position: i64,
    pub slot: Slot,
}

} // verus!

verus! {

pub(crate) fn index_slot(ptr: i64) -> (r: Slot)
    ensures
        r == (Slot { value: ptr, tag: Tag::Index, full: false }),
{
    Slot::new(ptr, Tag::Index)
}

/// `child_for_rank`, as a function of the counts: the child holding `rem`,
/// and the rank within it.
pub open spec fn cfr(counts: Seq<i64>, num: int, i: int, rem: int, inclusive: bool) -> (int, int)
    decreases num - i,
{
    if i + 1 < num && (rem > counts[i] || (!inclusive && rem == counts[i])) {
        cfr(counts, num, i + 1, rem - counts[i], inclusive)
    } else {
        (i, rem)
    }
}

/// The counts of the first `num` children are non-negative.
pub open spec fn counts_ok(node: BTreeNode) -> bool {
    &&& node.num <= BTREE_SLOT_COUNT
    &&& forall|j: int| 0 <= j < node.num ==> #[trigger] node.counts[j] >= 0
}

// the child of a branch that contains `rank`, and the rank within it. with
// `inclusive`, a rank at the end of a child (an insertion point) stays in it.
fn child_for_rank(node: &BTreeNode, rank: i64, inclusive: bool) -> (r: (usize, i64))
    requires
        counts_ok(*node),
        node.num >= 1,
    ensures
        r.0 < node.num,
        (r.0 as int, r.1 as int) == cfr(node.counts@, node.num as int, 0, rank as int, inclusive),
{
    let mut i = 0;
    let mut rem = rank;
    while i + 1 < node.num && (rem > node.counts[i] || (!inclusive && rem == node.counts[i]))
        invariant
            counts_ok(*node),
            i < node.num,
            cfr(node.counts@, node.num as int, i as int, rem as int, inclusive) == cfr(
                node.counts@,
                node.num as int,
                0,
                rank as int,
                inclusive,
            ),
        decreases node.num - i,
    {
        rem -= node.counts[i];
        i += 1;
    }
    (i, rem)
}

proof fn lemma_cfr_range_inner(counts: Seq<i64>, num: int, i: int, rem: int, inclusive: bool)
    requires
        0 <= i < num,
    ensures
        i <= cfr(counts, num, i, rem, inclusive).0 < num,
    decreases num - i,
{
    if i + 1 < num && (rem > counts[i] || (!inclusive && rem == counts[i])) {
        lemma_cfr_range_inner(counts, num, i + 1, rem - counts[i], inclusive);
    }
}

/// `child_for_rank` picks one of the node's children.
pub proof fn lemma_cfr_range(counts: Seq<i64>, num: int, i: int, rem: int, inclusive: bool)
    requires
        0 <= i < num,
    ensures
        0 <= cfr(counts, num, i, rem, inclusive).0 < num,
{
    lemma_cfr_range_inner(counts, num, i, rem, inclusive);
}

/// `child_for_rank`, for the other verified modules.
pub fn child_for_rank_pub(node: &BTreeNode, rank: i64, inclusive: bool) -> (r: (usize, i64))
    requires
        counts_ok(*node),
        node.num >= 1,
    ensures
        r.0 < node.num,
        (r.0 as int, r.1 as int) == cfr(node.counts@, node.num as int, 0, rank as int, inclusive),
{
    child_for_rank(node, rank, inclusive)
}

pub(crate) fn drop_child(branch: &mut BTreeNode, i: usize)
    requires
        old(branch).num <= BTREE_SLOT_COUNT,
        i < old(branch).num,
    ensures
        final(branch).kind == old(branch).kind,
        final(branch).values == old(branch).values,
        final(branch).num == old(branch).num - 1,
        final(branch).children@.subrange(0, final(branch).num as int) == old(branch).children@.subrange(0, old(branch).num as int).remove(i as int),
        final(branch).counts@.subrange(0, final(branch).num as int) == old(branch).counts@.subrange(0, old(branch).num as int).remove(i as int),
{
    let ghost c0 = branch.children@;
    let ghost n0 = branch.counts@;
    let num = branch.num;
    let mut j = i;
    while j + 1 < num
        invariant
            i <= j < num <= BTREE_SLOT_COUNT,
            branch.num == num,
            branch.kind == old(branch).kind,
            branch.values == old(branch).values,
            forall|k: int| 0 <= k < i ==> #[trigger] branch.children@[k] == c0[k],
            forall|k: int| 0 <= k < i ==> #[trigger] branch.counts@[k] == n0[k],
            forall|k: int| i <= k < j ==> #[trigger] branch.children@[k] == c0[k + 1],
            forall|k: int| i <= k < j ==> #[trigger] branch.counts@[k] == n0[k + 1],
            forall|k: int| j <= k < BTREE_SLOT_COUNT ==> #[trigger] branch.children@[k] == c0[k],
            forall|k: int| j <= k < BTREE_SLOT_COUNT ==> #[trigger] branch.counts@[k] == n0[k],
        decreases num - j,
    {
        branch.children[j] = branch.children[j + 1];
        branch.counts[j] = branch.counts[j + 1];
        j += 1;
    }
    branch.num = num - 1;
    branch.children[branch.num] = Slot::default();
    branch.counts[branch.num] = 0;
    assert(branch.children@.subrange(0, branch.num as int) =~= c0.subrange(0, num as int).remove(i as int));
    assert(branch.counts@.subrange(0, branch.num as int) =~= n0.subrange(0, num as int).remove(i as int));
}

/// The entries of a node: its values if it is a leaf, its children if it
/// is a branch.
pub open spec fn entries(node: BTreeNode) -> Seq<Slot> {
    match node.kind {
        BTreeNodeKind::Leaf => node.values@.subrange(0, node.num as int),
        BTreeNodeKind::Branch => node.children@.subrange(0, node.num as int),
    }
}

// two nodes of the same kind whose entries fit in one node, a before b
pub(crate) fn concat_nodes(a: &BTreeNode, b: &BTreeNode) -> (r: BTreeNode)
    requires
        a.kind == b.kind,
        a.num + b.num <= BTREE_SLOT_COUNT,
    ensures
        r.kind == a.kind,
        r.num == a.num + b.num,
        entries(r) == entries(*a) + entries(*b),
        a.kind == BTreeNodeKind::Branch ==> r.counts@.subrange(0, r.num as int) == a.counts@.subrange(0, a.num as int) + b.counts@.subrange(0, b.num as int),
{
    let mut node = *a;
    let mut j: usize = 0;
    while j < b.num
        invariant
            a.kind == b.kind,
            a.num + b.num <= BTREE_SLOT_COUNT,
            j <= b.num,
            node.kind == a.kind,
            node.num == a.num,
            forall|k: int| 0 <= k < a.num ==> #[trigger] node.values@[k] == a.values@[k],
            forall|k: int| 0 <= k < a.num ==> #[trigger] node.children@[k] == a.children@[k],
            forall|k: int| 0 <= k < a.num ==> #[trigger] node.counts@[k] == a.counts@[k],
            a.kind == BTreeNodeKind::Leaf ==> forall|k: int| a.num <= k < a.num + j ==> #[trigger] node.values@[k] == b.values@[k - a.num],
            a.kind == BTreeNodeKind::Branch ==> forall|k: int| a.num <= k < a.num + j ==> #[trigger] node.children@[k] == b.children@[k - a.num],
            a.kind == BTreeNodeKind::Branch ==> forall|k: int| a.num <= k < a.num + j ==> #[trigger] node.counts@[k] == b.counts@[k - a.num],
        decreases b.num - j,
    {
        match a.kind {
            BTreeNodeKind::Leaf => {
                node.values[a.num + j] = b.values[j];
            },
            BTreeNodeKind::Branch => {
                node.children[a.num + j] = b.children[j];
                node.counts[a.num + j] = b.counts[j];
            },
        }
        j += 1;
    }
    node.num = a.num + b.num;
    proof {
        match a.kind {
            BTreeNodeKind::Leaf => {
                assert(entries(node) =~= entries(*a) + entries(*b));
            },
            BTreeNodeKind::Branch => {
                assert(entries(node) =~= entries(*a) + entries(*b));
                assert(node.counts@.subrange(0, node.num as int) =~= a.counts@.subrange(0, a.num as int) + b.counts@.subrange(0, b.num as int));
            },
        }
    }
    node
}

pub(crate) fn leaf(values: &[Slot]) -> (r: BTreeNode)
    requires
        values@.len() <= BTREE_SLOT_COUNT,
    ensures
        r.kind == BTreeNodeKind::Leaf,
        r.num == values@.len(),
        entries(r) == values@,
{
    let mut node = BTreeNode::empty(BTreeNodeKind::Leaf, values.len());
    let mut j: usize = 0;
    while j < values.len()
        invariant
            values@.len() <= BTREE_SLOT_COUNT,
            j <= values@.len(),
            node.kind == BTreeNodeKind::Leaf,
            node.num == values@.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] node.values@[k] == values@[k],
        decreases values.len() - j,
    {
        node.values[j] = values[j];
        j += 1;
    }
    assert(entries(node) =~= values@);
    node
}

pub(crate) fn branch(children: &[Slot], counts: &[i64]) -> (r: BTreeNode)
    requires
        children@.len() <= BTREE_SLOT_COUNT,
        counts@.len() == children@.len(),
    ensures
        r.kind == BTreeNodeKind::Branch,
        r.num == children@.len(),
        entries(r) == children@,
        r.counts@.subrange(0, r.num as int) == counts@,
{
    let mut node = BTreeNode::empty(BTreeNodeKind::Branch, children.len());
    let mut j: usize = 0;
    while j < children.len()
        invariant
            children@.len() <= BTREE_SLOT_COUNT,
            counts@.len() == children@.len(),
            j <= children@.len(),
            node.kind == BTreeNodeKind::Branch,
            node.num == children@.len(),
            forall|k: int| 0 <= k < j ==> #[trigger] node.children@[k] == children@[k],
            forall|k: int| 0 <= k < j ==> #[trigger] node.counts@[k] == counts@[k],
        decreases children.len() - j,
    {
        node.children[j] = children[j];
        node.counts[j] = counts[j];
        j += 1;
    }
    assert(entries(node) =~= children@);
    assert(node.counts@.subrange(0, node.num as int) =~= counts@);
    node
}

} // verus!

impl<C: Core> Database<C> {


    // descend to the value slot at the given rank (0-based), returning a
    // pointer to it (its file position and current slot).
    // verified in btree_io.rs
    pub(crate) fn read_btree_slot(&self, root_ptr: i64, rank: i64) -> Result<SlotPointer> {
        crate::btree_io::read_btree_slot(&mut DbStore::new(self), root_ptr, rank)
    }

}
