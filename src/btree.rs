//! The count-augmented b-tree behind linked array lists.

use crate::core::Core;
use crate::database::Database;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::{SLOT_LENGTH, Slot, SlotPointer, Tag};
use crate::store::DbStore;
use vstd::prelude::*;

/// A node pointer plus the element count of its subtree (the right sibling
/// of a split).
#[derive(Debug, Clone, Copy)]
pub(crate) struct NodeRef {
    pub node_ptr: i64,
    pub count: i64,
}

/// A written node, plus its new right sibling if it overflowed.
#[derive(Debug, Clone, Copy)]
pub(crate) struct JoinResult {
    pub node_ptr: i64,
    pub count: i64,
    pub split: Option<NodeRef>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct InsertResult {
    pub join: JoinResult,
    pub value_position: i64,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct WriteSlot {
    pub node_ptr: i64,
    pub value_position: i64,
    pub slot: Slot,
}

fn value_position(node_ptr: i64, rank: usize) -> i64 {
    node_ptr + (BTREE_NODE_HEADER_SIZE + rank * SLOT_LENGTH) as i64
}

verus! {

fn index_slot(ptr: i64) -> (r: Slot)
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

fn drop_child(branch: &mut BTreeNode, i: usize)
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
fn concat_nodes(a: &BTreeNode, b: &BTreeNode) -> (r: BTreeNode)
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

fn leaf(values: &[Slot]) -> (r: BTreeNode)
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

fn branch(children: &[Slot], counts: &[i64]) -> (r: BTreeNode)
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
    // verified in btree_io.rs
    pub(crate) fn read_btree_node(&self, ptr: i64) -> Result<BTreeNode> {
        crate::btree_io::read_btree_node(&mut DbStore::new(self), ptr)
    }


    // appends the node as a fresh block and returns its position
    pub(crate) fn write_btree_node(&self, node: &BTreeNode) -> Result<i64> {
        self.append(&node.to_bytes())
    }

    // a node is safe to mutate in place when it was created in the current
    // transaction after the writing cursor's freeze point (see is_old), since
    // no committed moment and no pre-concat sharing can reference it. concat
    // advances tx_start (an implicit freeze) precisely so its shared subtrees
    // fall below it here.
    pub(crate) fn btree_reusable(&self, ptr: i64, frozen_at: i64) -> bool {
        // outside a transaction nothing can be reused
        matches!(self.is_old(ptr, frozen_at), Ok(false))
    }

    // write a new version of a node, reusing old_ptr's position in place if
    // that node belongs to this transaction, otherwise appending a copy
    // verified in btree_io.rs
    pub(crate) fn btree_write_node(&self, node: &BTreeNode, old_ptr: i64, frozen_at: i64) -> Result<i64> {
        let limit = self.tx_start.get().map(|tx_start| tx_start.max(frozen_at));
        crate::btree_io::btree_write_node(&mut DbStore::new(self), node, old_ptr, limit)
    }

    pub(crate) fn btree_new_root(&self) -> Result<i64> {
        self.write_btree_node(&BTreeNode::empty(BTreeNodeKind::Leaf, 0))
    }

    // descend to the value slot at the given rank (0-based), returning a
    // pointer to it (its file position and current slot).
    // verified in btree_io.rs
    pub(crate) fn read_btree_slot(&self, root_ptr: i64, rank: i64) -> Result<SlotPointer> {
        crate::btree_io::read_btree_slot(&mut DbStore::new(self), root_ptr, rank)
    }

    // insert a placeholder slot at `rank` within the subtree at node_ptr,
    // writing new nodes along the path. the caller fills in the value at the
    // returned value_position.
    pub(crate) fn btree_insert(&self, node_ptr: i64, rank: i64, frozen_at: i64) -> Result<InsertResult> {
        let node = self.read_btree_node(node_ptr)?;
        match node.kind {
            BTreeNodeKind::Leaf => {
                // build the entries with a placeholder spliced in at `rank`. the
                // placeholder is a NONE slot marked full so that, if the caller
                // never writes a value (e.g. append_cursor), iteration still
                // counts it as an element rather than skipping it as padding.
                let r = check_rank(rank, node.num, true)?;
                let mut vals = Vec::with_capacity(BTREE_SLOT_COUNT + 1);
                vals.extend_from_slice(&node.values[..r]);
                vals.push(Slot::default().with_full(true));
                vals.extend_from_slice(&node.values[r..node.num]);
                let total = vals.len();

                if total <= BTREE_SLOT_COUNT {
                    let ptr = self.btree_write_node(&leaf(&vals), node_ptr, frozen_at)?;
                    return Ok(InsertResult {
                        join: JoinResult { node_ptr: ptr, count: total as i64, split: None },
                        value_position: value_position(ptr, r),
                    });
                }

                // overflow: split into two leaves (reuse this node for the left half)
                let left_n = BTREE_SPLIT_COUNT;
                let left_ptr = self.btree_write_node(&leaf(&vals[..left_n]), node_ptr, frozen_at)?;
                let right_ptr = self.write_btree_node(&leaf(&vals[left_n..]))?;
                let value_position = if r < left_n {
                    value_position(left_ptr, r)
                } else {
                    value_position(right_ptr, r - left_n)
                };
                Ok(InsertResult {
                    join: JoinResult {
                        node_ptr: left_ptr,
                        count: left_n as i64,
                        split: Some(NodeRef { node_ptr: right_ptr, count: (total - left_n) as i64 }),
                    },
                    value_position,
                })
            }
            BTreeNodeKind::Branch => {
                // pick the child that contains `rank`
                let (i, rem) = child_for_rank(&node, rank, true);
                let child = self.btree_insert(node.children[i].value, rem, frozen_at)?;

                // rebuild this branch with the (possibly split) child
                let mut children = node.children[..node.num].to_vec();
                let mut counts = node.counts[..node.num].to_vec();
                children[i] = index_slot(child.join.node_ptr);
                counts[i] = child.join.count;
                if let Some(split) = child.join.split {
                    children.insert(i + 1, index_slot(split.node_ptr));
                    counts.insert(i + 1, split.count);
                }
                let total = children.len();

                if total <= BTREE_SLOT_COUNT {
                    let node = branch(&children, &counts);
                    let ptr = self.btree_write_node(&node, node_ptr, frozen_at)?;
                    return Ok(InsertResult {
                        join: JoinResult { node_ptr: ptr, count: node.subtree_count(), split: None },
                        value_position: child.value_position,
                    });
                }

                // overflow: split into two branches (reuse this node for the left half)
                let left_n = BTREE_SPLIT_COUNT;
                let left = branch(&children[..left_n], &counts[..left_n]);
                let right = branch(&children[left_n..], &counts[left_n..]);
                let left_ptr = self.btree_write_node(&left, node_ptr, frozen_at)?;
                let right_ptr = self.write_btree_node(&right)?;
                Ok(InsertResult {
                    join: JoinResult {
                        node_ptr: left_ptr,
                        count: left.subtree_count(),
                        split: Some(NodeRef { node_ptr: right_ptr, count: right.subtree_count() }),
                    },
                    value_position: child.value_position,
                })
            }
        }
    }

    // descend to the value slot at `rank` for writing, copy-on-writing only
    // the nodes that belong to a past transaction. the element count is
    // unchanged, so when the whole path is already this-transaction nothing
    // is rewritten and the caller writes straight into the existing leaf.
    pub(crate) fn btree_get_for_write(&self, node_ptr: i64, rank: i64, frozen_at: i64) -> Result<WriteSlot> {
        let mut node = self.read_btree_node(node_ptr)?;
        if node.kind == BTreeNodeKind::Leaf {
            let rank = check_rank(rank, node.num, false)?;
            let mut new_ptr = node_ptr;
            if !self.btree_reusable(node_ptr, frozen_at) {
                new_ptr = self.write_btree_node(&node)?;
            }
            return Ok(WriteSlot {
                node_ptr: new_ptr,
                value_position: value_position(new_ptr, rank),
                slot: node.values[rank],
            });
        }
        let (i, rem) = child_for_rank(&node, rank, false);
        let child_ptr = node.children[i].value;
        let child = self.btree_get_for_write(child_ptr, rem, frozen_at)?;
        // if the child stayed put, this branch is unchanged too
        if child.node_ptr == child_ptr {
            return Ok(WriteSlot { node_ptr, ..child });
        }
        node.children[i] = index_slot(child.node_ptr);
        let new_ptr = self.btree_write_node(&node, node_ptr, frozen_at)?;
        Ok(WriteSlot { node_ptr: new_ptr, ..child })
    }

    // remove the element at `rank` within the subtree at node_ptr, returning
    // the node left behind for the caller to write. an emptied child is
    // dropped and a child left under half full is merged with a neighbor it
    // fits with, so every leaf stays at the same depth.
    pub(crate) fn btree_remove(&self, node_ptr: i64, rank: i64, frozen_at: i64) -> Result<BTreeNode> {
        let mut node = self.read_btree_node(node_ptr)?;
        match node.kind {
            BTreeNodeKind::Leaf => {
                let r = check_rank(rank, node.num, false)?;
                node.values.copy_within(r + 1..node.num, r);
                node.num -= 1;
                node.values[node.num] = Slot::default();
            }
            BTreeNodeKind::Branch => {
                let (mut i, rem) = child_for_rank(&node, rank, false);
                let child_ptr = node.children[i].value;
                let mut child = self.btree_remove(child_ptr, rem, frozen_at)?;
                if child.num == 0 {
                    drop_child(&mut node, i);
                    return Ok(node);
                }
                if child.num < BTREE_SPLIT_COUNT && node.num > 1 {
                    // the pair is i and its right neighbor, or its left one if it is last
                    let (first, neighbor_i) = if i + 1 >= node.num { (i - 1, i - 1) } else { (i, i + 1) };
                    let neighbor = self.read_btree_node(node.children[neighbor_i].value)?;
                    if child.num + neighbor.num <= BTREE_SLOT_COUNT {
                        child = if first == i {
                            concat_nodes(&child, &neighbor)
                        } else {
                            concat_nodes(&neighbor, &child)
                        };
                        drop_child(&mut node, first + 1);
                        i = first;
                    }
                }
                let ptr = self.btree_write_node(&child, child_ptr, frozen_at)?;
                node.children[i] = index_slot(ptr);
                node.counts[i] = child.subtree_count();
            }
        }
        Ok(node)
    }

    // height of a tree = number of branch levels above the leaves
    fn btree_height(&self, root_ptr: i64) -> Result<usize> {
        let mut ptr = root_ptr;
        let mut height = 0;
        loop {
            let node = self.read_btree_node(ptr)?;
            if node.kind == BTreeNodeKind::Leaf {
                return Ok(height);
            }
            height += 1;
            ptr = node.children[0].value;
        }
    }

    // turns a join result into a root pointer, growing the tree a level if
    // the old root split
    pub(crate) fn btree_make_root(&self, result: JoinResult) -> Result<i64> {
        match result.split {
            Some(split) => {
                let root = branch(
                    &[index_slot(result.node_ptr), index_slot(split.node_ptr)],
                    &[result.count, split.count],
                );
                self.write_btree_node(&root)
            }
            None => Ok(result.node_ptr),
        }
    }

    // write `vals` as one leaf, or split into two balanced leaves if it
    // exceeds the node capacity
    fn btree_assemble_leaf(&self, vals: &[Slot]) -> Result<JoinResult> {
        let total = vals.len();
        if total <= BTREE_SLOT_COUNT {
            let ptr = self.write_btree_node(&leaf(vals))?;
            return Ok(JoinResult { node_ptr: ptr, count: total as i64, split: None });
        }
        let left_n = total / 2;
        let left_ptr = self.write_btree_node(&leaf(&vals[..left_n]))?;
        let right_ptr = self.write_btree_node(&leaf(&vals[left_n..]))?;
        Ok(JoinResult {
            node_ptr: left_ptr,
            count: left_n as i64,
            split: Some(NodeRef { node_ptr: right_ptr, count: (total - left_n) as i64 }),
        })
    }

    // write `children`/`counts` as one branch, or split into two balanced branches
    fn btree_assemble_branch(&self, children: &[Slot], counts: &[i64]) -> Result<JoinResult> {
        let total = children.len();
        if total <= BTREE_SLOT_COUNT {
            let node = branch(children, counts);
            let ptr = self.write_btree_node(&node)?;
            return Ok(JoinResult { node_ptr: ptr, count: node.subtree_count(), split: None });
        }
        let left_n = total / 2;
        let left = branch(&children[..left_n], &counts[..left_n]);
        let right = branch(&children[left_n..], &counts[left_n..]);
        let left_ptr = self.write_btree_node(&left)?;
        let right_ptr = self.write_btree_node(&right)?;
        Ok(JoinResult {
            node_ptr: left_ptr,
            count: left.subtree_count(),
            split: Some(NodeRef { node_ptr: right_ptr, count: right.subtree_count() }),
        })
    }

    // merge two nodes of equal height (a precedes b) into one or two nodes
    fn btree_merge_nodes(&self, a: &BTreeNode, b: &BTreeNode) -> Result<JoinResult> {
        if a.kind == BTreeNodeKind::Leaf {
            let vals = [&a.values[..a.num], &b.values[..b.num]].concat();
            return self.btree_assemble_leaf(&vals);
        }
        let children = [&a.children[..a.num], &b.children[..b.num]].concat();
        let counts = [&a.counts[..a.num], &b.counts[..b.num]].concat();
        self.btree_assemble_branch(&children, &counts)
    }

    // join b (shorter) into the rightmost spine of a (taller), at height hb
    fn btree_join_right(&self, a_ptr: i64, ha: usize, b_ptr: i64, hb: usize) -> Result<JoinResult> {
        let a = self.read_btree_node(a_ptr)?;
        let last = a.num.checked_sub(1).ok_or(Error::InvalidBTreeNode)?;
        let sub = if ha - 1 == hb {
            let last_child = self.read_btree_node(a.children[last].value)?;
            let b = self.read_btree_node(b_ptr)?;
            self.btree_merge_nodes(&last_child, &b)?
        } else {
            self.btree_join_right(a.children[last].value, ha - 1, b_ptr, hb)?
        };

        let mut children = a.children[..a.num].to_vec();
        let mut counts = a.counts[..a.num].to_vec();
        children[last] = index_slot(sub.node_ptr);
        counts[last] = sub.count;
        if let Some(split) = sub.split {
            children.push(index_slot(split.node_ptr));
            counts.push(split.count);
        }
        self.btree_assemble_branch(&children, &counts)
    }

    // join a (shorter) into the leftmost spine of b (taller), at height ha
    fn btree_join_left(&self, a_ptr: i64, ha: usize, b_ptr: i64, hb: usize) -> Result<JoinResult> {
        let b = self.read_btree_node(b_ptr)?;
        let sub = if hb - 1 == ha {
            let a = self.read_btree_node(a_ptr)?;
            let first_child = self.read_btree_node(b.children[0].value)?;
            self.btree_merge_nodes(&a, &first_child)?
        } else {
            self.btree_join_left(a_ptr, ha, b.children[0].value, hb - 1)?
        };

        let mut children = vec![index_slot(sub.node_ptr)];
        let mut counts = vec![sub.count];
        if let Some(split) = sub.split {
            children.push(index_slot(split.node_ptr));
            counts.push(split.count);
        }
        children.extend_from_slice(&b.children[1..b.num]);
        counts.extend_from_slice(&b.counts[1..b.num]);
        self.btree_assemble_branch(&children, &counts)
    }

    pub(crate) fn btree_join(&self, root_a: i64, root_b: i64) -> Result<i64> {
        let ha = self.btree_height(root_a)?;
        let hb = self.btree_height(root_b)?;
        let result = if ha == hb {
            let a = self.read_btree_node(root_a)?;
            let b = self.read_btree_node(root_b)?;
            self.btree_merge_nodes(&a, &b)?
        } else if ha > hb {
            self.btree_join_right(root_a, ha, root_b, hb)?
        } else {
            self.btree_join_left(root_a, ha, root_b, hb)?
        };
        self.btree_make_root(result)
    }

    // build a tree from a run of sibling children (already height-h-1
    // subtrees): empty -> a new empty leaf, one -> that child unwrapped,
    // many -> a branch
    fn btree_subtree(&self, children: &[Slot], counts: &[i64]) -> Result<i64> {
        match children.len() {
            0 => self.btree_new_root(),
            1 => Ok(children[0].value),
            _ => Ok(self.btree_assemble_branch(children, counts)?.node_ptr),
        }
    }

    /// Splits the tree at `rank`, returning the roots of the left and
    /// right parts.
    pub(crate) fn btree_split(&self, root_ptr: i64, rank: i64) -> Result<(i64, i64)> {
        let node = self.read_btree_node(root_ptr)?;
        if node.kind == BTreeNodeKind::Leaf {
            let r = check_rank(rank, node.num, true)?;
            let left_ptr = self.write_btree_node(&leaf(&node.values[..r]))?;
            let right_ptr = self.write_btree_node(&leaf(&node.values[r..node.num]))?;
            return Ok((left_ptr, right_ptr));
        }
        let (i, rem) = child_for_rank(&node, rank, true);
        let (child_left, child_right) = self.btree_split(node.children[i].value, rem)?;
        let left_sub = self.btree_subtree(&node.children[..i], &node.counts[..i])?;
        let right_sub = self.btree_subtree(&node.children[i + 1..node.num], &node.counts[i + 1..node.num])?;
        let joined_left = self.btree_join(left_sub, child_left)?;
        let joined_right = self.btree_join(child_right, right_sub)?;
        Ok((joined_left, joined_right))
    }
}
