//! The traversal behind `CursorIterator` (`src/cursor.rs`) over a
//! [`Store`], checked by Verus.
//!
//! Iterating only reads the file. Every stack index and position the
//! traversal computes is in range, and offsets read from a corrupt file
//! fail with an error instead of overflowing. Every walk is bounded (see
//! [`walk_bound`] and [`step_bound`]), so a corrupt file whose index blocks
//! form a cycle fails with an error, and the traversal is proved to finish.

use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;

verus! {

#[derive(Clone, Copy)]
pub struct IterLevel {
    pub position: i64,
    pub block: [Slot; SLOT_COUNT],
    pub index: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum IterKind {
    Empty,
    // a fixed number of items in an array list or b-tree
    Counted,
    // hash maps and sets, which are walked until the stack is empty
    Map,
}

pub struct IterState {
    pub kind: IterKind,
    pub size: i64,
    pub index: i64,
    pub stack: Vec<IterLevel>,
    // skips a b-tree node's kind+num header, or 0 for the radix trie
    pub node_offset: i64,
    // for array lists, the stack depth of the leaf blocks. every slot in them
    // is an item, even an empty one, so they are counted even when empty.
    pub leaf_depth: Option<usize>,
    pub done: bool,
    // how many steps one call to next_internal may take (see step_bound)
    pub steps: u64,
}

/// Every level's index is at most the block length.
pub open spec fn stack_ok(stack: Seq<IterLevel>) -> bool {
    forall|i: int| 0 <= i < stack.len() ==> #[trigger] stack[i].index <= SLOT_COUNT
}

pub open spec fn state_ok(st: IterState) -> bool {
    &&& stack_ok(st.stack@)
    &&& 0 <= st.node_offset <= BTREE_NODE_HEADER_SIZE
}

/// How many steps one call to [`next_internal`] may take. Each step pops a
/// level, pushes one or passes a slot. In a valid file, between two items
/// the walk goes up and back down a path of distinct blocks (at most
/// [`walk_bound`] of them) or, in a hash map, crosses blocks that are each
/// visited once, so it takes fewer steps than this.
pub fn step_bound<S: Store>(s: &mut S) -> (r: Result<u64>)
    ensures
        final(s).file() == old(s).file(),
{
    let n = walk_bound(s, INDEX_BLOCK_SIZE as u64)?;
    Ok(match n.checked_mul(2 * (SLOT_COUNT as u64 + 2)) {
        Some(m) => m,
        None => u64::MAX,
    })
}

/// Reads the index block at `position` as a fresh level.
pub fn level<S: Store>(s: &mut S, position: i64) -> (r: Result<IterLevel>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().index == 0 && r.unwrap().position == position,
{
    let mut buf = [0u8; INDEX_BLOCK_SIZE];
    s.read_at(position, &mut buf)?;
    Ok(IterLevel { position, block: decode_slots(&buf)?, index: 0 })
}

/// `stack_ok`, checked at run time.
pub fn check_stack(stack: &Vec<IterLevel>) -> (r: bool)
    ensures
        r == stack_ok(stack@),
{
    let mut i: usize = 0;
    while i < stack.len()
        invariant
            i <= stack@.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] stack@[k].index <= SLOT_COUNT,
        decreases stack.len() - i,
    {
        if stack[i].index > SLOT_COUNT {
            return false;
        }
        i += 1;
    }
    true
}

/// `state_ok`, checked at run time.
pub fn check_state(st: &IterState) -> (r: bool)
    ensures
        r == state_ok(*st),
{
    check_stack(&st.stack) && 0 <= st.node_offset && st.node_offset <= BTREE_NODE_HEADER_SIZE as i64
}

pub fn empty_state() -> (r: IterState)
    ensures
        state_ok(r),
        r.done,
{
    IterState { kind: IterKind::Empty, size: 0, index: 0, stack: Vec::new(), node_offset: 0, leaf_depth: None, done: true, steps: 0 }
}

/// `CursorIterator::new`: the iterator over the collection `slot` holds.
pub fn new_state<S: Store>(s: &mut S, slot: Slot) -> (r: Result<IterState>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> state_ok(r.unwrap()),
{
    let mut it = empty_state();
    match slot.tag {
        Tag::None => {},
        Tag::ArrayList => {
            let mut buf = [0u8; ARRAY_LIST_HEADER_LENGTH];
            s.read_at(slot.value, &mut buf)?;
            let header = ArrayListHeader::from_bytes(&buf)?;
            it.kind = IterKind::Counted;
            it.size = header.size;
            let l = level(s, header.ptr)?;
            it.stack = Vec::new();
            it.stack.push(l);
            it.leaf_depth = Some(array_list_shift(header.size - 1) as usize + 1);
        },
        Tag::LinkedArrayList | Tag::SortedMap | Tag::SortedSet => {
            // backed by a b-tree: read the header, then walk from the root
            // node's value/child slots (skipping its kind+num header)
            let mut buf = [0u8; BTREE_HEADER_LENGTH];
            s.read_at(slot.value, &mut buf)?;
            let header = BTreeHeader::from_bytes(&buf)?;
            it.kind = IterKind::Counted;
            it.size = header.size;
            it.node_offset = BTREE_NODE_HEADER_SIZE as i64;
            let pos = match header.root_ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let l = level(s, pos)?;
            it.stack = Vec::new();
            it.stack.push(l);
        },
        Tag::HashMap | Tag::HashSet => {
            it.kind = IterKind::Map;
            let l = level(s, slot.value)?;
            it.stack = Vec::new();
            it.stack.push(l);
        },
        Tag::CountedHashMap | Tag::CountedHashSet => {
            it.kind = IterKind::Map;
            let pos = match slot.value.checked_add(8) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let l = level(s, pos)?;
            it.stack = Vec::new();
            it.stack.push(l);
        },
        _ => return Err(Error::UnexpectedTag),
    }
    it.done = matches!(it.kind, IterKind::Empty);
    it.steps = step_bound(s)?;
    proof {
        assert(stack_ok(it.stack@));
    }
    Ok(it)
}

/// A counted iterator started at `index`, with a stack from a seek.
pub fn seeked_state<S: Store>(s: &mut S, size: i64, index: i64, node_offset: i64, stack: Vec<IterLevel>) -> (r: Result<IterState>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> state_ok(r.unwrap()),
{
    if !check_stack(&stack) || node_offset < 0 || node_offset > BTREE_NODE_HEADER_SIZE as i64 {
        return Err(Error::InvalidDatabase);
    }
    let steps = step_bound(s)?;
    Ok(IterState { kind: IterKind::Counted, size, index, stack, node_offset, leaf_depth: None, done: false, steps })
}

/// `resolve_start_index`: a possibly-negative start index as a rank, or
/// `None` if it is out of range.
pub fn resolve_start_index(index: i64, size: i64) -> (r: Option<i64>)
    ensures
        r is Some ==> 0 <= r.unwrap() < size,
{
    if size < 0 {
        return None;
    }
    let resolved = if index < 0 {
        match index.checked_add(size) {
            Some(r) => r,
            None => return None,
        }
    } else {
        index
    };
    if 0 <= resolved && resolved < size {
        Some(resolved)
    } else {
        None
    }
}

/// `array_list_from`: the stack of an array list iterator seeked to `idx`.
pub fn array_list_seek<S: Store>(s: &mut S, header: ArrayListHeader, idx: i64) -> (r: Result<Vec<IterLevel>>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> stack_ok(r.unwrap()@),
{
    if idx < 0 || header.size < 0 {
        return Err(Error::InvalidDatabase);
    }
    let mut shift = array_list_shift(header.size - 1);
    // descend the radix trie, pushing one level per tier with its index set
    // to that tier's child slot
    let mut stack: Vec<IterLevel> = Vec::new();
    let mut pos = header.ptr;
    loop
        invariant
            s.file() == old(s).file(),
            stack_ok(stack@),
            shift < 16,
            idx >= 0,
        decreases shift,
    {
        let l = level(s, pos)?;
        let block = l.block;
        let i = ((idx >> (shift as u32 * BIT_COUNT)) & MASK) as usize;
        proof {
            assert((idx >> (shift as u32 * 4u32)) & 15i64 >= 0i64 && (idx >> (shift as u32 * 4u32)) & 15i64 < 16i64) by (bit_vector)
                requires
                    shift < 16u8,
            ;
        }
        stack.push(IterLevel { position: pos, block, index: i });
        if shift == 0 {
            break;
        }
        // every tier above the leaf is a populated index slot for any index
        // below the size, so this child always exists
        pos = block[i].value;
        shift -= 1;
    }
    Ok(stack)
}

/// `linked_array_list_from`: the stack of a linked array list iterator
/// seeked to `idx`.
pub fn linked_array_list_seek<S: Store>(s: &mut S, header: BTreeHeader, idx: i64) -> (r: Result<Vec<IterLevel>>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> stack_ok(r.unwrap()@),
{
    let mut fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
    let mut stack: Vec<IterLevel> = Vec::new();
    let mut node_ptr = header.root_ptr;
    let mut rem = idx;
    loop
        invariant
            s.file() == old(s).file(),
            stack_ok(stack@),
        decreases fuel,
    {
        if fuel == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        fuel = fuel - 1;
        let node = crate::btree_io::read_btree_node(s, node_ptr)?;
        let position = match node_ptr.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        if matches!(node.kind, BTreeNodeKind::Leaf) {
            let index = check_rank(rem, node.num, false)?;
            stack.push(IterLevel { position, block: node.values, index });
            break;
        }
        if node.num == 0 {
            return Err(Error::InvalidBTreeNode);
        }
        let (i, next_rem) = crate::btree::child_for_rank_pub(&node, rem, false);
        rem = next_rem;
        stack.push(IterLevel { position, block: node.children, index: i });
        node_ptr = node.children[i].value;
    }
    Ok(stack)
}

/// `next_internal`: the next slot, or `None` once the stack is exhausted.
/// Empty slots are skipped, except in array list leaf blocks.
pub fn next_internal<S: Store>(s: &mut S, st: &mut IterState) -> (r: Result<Option<SlotPointer>>)
    ensures
        final(s).file() == old(s).file(),
        state_ok(*old(st)) ==> state_ok(*final(st)),
{
    if !check_state(st) {
        return Err(Error::InvalidDatabase);
    }
    let mut steps = st.steps;
    while st.stack.len() > 0
        invariant
            s.file() == old(s).file(),
            state_ok(*st),
        decreases steps,
    {
        if steps == 0 {
            return Err(Error::InvalidDatabase);
        }
        steps = steps - 1;
        let top = st.stack.len() - 1;
        let lvl = st.stack[top];
        if lvl.index >= SLOT_COUNT {
            st.stack.pop();
            if st.stack.len() > 0 {
                let p = st.stack.len() - 1;
                let mut parent = st.stack[p];
                if parent.index < SLOT_COUNT {
                    parent.index += 1;
                }
                st.stack.set(p, parent);
            }
            continue;
        }

        let next_slot = lvl.block[lvl.index];
        if matches!(next_slot.tag, Tag::Index) {
            // node_offset skips a b-tree node's kind+num header
            let next_pos = match next_slot.value.checked_add(st.node_offset) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let l = level(s, next_pos)?;
            st.stack.push(l);
            continue;
        }

        let mut cur = lvl;
        cur.index = cur.index + 1;
        st.stack.set(top, cur);
        let at_leaf = match st.leaf_depth {
            Some(d) => d == st.stack.len(),
            None => false,
        };
        if !next_slot.is_empty() || at_leaf {
            let position = match cur.position.checked_add(((cur.index - 1) * SLOT_LENGTH) as i64) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            return Ok(Some(SlotPointer::new(Some(position), next_slot)));
        }
    }
    Ok(None)
}

} // verus!
