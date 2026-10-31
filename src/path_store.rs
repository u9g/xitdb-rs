//! The bodies of the path steps (`Database::read_part`) over a [`Store`],
//! checked by Verus: creating or copying a collection, and the linked array
//! list operations, each writing its updated header.
//!
//! None of them changes a committed byte other than the root header
//! ([`tx_hdr_ok`]): they write new data at the end of the file, headers and
//! slots from `limit` on (the crate's `max(tx_start, frozen_at)`), and the
//! slot that points at the collection, which is either from `limit` on or
//! the root slot in the root header. Sizes read from a corrupt file fail
//! with an error instead of overflowing.

#![allow(unused_variables)] // ghost arguments, erased in normal builds

#[allow(unused_imports)]
use crate::array_list_store::*;
#[allow(unused_imports)]
use crate::btree_io::*;
#[allow(unused_imports)]
use crate::btree_join::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;

verus! {

/// Nothing before `limit` changed, except the root header.
pub open spec fn tx_hdr_ok(f: Seq<u8>, g: Seq<u8>, limit: int) -> bool {
    &&& limit <= f.len() ==> limit <= g.len()
    &&& forall|i: int| 0 <= i < limit && i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) ==> #[trigger] g[i] == f[i]
}

/// A position that may be written: from `limit` on, or the root slot.
pub open spec fn writable(pos: int, limit: int, len: int) -> bool {
    pos >= limit || (pos == ROOT_HEADER_START && ROOT_HEADER_END <= len)
}

pub proof fn lemma_kept_hdr(f: Seq<u8>, g: Seq<u8>, limit: int)
    requires
        kept_below(f, g, limit),
        0 <= limit <= f.len(),
    ensures
        tx_hdr_ok(f, g, limit),
{
    if limit <= f.len() {
        assert forall|i: int| 0 <= i < limit && i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] g[i] == f[i] by {
            assert(g.subrange(0, limit)[i] == f.subrange(0, limit)[i]);
        }
    }
}

pub proof fn lemma_hdr_trans(f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, limit: int)
    requires
        tx_hdr_ok(f, g, limit),
        tx_hdr_ok(g, h, limit),
        0 <= limit <= f.len(),
    ensures
        tx_hdr_ok(f, h, limit),
{
}

proof fn lemma_hdr_refl(f: Seq<u8>, limit: int)
    ensures
        tx_hdr_ok(f, f, limit),
{
}

/// Writes a slot at a writable position.
pub fn write_slot_tx<S: Store>(s: &mut S, pos: i64, slot: Slot, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= old(s).file().len(),
        writable(pos as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    write_slot_at(s, pos, slot)?;
    proof {
        let f = old(s).file();
        let g = s.file();
        lemma_slot_roundtrip(slot);
        if pos >= limit {
            lemma_overwrite_keeps(f, pos as int, slot_encode_spec(slot), limit as int);
            lemma_kept_hdr(f, g, limit as int);
        } else {
            assert forall|i: int| 0 <= i < limit && i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] g[i] == f[i] by {
                if i < pos {
                    assert(g[i] == f.subrange(0, pos as int)[i]);
                } else {
                    assert(g[i] == f.subrange(pos + 9, f.len() as int)[i - pos - 9]);
                }
            }
        }
    }
    Ok(())
}

/// Writes `data` at a position from `limit` on.
pub fn write_tx<S: Store>(s: &mut S, pos: i64, data: &[u8], limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= pos,
        limit <= old(s).file().len(),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    s.write_at(pos, data)?;
    proof {
        lemma_overwrite_keeps(old(s).file(), pos as int, data@, limit as int);
        lemma_kept_hdr(old(s).file(), s.file(), limit as int);
    }
    Ok(())
}

/// Appends `data`.
pub fn append_tx<S: Store>(s: &mut S, data: &[u8], limit: i64) -> (r: Result<i64>)
    requires
        0 <= limit <= old(s).file().len(),
    ensures
        r is Ok ==> r.unwrap() == old(s).file().len() && r.unwrap() >= limit,
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() == old(s).file().len() + data@.len(),
{
    let p = append(s, data)?;
    proof {
        assert(s.file().subrange(0, limit as int) =~= old(s).file().subrange(0, limit as int));
        lemma_kept_hdr(old(s).file(), s.file(), limit as int);
    }
    Ok(p)
}

fn read_array_list_header<S: Store>(s: &mut S, pos: i64) -> (r: Result<ArrayListHeader>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().size >= 0 && r.unwrap().ptr >= 0,
{
    let mut buf = [0u8; ARRAY_LIST_HEADER_LENGTH];
    s.read_at(pos, &mut buf)?;
    ArrayListHeader::from_bytes(&buf)
}

#[allow(dead_code)]
pub fn read_btree_header<S: Store>(s: &mut S, pos: i64) -> (r: Result<BTreeHeader>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().size >= 0 && r.unwrap().root_ptr >= 0,
{
    let mut buf = [0u8; BTREE_HEADER_LENGTH];
    s.read_at(pos, &mut buf)?;
    BTreeHeader::from_bytes(&buf)
}

/// `ArrayListInit`: creates an empty array list, or copies a committed one
/// into this transaction, and points the slot at `position` at it.
pub fn array_list_init<S: Store>(s: &mut S, position: i64, slot: Slot, limit: i64) -> (r: Result<SlotPointer>)
    requires
        0 <= limit <= old(s).file().len(),
        writable(position as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
        r is Ok ==> r.unwrap().slot.value >= limit,
{
    let ghost f0 = s.file();
    let array_list_start = match slot.tag {
        Tag::None => {
            let start = s.len()?;
            let ptr = match start.checked_add(ARRAY_LIST_HEADER_LENGTH as i64) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let header = ArrayListHeader { ptr, size: 0 };
            append_tx(s, &header.to_bytes(), limit)?;
            let ghost f1 = s.file();
            append_tx(s, &[0u8; INDEX_BLOCK_SIZE], limit)?;
            proof {
                lemma_hdr_trans(f0, f1, s.file(), limit as int);
            }
            start
        },
        Tag::ArrayList => {
            let mut start = slot.value;
            // copy it to the end unless it was made in this transaction
            if start < limit {
                let header = read_array_list_header(s, start)?;
                let mut block = [0u8; INDEX_BLOCK_SIZE];
                s.read_at(header.ptr, &mut block)?;
                let new_start = s.len()?;
                let ptr = match new_start.checked_add(ARRAY_LIST_HEADER_LENGTH as i64) {
                    Some(p) => p,
                    None => return Err(Error::InvalidOffset),
                };
                let header = ArrayListHeader { ptr, size: header.size };
                append_tx(s, &header.to_bytes(), limit)?;
                let ghost f1 = s.file();
                append_tx(s, &block, limit)?;
                proof {
                    lemma_hdr_trans(f0, f1, s.file(), limit as int);
                }
                start = new_start;
            } else {
                proof {
                    lemma_hdr_refl(f0, limit as int);
                }
            }
            start
        },
        _ => return Err(Error::UnexpectedTag),
    };
    let ghost f2 = s.file();
    let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(array_list_start, Tag::ArrayList));
    write_slot_tx(s, position, next_slot_ptr.slot, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(next_slot_ptr)
}

/// `copy_header_if_old`: a committed b-tree header, copied to the end.
pub fn copy_header_if_old<S: Store>(s: &mut S, header_ptr: i64, limit: i64) -> (r: Result<i64>)
    requires
        0 <= limit <= old(s).file().len(),
    ensures
        r is Ok ==> r.unwrap() >= limit || r.unwrap() == header_ptr,
        r is Ok ==> header_ptr < limit ==> r.unwrap() >= limit,
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    if header_ptr >= limit {
        proof {
            lemma_hdr_refl(s.file(), limit as int);
        }
        return Ok(header_ptr);
    }
    let mut buf = [0u8; BTREE_HEADER_LENGTH];
    s.read_at(header_ptr, &mut buf)?;
    append_tx(s, &buf, limit)
}

/// `LinkedArrayListInit`: creates an empty linked array list, or copies a
/// committed header into this transaction, and points the slot at
/// `position` at it.
pub fn linked_array_list_init<S: Store>(s: &mut S, position: i64, slot: Slot, limit: i64) -> (r: Result<SlotPointer>)
    requires
        0 <= limit <= old(s).file().len(),
        writable(position as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    let ghost f0 = s.file();
    let header_ptr = match slot.tag {
        Tag::None => {
            // create an empty tree: a single empty leaf plus a header
            let root_ptr = btree_new_root(s)?;
            proof {
                lemma_grows_hdr(f0, s.file(), limit as int);
            }
            let ghost f1 = s.file();
            let p = append_tx(s, &BTreeHeader { root_ptr, size: 0 }.to_bytes(), limit)?;
            proof {
                lemma_hdr_trans(f0, f1, s.file(), limit as int);
            }
            p
        },
        Tag::LinkedArrayList => copy_header_if_old(s, slot.value, limit)?,
        _ => return Err(Error::UnexpectedTag),
    };
    let ghost f2 = s.file();
    let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(header_ptr, Tag::LinkedArrayList));
    write_slot_tx(s, position, next_slot_ptr.slot, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(next_slot_ptr)
}

pub proof fn lemma_grows_hdr(f: Seq<u8>, g: Seq<u8>, limit: int)
    requires
        grows(f, g),
        0 <= limit <= f.len(),
    ensures
        tx_hdr_ok(f, g, limit),
{
    assert forall|i: int| 0 <= i < limit && i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] g[i] == f[i] by {
        assert(g.subrange(0, f.len() as int)[i] == f[i]);
    }
}

pub proof fn lemma_tx_hdr(f: Seq<u8>, g: Seq<u8>, limit: Option<i64>)
    requires
        crate::btree_io::tx_ok(f, g, limit),
        limit is Some,
        0 <= limit.unwrap() <= f.len(),
    ensures
        tx_hdr_ok(f, g, limit.unwrap() as int),
{
    lemma_kept_hdr(f, g, limit.unwrap() as int);
}

/// The linked array list step bodies all end by writing the header, which
/// belongs to this transaction.
fn write_header<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= header_ptr,
        limit <= old(s).file().len(),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    write_tx(s, header_ptr, &header.to_bytes(), limit)
}

/// `LinkedArrayListGet` in write mode: the value slot, with the nodes on the
/// way copied, and the header updated if the root moved.
pub fn linked_get_for_write<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, rank: i64, limit: i64) -> (r: Result<SlotPointer>)
    requires
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> r.unwrap().position is Some && r.unwrap().position.unwrap() >= limit,
{
    let fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f0 = s.file();
    let write_slot = btree_get_for_write(s, header.root_ptr, rank, Some(limit), fuel)?;
    let ghost f1 = s.file();
    proof {
        lemma_tx_hdr(f0, f1, Some(limit));
    }
    if write_slot.node_ptr != header.root_ptr {
        let new_header = BTreeHeader { root_ptr: write_slot.node_ptr, size: header.size };
        write_header(s, header_ptr, new_header, limit)?;
        proof {
            lemma_hdr_trans(f0, f1, s.file(), limit as int);
        }
    }
    Ok(SlotPointer::new(Some(write_slot.value_position), write_slot.slot))
}

/// `LinkedArrayListAppend` and `LinkedArrayListInsert`: a placeholder
/// inserted at `rank`, the header updated, and the slot to fill in.
pub fn linked_insert<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, rank: i64, limit: i64) -> (r: Result<SlotPointer>)
    requires
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> r.unwrap().position is Some && r.unwrap().position.unwrap() >= limit,
{
    let size = match header.size.checked_add(1) {
        Some(n) => n,
        None => return Err(Error::InvalidDatabase),
    };
    let fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f0 = s.file();
    let result = btree_insert(s, header.root_ptr, rank, Some(limit), fuel)?;
    let ghost f1 = s.file();
    proof {
        lemma_tx_hdr(f0, f1, Some(limit));
    }
    let new_root_ptr = btree_make_root(s, result.join)?;
    let ghost f2 = s.file();
    proof {
        lemma_grows_hdr(f1, f2, limit as int);
        lemma_hdr_trans(f0, f1, f2, limit as int);
    }
    // update the header before filling in the value, so that a failure in
    // the rest of the path leaves the tree and header consistent
    write_header(s, header_ptr, BTreeHeader { root_ptr: new_root_ptr, size }, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(SlotPointer::new(Some(result.value_position), Slot::new(0, Tag::None)))
}

/// `LinkedArrayListSlice`: the items `offset..offset + size`.
pub fn linked_slice<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, offset: i64, size: i64, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    // bounds-checked without overflow (offset + size could wrap)
    if offset < 0 || size < 0 || offset > header.size || size > header.size - offset {
        return Err(Error::KeyNotFound);
    }
    let fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f0 = s.file();
    // slice = drop [0, offset) then keep [0, size) of what's left
    let after_offset = btree_split(s, header.root_ptr, offset, fuel)?;
    let fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
    let ghost fm = s.file();
    let sliced = btree_split(s, after_offset.1, size, fuel)?;
    let ghost f1 = s.file();
    proof {
        lemma_grows_trans(f0, fm, f1);
        lemma_grows_hdr(f0, f1, limit as int);
    }
    write_header(s, header_ptr, BTreeHeader { root_ptr: sliced.0, size }, limit)?;
    proof {
        lemma_hdr_trans(f0, f1, s.file(), limit as int);
    }
    Ok(())
}

/// `LinkedArrayListConcat`, after the caller freezes everything written so
/// far: the join of two lists' trees.
pub fn linked_concat<S: Store>(s: &mut S, header_ptr: i64, header_a: BTreeHeader, header_b: BTreeHeader, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    let size = match header_a.size.checked_add(header_b.size) {
        Some(n) => n,
        None => return Err(Error::InvalidDatabase),
    };
    let ghost f0 = s.file();
    let new_root_ptr = btree_join(s, header_a.root_ptr, header_b.root_ptr)?;
    let ghost f1 = s.file();
    proof {
        lemma_grows_hdr(f0, f1, limit as int);
    }
    write_header(s, header_ptr, BTreeHeader { root_ptr: new_root_ptr, size }, limit)?;
    proof {
        lemma_hdr_trans(f0, f1, s.file(), limit as int);
    }
    Ok(())
}

/// `LinkedArrayListRemove`: the item at `rank` removed. A list of one item
/// gets a new empty root, and a root left with one child is replaced by it.
pub fn linked_remove<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, rank: i64, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
        header.size >= 0,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    if header.size == 0 {
        return Err(Error::KeyNotFound);
    }
    let ghost f0 = s.file();
    let new_root_ptr = if header.size == 1 {
        let p = btree_new_root(s)?;
        proof {
            lemma_grows_hdr(f0, s.file(), limit as int);
        }
        p
    } else {
        let fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
        let mut root = btree_remove(s, header.root_ptr, rank, Some(limit), fuel)?;
        let ghost f1 = s.file();
        proof {
            lemma_tx_hdr(f0, f1, Some(limit));
        }
        let mut new_root_ptr = btree_write_node(s, &root, header.root_ptr, Some(limit))?;
        proof {
            lemma_tx_hdr(f1, s.file(), Some(limit));
            lemma_hdr_trans(f0, f1, s.file(), limit as int);
        }
        // a root left with one child is replaced by it
        let mut fuel = walk_bound(s, BTREE_BRANCH_BLOCK_SIZE as u64)?;
        while matches!(root.kind, BTreeNodeKind::Branch) && root.num == 1
            invariant
                tx_hdr_ok(f0, s.file(), limit as int),
                0 <= limit <= f0.len(),
            decreases fuel,
        {
            if fuel == 0 {
                return Err(Error::InvalidBTreeNode);
            }
            fuel = fuel - 1;
            new_root_ptr = root.children[0].value;
            root = read_btree_node(s, new_root_ptr)?;
        }
        new_root_ptr
    };
    let ghost f2 = s.file();
    write_header(s, header_ptr, BTreeHeader { root_ptr: new_root_ptr, size: header.size - 1 }, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(())
}

// hash maps and sorted maps

/// `HashMapInit`: creates an empty hash map, or copies a committed one into
/// this transaction, and points the slot at `position` at it.
pub fn hash_map_init<S: Store>(s: &mut S, position: i64, slot: Slot, counted: bool, tag: Tag, limit: i64) -> (r: Result<SlotPointer>)
    requires
        0 <= limit <= old(s).file().len(),
        writable(position as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    let ghost f0 = s.file();
    let map_start = match slot.tag {
        Tag::None => {
            let map_start = s.len()?;
            if counted {
                append_tx(s, &[0u8; 8], limit)?;
            }
            let ghost f1 = s.file();
            append_tx(s, &[0u8; INDEX_BLOCK_SIZE], limit)?;
            proof {
                if !counted {
                    lemma_hdr_refl(f0, limit as int);
                }
                lemma_hdr_trans(f0, f1, s.file(), limit as int);
            }
            map_start
        },
        Tag::HashMap | Tag::HashSet | Tag::CountedHashMap | Tag::CountedHashSet => {
            let is_counted = matches!(slot.tag, Tag::CountedHashMap | Tag::CountedHashSet);
            if counted != is_counted {
                return Err(Error::UnexpectedTag);
            }
            let mut map_start = slot.value;
            // copy it to the end unless it was made in this transaction
            if map_start < limit {
                let len: usize = INDEX_BLOCK_SIZE + if counted { 8 } else { 0 };
                let mut buf = zeros_vec(len);
                s.read_at(map_start, buf.as_mut_slice())?;
                map_start = append_tx(s, buf.as_slice(), limit)?;
            } else {
                proof {
                    lemma_hdr_refl(f0, limit as int);
                }
            }
            map_start
        },
        _ => return Err(Error::UnexpectedTag),
    };
    let ghost f2 = s.file();
    let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(map_start, tag));
    write_slot_tx(s, position, next_slot_ptr.slot, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(next_slot_ptr)
}

fn zeros_vec(n: usize) -> (r: Vec<u8>)
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

/// Where a hash map's index block starts: after its count, if it has one.
pub fn map_index_pos(map_start: i64, counted: bool) -> (r: Result<i64>)
    ensures
        r is Ok ==> r.unwrap() >= map_start,
{
    if !counted {
        return Ok(map_start);
    }
    match map_start.checked_add(8) {
        Some(p) => Ok(p),
        None => Err(Error::InvalidOffset),
    }
}

/// A counted hash map's count, plus `delta` (wrapping, like the crate).
pub fn update_map_count<S: Store>(s: &mut S, map_start: i64, add: bool, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= map_start,
        limit <= old(s).file().len(),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    let mut buf = [0u8; 8];
    s.read_at(map_start, &mut buf)?;
    let count = read_i64(&buf);
    let next = if add { count.wrapping_add(1) } else { count.wrapping_sub(1) };
    write_tx(s, map_start, &crate::bytes::u64_to_be_bytes(next as u64), limit)
}

/// `SortedMapInit`: creates an empty sorted map, or copies a committed
/// header into this transaction, and points the slot at `position` at it.
pub fn sorted_map_init<S: Store>(s: &mut S, position: i64, slot: Slot, tag: Tag, limit: i64) -> (r: Result<SlotPointer>)
    requires
        0 <= limit <= old(s).file().len(),
        writable(position as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> final(s).file().len() >= old(s).file().len(),
{
    let ghost f0 = s.file();
    let header_ptr = match slot.tag {
        Tag::None => {
            let root_ptr = crate::sorted_store::write_sorted_node(s, &SortedNode::empty(BTreeNodeKind::Leaf, 0))?;
            proof {
                lemma_grows_hdr(f0, s.file(), limit as int);
            }
            let ghost f1 = s.file();
            let p = append_tx(s, &BTreeHeader { root_ptr, size: 0 }.to_bytes(), limit)?;
            proof {
                lemma_hdr_trans(f0, f1, s.file(), limit as int);
            }
            p
        },
        Tag::SortedMap | Tag::SortedSet => {
            if slot.tag.to_u8() != tag.to_u8() {
                return Err(Error::UnexpectedTag);
            }
            // copy the header into this transaction unless it was made in it
            copy_header_if_old(s, slot.value, limit)?
        },
        _ => return Err(Error::UnexpectedTag),
    };
    let ghost f2 = s.file();
    let next_slot_ptr = SlotPointer::new(Some(position), Slot::new(header_ptr, tag));
    write_slot_tx(s, position, next_slot_ptr.slot, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(next_slot_ptr)
}

/// `SortedMapGet` in write mode: the entry for `key`, inserted if new, with
/// the header updated before the value is filled in.
pub fn sorted_get_for_write<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, key: &[u8], limit: i64, hash_size: usize) -> (r: Result<Slot>)
    requires
        hash_size <= 0xffff,
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> r.unwrap().value >= limit,
{
    let fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f0 = s.file();
    let result = crate::sorted_store::sorted_put(s, header.root_ptr, key, Some(limit), hash_size, fuel)?;
    let ghost f1 = s.file();
    proof {
        lemma_tx_hdr(f0, f1, Some(limit));
    }
    let new_root_ptr = crate::sorted_store::sorted_grow_root(s, &result)?;
    let ghost f2 = s.file();
    proof {
        lemma_grows_hdr(f1, f2, limit as int);
        lemma_hdr_trans(f0, f1, f2, limit as int);
    }
    let added: i64 = if result.added { 1 } else { 0 };
    let size = match header.size.checked_add(added) {
        Some(n) => n,
        None => return Err(Error::InvalidDatabase),
    };
    // update the header before filling in the value, so that a failure in
    // the rest of the path leaves the tree and header consistent (the entry
    // exists with an empty value) rather than inserted-but-uncounted
    write_header(s, header_ptr, BTreeHeader { root_ptr: new_root_ptr, size }, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(result.kv_slot)
}

/// `SortedMapRemove`: removes `key` and updates the header.
pub fn sorted_remove_key<S: Store>(s: &mut S, header_ptr: i64, header: BTreeHeader, key: &[u8], limit: i64, hash_size: usize) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= limit <= old(s).file().len(),
        header_ptr >= limit,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    let fuel = walk_bound(s, SORTED_BRANCH_BLOCK_SIZE as u64)?;
    let ghost f0 = s.file();
    let (node_ptr, found) = crate::sorted_store::sorted_remove(s, header.root_ptr, key, Some(limit), hash_size, fuel)?;
    let ghost f1 = s.file();
    proof {
        lemma_tx_hdr(f0, f1, Some(limit));
    }
    if !found {
        return Err(Error::KeyNotFound);
    }
    let size = match header.size.checked_sub(1) {
        Some(n) => n,
        None => return Err(Error::InvalidDatabase),
    };
    write_header(s, header_ptr, BTreeHeader { root_ptr: node_ptr, size }, limit)?;
    proof {
        lemma_hdr_trans(f0, f1, s.file(), limit as int);
    }
    Ok(())
}

/// `WriteData`'s write: the slot for the data, at its position.
pub fn write_data_slot<S: Store>(s: &mut S, position: i64, slot: Slot, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= old(s).file().len(),
        writable(position as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    write_slot_tx(s, position, slot, limit)
}

/// An array list's header, written after an append or a slice. The list
/// belongs to this transaction (it was copied if not), so its header is
/// from `limit` on.
pub fn write_array_list_header<S: Store>(s: &mut S, start: i64, header: ArrayListHeader, limit: i64) -> (r: Result<()>)
    requires
        0 <= limit <= start,
        limit <= old(s).file().len(),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    write_tx(s, start, &header.to_bytes(), limit)
}

} // verus!
