//! Compaction over two [`Store`]s (`src/compact.rs`), checked by Verus.
//!
//! The source is only read. The target is only appended to, or written
//! inside blocks this compaction reserved at its end, so nothing the target
//! held when compaction started (before `base`) changes. That holds
//! whatever the offset map returns, because blocks are only written right
//! after being reserved. Offsets read from a corrupt source fail with an
//! error instead of overflowing.

#![allow(unused_variables)] // ghost arguments, erased in normal builds

#[allow(unused_imports)]
use crate::array_list_store::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The offset map, as compaction uses it. Nothing is assumed about what
/// it returns.
pub trait OffsetMapping {
    fn get(&mut self, source_offset: i64) -> (r: Result<Option<i64>>);
    fn put(&mut self, source_offset: i64, target_offset: i64) -> (r: Result<()>);
}

/// What compaction guarantees about the target: nothing before `base`
/// changed.
pub open spec fn target_ok(t0: Seq<u8>, t1: Seq<u8>, base: int) -> bool {
    kept_below(t0, t1, base)
}

proof fn lemma_target_trans(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, base: int)
    requires
        target_ok(a, b, base),
        target_ok(b, c, base),
    ensures
        target_ok(a, c, base),
{
    lemma_kept_trans(a, b, c, base);
}

fn zeros(n: usize) -> (r: Vec<u8>)
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

/// Appends `data` to the target.
fn append_target<T: Store>(t: &mut T, data: &[u8], base: Ghost<int>) -> (r: Result<i64>)
    requires
        0 <= base@ <= old(t).file().len(),
    ensures
        r is Ok ==> r.unwrap() == old(t).file().len() && r.unwrap() >= base@,
        r is Ok ==> target_ok(old(t).file(), final(t).file(), base@),
        r is Ok ==> final(t).file().len() == old(t).file().len() + data@.len(),
{
    let p = append(t, data)?;
    proof {
        assert(t.file().subrange(0, base@) =~= old(t).file().subrange(0, base@));
    }
    Ok(p)
}

/// Writes `data` at `pos`, inside a reserved block at or after `base`.
fn write_target<T: Store>(t: &mut T, pos: i64, data: &[u8], base: Ghost<int>) -> (r: Result<()>)
    requires
        0 <= base@ <= pos,
        base@ <= old(t).file().len(),
    ensures
        r is Ok ==> target_ok(old(t).file(), final(t).file(), base@),
        r is Ok ==> final(t).file().len() >= old(t).file().len(),
{
    t.write_at(pos, data)?;
    proof {
        lemma_overwrite_keeps(old(t).file(), pos as int, data@, base@);
        let f = old(t).file();
        let g = t.file();
        assert(g.len() >= f.len());
    }
    Ok(())
}

fn read_index_block<S: Store>(s: &mut S, pos: i64) -> (r: Result<[Slot; SLOT_COUNT]>)
    ensures
        final(s).file() == old(s).file(),
{
    let mut buf = [0u8; INDEX_BLOCK_SIZE];
    s.read_at(pos, &mut buf)?;
    decode_slots(&buf)
}

fn read_i64_at<S: Store>(s: &mut S, pos: i64) -> (r: Result<i64>)
    ensures
        final(s).file() == old(s).file(),
{
    let mut buf = [0u8; 8];
    s.read_at(pos, &mut buf)?;
    Ok(read_i64(&buf))
}

/// `visit_object`: the target offset of a source object, copying it the
/// first time.
fn visit_object<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    size: usize,
    populate: Populate,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<i64>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 9int,
{
    if let Some(target_offset) = map.get(source_offset)? {
        proof {
            assert(tgt.file().subrange(0, base@) =~= old(tgt).file().subrange(0, base@));
        }
        return Ok(target_offset);
    }
    let block = zeros(size);
    let target_offset = append_target(tgt, block.as_slice(), base)?;
    let ghost t1 = tgt.file();
    map.put(source_offset, target_offset)?;
    populate_object(src, tgt, map, populate, source_offset, target_offset, hash_size, base, fuel)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
    }
    Ok(target_offset)
}

#[derive(Clone, Copy)]
pub enum Populate {
    Index,
    ArrayList,
    BTree,
    HashMap { counted: bool },
    KvPair(Tag),
    SortedMap,
    BTreeLeaf { num: u8 },
    BTreeBranch { num: u8 },
    SortedLeaf { num: u8 },
    SortedBranch { num: u8 },
}

fn populate_object<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    populate: Populate,
    source_offset: i64,
    target_offset: i64,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 8int,
{
    match populate {
        Populate::Index => populate_index(src, tgt, map, source_offset, target_offset, hash_size, base, fuel),
        Populate::ArrayList => populate_array_list(src, tgt, map, source_offset, target_offset, hash_size, base, fuel),
        Populate::BTree => populate_btree(src, tgt, map, source_offset, target_offset, false, hash_size, base, fuel),
        Populate::SortedMap => populate_btree(src, tgt, map, source_offset, target_offset, true, hash_size, base, fuel),
        Populate::HashMap { counted } => populate_hash_map(src, tgt, map, source_offset, target_offset, counted, hash_size, base, fuel),
        Populate::KvPair(tag) => populate_kv_pair(src, tgt, map, source_offset, target_offset, tag, hash_size, base, fuel),
        Populate::BTreeLeaf { num } => populate_leaf(src, tgt, map, source_offset, target_offset, num, hash_size, base, fuel),
        Populate::SortedLeaf { num } => populate_leaf(src, tgt, map, source_offset, target_offset, num, hash_size, base, fuel),
        Populate::BTreeBranch { num } => populate_branch(src, tgt, map, source_offset, target_offset, num, false, hash_size, base, fuel),
        Populate::SortedBranch { num } => populate_branch(src, tgt, map, source_offset, target_offset, num, true, hash_size, base, fuel),
    }
}

/// `remap_slot`: the slot as it reads in the target, copying what it points
/// to.
pub fn remap_slot<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    slot: Slot,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<Slot>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 3int,
{
    if fuel == 0 {
        return Err(Error::InvalidDatabase);
    }
    let new_offset = match slot.tag {
        Tag::None | Tag::Uint | Tag::Int | Tag::Float | Tag::ShortBytes => {
            proof {
                assert(tgt.file().subrange(0, base@) =~= old(tgt).file().subrange(0, base@));
            }
            return Ok(slot);
        },
        Tag::Bytes => remap_bytes(src, tgt, map, slot, base)?,
        Tag::Index => visit_object(src, tgt, map, slot.value, INDEX_BLOCK_SIZE, Populate::Index, hash_size, base, fuel - 1)?,
        Tag::ArrayList => visit_object(src, tgt, map, slot.value, ARRAY_LIST_HEADER_LENGTH, Populate::ArrayList, hash_size, base, fuel - 1)?,
        Tag::LinkedArrayList => visit_object(src, tgt, map, slot.value, BTREE_HEADER_LENGTH, Populate::BTree, hash_size, base, fuel - 1)?,
        Tag::HashMap | Tag::HashSet => visit_object(src, tgt, map, slot.value, INDEX_BLOCK_SIZE, Populate::HashMap { counted: false }, hash_size, base, fuel - 1)?,
        Tag::CountedHashMap | Tag::CountedHashSet => visit_object(
            src,
            tgt,
            map,
            slot.value,
            INDEX_BLOCK_SIZE + 8,
            Populate::HashMap { counted: true },
            hash_size,
            base,
            fuel - 1,
        )?,
        Tag::KvPair => {
            let size = key_value_pair_length(hash_size);
            visit_object(src, tgt, map, slot.value, size, Populate::KvPair(Tag::KvPair), hash_size, base, fuel - 1)?
        },
        Tag::SortedKvPair => visit_object(
            src,
            tgt,
            map,
            slot.value,
            SORTED_KEY_VALUE_PAIR_LENGTH,
            Populate::KvPair(Tag::SortedKvPair),
            hash_size,
            base,
            fuel - 1,
        )?,
        Tag::SortedMap | Tag::SortedSet => visit_object(src, tgt, map, slot.value, BTREE_HEADER_LENGTH, Populate::SortedMap, hash_size, base, fuel - 1)?,
    };
    Ok(Slot { value: new_offset, tag: slot.tag, full: slot.full })
}

/// `remap_bytes`: a byte array copied to the end of the target, once.
fn remap_bytes<S: Store, T: Store, M: OffsetMapping>(src: &mut S, tgt: &mut T, map: &mut M, slot: Slot, base: Ghost<int>) -> (r: Result<i64>)
    requires
        0 <= base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
{
    if let Some(target_offset) = map.get(slot.value)? {
        proof {
            assert(tgt.file().subrange(0, base@) =~= old(tgt).file().subrange(0, base@));
        }
        return Ok(target_offset);
    }

    let length = read_i64_at(src, slot.value)?;
    let format_tag_size: i64 = if slot.full { 2 } else { 0 };
    let mut remaining = match length.checked_add(format_tag_size) {
        Some(n) => n,
        None => return Err(Error::InvalidDatabase),
    };
    let mut pos = match slot.value.checked_add(8) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };

    let new_offset = append_target(tgt, &crate::bytes::u64_to_be_bytes(length as u64), base)?;
    let cap: usize = if remaining <= 0 { 0 } else if remaining > 4096 { 4096 } else { remaining as usize };
    while remaining > 0
        invariant
            src.file() == old(src).file(),
            0 <= base@ <= old(tgt).file().len(),
            old(tgt).file().len() <= tgt.file().len(),
            target_ok(old(tgt).file(), tgt.file(), base@),
            remaining > 0 ==> cap > 0,
            cap <= 4096,
        decreases remaining,
    {
        let chunk: usize = if remaining < cap as i64 { remaining as usize } else { cap };
        let mut buf = zeros(chunk);
        // the target is appended to, so it is written at its end each time
        src.read_at(pos, buf.as_mut_slice())?;
        let ghost t1 = tgt.file();
        append_target(tgt, buf.as_slice(), base)?;
        proof {
            lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
        }
        pos = match pos.checked_add(chunk as i64) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        remaining = remaining - chunk as i64;
    }

    map.put(slot.value, new_offset)?;
    Ok(new_offset)
}

/// `remap_slots`.
fn remap_slots<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    slots: &[Slot; SLOT_COUNT],
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<[Slot; SLOT_COUNT]>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 4int,
{
    let mut out = *slots;
    let mut i: usize = 0;
    proof {
        assert(tgt.file().subrange(0, base@) =~= old(tgt).file().subrange(0, base@));
    }
    while i < SLOT_COUNT
        invariant
            i <= SLOT_COUNT,
            hash_size <= 0xffff,
            src.file() == old(src).file(),
            0 <= base@ <= old(tgt).file().len(),
            old(tgt).file().len() <= tgt.file().len(),
            target_ok(old(tgt).file(), tgt.file(), base@),
        decreases SLOT_COUNT - i,
    {
        let ghost t1 = tgt.file();
        out[i] = remap_slot(src, tgt, map, slots[i], hash_size, base, fuel)?;
        proof {
            lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
        }
        i += 1;
    }
    Ok(out)
}

fn encode_block(slots: &[Slot; SLOT_COUNT]) -> (r: Vec<u8>) {
    let mut buf = Vec::new();
    encode_slots(&mut buf, slots);
    buf
}

fn populate_index<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let block = read_index_block(src, source_offset)?;
    let remapped = remap_slots(src, tgt, map, &block, hash_size, base, fuel)?;
    let ghost t1 = tgt.file();
    write_target(tgt, target_offset, encode_block(&remapped).as_slice(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
    }
    Ok(())
}

/// `remap_array_list_index`: full blocks go through the cache; partial
/// ones, which lists of different sizes may share, are copied separately.
fn remap_array_list_index<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    size: i64,
    shift: u8,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<i64>)
    requires
        hash_size <= 0xffff,
        shift < 16,
        0 <= base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 6int,
{
    if fuel == 0 {
        return Err(Error::InvalidDatabase);
    }
    let child_size: i64 = 1i64 << (shift as u32 * BIT_COUNT);
    proof {
        assert(1i64 << (shift as u32 * 4u32) > 0i64) by (bit_vector)
            requires
                shift < 16u8,
        ;
    }

    if child_size <= i64::MAX / SLOT_COUNT as i64 && size == child_size * SLOT_COUNT as i64 {
        return Ok(remap_slot(src, tgt, map, Slot::new(source_offset, Tag::Index), hash_size, base, fuel)?.value);
    }

    let target_offset = append_target(tgt, zeros(INDEX_BLOCK_SIZE).as_slice(), base)?;
    let ghost t1 = tgt.file();
    let block = read_index_block(src, source_offset)?;
    let mut remapped_block = [Slot::new(0, Tag::None); SLOT_COUNT];
    let mut remaining = size;
    let mut i: usize = 0;
    while i < SLOT_COUNT
        invariant
            i <= SLOT_COUNT,
            hash_size <= 0xffff,
            shift < 16,
            child_size > 0,
            fuel > 0,
            src.file() == old(src).file(),
            0 <= base@ <= target_offset,
            t1.len() <= tgt.file().len(),
            target_ok(t1, tgt.file(), base@),
            base@ <= t1.len(),
        decreases SLOT_COUNT - i,
    {
        if remaining <= 0 {
            break;
        }
        let count = if remaining < child_size { remaining } else { child_size };
        let child_slot = block[i];
        let ghost t2 = tgt.file();
        remapped_block[i] = if shift == 0 {
            remap_slot(src, tgt, map, child_slot, hash_size, base, fuel)?
        } else {
            if !matches!(child_slot.tag, Tag::Index) {
                return Err(Error::UnexpectedTag);
            }
            let value = remap_array_list_index(src, tgt, map, child_slot.value, count, shift - 1, hash_size, base, fuel - 1)?;
            Slot { value, ..child_slot }
        };
        proof {
            lemma_target_trans(t1, t2, tgt.file(), base@);
        }
        remaining = remaining - count;
        i += 1;
    }

    let ghost t3 = tgt.file();
    write_target(tgt, target_offset, encode_block(&remapped_block).as_slice(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, t3, base@);
        lemma_target_trans(old(tgt).file(), t3, tgt.file(), base@);
    }
    Ok(target_offset)
}

fn populate_array_list<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let mut buf = [0u8; ARRAY_LIST_HEADER_LENGTH];
    src.read_at(source_offset, &mut buf)?;
    let header = ArrayListHeader::from_bytes(&buf)?;
    let shift = array_list_shift(header.size - 1);
    let ptr = remap_array_list_index(src, tgt, map, header.ptr, header.size, shift, hash_size, base, fuel)?;
    let ghost t1 = tgt.file();
    write_target(tgt, target_offset, &ArrayListHeader { ptr, size: header.size }.to_bytes(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
    }
    Ok(())
}

fn populate_btree<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    sorted: bool,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let mut buf = [0u8; BTREE_HEADER_LENGTH];
    src.read_at(source_offset, &mut buf)?;
    let header = BTreeHeader::from_bytes(&buf)?;
    let root_ptr = remap_node(src, tgt, map, header.root_ptr, sorted, hash_size, base, fuel)?;
    let ghost t1 = tgt.file();
    write_target(tgt, target_offset, &BTreeHeader { root_ptr, size: header.size }.to_bytes(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
    }
    Ok(())
}

fn remap_node<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    node_offset: i64,
    sorted: bool,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<i64>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 5int,
{
    if fuel == 0 {
        return Err(Error::InvalidDatabase);
    }
    if let Some(mapped) = map.get(node_offset)? {
        proof {
            assert(tgt.file().subrange(0, base@) =~= old(tgt).file().subrange(0, base@));
        }
        return Ok(mapped);
    }
    let mut header = [0u8; BTREE_NODE_HEADER_SIZE];
    src.read_at(node_offset, &mut header)?;
    let (kind, num) = decode_node_header(&header)?;
    let num = num as u8;
    let (size, populate) = match (kind, sorted) {
        (BTreeNodeKind::Leaf, false) => (BTREE_LEAF_BLOCK_SIZE, Populate::BTreeLeaf { num }),
        (BTreeNodeKind::Branch, false) => (BTREE_BRANCH_BLOCK_SIZE, Populate::BTreeBranch { num }),
        (BTreeNodeKind::Leaf, true) => (SORTED_LEAF_BLOCK_SIZE, Populate::SortedLeaf { num }),
        (BTreeNodeKind::Branch, true) => (SORTED_BRANCH_BLOCK_SIZE, Populate::SortedBranch { num }),
    };
    visit_object(src, tgt, map, node_offset, size, populate, hash_size, base, fuel - 1)
}

// leaves of both kinds of b-tree are a header followed by slots that are
// remapped like any other
fn populate_leaf<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    num: u8,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let mut body = [0u8; SLOT_LENGTH * BTREE_SLOT_COUNT];
    let body_pos = match source_offset.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    src.read_at(body_pos, &mut body)?;
    let slots = remap_slots(src, tgt, map, &decode_slots(&body)?, hash_size, base, fuel)?;
    let mut buf = Vec::new();
    buf.push(BTreeNodeKind::Leaf.to_u8());
    buf.push(num);
    encode_slots(&mut buf, &slots);
    let ghost t1 = tgt.file();
    write_target(tgt, target_offset, buf.as_slice(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
    }
    Ok(())
}

fn populate_branch<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    num: u8,
    sorted: bool,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let slot_blocks: usize = if sorted { 2 } else { 1 };
    let body_len = (SLOT_LENGTH * slot_blocks + 8) * BTREE_SLOT_COUNT;
    let mut body = zeros(body_len);
    let body_pos = match source_offset.checked_add(BTREE_NODE_HEADER_SIZE as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    src.read_at(body_pos, body.as_mut_slice())?;

    let mut children = decode_slots(body.as_slice())?;
    let mut i: usize = 0;
    proof {
        assert(tgt.file().subrange(0, base@) =~= old(tgt).file().subrange(0, base@));
    }
    while i < SLOT_COUNT
        invariant
            i <= SLOT_COUNT,
            hash_size <= 0xffff,
            src.file() == old(src).file(),
            0 <= base@ <= target_offset,
            base@ <= old(tgt).file().len(),
            old(tgt).file().len() <= tgt.file().len(),
            target_ok(old(tgt).file(), tgt.file(), base@),
        decreases SLOT_COUNT - i,
    {
        // non-index children are copied verbatim
        if matches!(children[i].tag, Tag::Index) {
            let ghost t1 = tgt.file();
            let v = remap_node(src, tgt, map, children[i].value, sorted, hash_size, base, fuel)?;
            children[i] = Slot { value: v, ..children[i] };
            proof {
                lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
            }
        }
        i += 1;
    }
    let ghost t2 = tgt.file();
    let separators = if sorted {
        let decoded = decode_slots(slice_subrange(body.as_slice(), SLOT_LENGTH * BTREE_SLOT_COUNT, body_len))?;
        Some(remap_slots(src, tgt, map, &decoded, hash_size, base, fuel)?)
    } else {
        None
    };
    proof {
        if separators is None {
            assert(tgt.file() == t2);
        }
        lemma_target_trans(old(tgt).file(), t2, tgt.file(), base@);
    }
    let counts = decode_counts(slice_subrange(body.as_slice(), SLOT_LENGTH * slot_blocks * BTREE_SLOT_COUNT, body_len))?;

    let mut buf = Vec::new();
    buf.push(BTreeNodeKind::Branch.to_u8());
    buf.push(num);
    encode_slots(&mut buf, &children);
    if let Some(separators) = separators {
        encode_slots(&mut buf, &separators);
    }
    encode_counts(&mut buf, &counts);
    let ghost t3 = tgt.file();
    write_target(tgt, target_offset, buf.as_slice(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t3, tgt.file(), base@);
    }
    Ok(())
}

fn populate_hash_map<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    counted: bool,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let (count, index_offset) = if counted {
        let c = read_i64_at(src, source_offset)?;
        let p = match source_offset.checked_add(8) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        (Some(c), p)
    } else {
        (None, source_offset)
    };
    let block = read_index_block(src, index_offset)?;
    let remapped = remap_slots(src, tgt, map, &block, hash_size, base, fuel)?;

    let mut buf = Vec::new();
    if let Some(count) = count {
        let cb = crate::bytes::u64_to_be_bytes(count as u64);
        let mut k: usize = 0;
        while k < 8
            invariant
                k <= 8,
            decreases 8 - k,
        {
            buf.push(cb[k]);
            k += 1;
        }
    }
    encode_slots(&mut buf, &remapped);
    let ghost t1 = tgt.file();
    write_target(tgt, target_offset, buf.as_slice(), base)?;
    proof {
        lemma_target_trans(old(tgt).file(), t1, tgt.file(), base@);
    }
    Ok(())
}

fn populate_kv_pair<S: Store, T: Store, M: OffsetMapping>(
    src: &mut S,
    tgt: &mut T,
    map: &mut M,
    source_offset: i64,
    target_offset: i64,
    tag: Tag,
    hash_size: usize,
    base: Ghost<int>,
    fuel: u64,
) -> (r: Result<()>)
    requires
        hash_size <= 0xffff,
        0 <= base@ <= target_offset,
        base@ <= old(tgt).file().len(),
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> target_ok(old(tgt).file(), final(tgt).file(), base@),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len(),
    decreases fuel, 7int,
{
    let mut kv = crate::sorted_store::read_kv_pair(src, Slot::new(source_offset, tag), hash_size)?;
    // remap the key and value slots, and write the pair in the same form
    let ghost t0 = tgt.file();
    kv.key_slot = remap_slot(src, tgt, map, kv.key_slot, hash_size, base, fuel)?;
    let ghost t1 = tgt.file();
    kv.value_slot = remap_slot(src, tgt, map, kv.value_slot, hash_size, base, fuel)?;
    let ghost t2 = tgt.file();
    let bytes = kv.encode(tag)?;
    write_target(tgt, target_offset, bytes.as_slice(), base)?;
    proof {
        lemma_target_trans(t0, t1, t2, base@);
        lemma_target_trans(t0, t2, tgt.file(), base@);
    }
    Ok(())
}

/// Compacts the data `slot` points to into the target, and returns the slot
/// as it reads there. Nothing the target held before changes.
pub fn compact_slot<S: Store, T: Store, M: OffsetMapping>(src: &mut S, tgt: &mut T, map: &mut M, slot: Slot, hash_size: usize) -> (r: Result<Slot>)
    ensures
        final(src).file() == old(src).file(),
        r is Ok ==> final(tgt).file().len() >= old(tgt).file().len()
            && final(tgt).file().subrange(0, old(tgt).file().len() as int) == old(tgt).file(),
{
    if hash_size > 0xffff {
        return Err(Error::InvalidHashSize);
    }
    let fuel = walk_bound(src, ARRAY_LIST_HEADER_LENGTH as u64)?;
    let ghost base = tgt.file().len() as int;
    let r = remap_slot(src, tgt, map, slot, hash_size, Ghost(base), fuel);
    proof {
        if r is Ok {
            assert(old(tgt).file().subrange(0, base) =~= old(tgt).file());
        }
    }
    r
}

} // verus!
