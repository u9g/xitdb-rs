//! The hash map's slot walk (`read_map_slot`) and removal
//! (`remove_map_slot`) over a [`Store`], checked by Verus.
//!
//! In read mode the walk returns exactly what the file's bytes lead to
//! ([`map_read`]). In write mode, and in removal, nothing before `limit`
//! (the crate's `max(tx_start, frozen_at)`) changes, and the slot the walk
//! returns for writing is at or after `limit`, so committed data stays as
//! it was.

use crate::array_list_store::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;

verus! {

/// Which part of a hash map entry the walk returns.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MapTarget {
    KvPair,
    Key,
    Value,
}

pub struct MapSlot {
    pub slot_ptr: SlotPointer,
    pub is_empty: bool,
}

/// Nibble `offset` of the big-endian hash `h`, counting from its least
/// significant end, or 0 past the end of the hash.
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

/// `hash_nibble`.
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
        assert(byte & 0xf < 16 && byte >> 4 < 16) by (bit_vector);
    }
    (if offset % 2 == 0 { byte & 0xf } else { byte >> 4 }) as usize
}

/// The key/value pair `(hash, key, value)` is encoded at `pos`.
pub open spec fn kv_at(f: Seq<u8>, pos: int, hash_size: int, kv: (Seq<u8>, Slot, Slot)) -> bool {
    let (h, k, v) = kv;
    &&& 0 <= pos
    &&& pos + hash_size + 2 * SLOT_LENGTH <= f.len()
    &&& h.len() == hash_size
    &&& h + slot_encode_spec(k) + slot_encode_spec(v) == f.subrange(pos, pos + hash_size + 2 * SLOT_LENGTH)
}

pub open spec fn kv_spec(f: Seq<u8>, pos: int, hash_size: int) -> Option<(Seq<u8>, Slot, Slot)> {
    if exists|kv: (Seq<u8>, Slot, Slot)| kv_at(f, pos, hash_size, kv) {
        Some(choose|kv: (Seq<u8>, Slot, Slot)| kv_at(f, pos, hash_size, kv))
    } else {
        None
    }
}

proof fn lemma_kv_spec(f: Seq<u8>, pos: int, hash_size: int, kv: (Seq<u8>, Slot, Slot))
    requires
        kv_at(f, pos, hash_size, kv),
    ensures
        kv_spec(f, pos, hash_size) == Some(kv),
{
    let other = choose|o: (Seq<u8>, Slot, Slot)| kv_at(f, pos, hash_size, o);
    let (h, k, v) = kv;
    let (h2, k2, v2) = other;
    let e = f.subrange(pos, pos + hash_size + 18);
    lemma_slot_roundtrip(k);
    lemma_slot_roundtrip(v);
    lemma_slot_roundtrip(k2);
    lemma_slot_roundtrip(v2);
    assert(h =~= e.subrange(0, hash_size));
    assert(h2 =~= e.subrange(0, hash_size));
    assert(slot_encode_spec(k) =~= e.subrange(hash_size, hash_size + 9));
    assert(slot_encode_spec(k2) =~= e.subrange(hash_size, hash_size + 9));
    assert(slot_encode_spec(v) =~= e.subrange(hash_size + 9, hash_size + 18));
    assert(slot_encode_spec(v2) =~= e.subrange(hash_size + 9, hash_size + 18));
    lemma_slot_encode_injective(k, k2);
    lemma_slot_encode_injective(v, v2);
}

/// The slot the target asks for, given the entry's slot at `slot_pos` and
/// its pair at `kv_pos`.
pub open spec fn target_spec(target: MapTarget, slot_pos: int, slot: Slot, kv_pos: int, hash_size: int, kv: (Seq<u8>, Slot, Slot)) -> (int, Slot) {
    match target {
        MapTarget::KvPair => (slot_pos, slot),
        MapTarget::Key => (kv_pos + hash_size, kv.1),
        MapTarget::Value => (kv_pos + hash_size + SLOT_LENGTH, kv.2),
    }
}

/// The walk in read mode, over the bytes.
pub open spec fn map_read(f: Seq<u8>, index_pos: int, hash: Seq<u8>, offset: int, hash_size: int, target: MapTarget) -> Option<(int, Slot)>
    decreases hash_size * 2 + 1 - offset,
{
    if offset > hash_size * 2 || offset < 0 {
        None
    } else {
        let slot_pos = index_pos + SLOT_LENGTH * nibble(hash, offset);
        match slot_spec(f, slot_pos) {
            None => None,
            Some(slot) => if slot.tag == Tag::Index {
                map_read(f, slot.value as int, hash, offset + 1, hash_size, target)
            } else if slot.tag == Tag::KvPair {
                match kv_spec(f, slot.value as int, hash_size) {
                    Some(kv) => if kv.0 == hash {
                        Some(target_spec(target, slot_pos, slot, slot.value as int, hash_size, kv))
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
        }
    }
}

fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

fn zero_bytes(n: usize) -> (r: Vec<u8>)
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

fn copy_slice(b: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == b@,
{
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < b.len()
        invariant
            i <= b@.len(),
            r@ == b@.subrange(0, i as int),
        decreases b.len() - i,
    {
        r.push(b[i]);
        i += 1;
        assert(r@ =~= b@.subrange(0, i as int));
    }
    assert(b@.subrange(0, i as int) =~= b@);
    r
}

/// Reads the key/value pair at `pos`.
fn read_kv_at<S: Store>(s: &mut S, pos: i64, hash_size: usize) -> (r: Result<KeyValuePair>)
    requires
        hash_size <= 0xffff,
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> kv_at(old(s).file(), pos as int, hash_size as int, (r.unwrap().hash@, r.unwrap().key_slot, r.unwrap().value_slot)),
{
    let mut buf = zero_bytes(key_value_pair_length(hash_size));
    s.read_at(pos, buf.as_mut_slice())?;
    let kv = KeyValuePair::from_bytes(buf.as_slice(), hash_size)?;
    proof {
        assert(buf@.subrange(0, hash_size + 18) =~= buf@);
    }
    Ok(kv)
}

fn target_slot_ptr(target: MapTarget, slot_pos: i64, slot: Slot, kv_pos: i64, hash_size: usize, kv: &KeyValuePair) -> (r: Result<SlotPointer>)
    requires
        hash_size <= 0xffff,
    ensures
        r is Ok ==> r.unwrap().position is Some && (r.unwrap().position.unwrap() as int, r.unwrap().slot) == target_spec(
            target,
            slot_pos as int,
            slot,
            kv_pos as int,
            hash_size as int,
            (kv.hash@, kv.key_slot, kv.value_slot),
        ),
        r is Ok ==> target != MapTarget::KvPair ==> r.unwrap().position.unwrap() >= kv_pos,
{
    let key_slot_pos = match kv_pos.checked_add(hash_size as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let value_slot_pos = match key_slot_pos.checked_add(SLOT_LENGTH as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    Ok(match target {
        MapTarget::KvPair => SlotPointer::new(Some(slot_pos), slot),
        MapTarget::Key => SlotPointer::new(Some(key_slot_pos), kv.key_slot),
        MapTarget::Value => SlotPointer::new(Some(value_slot_pos), kv.value_slot),
    })
}

/// `read_map_slot`.
pub fn read_map_slot<S: Store>(
    s: &mut S,
    index_pos: i64,
    key_hash: &[u8],
    key_offset: usize,
    write: bool,
    target: MapTarget,
    limit: Option<i64>,
    hash_size: usize,
) -> (r: Result<MapSlot>)
    requires
        hash_size <= 0xffff,
        key_hash@.len() == hash_size,
        key_offset <= hash_size * 2 + 1,
        write ==> (limit is Some && 0 <= limit.unwrap() <= old(s).file().len() && index_pos >= limit.unwrap()),
    ensures
        !write ==> final(s).file() == old(s).file(),
        (!write && r is Ok) ==> (r.unwrap().slot_ptr.position is Some && map_read(old(s).file(), index_pos as int, key_hash@,
            key_offset as int, hash_size as int, target) == Some((r.unwrap().slot_ptr.position.unwrap() as int, r.unwrap().slot_ptr.slot))),
        (write && r is Ok) ==> kept_below(old(s).file(), final(s).file(), limit.unwrap() as int),
        (write && r is Ok) ==> (r.unwrap().slot_ptr.position is Some && r.unwrap().slot_ptr.position.unwrap() >= limit.unwrap()),
    decreases hash_size * 2 + 1 - key_offset,
{
    let max_offset = hash_size * 8 / 4;
    if key_offset > max_offset {
        return Err(Error::KeyOffsetExceeded);
    }

    let i = hash_nibble(key_hash, key_offset);
    let slot_pos = match index_pos.checked_add((SLOT_LENGTH * i) as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let slot = read_slot_at(s, slot_pos)?;
    let ptr = slot.value;
    let ghost f0 = s.file();
    let ghost l = if write { limit.unwrap() as int } else { 0 };
    proof {
        lemma_slot_spec(f0, slot_pos as int, slot);
    }

    match slot.tag {
        Tag::None => if !write {
            Err(Error::KeyNotFound)
        } else {
            // write hash and key/val slots
            let kv = KeyValuePair { value_slot: Slot::new(0, Tag::None), key_slot: Slot::new(0, Tag::None), hash: copy_slice(key_hash) };
            let hash_pos = append(s, &kv.to_bytes())?;
            let ghost f1 = s.file();
            // point slot to hash pos
            let next_slot = Slot::new(hash_pos, Tag::KvPair);
            write_slot_at(s, slot_pos, next_slot)?;
            proof {
                assert(f1.subrange(0, l) =~= f0.subrange(0, l));
                lemma_overwrite_keeps(f1, slot_pos as int, slot_encode_spec(next_slot), l);
                lemma_kept_trans(f0, f1, s.file(), l);
            }
            let slot_ptr = target_slot_ptr(target, slot_pos, next_slot, hash_pos, hash_size, &kv)?;
            Ok(MapSlot { slot_ptr, is_empty: true })
        },
        Tag::Index => {
            let mut next_ptr = ptr;
            if write {
                next_ptr = copy_index_block_if_old(s, ptr, limit)?;
                if next_ptr != ptr {
                    // make slot point to the copied block
                    let ghost f1 = s.file();
                    write_slot_at(s, slot_pos, Slot::new(next_ptr, Tag::Index))?;
                    proof {
                        lemma_overwrite_keeps(f1, slot_pos as int, slot_encode_spec(Slot { value: next_ptr, tag: Tag::Index, full: false }), l);
                        lemma_kept_trans(f0, f1, s.file(), l);
                    }
                }
            }
            if key_offset + 1 > hash_size * 2 + 1 {
                return Err(Error::KeyOffsetExceeded);
            }
            let ghost f2 = s.file();
            let r = read_map_slot(s, next_ptr, key_hash, key_offset + 1, write, target, limit, hash_size);
            proof {
                if write && r is Ok {
                    lemma_kept_trans(f0, f2, s.file(), l);
                }
            }
            r
        },
        Tag::KvPair => {
            let kv = read_kv_at(s, ptr, hash_size)?;
            proof {
                lemma_kv_spec(f0, ptr as int, hash_size as int, (kv.hash@, kv.key_slot, kv.value_slot));
            }
            if bytes_eq(kv.hash.as_slice(), key_hash) {
                if write {
                    let lim = match limit {
                        Some(l) => l,
                        None => return Err(Error::ExpectedTxStart),
                    };
                    if ptr < lim {
                        let hash_pos = append(s, &kv.to_bytes())?;
                        let ghost f1 = s.file();
                        let next_slot = Slot::new(hash_pos, Tag::KvPair);
                        write_slot_at(s, slot_pos, next_slot)?;
                        proof {
                            assert(f1.subrange(0, l) =~= f0.subrange(0, l));
                            lemma_overwrite_keeps(f1, slot_pos as int, slot_encode_spec(next_slot), l);
                            lemma_kept_trans(f0, f1, s.file(), l);
                        }
                        let slot_ptr = target_slot_ptr(target, slot_pos, next_slot, hash_pos, hash_size, &kv)?;
                        return Ok(MapSlot { slot_ptr, is_empty: false });
                    }
                }
                let slot_ptr = target_slot_ptr(target, slot_pos, slot, ptr, hash_size, &kv)?;
                return Ok(MapSlot { slot_ptr, is_empty: false });
            }

            // hash collision - different keys
            if !write {
                Err(Error::KeyNotFound)
            } else {
                if key_offset + 1 >= max_offset {
                    return Err(Error::KeyOffsetExceeded);
                }
                let next_i = hash_nibble(kv.hash.as_slice(), key_offset + 1);
                let next_index_pos = append(s, &[0u8; INDEX_BLOCK_SIZE])?;
                let ghost f1 = s.file();
                let moved_pos = match next_index_pos.checked_add((SLOT_LENGTH * next_i) as i64) {
                    Some(p) => p,
                    None => return Err(Error::InvalidOffset),
                };
                write_slot_at(s, moved_pos, slot)?;
                let ghost f2 = s.file();
                proof {
                    assert(f1.subrange(0, l) =~= f0.subrange(0, l));
                    lemma_overwrite_keeps(f1, moved_pos as int, slot_encode_spec(slot), l);
                    lemma_kept_trans(f0, f1, f2, l);
                }
                let res = read_map_slot(s, next_index_pos, key_hash, key_offset + 1, write, target, limit, hash_size)?;
                let ghost f3 = s.file();
                write_slot_at(s, slot_pos, Slot::new(next_index_pos, Tag::Index))?;
                proof {
                    lemma_kept_trans(f0, f2, f3, l);
                    lemma_overwrite_keeps(f3, slot_pos as int, slot_encode_spec(Slot { value: next_index_pos, tag: Tag::Index, full: false }), l);
                    lemma_kept_trans(f0, f3, s.file(), l);
                }
                Ok(res)
            }
        },
        _ => Err(Error::UnexpectedTag),
    }
}

/// `remove_map_slot`: returns the slot that replaces the block at
/// `index_pos`. Blocks are only written if they belong to the current
/// transaction (the root, which the caller copied) or were just copied.
pub fn remove_map_slot<S: Store>(
    s: &mut S,
    index_pos: i64,
    key_hash: &[u8],
    key_offset: usize,
    limit: Option<i64>,
    hash_size: usize,
) -> (r: Result<Slot>)
    requires
        hash_size <= 0xffff,
        key_hash@.len() == hash_size,
        key_offset <= hash_size * 2 + 1,
        limit is Some && 0 <= limit.unwrap() <= old(s).file().len(),
        key_offset == 0 ==> index_pos >= limit.unwrap(),
    ensures
        r is Ok ==> kept_below(old(s).file(), final(s).file(), limit.unwrap() as int),
    decreases hash_size * 2 + 1 - key_offset,
{
    if key_offset > hash_size * 8 / 4 {
        return Err(Error::KeyOffsetExceeded);
    }
    let ghost l = limit.unwrap() as int;
    let ghost f0 = s.file();

    // read block
    let mut buf = [0u8; INDEX_BLOCK_SIZE];
    s.read_at(index_pos, &mut buf)?;
    let mut slot_block = decode_slots(&buf)?;
    let i = hash_nibble(key_hash, key_offset);
    let slot_pos = match index_pos.checked_add((SLOT_LENGTH * i) as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let slot = slot_block[i];

    let next_slot = match slot.tag {
        Tag::None => return Err(Error::KeyNotFound),
        Tag::Index => {
            if key_offset + 1 > hash_size * 2 + 1 {
                return Err(Error::KeyOffsetExceeded);
            }
            remove_map_slot(s, slot.value, key_hash, key_offset + 1, limit, hash_size)?
        },
        Tag::KvPair => {
            let kv = read_kv_at(s, slot.value, hash_size)?;
            if !bytes_eq(kv.hash.as_slice(), key_hash) {
                return Err(Error::KeyNotFound);
            }
            Slot::new(0, Tag::None)
        },
        _ => return Err(Error::UnexpectedTag),
    };
    let ghost f1 = s.file();

    // if we're the root node, just write the new slot and finish
    if key_offset == 0 {
        write_slot_at(s, slot_pos, next_slot)?;
        proof {
            lemma_overwrite_keeps(f1, slot_pos as int, slot_encode_spec(next_slot), l);
            lemma_kept_trans(f0, f1, s.file(), l);
        }
        return Ok(Slot::new(index_pos, Tag::Index));
    }

    // get slot to return if there is only one used slot in this index block
    slot_block[i] = next_slot;
    let mut slot_to_return: Option<Slot> = Some(Slot::new(0, Tag::None));
    let mut j: usize = 0;
    while j < SLOT_COUNT
        invariant
            j <= SLOT_COUNT,
        decreases SLOT_COUNT - j,
    {
        let block_slot = slot_block[j];
        j += 1;
        if matches!(block_slot.tag, Tag::None) {
            continue;
        }
        if let Some(existing) = slot_to_return {
            if !matches!(existing.tag, Tag::None) {
                slot_to_return = None;
                break;
            }
        }
        slot_to_return = Some(block_slot);
    }
    if let Some(slot_to_return) = slot_to_return {
        if matches!(slot_to_return.tag, Tag::None | Tag::KvPair) {
            return Ok(slot_to_return);
        }
    }

    // there was more than one used slot, or a single INDEX slot,
    // so we must keep this index block. update the slot in it,
    // copying the block first unless it belongs to this transaction.
    let next_index_pos = copy_index_block_if_old(s, index_pos, limit)?;
    let ghost f2 = s.file();
    let pos = match next_index_pos.checked_add((SLOT_LENGTH * i) as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    write_slot_at(s, pos, next_slot)?;
    proof {
        lemma_kept_trans(f0, f1, f2, l);
        lemma_overwrite_keeps(f2, pos as int, slot_encode_spec(next_slot), l);
        lemma_kept_trans(f0, f2, s.file(), l);
    }
    Ok(Slot::new(next_index_pos, Tag::Index))
}

} // verus!
