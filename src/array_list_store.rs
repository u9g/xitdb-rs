//! The array list's slot walk (`read_array_list_slot`) over a [`Store`],
//! checked by Verus.
//!
//! In read mode it returns exactly the slot the bytes of the file lead to
//! ([`al_read`]). In write mode it creates missing index blocks and copies
//! committed ones, and it never changes a committed byte: everything
//! before `limit` (the crate's `max(tx_start, frozen_at)`) is left as it
//! was, and the slot it returns is at or after `limit`, so writing it can't
//! change committed data either.

#[allow(unused_imports)]
use crate::arith::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;

verus! {

/// The slot `s` is encoded at `pos`.
pub open spec fn slot_at(f: Seq<u8>, pos: int, s: Slot) -> bool {
    0 <= pos && pos + SLOT_LENGTH <= f.len() && slot_encode_spec(s) == f.subrange(pos, pos + SLOT_LENGTH)
}

/// The slot encoded at `pos`, if any.
pub open spec fn slot_spec(f: Seq<u8>, pos: int) -> Option<Slot> {
    if exists|s: Slot| slot_at(f, pos, s) {
        Some(choose|s: Slot| slot_at(f, pos, s))
    } else {
        None
    }
}

/// `f` and `g` agree on everything before `limit`.
pub open spec fn kept_below(f: Seq<u8>, g: Seq<u8>, limit: int) -> bool {
    limit <= f.len() ==> limit <= g.len() && g.subrange(0, limit) == f.subrange(0, limit)
}

proof fn lemma_slot_spec(f: Seq<u8>, pos: int, s: Slot)
    requires
        slot_at(f, pos, s),
    ensures
        slot_spec(f, pos) == Some(s),
{
    let t = choose|t: Slot| slot_at(f, pos, t);
    lemma_slot_encode_injective(s, t);
}

proof fn lemma_overwrite_keeps(f: Seq<u8>, pos: int, data: Seq<u8>, limit: int)
    requires
        0 <= limit <= pos,
    ensures
        kept_below(f, overwrite(f, pos, data), limit),
        overwrite(f, pos, data).len() >= pos + data.len(),
{
    let g = overwrite(f, pos, data);
    if limit <= f.len() {
        assert(g.subrange(0, limit) =~= f.subrange(0, limit));
    }
}

proof fn lemma_kept_trans(f: Seq<u8>, g: Seq<u8>, h: Seq<u8>, limit: int)
    requires
        kept_below(f, g, limit),
        kept_below(g, h, limit),
    ensures
        kept_below(f, h, limit),
{
}

/// The slot walk in read mode, over the bytes: the position of the slot
/// for `key` and the slot there.
pub open spec fn al_read(f: Seq<u8>, index_pos: int, key: int, shift: nat) -> Option<(int, Slot)>
    decreases shift,
{
    if shift >= MAX_BRANCH_LENGTH {
        None
    } else {
        let slot_pos = index_pos + SLOT_LENGTH * digit(key, shift);
        match slot_spec(f, slot_pos) {
            None => None,
            Some(s) => if shift == 0 {
                Some((slot_pos, s))
            } else if s.tag == Tag::Index {
                al_read(f, s.value as int, key, (shift - 1) as nat)
            } else {
                None
            },
        }
    }
}

pub fn read_slot_at<S: Store>(s: &mut S, pos: i64) -> (r: Result<Slot>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> slot_at(old(s).file(), pos as int, r.unwrap()),
{
    let mut buf = [0u8; SLOT_LENGTH];
    s.read_at(pos, &mut buf)?;
    let slot = Slot::from_bytes(&buf)?;
    proof {
        assert(buf@.subrange(0, 9) =~= buf@);
    }
    Ok(slot)
}

pub fn write_slot_at<S: Store>(s: &mut S, pos: i64, slot: Slot) -> (r: Result<()>)
    ensures
        r is Ok ==> 0 <= pos && final(s).file() == overwrite(old(s).file(), pos as int, slot_encode_spec(slot)),
{
    s.write_at(pos, &slot.to_bytes())
}

/// `copy_index_block_if_old`: an index block from before `limit` is copied
/// to the end. `limit` is `None` outside a transaction, where nothing can
/// be written (`Error::ExpectedTxStart`).
pub fn copy_index_block_if_old<S: Store>(s: &mut S, ptr: i64, limit: Option<i64>) -> (r: Result<i64>)
    requires
        limit is Some ==> 0 <= limit.unwrap() <= old(s).file().len(),
    ensures
        r is Ok ==> limit is Some,
        r is Ok ==> r.unwrap() >= limit.unwrap() && kept_below(old(s).file(), final(s).file(), limit.unwrap() as int),
        r is Ok ==> (r.unwrap() == ptr && final(s).file() == old(s).file()) || (r.unwrap() == old(s).file().len()
            && final(s).file() == old(s).file() + old(s).file().subrange(ptr as int, ptr + INDEX_BLOCK_SIZE)),
{
    let limit = match limit {
        Some(l) => l,
        None => return Err(Error::ExpectedTxStart),
    };
    if ptr >= limit {
        return Ok(ptr);
    }
    let mut block = [0u8; INDEX_BLOCK_SIZE];
    s.read_at(ptr, &mut block)?;
    let ghost f = s.file();
    let p = append(s, &block)?;
    proof {
        let g = s.file();
        assert(g.subrange(0, limit as int) =~= f.subrange(0, limit as int));
    }
    Ok(p)
}

/// `read_array_list_slot`.
pub fn read_array_list_slot<S: Store>(
    s: &mut S,
    index_pos: i64,
    key: i64,
    shift: u8,
    write: bool,
    limit: Option<i64>,
) -> (r: Result<SlotPointer>)
    requires
        key >= 0,
        write ==> (limit is Some && 0 <= limit.unwrap() <= old(s).file().len() && index_pos >= limit.unwrap()),
    ensures
        !write ==> final(s).file() == old(s).file(),
        (!write && r is Ok) ==> (r.unwrap().position is Some && al_read(old(s).file(), index_pos as int, key as int, shift as nat)
            == Some((r.unwrap().position.unwrap() as int, r.unwrap().slot))),
        (write && r is Ok) ==> kept_below(old(s).file(), final(s).file(), limit.unwrap() as int),
        (write && r is Ok) ==> (r.unwrap().position is Some && r.unwrap().position.unwrap() >= limit.unwrap()
            && slot_at(final(s).file(), r.unwrap().position.unwrap() as int, r.unwrap().slot)),
    decreases shift,
{
    if shift >= MAX_BRANCH_LENGTH {
        return Err(Error::MaxShiftExceeded);
    }
    let i = (key >> (shift as u32 * BIT_COUNT)) & MASK;
    proof {
        lemma_key_digit(key, shift);
    }
    let slot_pos = match index_pos.checked_add(SLOT_LENGTH as i64 * i) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let slot = read_slot_at(s, slot_pos)?;
    proof {
        lemma_slot_spec(old(s).file(), slot_pos as int, slot);
    }

    if shift == 0 {
        return Ok(SlotPointer::new(Some(slot_pos), slot));
    }

    match slot.tag {
        Tag::None => if !write {
            Err(Error::KeyNotFound)
        } else {
            let ghost f0 = s.file();
            let next_index_pos = append(s, &[0u8; INDEX_BLOCK_SIZE])?;
            let ghost f1 = s.file();
            write_slot_at(s, slot_pos, Slot::new(next_index_pos, Tag::Index))?;
            proof {
                let l = limit.unwrap() as int;
                assert(f1.subrange(0, l) =~= f0.subrange(0, l));
                lemma_overwrite_keeps(f1, slot_pos as int, slot_encode_spec(Slot { value: next_index_pos, tag: Tag::Index, full: false }), l);
                lemma_kept_trans(f0, f1, s.file(), l);
            }
            let ghost f2 = s.file();
            let r = read_array_list_slot(s, next_index_pos, key, shift - 1, write, limit);
            proof {
                if r is Ok {
                    lemma_kept_trans(f0, f2, s.file(), limit.unwrap() as int);
                }
            }
            r
        },
        Tag::Index => {
            let ptr = slot.value;
            let mut next_ptr = ptr;
            let ghost f0 = s.file();
            if write {
                next_ptr = copy_index_block_if_old(s, ptr, limit)?;
                if next_ptr != ptr {
                    let ghost f1 = s.file();
                    write_slot_at(s, slot_pos, Slot::new(next_ptr, Tag::Index))?;
                    proof {
                        let l = limit.unwrap() as int;
                        lemma_overwrite_keeps(f1, slot_pos as int, slot_encode_spec(Slot { value: next_ptr, tag: Tag::Index, full: false }), l);
                        lemma_kept_trans(f0, f1, s.file(), l);
                    }
                }
            }
            let ghost f2 = s.file();
            let r = read_array_list_slot(s, next_ptr, key, shift - 1, write, limit);
            proof {
                if write && r is Ok {
                    lemma_kept_trans(f0, f2, s.file(), limit.unwrap() as int);
                }
            }
            r
        },
        _ => Err(Error::UnexpectedTag),
    }
}

/// The slot index the code computes is nibble `shift` of the key.
proof fn lemma_key_digit(key: i64, shift: u8)
    requires
        key >= 0,
        shift < 16,
    ensures
        ((key >> (shift as u32 * 4u32)) & 15i64) as int == digit(key as int, shift as nat),
        0 <= (key >> (shift as u32 * 4u32)) & 15i64 < 16,
{
    let n: u32 = (shift as u32 * 4u32) as u32;
    let k = key as u64;
    assert((key >> n) & 15i64 == ((k >> (n as u64)) & 15u64) as i64) by (bit_vector)
        requires
            k == key as u64,
            key >= 0i64,
            n < 64u32,
    ;
    vstd::bits::lemma_u64_shr_is_div(k, n as u64);
    lemma_pow16_pow2(shift as nat);
    let q = k >> (n as u64);
    assert(q & 15u64 == q % 16u64) by (bit_vector);
    assert((key >> n) & 15i64 >= 0i64 && (key >> n) & 15i64 < 16i64) by (bit_vector)
        requires
            n < 64u32,
    ;
}

} // verus!
