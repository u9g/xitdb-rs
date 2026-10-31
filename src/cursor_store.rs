//! The file side of cursors (`src/cursor.rs`) over a [`Store`], checked by
//! Verus: reading byte arrays, the positions of a key/value pair's slots,
//! and the byte writer's steps.
//!
//! Reads leave the file unchanged. The writer only writes inside the byte
//! array it appended in this transaction, at its end, and at the slot that
//! points to it, so nothing committed changes other than the root header.
//! Offsets read from a corrupt file fail with an error instead of
//! overflowing.

#![allow(unused_variables)] // ghost arguments, erased in normal builds

use crate::error::{Error, Result};
use crate::format::*;
use crate::path_store::*;
use crate::slot::*;
use crate::sorted::short_bytes_value;
use crate::sorted_store::checked_len;
use crate::store::*;
use vstd::prelude::*;

verus! {

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

/// A byte array's value and format tag, as `read_bytes_object` reads them.
pub fn read_bytes_value<S: Store>(s: &mut S, slot: Slot, max_size: Option<u64>) -> (r: Result<(Vec<u8>, Option<[u8; 2]>)>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> max_size is Some ==> r.unwrap().0@.len() <= max_size.unwrap(),
{
    match slot.tag {
        Tag::None => Ok((Vec::new(), None)),
        Tag::Bytes => {
            let mut lbuf = [0u8; 8];
            s.read_at(slot.value, &mut lbuf)?;
            let value_size = read_i64(&lbuf);
            if value_size < 0 {
                return Err(Error::ExpectedUnsignedLong);
            }
            if let Some(max) = max_size {
                if value_size as u64 > max {
                    return Err(Error::StreamTooLong);
                }
            }
            let start = match slot.value.checked_add(8) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            let len = checked_len(s, start, value_size)?;
            let mut value = zeros(len);
            s.read_at(start, value.as_mut_slice())?;
            let format_tag = if slot.full {
                let tag_pos = match start.checked_add(value_size) {
                    Some(p) => p,
                    None => return Err(Error::InvalidOffset),
                };
                let mut tag = [0u8; 2];
                s.read_at(tag_pos, &mut tag)?;
                Some(tag)
            } else {
                None
            };
            Ok((value, format_tag))
        },
        Tag::ShortBytes => {
            let (buf, len) = short_bytes_value(slot);
            if let Some(max) = max_size {
                if len as u64 > max {
                    return Err(Error::StreamTooLong);
                }
            }
            let format_tag = if slot.full { Some([buf[6], buf[7]]) } else { None };
            let mut value = Vec::new();
            let mut i: usize = 0;
            while i < len
                invariant
                    i <= len <= 8,
                    value@.len() == i,
                decreases len - i,
            {
                value.push(buf[i]);
                i += 1;
            }
            Ok((value, format_tag))
        },
        _ => Err(Error::UnexpectedTag),
    }
}

/// Where a byte array's bytes start and how many there are, for a reader:
/// `(start, size, inline bytes of short bytes)`.
pub fn reader_bounds<S: Store>(s: &mut S, slot: Slot) -> (r: Result<(u64, u64, Option<[u8; 8]>)>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap().2 is Some ==> r.unwrap().0 == 0 && r.unwrap().1 <= 8,
        r is Ok ==> r.unwrap().2 is None ==> r.unwrap().0 <= i64::MAX && r.unwrap().0 + r.unwrap().1 <= u64::MAX,
{
    match slot.tag {
        Tag::Bytes => {
            let mut lbuf = [0u8; 8];
            s.read_at(slot.value, &mut lbuf)?;
            let size = read_i64(&lbuf);
            let start = match slot.value.checked_add(8) {
                Some(p) => p,
                None => return Err(Error::InvalidOffset),
            };
            if start < 0 {
                return Err(Error::InvalidOffset);
            }
            let size = checked_len(s, start, size)? as u64;
            Ok((start as u64, size, None))
        },
        Tag::ShortBytes => {
            // short bytes are stored in the slot itself, which we already have
            let (buf, len) = short_bytes_value(slot);
            Ok((0, len as u64, Some(buf)))
        },
        _ => Err(Error::UnexpectedTag),
    }
}

/// `CursorReader::read_fully`'s check and position: `None` is
/// `Error::EndOfStream`.
pub fn reader_range(size: u64, start: u64, relative: u64, len: usize) -> (r: Option<u64>)
    ensures
        r is Some ==> relative <= size && size - relative >= len && r.unwrap() == start + relative,
{
    if size < relative || size - relative < len as u64 {
        return None;
    }
    match start.checked_add(relative) {
        Some(p) => Some(p),
        None => None,
    }
}

/// The positions of a key/value pair's key and value slots.
pub fn kv_slot_positions(kv_value: i64, key_offset: i64) -> (r: Result<(i64, i64)>)
    requires
        0 <= key_offset,
    ensures
        r is Ok ==> r.unwrap().0 == kv_value + key_offset && r.unwrap().1 == kv_value + key_offset + 9,
{
    let key_slot_pos = match kv_value.checked_add(key_offset) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    let value_slot_pos = match key_slot_pos.checked_add(SLOT_LENGTH as i64) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    Ok((key_slot_pos, value_slot_pos))
}

/// `WriteCursor::writer`: appends the byte array's length placeholder.
/// Returns where it is, and where the bytes start.
pub fn writer_begin<S: Store>(s: &mut S, limit: i64) -> (r: Result<(i64, i64)>)
    requires
        0 <= limit <= old(s).file().len(),
    ensures
        r is Ok ==> r.unwrap().0 >= limit && r.unwrap().1 == r.unwrap().0 + 8,
        r is Ok ==> r.unwrap().1 == final(s).file().len(),
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    let ptr_pos = append_tx(s, &[0u8; 8], limit)?;
    let start_position = s.len()?;
    Ok((ptr_pos, start_position))
}

/// `CursorWriter::write_bytes`: writes `buf` at the writer's position.
/// Returns the new position and size.
pub fn writer_write<S: Store>(s: &mut S, start: i64, size: i64, relative: i64, buf: &[u8], limit: i64) -> (r: Result<(i64, i64)>)
    requires
        0 <= limit <= start,
        limit <= old(s).file().len(),
        0 <= size,
        0 <= relative,
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
        r is Ok ==> r.unwrap().0 >= 0 && r.unwrap().1 >= r.unwrap().0 && r.unwrap().1 >= size,
{
    if size < relative {
        return Err(Error::EndOfStream);
    }
    if buf.len() as u64 > i64::MAX as u64 {
        return Err(Error::StreamTooLong);
    }
    let new_position = match relative.checked_add(buf.len() as i64) {
        Some(p) => p,
        None => return Err(Error::StreamTooLong),
    };
    let end = match start.checked_add(size) {
        Some(e) => e,
        None => return Err(Error::InvalidOffset),
    };

    // another allocation may now follow this byte array. extending it would
    // overwrite that allocation.
    if new_position > size && s.len()? != end {
        return Err(Error::UnexpectedWriterPosition);
    }

    let pos = match start.checked_add(relative) {
        Some(p) => p,
        None => return Err(Error::InvalidOffset),
    };
    write_tx(s, pos, buf, limit)?;
    let new_size = if size > new_position { size } else { new_position };
    Ok((new_position, new_size))
}

/// `CursorWriter::finish`: writes the format tag after the bytes, the
/// length, and the slot pointing to the byte array.
pub fn writer_finish<S: Store>(
    s: &mut S,
    slot: Slot,
    start: i64,
    size: i64,
    format_tag: Option<[u8; 2]>,
    position: i64,
    limit: i64,
) -> (r: Result<Slot>)
    requires
        0 <= limit <= slot.value,
        limit <= old(s).file().len(),
        writable(position as int, limit as int, old(s).file().len() as int),
    ensures
        r is Ok ==> tx_hdr_ok(old(s).file(), final(s).file(), limit as int),
{
    let ghost f0 = s.file();
    let mut slot = slot;
    if let Some(format_tag) = format_tag {
        slot = slot.with_full(true);
        let format_tag_pos = s.len()?;
        let end = match start.checked_add(size) {
            Some(e) => e,
            None => return Err(Error::InvalidOffset),
        };
        if end != format_tag_pos {
            return Err(Error::UnexpectedWriterPosition);
        }
        append_tx(s, &format_tag, limit)?;
    }
    let ghost f1 = s.file();
    proof {
        if format_tag is None {
            assert(tx_hdr_ok(f0, f1, limit as int));
        }
    }
    write_tx(s, slot.value, &crate::bytes::u64_to_be_bytes(size as u64), limit)?;
    let ghost f2 = s.file();
    proof {
        lemma_hdr_trans(f0, f1, f2, limit as int);
    }
    write_slot_tx(s, position, slot, limit)?;
    proof {
        lemma_hdr_trans(f0, f2, s.file(), limit as int);
    }
    Ok(slot)
}

/// The bytes short `value` packs into: the value, zeros, then the format
/// tag in the last two bytes if there is one.
pub open spec fn short_packed(value: Seq<u8>, format_tag: Option<[u8; 2]>) -> Seq<u8> {
    Seq::new(8, |i: int| if i < value.len() {
        value[i]
    } else if format_tag is Some && i >= 6 {
        format_tag.unwrap()@[i - 6]
    } else {
        0u8
    })
}

/// `WriteData` for short bytes: the slot holding them inline.
pub fn short_bytes_slot(value: &[u8], format_tag: Option<[u8; 2]>) -> (r: Slot)
    requires
        value@.len() <= (if format_tag is Some { 6int } else { 8int }),
        forall|i: int| 0 <= i < value@.len() ==> #[trigger] value@[i] != 0,
    ensures
        r.tag == Tag::ShortBytes,
        r.full == (format_tag is Some),
        crate::bytes::u64_be_spec(crate::bytes::i2u(r.value)) == short_packed(value@, format_tag),
{
    let mut buf = [0u8; 8];
    let mut i: usize = 0;
    while i < value.len()
        invariant
            i <= value@.len() <= 8,
            forall|k: int| 0 <= k < i ==> #[trigger] buf@[k] == value@[k],
            forall|k: int| i <= k < 8 ==> #[trigger] buf@[k] == 0,
        decreases value.len() - i,
    {
        buf[i] = value[i];
        i += 1;
    }
    if let Some(tag) = format_tag {
        buf[6] = tag[0];
        buf[7] = tag[1];
    }
    let v = crate::bytes::u64_from_be_bytes(buf.as_slice()) as i64;
    proof {
        crate::bytes::lemma_u64_be_roundtrip(buf@);
        crate::bytes::lemma_i64_u64_roundtrip(v, crate::bytes::be_u64_spec(buf@));
        assert(buf@ =~= short_packed(value@, format_tag));
    }
    Slot::new(v, Tag::ShortBytes).with_full(format_tag.is_some())
}

/// Unpacking short bytes gives back the value and format tag they were
/// packed from.
pub proof fn lemma_short_bytes_roundtrip(value: Seq<u8>, format_tag: Option<[u8; 2]>, buf: Seq<u8>, len: int)
    requires
        value.len() <= (if format_tag is Some { 6int } else { 8int }),
        forall|i: int| 0 <= i < value.len() ==> #[trigger] value[i] != 0,
        buf == short_packed(value, format_tag),
        0 <= len <= (if format_tag is Some { 6int } else { 8int }),
        forall|i: int| 0 <= i < len ==> #[trigger] buf[i] != 0,
        len < (if format_tag is Some { 6int } else { 8int }) ==> buf[len] == 0,
    ensures
        len == value.len(),
        buf.subrange(0, len) == value,
        format_tag is Some ==> buf[6] == format_tag.unwrap()@[0] && buf[7] == format_tag.unwrap()@[1],
{
    let total: int = if format_tag is Some { 6 } else { 8 };
    if len < value.len() {
        assert(0 <= len < 8);
        assert(buf[len] == value[len]);
        assert(false);
    }
    if len > value.len() {
        let n = value.len() as int;
        assert(0 <= n < total);
        assert(buf[n] == 0u8);
        assert(false);
    }
    assert(buf.subrange(0, len) =~= value);
}

} // verus!
