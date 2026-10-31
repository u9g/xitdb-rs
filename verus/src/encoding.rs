//! The on-disk encodings of `src/slot.rs` and `src/format.rs`.
//!
//! Each `*_to_bytes` / `*_from_bytes` pair is executable code that mirrors
//! the crate's, and is proved to round-trip in both directions: decoding an
//! encoding gives back the value, and every byte string that decodes
//! successfully is the encoding of what it decodes to (so there is exactly
//! one encoding per value, and no two values share one).

use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

// big-endian integers

pub open spec fn be_u64_spec(b: Seq<u8>) -> u64 {
    ((b[0] as u64) << 56u64) | ((b[1] as u64) << 48u64) | ((b[2] as u64) << 40u64) | ((b[3] as u64)
        << 32u64) | ((b[4] as u64) << 24u64) | ((b[5] as u64) << 16u64) | ((b[6] as u64) << 8u64)
        | (b[7] as u64)
}

pub open spec fn u64_be_spec(x: u64) -> Seq<u8> {
    seq![
        (x >> 56u64) as u8,
        (x >> 48u64) as u8,
        (x >> 40u64) as u8,
        (x >> 32u64) as u8,
        (x >> 24u64) as u8,
        (x >> 16u64) as u8,
        (x >> 8u64) as u8,
        x as u8,
    ]
}

proof fn lemma_u64_bytes(x: u64)
    by (bit_vector)
    ensures
        ((((x >> 56u64) as u8) as u64) << 56u64) | ((((x >> 48u64) as u8) as u64) << 48u64) | ((((x
            >> 40u64) as u8) as u64) << 40u64) | ((((x >> 32u64) as u8) as u64) << 32u64) | ((((x
            >> 24u64) as u8) as u64) << 24u64) | ((((x >> 16u64) as u8) as u64) << 16u64) | ((((x
            >> 8u64) as u8) as u64) << 8u64) | ((x as u8) as u64) == x,
{
}

proof fn lemma_bytes_u64(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8)
    by (bit_vector)
    ensures
        ({
            let x = ((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((
            b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64)
                << 8u64) | (b7 as u64);
            &&& (x >> 56u64) as u8 == b0
            &&& (x >> 48u64) as u8 == b1
            &&& (x >> 40u64) as u8 == b2
            &&& (x >> 32u64) as u8 == b3
            &&& (x >> 24u64) as u8 == b4
            &&& (x >> 16u64) as u8 == b5
            &&& (x >> 8u64) as u8 == b6
            &&& x as u8 == b7
        }),
{
}

/// `u64::from_be_bytes(..)` of `u64::to_be_bytes(x)` is `x`.
pub proof fn lemma_be_u64_roundtrip(x: u64)
    ensures
        u64_be_spec(x).len() == 8,
        be_u64_spec(u64_be_spec(x)) == x,
{
    lemma_u64_bytes(x);
}

/// `u64::to_be_bytes(..)` of `u64::from_be_bytes(b)` is `b`.
pub proof fn lemma_u64_be_roundtrip(b: Seq<u8>)
    requires
        b.len() == 8,
    ensures
        u64_be_spec(be_u64_spec(b)) == b,
{
    lemma_bytes_u64(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    assert(u64_be_spec(be_u64_spec(b)) =~= b);
}

/// Two's complement reinterpretation, as `x as u64` / `x as i64` do.
pub open spec fn i2u(x: i64) -> u64 {
    #[verifier::truncate]
    (x as u64)
}

pub open spec fn u2i(x: u64) -> i64 {
    #[verifier::truncate]
    (x as i64)
}

proof fn lemma_i2u_bv(x: i64)
    by (bit_vector)
    ensures
        (#[verifier::truncate] ((#[verifier::truncate] (x as u64)) as i64)) == x,
{
}

proof fn lemma_u2i_bv(x: u64)
    by (bit_vector)
    ensures
        (#[verifier::truncate] ((#[verifier::truncate] (x as i64)) as u64)) == x,
{
}

pub proof fn lemma_i64_u64_roundtrip(x: i64, y: u64)
    ensures
        u2i(i2u(x)) == x,
        i2u(u2i(y)) == y,
{
    lemma_i2u_bv(x);
    lemma_u2i_bv(y);
}

pub fn u64_to_be_bytes(x: u64) -> (r: [u8; 8])
    ensures
        r@ == u64_be_spec(x),
{
    let r = [
        (x >> 56) as u8,
        (x >> 48) as u8,
        (x >> 40) as u8,
        (x >> 32) as u8,
        (x >> 24) as u8,
        (x >> 16) as u8,
        (x >> 8) as u8,
        x as u8,
    ];
    assert(r@ =~= u64_be_spec(x));
    r
}

pub fn u64_from_be_bytes(b: &[u8]) -> (r: u64)
    requires
        b@.len() == 8,
    ensures
        r == be_u64_spec(b@),
{
    ((b[0] as u64) << 56) | ((b[1] as u64) << 48) | ((b[2] as u64) << 40) | ((b[3] as u64) << 32)
        | ((b[4] as u64) << 24) | ((b[5] as u64) << 16) | ((b[6] as u64) << 8) | (b[7] as u64)
}

pub open spec fn be_u16_spec(b: Seq<u8>) -> u16 {
    ((b[0] as u16) << 8u16) | (b[1] as u16)
}

pub open spec fn u16_be_spec(x: u16) -> Seq<u8> {
    seq![(x >> 8u16) as u8, x as u8]
}

proof fn lemma_u16_bytes(x: u16)
    by (bit_vector)
    ensures
        ((((x >> 8u16) as u8) as u16) << 8u16) | ((x as u8) as u16) == x,
{
}

proof fn lemma_bytes_u16(b0: u8, b1: u8)
    by (bit_vector)
    ensures
        ((((b0 as u16) << 8u16) | (b1 as u16)) >> 8u16) as u8 == b0,
        (((b0 as u16) << 8u16) | (b1 as u16)) as u8 == b1,
{
}

pub open spec fn be_u32_spec(b: Seq<u8>) -> u32 {
    ((b[0] as u32) << 24u32) | ((b[1] as u32) << 16u32) | ((b[2] as u32) << 8u32) | (b[3] as u32)
}

pub open spec fn u32_be_spec(x: u32) -> Seq<u8> {
    seq![(x >> 24u32) as u8, (x >> 16u32) as u8, (x >> 8u32) as u8, x as u8]
}

proof fn lemma_u32_bytes(x: u32)
    by (bit_vector)
    ensures
        ((((x >> 24u32) as u8) as u32) << 24u32) | ((((x >> 16u32) as u8) as u32) << 16u32) | ((((x
            >> 8u32) as u8) as u32) << 8u32) | ((x as u8) as u32) == x,
{
}

proof fn lemma_bytes_u32(b0: u8, b1: u8, b2: u8, b3: u8)
    by (bit_vector)
    ensures
        ({
            let x = ((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (
            b3 as u32);
            &&& (x >> 24u32) as u8 == b0
            &&& (x >> 16u32) as u8 == b1
            &&& (x >> 8u32) as u8 == b2
            &&& x as u8 == b3
        }),
{
}

// Tag (src/slot.rs)

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Tag {
    None,
    Index,
    ArrayList,
    LinkedArrayList,
    HashMap,
    KvPair,
    Bytes,
    ShortBytes,
    Uint,
    Int,
    Float,
    HashSet,
    CountedHashMap,
    CountedHashSet,
    SortedMap,
    SortedSet,
    SortedKvPair,
}

/// `tag as u8`, the enum's `#[repr(u8)]` discriminant.
pub open spec fn tag_byte_spec(t: Tag) -> u8 {
    match t {
        Tag::None => 0,
        Tag::Index => 1,
        Tag::ArrayList => 2,
        Tag::LinkedArrayList => 3,
        Tag::HashMap => 4,
        Tag::KvPair => 5,
        Tag::Bytes => 6,
        Tag::ShortBytes => 7,
        Tag::Uint => 8,
        Tag::Int => 9,
        Tag::Float => 10,
        Tag::HashSet => 11,
        Tag::CountedHashMap => 12,
        Tag::CountedHashSet => 13,
        Tag::SortedMap => 14,
        Tag::SortedSet => 15,
        Tag::SortedKvPair => 16,
    }
}

pub fn tag_to_u8(t: Tag) -> (r: u8)
    ensures
        r == tag_byte_spec(t),
        r <= 16,
{
    match t {
        Tag::None => 0,
        Tag::Index => 1,
        Tag::ArrayList => 2,
        Tag::LinkedArrayList => 3,
        Tag::HashMap => 4,
        Tag::KvPair => 5,
        Tag::Bytes => 6,
        Tag::ShortBytes => 7,
        Tag::Uint => 8,
        Tag::Int => 9,
        Tag::Float => 10,
        Tag::HashSet => 11,
        Tag::CountedHashMap => 12,
        Tag::CountedHashSet => 13,
        Tag::SortedMap => 14,
        Tag::SortedSet => 15,
        Tag::SortedKvPair => 16,
    }
}

/// `Tag::from_u8`: accepts exactly the bytes that are some tag's
/// discriminant, and returns that tag.
pub fn tag_from_u8(v: u8) -> (r: Option<Tag>)
    ensures
        r matches Some(t) ==> tag_byte_spec(t) == v,
        r is None <==> v > 16,
{
    match v {
        0 => Some(Tag::None),
        1 => Some(Tag::Index),
        2 => Some(Tag::ArrayList),
        3 => Some(Tag::LinkedArrayList),
        4 => Some(Tag::HashMap),
        5 => Some(Tag::KvPair),
        6 => Some(Tag::Bytes),
        7 => Some(Tag::ShortBytes),
        8 => Some(Tag::Uint),
        9 => Some(Tag::Int),
        10 => Some(Tag::Float),
        11 => Some(Tag::HashSet),
        12 => Some(Tag::CountedHashMap),
        13 => Some(Tag::CountedHashSet),
        14 => Some(Tag::SortedMap),
        15 => Some(Tag::SortedSet),
        16 => Some(Tag::SortedKvPair),
        _ => None,
    }
}

pub proof fn lemma_tag_byte_injective(a: Tag, b: Tag)
    ensures
        tag_byte_spec(a) == tag_byte_spec(b) ==> a == b,
{
}

// Slot (src/slot.rs)

pub const SLOT_LENGTH: usize = 9;

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct Slot {
    pub value: i64,
    pub tag: Tag,
    pub full: bool,
}

pub open spec fn slot_tag_byte_spec(s: Slot) -> u8 {
    if s.full {
        tag_byte_spec(s.tag) | 0x80u8
    } else {
        tag_byte_spec(s.tag)
    }
}

pub open spec fn slot_encode_spec(s: Slot) -> Seq<u8> {
    seq![slot_tag_byte_spec(s)] + u64_be_spec(i2u(s.value))
}

proof fn lemma_tag_byte_bits(t: u8, full: bool)
    by (bit_vector)
    requires
        t <= 16,
    ensures
        full ==> ((t | 0x80u8) & 0x80u8) != 0 && (t | 0x80u8) & 0x7fu8 == t,
        !full ==> (t & 0x80u8) == 0 && t & 0x7fu8 == t,
{
}

proof fn lemma_tag_byte_split(b: u8)
    by (bit_vector)
    ensures
        (b & 0x80u8) != 0 ==> (b & 0x7fu8) | 0x80u8 == b,
        (b & 0x80u8) == 0 ==> (b & 0x7fu8) == b,
        (b & 0x7fu8) <= 127,
{
}

/// `Slot::to_bytes`: the tag byte, with the top bit set if the slot is
/// full, then the value as a big-endian i64.
pub fn slot_to_bytes(s: Slot) -> (r: [u8; SLOT_LENGTH])
    ensures
        r@ == slot_encode_spec(s),
{
    let mut tag_byte = tag_to_u8(s.tag);
    if s.full {
        tag_byte = tag_byte | 0b1000_0000;
    }
    let v = u64_to_be_bytes(s.value as u64);
    let r = [tag_byte, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]];
    assert(r@ =~= slot_encode_spec(s));
    r
}

/// `Slot::from_bytes`, with `Error::UnexpectedTag` as `None`.
pub fn slot_from_bytes(bytes: &[u8]) -> (r: Option<Slot>)
    requires
        bytes@.len() >= SLOT_LENGTH,
    ensures
        r matches Some(s) ==> slot_encode_spec(s) == bytes@.subrange(0, SLOT_LENGTH as int),
        r is None <==> (bytes@[0] & 0x7fu8) > 16,
{
    let full = bytes[0] & 0b1000_0000 != 0;
    let tag = tag_from_u8(bytes[0] & 0b0111_1111);
    match tag {
        None => None,
        Some(tag) => {
            let value_bytes = slice_subrange(bytes, 1, SLOT_LENGTH);
            let value = u64_from_be_bytes(value_bytes) as i64;
            let s = Slot { value, tag, full };
            proof {
                let b = bytes@;
                lemma_tag_byte_split(b[0]);
                lemma_u64_be_roundtrip(b.subrange(1, 9));
                lemma_i64_u64_roundtrip(value, be_u64_spec(b.subrange(1, 9)));
                assert(slot_encode_spec(s) =~= b.subrange(0, 9));
            }
            Some(s)
        },
    }
}

/// Decoding the encoding of any slot gives back that slot.
pub proof fn lemma_slot_roundtrip(s: Slot)
    ensures
        slot_encode_spec(s).len() == SLOT_LENGTH,
        (slot_encode_spec(s)[0] & 0x7fu8) == tag_byte_spec(s.tag),
        (slot_encode_spec(s)[0] & 0x80u8 != 0) == s.full,
        u2i(be_u64_spec(slot_encode_spec(s).subrange(1, 9))) == s.value,
{
    lemma_tag_byte_bits(tag_byte_spec(s.tag), s.full);
    lemma_be_u64_roundtrip(i2u(s.value));
    lemma_i64_u64_roundtrip(s.value, 0);
    assert(slot_encode_spec(s).subrange(1, 9) =~= u64_be_spec(i2u(s.value)));
}

/// The encoding is injective, so `from_bytes` never confuses two slots.
pub proof fn lemma_slot_encode_injective(a: Slot, b: Slot)
    requires
        slot_encode_spec(a) == slot_encode_spec(b),
    ensures
        a == b,
{
    lemma_slot_roundtrip(a);
    lemma_slot_roundtrip(b);
    lemma_tag_byte_injective(a.tag, b.tag);
}

/// `slot_from_bytes(slot_to_bytes(s)) == Some(s)`, checked on the
/// executable functions themselves.
pub fn check_slot_roundtrip(s: Slot)
    ensures
        true,
{
    let bytes = slot_to_bytes(s);
    let decoded = slot_from_bytes(&bytes);
    proof {
        lemma_slot_roundtrip(s);
    }
    match decoded {
        Some(d) => {
            proof {
                assert(bytes@.subrange(0, 9) =~= bytes@);
                lemma_slot_encode_injective(d, s);
            }
            assert(d == s);
        },
        None => {
            assert(false);
        },
    }
}

// Header (src/format.rs)

pub const HEADER_LENGTH: usize = 20;

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct Header {
    pub file_id: u64,
    pub hash_id: u32,
    pub hash_size: u16,
    pub version: u16,
    pub magic_number: [u8; 3],
}

pub open spec fn header_encode_spec(h: Header) -> Seq<u8> {
    h.magic_number@ + seq![0u8] + u16_be_spec(h.version) + u16_be_spec(h.hash_size) + u32_be_spec(
        h.hash_id,
    ) + u64_be_spec(h.file_id)
}

pub open spec fn header_decode_spec(b: Seq<u8>) -> Header {
    Header {
        magic_number: [b[0], b[1], b[2]],
        version: be_u16_spec(b.subrange(4, 6)),
        hash_size: be_u16_spec(b.subrange(6, 8)),
        hash_id: be_u32_spec(b.subrange(8, 12)),
        file_id: be_u64_spec(b.subrange(12, 20)),
    }
}

pub fn header_to_bytes(h: Header) -> (r: [u8; HEADER_LENGTH])
    ensures
        r@ == header_encode_spec(h),
{
    let m = h.magic_number;
    let f = u64_to_be_bytes(h.file_id);
    let r = [
        m[0],
        m[1],
        m[2],
        0,
        (h.version >> 8) as u8,
        h.version as u8,
        (h.hash_size >> 8) as u8,
        h.hash_size as u8,
        (h.hash_id >> 24) as u8,
        (h.hash_id >> 16) as u8,
        (h.hash_id >> 8) as u8,
        h.hash_id as u8,
        f[0],
        f[1],
        f[2],
        f[3],
        f[4],
        f[5],
        f[6],
        f[7],
    ];
    assert(r@ =~= header_encode_spec(h));
    r
}

pub fn header_from_bytes(b: &[u8; HEADER_LENGTH]) -> (r: Header)
    ensures
        r == header_decode_spec(b@),
{
    let f = u64_from_be_bytes(slice_subrange(b.as_slice(), 12, 20));
    Header {
        magic_number: [b[0], b[1], b[2]],
        version: ((b[4] as u16) << 8) | (b[5] as u16),
        hash_size: ((b[6] as u16) << 8) | (b[7] as u16),
        hash_id: ((b[8] as u32) << 24) | ((b[9] as u32) << 16) | ((b[10] as u32) << 8) | (
        b[11] as u32),
        file_id: f,
    }
}

proof fn lemma_header_fields(h: Header)
    ensures
        header_encode_spec(h).len() == HEADER_LENGTH,
        header_encode_spec(h).subrange(0, 3) == h.magic_number@,
        header_encode_spec(h).subrange(4, 6) == u16_be_spec(h.version),
        header_encode_spec(h).subrange(6, 8) == u16_be_spec(h.hash_size),
        header_encode_spec(h).subrange(8, 12) == u32_be_spec(h.hash_id),
        header_encode_spec(h).subrange(12, 20) == u64_be_spec(h.file_id),
{
    let e = header_encode_spec(h);
    assert(e.subrange(0, 3) =~= h.magic_number@);
    assert(e.subrange(4, 6) =~= u16_be_spec(h.version));
    assert(e.subrange(6, 8) =~= u16_be_spec(h.hash_size));
    assert(e.subrange(8, 12) =~= u32_be_spec(h.hash_id));
    assert(e.subrange(12, 20) =~= u64_be_spec(h.file_id));
}

/// Decoding an encoded header gives back the header.
pub proof fn lemma_header_roundtrip(h: Header)
    ensures
        header_encode_spec(h).len() == HEADER_LENGTH,
        header_decode_spec(header_encode_spec(h)) == h,
{
    let e = header_encode_spec(h);
    lemma_header_fields(h);
    lemma_u16_bytes(h.version);
    lemma_u16_bytes(h.hash_size);
    lemma_u32_bytes(h.hash_id);
    lemma_u64_bytes(h.file_id);
    let d = header_decode_spec(e);
    assert(d.version == h.version);
    assert(d.hash_size == h.hash_size);
    assert(d.hash_id == h.hash_id);
    assert(d.file_id == h.file_id);
    assert(e[0] == e.subrange(0, 3)[0] && e[1] == e.subrange(0, 3)[1] && e[2] == e.subrange(0, 3)[2]);
    assert(d.magic_number@ =~= h.magic_number@);
    assert(d.magic_number == h.magic_number);
}

/// `Header::from_bytes` ignores byte 3, the padding, so a header read from
/// disk re-encodes to the same bytes exactly when that byte is zero.
pub proof fn lemma_header_reencode(b: Seq<u8>)
    requires
        b.len() == HEADER_LENGTH,
    ensures
        header_encode_spec(header_decode_spec(b)) == b <==> b[3] == 0,
{
    let h = header_decode_spec(b);
    lemma_bytes_u16(b[4], b[5]);
    lemma_bytes_u16(b[6], b[7]);
    lemma_bytes_u32(b[8], b[9], b[10], b[11]);
    lemma_bytes_u64(b[12], b[13], b[14], b[15], b[16], b[17], b[18], b[19]);
    let e = header_encode_spec(h);
    if b[3] == 0 {
        assert(e =~= b);
    } else {
        assert(e[3] != b[3]);
    }
}

// ArrayListHeader and BTreeHeader (src/format.rs): `size` then pointer,
// both big-endian i64s that must be non-negative

pub open spec fn size_ptr_encode_spec(size: i64, ptr: i64) -> Seq<u8> {
    u64_be_spec(i2u(size)) + u64_be_spec(i2u(ptr))
}

pub fn size_ptr_to_bytes(size: i64, ptr: i64) -> (r: [u8; 16])
    ensures
        r@ == size_ptr_encode_spec(size, ptr),
{
    let s = u64_to_be_bytes(size as u64);
    let p = u64_to_be_bytes(ptr as u64);
    let r = [
        s[0],
        s[1],
        s[2],
        s[3],
        s[4],
        s[5],
        s[6],
        s[7],
        p[0],
        p[1],
        p[2],
        p[3],
        p[4],
        p[5],
        p[6],
        p[7],
    ];
    assert(r@ =~= size_ptr_encode_spec(size, ptr));
    r
}

/// `ArrayListHeader::from_bytes` / `BTreeHeader::from_bytes`: `None` is
/// `Error::ExpectedUnsignedLong`.
pub fn size_ptr_from_bytes(b: &[u8]) -> (r: Option<(i64, i64)>)
    requires
        b@.len() == 16,
    ensures
        r matches Some((size, ptr)) ==> size >= 0 && ptr >= 0 && size_ptr_encode_spec(size, ptr)
            == b@,
        r is None ==> !exists|size: i64, ptr: i64|
            size >= 0 && ptr >= 0 && size_ptr_encode_spec(size, ptr) == b@,
{
    let size = u64_from_be_bytes(slice_subrange(b, 0, 8)) as i64;
    let ptr = u64_from_be_bytes(slice_subrange(b, 8, 16)) as i64;
    proof {
        lemma_u64_be_roundtrip(b@.subrange(0, 8));
        lemma_u64_be_roundtrip(b@.subrange(8, 16));
        lemma_i64_u64_roundtrip(size, be_u64_spec(b@.subrange(0, 8)));
        lemma_i64_u64_roundtrip(ptr, be_u64_spec(b@.subrange(8, 16)));
        assert(size_ptr_encode_spec(size, ptr) =~= b@);
    }
    if size < 0 || ptr < 0 {
        proof {
            assert forall|s2: i64, p2: i64|
                s2 >= 0 && p2 >= 0 && size_ptr_encode_spec(s2, p2) == b@ implies false by {
                lemma_be_u64_roundtrip(i2u(s2));
                lemma_be_u64_roundtrip(i2u(p2));
                lemma_i64_u64_roundtrip(s2, 0);
                lemma_i64_u64_roundtrip(p2, 0);
                assert(size_ptr_encode_spec(s2, p2).subrange(0, 8) =~= u64_be_spec(i2u(s2)));
                assert(size_ptr_encode_spec(s2, p2).subrange(8, 16) =~= u64_be_spec(i2u(p2)));
            }
        }
        return None;
    }
    Some((size, ptr))
}

pub proof fn lemma_size_ptr_roundtrip(size: i64, ptr: i64)
    ensures
        ({
            let e = size_ptr_encode_spec(size, ptr);
            u2i(be_u64_spec(e.subrange(0, 8))) == size && u2i(be_u64_spec(e.subrange(8, 16)))
                == ptr
        }),
{
    let e = size_ptr_encode_spec(size, ptr);
    lemma_be_u64_roundtrip(i2u(size));
    lemma_be_u64_roundtrip(i2u(ptr));
    lemma_i64_u64_roundtrip(size, 0);
    lemma_i64_u64_roundtrip(ptr, 0);
    assert(e.subrange(0, 8) =~= u64_be_spec(i2u(size)));
    assert(e.subrange(8, 16) =~= u64_be_spec(i2u(ptr)));
}

} // verus!
