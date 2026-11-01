use crate::bytes::*;
use crate::error::{Error, Result};
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// The type of the data a [`Slot`] points to or contains.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
#[repr(u8)]
pub enum Tag {
    #[default]
    None = 0,
    Index = 1,
    ArrayList = 2,
    LinkedArrayList = 3,
    HashMap = 4,
    KvPair = 5,
    Bytes = 6,
    ShortBytes = 7,
    Uint = 8,
    Int = 9,
    Float = 10,
    HashSet = 11,
    CountedHashMap = 12,
    CountedHashSet = 13,
    SortedMap = 14,
    SortedSet = 15,
    SortedKvPair = 16,
}

/// The discriminant of a tag, as `tag as u8` gives it.
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

impl Tag {
    /// Converts a byte read from disk into a tag, so corrupted data
    /// yields an error instead of being silently propagated.
    pub fn from_u8(value: u8) -> (r: Result<Tag>)
        ensures
            r matches Ok(t) ==> tag_byte_spec(t) == value,
            r is Err <==> value > 16,
    {
        Ok(match value {
            0 => Tag::None,
            1 => Tag::Index,
            2 => Tag::ArrayList,
            3 => Tag::LinkedArrayList,
            4 => Tag::HashMap,
            5 => Tag::KvPair,
            6 => Tag::Bytes,
            7 => Tag::ShortBytes,
            8 => Tag::Uint,
            9 => Tag::Int,
            10 => Tag::Float,
            11 => Tag::HashSet,
            12 => Tag::CountedHashMap,
            13 => Tag::CountedHashSet,
            14 => Tag::SortedMap,
            15 => Tag::SortedSet,
            16 => Tag::SortedKvPair,
            _ => return Err(Error::UnexpectedTag),
        })
    }

    /// The tag's discriminant (`self as u8`).
    pub fn to_u8(self) -> (r: u8)
        ensures
            r == tag_byte_spec(self),
            r <= 16,
    {
        match self {
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
}

pub proof fn lemma_tag_byte_injective(a: Tag, b: Tag)
    ensures
        tag_byte_spec(a) == tag_byte_spec(b) ==> a == b,
{
}

pub const SLOT_LENGTH: usize = 9;

/// The basic unit of storage: a 64-bit value plus a tag saying what it is.
/// Scalars are stored inline in the value; everything else stores its
/// position in the database.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
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

/// The encoding of a slot: the tag byte, with the top bit set if the slot
/// is full, then the value as a big-endian i64.
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

/// Decoding the encoding of a slot gives back the slot.
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

/// No two slots share an encoding.
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

impl Slot {
    pub const fn new(value: i64, tag: Tag) -> (r: Slot)
        ensures
            r == (Slot { value, tag, full: false }),
    {
        Slot { value, tag, full: false }
    }

    pub const fn with_tag(self, tag: Tag) -> (r: Slot)
        ensures
            r == (Slot { tag, ..self }),
    {
        Slot { tag, ..self }
    }

    pub const fn with_full(self, full: bool) -> (r: Slot)
        ensures
            r == (Slot { full, ..self }),
    {
        Slot { full, ..self }
    }

    pub fn is_empty(self) -> (r: bool)
        ensures
            r == (self.tag == Tag::None && !self.full),
    {
        matches!(self.tag, Tag::None) && !self.full
    }

    pub fn to_bytes(self) -> (r: [u8; SLOT_LENGTH])
        ensures
            r@ == slot_encode_spec(self),
    {
        let mut tag_byte = self.tag.to_u8();
        if self.full {
            tag_byte |= 0b1000_0000;
        }
        let v = u64_to_be_bytes(self.value as u64);
        let r = [tag_byte, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]];
        assert(r@ =~= slot_encode_spec(self));
        r
    }

    /// Decodes a slot without validating its tag. Unknown tags are
    /// reported as [`Error::UnexpectedTag`].
    pub fn from_bytes(bytes: &[u8]) -> (r: Result<Slot>)
        requires
            bytes@.len() >= SLOT_LENGTH,
        ensures
            r matches Ok(s) ==> slot_encode_spec(s) == bytes@.subrange(0, SLOT_LENGTH as int),
            r is Err <==> (bytes@[0] & 0x7fu8) > 16,
    {
        let full = bytes[0] & 0b1000_0000 != 0;
        let tag = Tag::from_u8(bytes[0] & 0b0111_1111)?;
        let value = u64_from_be_bytes(slice_subrange(bytes, 1, SLOT_LENGTH)) as i64;
        let s = Slot { value, tag, full };
        proof {
            let b = bytes@;
            lemma_tag_byte_split(b[0]);
            lemma_u64_be_roundtrip(b.subrange(1, 9));
            lemma_i64_u64_roundtrip(value, be_u64_spec(b.subrange(1, 9)));
            assert(slot_encode_spec(s) =~= b.subrange(0, 9));
        }
        Ok(s)
    }
}

/// A slot plus the position in the database it was read from, if any.
/// Only slot pointers with a position can be written to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SlotPointer {
    pub position: Option<i64>,
    pub slot: Slot,
}

impl SlotPointer {
    pub const fn new(position: Option<i64>, slot: Slot) -> (r: SlotPointer)
        ensures
            r == (SlotPointer { position, slot }),
    {
        SlotPointer { position, slot }
    }

    pub const fn with_slot(self, slot: Slot) -> (r: SlotPointer)
        ensures
            r == (SlotPointer { position: self.position, slot }),
    {
        SlotPointer { position: self.position, slot }
    }
}

} // verus!
