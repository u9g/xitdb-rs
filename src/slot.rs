use crate::error::{Error, Result};

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

impl Tag {
    /// Converts a byte read from disk into a tag, so corrupted data
    /// yields an error instead of being silently propagated.
    pub fn from_u8(value: u8) -> Result<Tag> {
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

impl Slot {
    pub const fn new(value: i64, tag: Tag) -> Slot {
        Slot { value, tag, full: false }
    }

    pub const fn with_tag(self, tag: Tag) -> Slot {
        Slot { tag, ..self }
    }

    pub const fn with_full(self, full: bool) -> Slot {
        Slot { full, ..self }
    }

    pub fn is_empty(self) -> bool {
        self.tag == Tag::None && !self.full
    }

    pub fn to_bytes(self) -> [u8; SLOT_LENGTH] {
        let mut buf = [0u8; SLOT_LENGTH];
        let mut tag_byte = self.tag as u8;
        if self.full {
            tag_byte |= 0b1000_0000;
        }
        buf[0] = tag_byte;
        buf[1..].copy_from_slice(&self.value.to_be_bytes());
        buf
    }

    /// Decodes a slot without validating its tag. Unknown tags are
    /// reported as [`Error::UnexpectedTag`].
    pub fn from_bytes(bytes: &[u8]) -> Result<Slot> {
        let full = bytes[0] & 0b1000_0000 != 0;
        let tag = Tag::from_u8(bytes[0] & 0b0111_1111)?;
        let value = i64::from_be_bytes(bytes[1..SLOT_LENGTH].try_into().unwrap());
        Ok(Slot { value, tag, full })
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
    pub const fn new(position: Option<i64>, slot: Slot) -> SlotPointer {
        SlotPointer { position, slot }
    }

    pub const fn with_slot(self, slot: Slot) -> SlotPointer {
        SlotPointer { position: self.position, slot }
    }
}
