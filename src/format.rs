//! The binary layout of everything xitdb stores. All integers are big endian.

use crate::crc64;
use crate::error::{Error, Result};
use crate::slot::{SLOT_LENGTH, Slot, Tag};

pub const VERSION: u16 = 1;
pub const MAGIC_NUMBER: [u8; 3] = *b"xit";

pub const BIT_COUNT: u32 = 4;
pub const SLOT_COUNT: usize = 1 << BIT_COUNT;
pub const MASK: i64 = SLOT_COUNT as i64 - 1;
pub const INDEX_BLOCK_SIZE: usize = SLOT_LENGTH * SLOT_COUNT;
pub const MAX_BRANCH_LENGTH: u8 = 16;

// b-tree (backs LinkedArrayList, SortedMap and SortedSet): nodes hold up to
// BTREE_SLOT_COUNT entries
pub const BTREE_SLOT_COUNT: usize = SLOT_COUNT;
pub const BTREE_SPLIT_COUNT: usize = BTREE_SLOT_COUNT.div_ceil(2);
pub const BTREE_NODE_HEADER_SIZE: usize = 2;
pub const BTREE_LEAF_BLOCK_SIZE: usize = BTREE_NODE_HEADER_SIZE + SLOT_LENGTH * BTREE_SLOT_COUNT;
pub const BTREE_BRANCH_BLOCK_SIZE: usize =
    BTREE_NODE_HEADER_SIZE + (SLOT_LENGTH + 8) * BTREE_SLOT_COUNT;
// sorted_map / sorted_set node block: a leaf holds BTREE_SLOT_COUNT entry
// slots; a branch holds child slots, separator slots, then BTREE_SLOT_COUNT
// u64 counts
pub const SORTED_LEAF_BLOCK_SIZE: usize = BTREE_NODE_HEADER_SIZE + SLOT_LENGTH * BTREE_SLOT_COUNT;
pub const SORTED_BRANCH_BLOCK_SIZE: usize =
    BTREE_NODE_HEADER_SIZE + (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT;

pub(crate) fn read_i64(bytes: &[u8]) -> i64 {
    i64::from_be_bytes(bytes[..8].try_into().unwrap())
}

pub(crate) fn read_u64(bytes: &[u8]) -> u64 {
    u64::from_be_bytes(bytes[..8].try_into().unwrap())
}

/// The shift of the root index block of an array list whose last key is
/// `key`: the integer log16 of it, or 0 if it fits in one block.
pub(crate) fn array_list_shift(key: i64) -> u8 {
    if key < SLOT_COUNT as i64 {
        0
    } else {
        ((63 - key.leading_zeros()) / BIT_COUNT) as u8
    }
}

// Header

pub const HEADER_LENGTH: usize = 20;

/// The database header at the start of the file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    /// A random ID that never changes. It is part of every trailer's
    /// checksum, so a replica can't be extended with bytes from a
    /// different file.
    pub file_id: u64,
    pub hash_id: u32,
    pub hash_size: u16,
    /// The file format version.
    pub version: u16,
    pub magic_number: [u8; 3],
}

impl Header {
    pub fn to_bytes(self) -> [u8; HEADER_LENGTH] {
        let mut buf = [0u8; HEADER_LENGTH];
        buf[0..3].copy_from_slice(&self.magic_number);
        // buf[3] is currently unused padding
        buf[4..6].copy_from_slice(&self.version.to_be_bytes());
        buf[6..8].copy_from_slice(&self.hash_size.to_be_bytes());
        buf[8..12].copy_from_slice(&self.hash_id.to_be_bytes());
        buf[12..20].copy_from_slice(&self.file_id.to_be_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8; HEADER_LENGTH]) -> Header {
        Header {
            magic_number: buf[0..3].try_into().unwrap(),
            version: u16::from_be_bytes(buf[4..6].try_into().unwrap()),
            hash_size: u16::from_be_bytes(buf[6..8].try_into().unwrap()),
            hash_id: u32::from_be_bytes(buf[8..12].try_into().unwrap()),
            file_id: read_u64(&buf[12..20]),
        }
    }

    /// Reads a header at the core's current position, so the hash size
    /// and hash id of a database can be checked before opening it.
    pub fn read(core: &mut impl crate::Core) -> Result<Header> {
        let mut buf = [0u8; HEADER_LENGTH];
        core.read(&mut buf)?;
        Ok(Header::from_bytes(&buf))
    }

    pub fn validate(&self) -> Result<()> {
        if self.magic_number != MAGIC_NUMBER {
            return Err(Error::InvalidDatabase);
        }
        if self.version != VERSION {
            return Err(Error::InvalidVersion);
        }
        Ok(())
    }
}

// ArrayListHeader

pub const ARRAY_LIST_HEADER_LENGTH: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArrayListHeader {
    pub ptr: i64,
    pub size: i64,
}

impl ArrayListHeader {
    pub fn to_bytes(self) -> [u8; ARRAY_LIST_HEADER_LENGTH] {
        let mut buf = [0u8; ARRAY_LIST_HEADER_LENGTH];
        buf[0..8].copy_from_slice(&self.size.to_be_bytes());
        buf[8..16].copy_from_slice(&self.ptr.to_be_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8]) -> Result<ArrayListHeader> {
        let size = read_i64(&buf[0..8]);
        let ptr = read_i64(&buf[8..16]);
        if size < 0 || ptr < 0 {
            return Err(Error::ExpectedUnsignedLong);
        }
        Ok(ArrayListHeader { ptr, size })
    }
}

// RootHeader

// the database header is followed by the root header. the top-level data
// is a root slot of any type, and every write to it is a copy-on-write
// transaction that appends a trailer holding the new root slot. the root
// header only caches the latest trailer, so every other committed byte is
// immutable, and a replica stays in sync by copying the bytes it doesn't have.
pub const ROOT_HEADER_START: i64 = HEADER_LENGTH as i64;
// rewritten at every commit, as a cache of the latest trailer.
// the root slot comes first on disk.
pub const ROOT_HEADER_LENGTH: usize = SLOT_LENGTH + 8;
pub const ROOT_HEADER_END: i64 = ROOT_HEADER_START + ROOT_HEADER_LENGTH as i64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RootHeader {
    pub file_size: i64,
    pub root: Slot,
}

impl RootHeader {
    pub fn to_bytes(self) -> [u8; ROOT_HEADER_LENGTH] {
        let mut buf = [0u8; ROOT_HEADER_LENGTH];
        buf[0..SLOT_LENGTH].copy_from_slice(&self.root.to_bytes());
        buf[SLOT_LENGTH..].copy_from_slice(&self.file_size.to_be_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8]) -> Result<RootHeader> {
        Ok(RootHeader {
            root: Slot::from_bytes(&buf[0..SLOT_LENGTH])?,
            file_size: read_i64(&buf[SLOT_LENGTH..SLOT_LENGTH + 8]),
        })
    }
}

// RootTrailer

// appended at the end of every transaction, so the committed bytes (up to
// the root header's file_size) always end with one. the root slot comes
// first on disk.
pub const ROOT_TRAILER_LENGTH: usize = SLOT_LENGTH + 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RootTrailer {
    pub checksum: u64,
    /// Random for every transaction except the first, so separately
    /// written copies of a file can't end up with the same trailers, even
    /// when they write data of the same size. That is how a replica
    /// notices it is being sent bytes from a different history.
    pub commit_id: u64,
    pub root: Slot,
}

impl RootTrailer {
    pub fn new(file_id: u64, position: i64, root: Slot, commit_id: u64) -> RootTrailer {
        RootTrailer {
            checksum: root_trailer_checksum(file_id, position, root, commit_id),
            commit_id,
            root,
        }
    }

    pub fn to_bytes(self) -> [u8; ROOT_TRAILER_LENGTH] {
        let mut buf = [0u8; ROOT_TRAILER_LENGTH];
        buf[0..SLOT_LENGTH].copy_from_slice(&self.root.to_bytes());
        buf[SLOT_LENGTH..SLOT_LENGTH + 8].copy_from_slice(&self.commit_id.to_be_bytes());
        buf[SLOT_LENGTH + 8..].copy_from_slice(&self.checksum.to_be_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8]) -> Result<RootTrailer> {
        Ok(RootTrailer {
            root: Slot::from_bytes(&buf[0..SLOT_LENGTH])?,
            commit_id: read_u64(&buf[SLOT_LENGTH..SLOT_LENGTH + 8]),
            checksum: read_u64(&buf[SLOT_LENGTH + 8..SLOT_LENGTH + 16]),
        })
    }
}

/// CRC-64/XZ of the file ID, the trailer's position, root, and the commit
/// ID, all big endian. Including the file ID and position means the
/// trailer can't be mistaken for one written elsewhere. 64 bits makes it
/// safe to find the last trailer by scanning a file whose root header
/// can't be trusted.
pub fn root_trailer_checksum(file_id: u64, position: i64, root: Slot, commit_id: u64) -> u64 {
    let mut buf = [0u8; 24 + SLOT_LENGTH];
    buf[0..8].copy_from_slice(&file_id.to_be_bytes());
    buf[8..16].copy_from_slice(&position.to_be_bytes());
    buf[16..16 + SLOT_LENGTH].copy_from_slice(&root.to_bytes());
    buf[16 + SLOT_LENGTH..].copy_from_slice(&commit_id.to_be_bytes());
    crc64::checksum(&buf)
}

/// What a replica sends its source, so the source knows which bytes to
/// send back (see [`Database::replication_start`](crate::Database::replication_start)).
///
/// With the `serde` feature, it implements `Serialize` and `Deserialize` as
/// `{"committedSize":123,"checksum":"456"}`, with the u64 checksum as a
/// decimal string, because a JSON number can't always hold it exactly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReplicaState {
    pub committed_size: i64,
    /// The checksum of the trailer that ends the committed bytes. It
    /// covers the file ID and the commit's random ID, so it identifies both
    /// the file and the history that led to the commit.
    pub checksum: u64,
}

// BTreeHeader: a root pointer plus the element count

pub const BTREE_HEADER_LENGTH: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BTreeHeader {
    pub root_ptr: i64,
    pub size: i64,
}

impl BTreeHeader {
    pub fn to_bytes(self) -> [u8; BTREE_HEADER_LENGTH] {
        let mut buf = [0u8; BTREE_HEADER_LENGTH];
        buf[0..8].copy_from_slice(&self.size.to_be_bytes());
        buf[8..16].copy_from_slice(&self.root_ptr.to_be_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8]) -> Result<BTreeHeader> {
        let size = read_i64(&buf[0..8]);
        let root_ptr = read_i64(&buf[8..16]);
        if size < 0 || root_ptr < 0 {
            return Err(Error::ExpectedUnsignedLong);
        }
        Ok(BTreeHeader { root_ptr, size })
    }
}

// KeyValuePair

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyValuePair {
    pub value_slot: Slot,
    pub key_slot: Slot,
    pub hash: Vec<u8>,
}

pub const fn key_value_pair_length(hash_size: usize) -> usize {
    hash_size + SLOT_LENGTH * 2
}

// a KeyValuePair without the hash, which sorted maps don't need. it is the
// key slot followed by the value slot.
pub const SORTED_KEY_VALUE_PAIR_LENGTH: usize = SLOT_LENGTH * 2;

impl KeyValuePair {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.hash.len() + SLOT_LENGTH * 2);
        buf.extend_from_slice(&self.hash);
        buf.extend_from_slice(&self.key_slot.to_bytes());
        buf.extend_from_slice(&self.value_slot.to_bytes());
        buf
    }

    pub fn from_bytes(buf: &[u8], hash_size: usize) -> Result<KeyValuePair> {
        Ok(KeyValuePair {
            hash: buf[..hash_size].to_vec(),
            key_slot: Slot::from_bytes(&buf[hash_size..hash_size + SLOT_LENGTH])?,
            value_slot: Slot::from_bytes(&buf[hash_size + SLOT_LENGTH..hash_size + SLOT_LENGTH * 2])?,
        })
    }

    /// Encodes a [`Tag::KvPair`] or [`Tag::SortedKvPair`] entry. A sorted
    /// entry leaves out the hash.
    pub fn encode(&self, tag: Tag) -> Result<Vec<u8>> {
        match tag {
            Tag::KvPair => Ok(self.to_bytes()),
            Tag::SortedKvPair => {
                let mut buf = Vec::with_capacity(SORTED_KEY_VALUE_PAIR_LENGTH);
                buf.extend_from_slice(&self.key_slot.to_bytes());
                buf.extend_from_slice(&self.value_slot.to_bytes());
                Ok(buf)
            }
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// The encoded length of a [`Tag::KvPair`] or [`Tag::SortedKvPair`] entry.
    pub fn encoded_len(tag: Tag, hash_size: usize) -> Result<usize> {
        match tag {
            Tag::KvPair => Ok(key_value_pair_length(hash_size)),
            Tag::SortedKvPair => Ok(SORTED_KEY_VALUE_PAIR_LENGTH),
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// Decodes a [`Tag::KvPair`] or [`Tag::SortedKvPair`] entry. A sorted
    /// entry has no hash, so it is all zeros.
    pub fn decode(buf: &[u8], tag: Tag, hash_size: usize) -> Result<KeyValuePair> {
        match tag {
            Tag::KvPair => KeyValuePair::from_bytes(buf, hash_size),
            Tag::SortedKvPair => {
                let mut kv = KeyValuePair::from_bytes(buf, 0)?;
                kv.hash = vec![0; hash_size];
                Ok(kv)
            }
            _ => Err(Error::UnexpectedTag),
        }
    }
}

// b-tree nodes

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum BTreeNodeKind {
    Leaf = 0,
    Branch = 1,
}

impl BTreeNodeKind {
    pub fn from_u8(value: u8) -> Result<BTreeNodeKind> {
        match value {
            0 => Ok(BTreeNodeKind::Leaf),
            1 => Ok(BTreeNodeKind::Branch),
            _ => Err(Error::InvalidBTreeNodeKind),
        }
    }
}

/// Reads the kind and entry count from a node's header.
pub fn decode_node_header(buf: &[u8]) -> Result<(BTreeNodeKind, usize)> {
    let kind = BTreeNodeKind::from_u8(buf[0])?;
    let num = buf[1] as usize;
    if num > BTREE_SLOT_COUNT {
        return Err(Error::InvalidBTreeNode);
    }
    Ok((kind, num))
}

pub(crate) fn decode_slots(buf: &[u8]) -> Result<[Slot; SLOT_COUNT]> {
    let mut slots = [Slot::default(); SLOT_COUNT];
    for (i, slot) in slots.iter_mut().enumerate() {
        *slot = Slot::from_bytes(&buf[i * SLOT_LENGTH..(i + 1) * SLOT_LENGTH])?;
    }
    Ok(slots)
}

/// Decodes 16 counts. A negative count can only come from a corrupt file,
/// and is rejected as [`Error::InvalidBTreeNode`].
pub(crate) fn decode_counts(buf: &[u8]) -> Result<[i64; SLOT_COUNT]> {
    let mut counts = [0i64; SLOT_COUNT];
    for (i, count) in counts.iter_mut().enumerate() {
        *count = read_i64(&buf[i * 8..i * 8 + 8]);
        if *count < 0 {
            return Err(Error::InvalidBTreeNode);
        }
    }
    Ok(counts)
}

pub(crate) fn encode_slots(buf: &mut Vec<u8>, slots: &[Slot]) {
    for slot in slots {
        buf.extend_from_slice(&slot.to_bytes());
    }
}

pub(crate) fn encode_counts(buf: &mut Vec<u8>, counts: &[i64]) {
    for count in counts {
        buf.extend_from_slice(&count.to_be_bytes());
    }
}

/// A node of the count-augmented b-tree behind a linked array list: a leaf
/// holds value slots; a branch holds child slots (tagged
/// [`Tag::Index`]) plus a per-child subtree count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BTreeNode {
    pub kind: BTreeNodeKind,
    pub num: usize,
    pub values: [Slot; BTREE_SLOT_COUNT],
    pub children: [Slot; BTREE_SLOT_COUNT],
    pub counts: [i64; BTREE_SLOT_COUNT],
}

/// Checks that `rank` is the index of an entry of a leaf with `num`
/// entries (or, with `allow_end`, the position just past them).
pub(crate) fn check_rank(rank: i64, num: usize, allow_end: bool) -> Result<usize> {
    match usize::try_from(rank) {
        Ok(rank) if rank < num || (allow_end && rank == num) => Ok(rank),
        _ => Err(Error::InvalidBTreeNode),
    }
}

impl BTreeNode {
    pub fn empty(kind: BTreeNodeKind, num: usize) -> BTreeNode {
        BTreeNode {
            kind,
            num,
            values: [Slot::default(); BTREE_SLOT_COUNT],
            children: [Slot::default(); BTREE_SLOT_COUNT],
            counts: [0; BTREE_SLOT_COUNT],
        }
    }

    pub fn subtree_count(&self) -> i64 {
        match self.kind {
            BTreeNodeKind::Leaf => self.num as i64,
            BTreeNodeKind::Branch => self.counts[..self.num].iter().fold(0, |sum, &count| sum.wrapping_add(count)),
        }
    }

    pub fn to_bytes(self) -> Vec<u8> {
        let size = match self.kind {
            BTreeNodeKind::Leaf => BTREE_LEAF_BLOCK_SIZE,
            BTreeNodeKind::Branch => BTREE_BRANCH_BLOCK_SIZE,
        };
        let mut buf = Vec::with_capacity(size);
        buf.push(self.kind as u8);
        buf.push(self.num as u8);
        match self.kind {
            BTreeNodeKind::Leaf => encode_slots(&mut buf, &self.values),
            BTreeNodeKind::Branch => {
                encode_slots(&mut buf, &self.children);
                encode_counts(&mut buf, &self.counts);
            }
        }
        buf
    }
}

/// A node of the count-augmented B+tree behind sorted maps and sets, keyed
/// on byte strings ordered lexicographically. A leaf holds
/// [`Tag::SortedKvPair`] entries in ascending key order; a branch holds
/// child slots, separator slots (the smallest key in each child's subtree;
/// `separators[0]` is an unused sentinel), and per-child subtree counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SortedNode {
    pub kind: BTreeNodeKind,
    pub num: usize,
    pub entries: [Slot; BTREE_SLOT_COUNT],
    pub children: [Slot; BTREE_SLOT_COUNT],
    pub separators: [Slot; BTREE_SLOT_COUNT],
    pub counts: [i64; BTREE_SLOT_COUNT],
}

impl SortedNode {
    pub fn empty(kind: BTreeNodeKind, num: usize) -> SortedNode {
        SortedNode {
            kind,
            num,
            entries: [Slot::default(); BTREE_SLOT_COUNT],
            children: [Slot::default(); BTREE_SLOT_COUNT],
            separators: [Slot::default(); BTREE_SLOT_COUNT],
            counts: [0; BTREE_SLOT_COUNT],
        }
    }

    pub fn subtree_count(&self) -> i64 {
        match self.kind {
            BTreeNodeKind::Leaf => self.num as i64,
            BTreeNodeKind::Branch => self.counts[..self.num].iter().fold(0, |sum, &count| sum.wrapping_add(count)),
        }
    }

    pub fn to_bytes(self) -> Vec<u8> {
        let size = match self.kind {
            BTreeNodeKind::Leaf => SORTED_LEAF_BLOCK_SIZE,
            BTreeNodeKind::Branch => SORTED_BRANCH_BLOCK_SIZE,
        };
        let mut buf = Vec::with_capacity(size);
        buf.push(self.kind as u8);
        buf.push(self.num as u8);
        match self.kind {
            BTreeNodeKind::Leaf => encode_slots(&mut buf, &self.entries),
            BTreeNodeKind::Branch => {
                encode_slots(&mut buf, &self.children);
                encode_slots(&mut buf, &self.separators);
                encode_counts(&mut buf, &self.counts);
            }
        }
        buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shift_matches_log16() {
        assert_eq!(array_list_shift(0), 0);
        assert_eq!(array_list_shift(15), 0);
        assert_eq!(array_list_shift(16), 1);
        assert_eq!(array_list_shift(255), 1);
        assert_eq!(array_list_shift(256), 2);
        assert_eq!(array_list_shift(4095), 2);
        assert_eq!(array_list_shift(4096), 3);
        for key in 16..100_000i64 {
            let expected = ((key as f64).ln() / 16f64.ln()) as u8;
            assert_eq!(array_list_shift(key), expected, "key {key}");
        }
    }
}
