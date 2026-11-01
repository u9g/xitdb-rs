//! The binary layout of everything xitdb stores. All integers are big endian.
//!
//! The encoders and decoders here are checked by Verus against byte-level
//! specifications: each header round-trips, and the trailer checksum is
//! CRC-64/XZ of its fields.

#[allow(unused_imports)]
use crate::arith::*;
use crate::bytes::*;
#[allow(unused_imports)]
use crate::crc64::{self, *};
use crate::error::{Error, Result};
#[allow(unused_imports)]
use crate::slot::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

pub const VERSION: u16 = 1;
pub const MAGIC_NUMBER: [u8; 3] = [0x78, 0x69, 0x74]; // "xit"

pub const BIT_COUNT: u32 = 4;
pub const SLOT_COUNT: usize = 16; // 1 << BIT_COUNT
pub const MASK: i64 = SLOT_COUNT as i64 - 1;
pub const INDEX_BLOCK_SIZE: usize = SLOT_LENGTH * SLOT_COUNT;
pub const MAX_BRANCH_LENGTH: u8 = 16;

// b-tree (backs LinkedArrayList, SortedMap and SortedSet): nodes hold up to
// BTREE_SLOT_COUNT entries
pub const BTREE_SLOT_COUNT: usize = SLOT_COUNT;
pub const BTREE_SPLIT_COUNT: usize = (BTREE_SLOT_COUNT + 1) / 2;
pub const BTREE_NODE_HEADER_SIZE: usize = 2;
pub const BTREE_LEAF_BLOCK_SIZE: usize = BTREE_NODE_HEADER_SIZE + SLOT_LENGTH * BTREE_SLOT_COUNT;
pub const BTREE_BRANCH_BLOCK_SIZE: usize = BTREE_NODE_HEADER_SIZE + (SLOT_LENGTH + 8) * BTREE_SLOT_COUNT;
// sorted_map / sorted_set node block: a leaf holds BTREE_SLOT_COUNT entry
// slots; a branch holds child slots, separator slots, then BTREE_SLOT_COUNT
// u64 counts
pub const SORTED_LEAF_BLOCK_SIZE: usize = BTREE_NODE_HEADER_SIZE + SLOT_LENGTH * BTREE_SLOT_COUNT;
pub const SORTED_BRANCH_BLOCK_SIZE: usize = BTREE_NODE_HEADER_SIZE + (SLOT_LENGTH * 2 + 8) * BTREE_SLOT_COUNT;

pub(crate) fn read_i64(bytes: &[u8]) -> (r: i64)
    requires
        bytes@.len() >= 8,
    ensures
        r == u2i(be_u64_spec(bytes@.subrange(0, 8))),
{
    u64_from_be_bytes(slice_subrange(bytes, 0, 8)) as i64
}

pub(crate) fn read_u64(bytes: &[u8]) -> (r: u64)
    requires
        bytes@.len() >= 8,
    ensures
        r == be_u64_spec(bytes@.subrange(0, 8)),
{
    u64_from_be_bytes(slice_subrange(bytes, 0, 8))
}

/// The shift of the root index block of an array list whose last key is
/// `key`: the integer log16 of it, or 0 if it fits in one block.
pub(crate) fn array_list_shift(key: i64) -> (r: u8)
    ensures
        r as nat == log16(key as int),
        r < MAX_BRANCH_LENGTH,
{
    if key < SLOT_COUNT as i64 {
        0
    } else {
        let lz = (key as u64).leading_zeros();
        proof {
            lemma_leading_zeros(key as u64);
            lemma_log2_log16(key as int);
            lemma_log16_bounds(key as int, 15);
            lemma_pow16_pow2(16);
            vstd::arithmetic::power2::lemma2_to64_rest();
        }
        ((63 - lz) / BIT_COUNT) as u8
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

pub open spec fn header_encode_spec(h: Header) -> Seq<u8> {
    h.magic_number@ + seq![0u8] + u16_be_spec(h.version) + u16_be_spec(h.hash_size) + u32_be_spec(h.hash_id)
        + u64_be_spec(h.file_id)
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

impl Header {
    pub fn to_bytes(self) -> (r: [u8; HEADER_LENGTH])
        ensures
            r@ == header_encode_spec(self),
    {
        let m = self.magic_number;
        let f = u64_to_be_bytes(self.file_id);
        // buf[3] is currently unused padding
        let r = [
            m[0],
            m[1],
            m[2],
            0,
            (self.version >> 8) as u8,
            self.version as u8,
            (self.hash_size >> 8) as u8,
            self.hash_size as u8,
            (self.hash_id >> 24) as u8,
            (self.hash_id >> 16) as u8,
            (self.hash_id >> 8) as u8,
            self.hash_id as u8,
            f[0],
            f[1],
            f[2],
            f[3],
            f[4],
            f[5],
            f[6],
            f[7],
        ];
        assert(r@ =~= header_encode_spec(self));
        r
    }

    pub fn from_bytes(buf: &[u8; HEADER_LENGTH]) -> (r: Header)
        ensures
            r == header_decode_spec(buf@),
    {
        let f = u64_from_be_bytes(slice_subrange(buf.as_slice(), 12, 20));
        Header {
            magic_number: [buf[0], buf[1], buf[2]],
            version: ((buf[4] as u16) << 8) | (buf[5] as u16),
            hash_size: ((buf[6] as u16) << 8) | (buf[7] as u16),
            hash_id: ((buf[8] as u32) << 24) | ((buf[9] as u32) << 16) | ((buf[10] as u32) << 8) | (buf[11] as u32),
            file_id: f,
        }
    }

    pub fn validate(&self) -> (r: Result<()>)
        ensures
            r is Ok <==> self.magic_number == MAGIC_NUMBER && self.version == VERSION,
    {
        if !(self.magic_number[0] == MAGIC_NUMBER[0] && self.magic_number[1] == MAGIC_NUMBER[1]
            && self.magic_number[2] == MAGIC_NUMBER[2]) {
            proof {
                if self.magic_number == MAGIC_NUMBER {
                    assert(self.magic_number[0] == MAGIC_NUMBER[0]);
                }
            }
            return Err(Error::InvalidDatabase);
        }
        assert(self.magic_number@ =~= MAGIC_NUMBER@);
        assert(self.magic_number == MAGIC_NUMBER);
        if self.version != VERSION {
            return Err(Error::InvalidVersion);
        }
        Ok(())
    }
}

// ArrayListHeader and BTreeHeader: the size, then a pointer, both
// non-negative big-endian i64s

pub open spec fn size_ptr_encode_spec(size: i64, ptr: i64) -> Seq<u8> {
    u64_be_spec(i2u(size)) + u64_be_spec(i2u(ptr))
}

fn size_ptr_to_bytes(size: i64, ptr: i64) -> (r: [u8; 16])
    ensures
        r@ == size_ptr_encode_spec(size, ptr),
{
    let s = u64_to_be_bytes(size as u64);
    let p = u64_to_be_bytes(ptr as u64);
    let r = [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7]];
    assert(r@ =~= size_ptr_encode_spec(size, ptr));
    r
}

/// `None` is `Error::ExpectedUnsignedLong`: exactly the bytes that aren't the
/// encoding of a non-negative size and pointer.
fn size_ptr_from_bytes(b: &[u8]) -> (r: Option<(i64, i64)>)
    requires
        b@.len() >= 16,
    ensures
        r matches Some((size, ptr)) ==> size >= 0 && ptr >= 0 && size_ptr_encode_spec(size, ptr) == b@.subrange(0, 16),
        r is None ==> !exists|size: i64, ptr: i64|
            size >= 0 && ptr >= 0 && size_ptr_encode_spec(size, ptr) == b@.subrange(0, 16),
{
    let size = read_i64(slice_subrange(b, 0, 8));
    let ptr = read_i64(slice_subrange(b, 8, 16));
    proof {
        let bb = b@.subrange(0, 16);
        assert(b@.subrange(0, 8).subrange(0, 8) =~= bb.subrange(0, 8));
        assert(b@.subrange(8, 16).subrange(0, 8) =~= bb.subrange(8, 16));
        lemma_u64_be_roundtrip(bb.subrange(0, 8));
        lemma_u64_be_roundtrip(bb.subrange(8, 16));
        lemma_i64_u64_roundtrip(size, be_u64_spec(bb.subrange(0, 8)));
        lemma_i64_u64_roundtrip(ptr, be_u64_spec(bb.subrange(8, 16)));
        assert(size_ptr_encode_spec(size, ptr) =~= bb);
    }
    if size < 0 || ptr < 0 {
        proof {
            let bb = b@.subrange(0, 16);
            assert forall|s2: i64, p2: i64| s2 >= 0 && p2 >= 0 && size_ptr_encode_spec(s2, p2) == bb implies false by {
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

pub const ARRAY_LIST_HEADER_LENGTH: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArrayListHeader {
    pub ptr: i64,
    pub size: i64,
}

impl ArrayListHeader {
    pub fn to_bytes(self) -> (r: [u8; ARRAY_LIST_HEADER_LENGTH])
        ensures
            r@ == size_ptr_encode_spec(self.size, self.ptr),
    {
        size_ptr_to_bytes(self.size, self.ptr)
    }

    pub fn from_bytes(buf: &[u8]) -> (r: Result<ArrayListHeader>)
        requires
            buf@.len() >= ARRAY_LIST_HEADER_LENGTH,
        ensures
            r matches Ok(h) ==> h.size >= 0 && h.ptr >= 0 && size_ptr_encode_spec(h.size, h.ptr) == buf@.subrange(0, 16),
            r is Err ==> !exists|size: i64, ptr: i64|
                size >= 0 && ptr >= 0 && size_ptr_encode_spec(size, ptr) == buf@.subrange(0, 16),
    {
        match size_ptr_from_bytes(buf) {
            Some((size, ptr)) => Ok(ArrayListHeader { ptr, size }),
            None => Err(Error::ExpectedUnsignedLong),
        }
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

pub open spec fn root_header_encode_spec(h: RootHeader) -> Seq<u8> {
    slot_encode_spec(h.root) + u64_be_spec(i2u(h.file_size))
}

impl RootHeader {
    pub fn to_bytes(self) -> (r: [u8; ROOT_HEADER_LENGTH])
        ensures
            r@ == root_header_encode_spec(self),
    {
        let s = self.root.to_bytes();
        let f = u64_to_be_bytes(self.file_size as u64);
        let r = [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7]];
        assert(r@ =~= root_header_encode_spec(self));
        r
    }

    pub fn from_bytes(buf: &[u8]) -> (r: Result<RootHeader>)
        requires
            buf@.len() >= ROOT_HEADER_LENGTH,
        ensures
            r matches Ok(h) ==> root_header_encode_spec(h) == buf@.subrange(0, ROOT_HEADER_LENGTH as int),
            r is Err <==> (buf@[0] & 0x7fu8) > 16,
    {
        let root = Slot::from_bytes(slice_subrange(buf, 0, SLOT_LENGTH))?;
        let file_size = read_i64(slice_subrange(buf, SLOT_LENGTH, SLOT_LENGTH + 8));
        let h = RootHeader { root, file_size };
        proof {
            let b = buf@;
            assert(b.subrange(0, 9).subrange(0, 9) =~= b.subrange(0, 9));
            assert(b.subrange(9, 17).subrange(0, 8) =~= b.subrange(9, 17));
            lemma_u64_be_roundtrip(b.subrange(9, 17));
            lemma_i64_u64_roundtrip(file_size, be_u64_spec(b.subrange(9, 17)));
            assert(root_header_encode_spec(h) =~= b.subrange(0, 17));
        }
        Ok(h)
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

pub open spec fn root_trailer_encode_spec(t: RootTrailer) -> Seq<u8> {
    slot_encode_spec(t.root) + u64_be_spec(t.commit_id) + u64_be_spec(t.checksum)
}

/// What a trailer's checksum covers: the file ID, the trailer's position,
/// root and commit ID.
pub open spec fn trailer_checksum_input(file_id: u64, position: i64, root: Slot, commit_id: u64) -> Seq<u8> {
    u64_be_spec(file_id) + u64_be_spec(i2u(position)) + slot_encode_spec(root) + u64_be_spec(commit_id)
}

impl RootTrailer {
    pub fn new(file_id: u64, position: i64, root: Slot, commit_id: u64) -> (r: RootTrailer)
        ensures
            r.root == root,
            r.commit_id == commit_id,
            r.checksum == crc64_spec(trailer_checksum_input(file_id, position, root, commit_id)),
    {
        RootTrailer { checksum: root_trailer_checksum(file_id, position, root, commit_id), commit_id, root }
    }

    pub fn to_bytes(self) -> (r: [u8; ROOT_TRAILER_LENGTH])
        ensures
            r@ == root_trailer_encode_spec(self),
    {
        let s = self.root.to_bytes();
        let c = u64_to_be_bytes(self.commit_id);
        let k = u64_to_be_bytes(self.checksum);
        let r = [
            s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8],
            c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7],
            k[0], k[1], k[2], k[3], k[4], k[5], k[6], k[7],
        ];
        assert(r@ =~= root_trailer_encode_spec(self));
        r
    }

    pub fn from_bytes(buf: &[u8]) -> (r: Result<RootTrailer>)
        requires
            buf@.len() >= ROOT_TRAILER_LENGTH,
        ensures
            r matches Ok(t) ==> root_trailer_encode_spec(t) == buf@.subrange(0, ROOT_TRAILER_LENGTH as int),
            r is Err <==> (buf@[0] & 0x7fu8) > 16,
    {
        let root = Slot::from_bytes(slice_subrange(buf, 0, SLOT_LENGTH))?;
        let commit_id = read_u64(slice_subrange(buf, SLOT_LENGTH, SLOT_LENGTH + 8));
        let checksum = read_u64(slice_subrange(buf, SLOT_LENGTH + 8, SLOT_LENGTH + 16));
        let t = RootTrailer { root, commit_id, checksum };
        proof {
            let b = buf@;
            assert(b.subrange(0, 9).subrange(0, 9) =~= b.subrange(0, 9));
            assert(b.subrange(9, 17).subrange(0, 8) =~= b.subrange(9, 17));
            assert(b.subrange(17, 25).subrange(0, 8) =~= b.subrange(17, 25));
            lemma_u64_be_roundtrip(b.subrange(9, 17));
            lemma_u64_be_roundtrip(b.subrange(17, 25));
            assert(root_trailer_encode_spec(t) =~= b.subrange(0, 25));
        }
        Ok(t)
    }
}

/// CRC-64/XZ of the file ID, the trailer's position, root, and the commit
/// ID, all big endian. Including the file ID and position means the
/// trailer can't be mistaken for one written elsewhere. 64 bits makes it
/// safe to find the last trailer by scanning a file whose root header
/// can't be trusted.
pub fn root_trailer_checksum(file_id: u64, position: i64, root: Slot, commit_id: u64) -> (r: u64)
    ensures
        r == crc64_spec(trailer_checksum_input(file_id, position, root, commit_id)),
{
    let f = u64_to_be_bytes(file_id);
    let p = u64_to_be_bytes(position as u64);
    let s = root.to_bytes();
    let c = u64_to_be_bytes(commit_id);
    let buf = [
        f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7],
        p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7],
        s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8],
        c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7],
    ];
    assert(buf@ =~= trailer_checksum_input(file_id, position, root, commit_id));
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
    pub fn to_bytes(self) -> (r: [u8; BTREE_HEADER_LENGTH])
        ensures
            r@ == size_ptr_encode_spec(self.size, self.root_ptr),
    {
        size_ptr_to_bytes(self.size, self.root_ptr)
    }

    pub fn from_bytes(buf: &[u8]) -> (r: Result<BTreeHeader>)
        requires
            buf@.len() >= BTREE_HEADER_LENGTH,
        ensures
            r matches Ok(h) ==> h.size >= 0 && h.root_ptr >= 0 && size_ptr_encode_spec(h.size, h.root_ptr) == buf@.subrange(0, 16),
            r is Err ==> !exists|size: i64, ptr: i64|
                size >= 0 && ptr >= 0 && size_ptr_encode_spec(size, ptr) == buf@.subrange(0, 16),
    {
        match size_ptr_from_bytes(buf) {
            Some((size, root_ptr)) => Ok(BTreeHeader { root_ptr, size }),
            None => Err(Error::ExpectedUnsignedLong),
        }
    }
}

// KeyValuePair

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyValuePair {
    pub value_slot: Slot,
    pub key_slot: Slot,
    pub hash: Vec<u8>,
}

pub open spec fn kv_encode_spec(kv: KeyValuePair) -> Seq<u8> {
    kv.hash@ + slot_encode_spec(kv.key_slot) + slot_encode_spec(kv.value_slot)
}

pub open spec fn sorted_kv_encode_spec(kv: KeyValuePair) -> Seq<u8> {
    slot_encode_spec(kv.key_slot) + slot_encode_spec(kv.value_slot)
}

pub const fn key_value_pair_length(hash_size: usize) -> (r: usize)
    requires
        hash_size + SLOT_LENGTH * 2 <= usize::MAX,
    ensures
        r == hash_size + SLOT_LENGTH * 2,
{
    hash_size + SLOT_LENGTH * 2
}

// a KeyValuePair without the hash, which sorted maps don't need. it is the
// key slot followed by the value slot.
pub const SORTED_KEY_VALUE_PAIR_LENGTH: usize = SLOT_LENGTH * 2;

fn push_bytes(buf: &mut Vec<u8>, bytes: &[u8])
    ensures
        final(buf)@ == old(buf)@ + bytes@,
{
    let mut i: usize = 0;
    while i < bytes.len()
        invariant
            i <= bytes@.len(),
            buf@ == old(buf)@ + bytes@.subrange(0, i as int),
        decreases bytes.len() - i,
    {
        buf.push(bytes[i]);
        i += 1;
        assert(buf@ =~= old(buf)@ + bytes@.subrange(0, i as int));
    }
    assert(bytes@.subrange(0, i as int) =~= bytes@);
}

fn copy_bytes(bytes: &[u8], start: usize, end: usize) -> (r: Vec<u8>)
    requires
        start <= end <= bytes@.len(),
    ensures
        r@ == bytes@.subrange(start as int, end as int),
{
    let mut r = Vec::new();
    push_bytes(&mut r, slice_subrange(bytes, start, end));
    assert(r@ =~= bytes@.subrange(start as int, end as int));
    r
}

impl KeyValuePair {
    pub fn to_bytes(&self) -> (r: Vec<u8>)
        ensures
            r@ == kv_encode_spec(*self),
    {
        let mut buf = Vec::new();
        push_bytes(&mut buf, self.hash.as_slice());
        push_bytes(&mut buf, &self.key_slot.to_bytes());
        push_bytes(&mut buf, &self.value_slot.to_bytes());
        assert(buf@ =~= kv_encode_spec(*self));
        buf
    }

    pub fn from_bytes(buf: &[u8], hash_size: usize) -> (r: Result<KeyValuePair>)
        requires
            hash_size + SLOT_LENGTH * 2 <= usize::MAX,
            buf@.len() >= hash_size + SLOT_LENGTH * 2,
        ensures
            r matches Ok(kv) ==> kv.hash@.len() == hash_size && kv_encode_spec(kv) == buf@.subrange(0, hash_size + SLOT_LENGTH * 2),
            r is Err <==> (buf@[hash_size as int] & 0x7fu8) > 16 || (buf@[hash_size + SLOT_LENGTH] & 0x7fu8) > 16,
    {
        let hash = copy_bytes(buf, 0, hash_size);
        let key_slot = Slot::from_bytes(slice_subrange(buf, hash_size, hash_size + SLOT_LENGTH))?;
        let value_slot = Slot::from_bytes(slice_subrange(buf, hash_size + SLOT_LENGTH, hash_size + SLOT_LENGTH * 2))?;
        let kv = KeyValuePair { hash, key_slot, value_slot };
        proof {
            let b = buf@;
            let k0 = hash_size as int;
            assert(b.subrange(k0, k0 + 9).subrange(0, 9) =~= b.subrange(k0, k0 + 9));
            assert(b.subrange(k0 + 9, k0 + 18).subrange(0, 9) =~= b.subrange(k0 + 9, k0 + 18));
            assert(kv_encode_spec(kv) =~= b.subrange(0, k0 + 18));
        }
        Ok(kv)
    }

    /// Encodes a [`Tag::KvPair`] or [`Tag::SortedKvPair`] entry. A sorted
    /// entry leaves out the hash.
    pub fn encode(&self, tag: Tag) -> (r: Result<Vec<u8>>)
        ensures
            tag == Tag::KvPair ==> r is Ok && r.unwrap()@ == kv_encode_spec(*self),
            tag == Tag::SortedKvPair ==> r is Ok && r.unwrap()@ == sorted_kv_encode_spec(*self),
            !(tag == Tag::KvPair || tag == Tag::SortedKvPair) ==> r is Err,
    {
        match tag {
            Tag::KvPair => Ok(self.to_bytes()),
            Tag::SortedKvPair => {
                let mut buf = Vec::new();
                push_bytes(&mut buf, &self.key_slot.to_bytes());
                push_bytes(&mut buf, &self.value_slot.to_bytes());
                assert(buf@ =~= sorted_kv_encode_spec(*self));
                Ok(buf)
            },
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// The encoded length of a [`Tag::KvPair`] or [`Tag::SortedKvPair`] entry.
    pub fn encoded_len(tag: Tag, hash_size: usize) -> (r: Result<usize>)
        requires
            hash_size + SLOT_LENGTH * 2 <= usize::MAX,
        ensures
            tag == Tag::KvPair ==> r is Ok && r.unwrap() == hash_size + SLOT_LENGTH * 2,
            tag == Tag::SortedKvPair ==> r is Ok && r.unwrap() == SORTED_KEY_VALUE_PAIR_LENGTH,
            !(tag == Tag::KvPair || tag == Tag::SortedKvPair) ==> r is Err,
    {
        match tag {
            Tag::KvPair => Ok(key_value_pair_length(hash_size)),
            Tag::SortedKvPair => Ok(SORTED_KEY_VALUE_PAIR_LENGTH),
            _ => Err(Error::UnexpectedTag),
        }
    }

    /// Decodes a [`Tag::KvPair`] or [`Tag::SortedKvPair`] entry. A sorted
    /// entry has no hash, so it is all zeros.
    pub fn decode(buf: &[u8], tag: Tag, hash_size: usize) -> (r: Result<KeyValuePair>)
        requires
            hash_size + SLOT_LENGTH * 2 <= usize::MAX,
            tag == Tag::KvPair ==> buf@.len() >= hash_size + SLOT_LENGTH * 2,
            tag == Tag::SortedKvPair ==> buf@.len() >= SLOT_LENGTH * 2,
        ensures
            r matches Ok(kv) ==> kv.hash@.len() == hash_size,
            r matches Ok(kv) ==> tag == Tag::KvPair ==> kv_encode_spec(kv) == buf@.subrange(0, hash_size + SLOT_LENGTH * 2),
            r matches Ok(kv) ==> tag == Tag::SortedKvPair ==> sorted_kv_encode_spec(kv) == buf@.subrange(0, SLOT_LENGTH * 2),
            !(tag == Tag::KvPair || tag == Tag::SortedKvPair) ==> r is Err,
    {
        match tag {
            Tag::KvPair => KeyValuePair::from_bytes(buf, hash_size),
            Tag::SortedKvPair => {
                let mut kv = KeyValuePair::from_bytes(buf, 0)?;
                proof {
                    assert(kv.hash@ =~= Seq::<u8>::empty());
                    assert(kv_encode_spec(kv) =~= sorted_kv_encode_spec(kv));
                }
                let ghost enc = sorted_kv_encode_spec(kv);
                kv.hash = zeros(hash_size);
                assert(sorted_kv_encode_spec(kv) == enc);
                Ok(kv)
            },
            _ => Err(Error::UnexpectedTag),
        }
    }
}

fn zeros(n: usize) -> (r: Vec<u8>)
    ensures
        r@.len() == n,
        forall|i: int| 0 <= i < n ==> r@[i] == 0,
{
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> r@[j] == 0,
        decreases n - i,
    {
        r.push(0);
        i += 1;
    }
    r
}

// b-tree nodes

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum BTreeNodeKind {
    Leaf = 0,
    Branch = 1,
}

pub open spec fn kind_byte_spec(k: BTreeNodeKind) -> u8 {
    match k {
        BTreeNodeKind::Leaf => 0,
        BTreeNodeKind::Branch => 1,
    }
}

impl BTreeNodeKind {
    pub fn from_u8(value: u8) -> (r: Result<BTreeNodeKind>)
        ensures
            r matches Ok(k) ==> kind_byte_spec(k) == value,
            r is Err <==> value > 1,
    {
        match value {
            0 => Ok(BTreeNodeKind::Leaf),
            1 => Ok(BTreeNodeKind::Branch),
            _ => Err(Error::InvalidBTreeNodeKind),
        }
    }

    pub fn to_u8(self) -> (r: u8)
        ensures
            r == kind_byte_spec(self),
    {
        match self {
            BTreeNodeKind::Leaf => 0,
            BTreeNodeKind::Branch => 1,
        }
    }
}

/// Reads the kind and entry count from a node's header.
pub fn decode_node_header(buf: &[u8]) -> (r: Result<(BTreeNodeKind, usize)>)
    requires
        buf@.len() >= 2,
    ensures
        r matches Ok((kind, num)) ==> kind_byte_spec(kind) == buf@[0] && num == buf@[1] && num <= BTREE_SLOT_COUNT,
        r is Err <==> buf@[0] > 1 || buf@[1] > BTREE_SLOT_COUNT,
{
    let kind = BTreeNodeKind::from_u8(buf[0])?;
    let num = buf[1] as usize;
    if num > BTREE_SLOT_COUNT {
        return Err(Error::InvalidBTreeNode);
    }
    Ok((kind, num))
}

/// The encoding of a sequence of slots.
pub open spec fn slots_encode_spec(slots: Seq<Slot>) -> Seq<u8>
    decreases slots.len(),
{
    if slots.len() == 0 {
        Seq::empty()
    } else {
        slots_encode_spec(slots.drop_last()) + slot_encode_spec(slots.last())
    }
}

/// The encoding of a sequence of counts.
pub open spec fn counts_encode_spec(counts: Seq<i64>) -> Seq<u8>
    decreases counts.len(),
{
    if counts.len() == 0 {
        Seq::empty()
    } else {
        counts_encode_spec(counts.drop_last()) + u64_be_spec(i2u(counts.last()))
    }
}

proof fn lemma_slots_encode_len(slots: Seq<Slot>)
    ensures
        slots_encode_spec(slots).len() == slots.len() * SLOT_LENGTH,
    decreases slots.len(),
{
    if slots.len() > 0 {
        lemma_slots_encode_len(slots.drop_last());
        lemma_slot_roundtrip(slots.last());
    }
}

proof fn lemma_slots_encode_at(slots: Seq<Slot>, i: int)
    requires
        0 <= i < slots.len(),
    ensures
        slots_encode_spec(slots).subrange(i * 9, i * 9 + 9) == slot_encode_spec(slots[i]),
    decreases slots.len(),
{
    let p = slots.drop_last();
    lemma_slots_encode_len(p);
    lemma_slot_roundtrip(slots.last());
    if i < slots.len() - 1 {
        lemma_slots_encode_at(p, i);
        assert(slots_encode_spec(slots).subrange(i * 9, i * 9 + 9) =~= slots_encode_spec(p).subrange(i * 9, i * 9 + 9));
    } else {
        assert(slots_encode_spec(slots).subrange(i * 9, i * 9 + 9) =~= slot_encode_spec(slots.last()));
    }
}

/// Decodes 16 slots: each is the slot whose encoding is at its place.
pub(crate) fn decode_slots(buf: &[u8]) -> (r: Result<[Slot; SLOT_COUNT]>)
    requires
        buf@.len() >= SLOT_LENGTH * SLOT_COUNT,
    ensures
        r matches Ok(slots) ==> forall|i: int| 0 <= i < SLOT_COUNT ==> #[trigger] slot_encode_spec(slots[i]) == buf@.subrange(i * 9, i * 9 + 9),
{
    let mut slots = [Slot::default(); SLOT_COUNT];
    let mut i: usize = 0;
    while i < SLOT_COUNT
        invariant
            i <= SLOT_COUNT,
            buf@.len() >= SLOT_LENGTH * SLOT_COUNT,
            forall|j: int| 0 <= j < i ==> #[trigger] slot_encode_spec(slots[j]) == buf@.subrange(j * 9, j * 9 + 9),
        decreases SLOT_COUNT - i,
    {
        let s = Slot::from_bytes(slice_subrange(buf, i * SLOT_LENGTH, (i + 1) * SLOT_LENGTH))?;
        proof {
            assert(buf@.subrange(i * 9, (i + 1) * 9).subrange(0, 9) =~= buf@.subrange(i * 9, i * 9 + 9));
        }
        slots[i] = s;
        i += 1;
    }
    Ok(slots)
}

/// Decodes 16 counts. A negative count can only come from a corrupt file,
/// and is rejected as `Error::InvalidBTreeNode`.
pub(crate) fn decode_counts(buf: &[u8]) -> (r: Result<[i64; SLOT_COUNT]>)
    requires
        buf@.len() >= 8 * SLOT_COUNT,
    ensures
        r matches Ok(counts) ==> forall|i: int| 0 <= i < SLOT_COUNT ==> #[trigger] counts[i] == u2i(be_u64_spec(buf@.subrange(i * 8, i * 8 + 8))) && counts[i] >= 0,
        r is Err ==> exists|i: int| 0 <= i < SLOT_COUNT && #[trigger] u2i(be_u64_spec(buf@.subrange(i * 8, i * 8 + 8))) < 0,
{
    let mut counts = [0i64; SLOT_COUNT];
    let mut i: usize = 0;
    while i < SLOT_COUNT
        invariant
            i <= SLOT_COUNT,
            buf@.len() >= 8 * SLOT_COUNT,
            forall|j: int| 0 <= j < i ==> #[trigger] counts[j] == u2i(be_u64_spec(buf@.subrange(j * 8, j * 8 + 8))) && counts[j] >= 0,
        decreases SLOT_COUNT - i,
    {
        let c = read_i64(slice_subrange(buf, i * 8, i * 8 + 8));
        proof {
            assert(buf@.subrange(i * 8, i * 8 + 8).subrange(0, 8) =~= buf@.subrange(i * 8, i * 8 + 8));
        }
        if c < 0 {
            return Err(Error::InvalidBTreeNode);
        }
        counts[i] = c;
        i += 1;
    }
    Ok(counts)
}

pub(crate) fn encode_slots(buf: &mut Vec<u8>, slots: &[Slot])
    ensures
        final(buf)@ == old(buf)@ + slots_encode_spec(slots@),
{
    let mut i: usize = 0;
    while i < slots.len()
        invariant
            i <= slots@.len(),
            buf@ == old(buf)@ + slots_encode_spec(slots@.subrange(0, i as int)),
        decreases slots.len() - i,
    {
        push_bytes(buf, &slots[i].to_bytes());
        proof {
            assert(slots@.subrange(0, i + 1).drop_last() =~= slots@.subrange(0, i as int));
        }
        i += 1;
    }
    assert(slots@.subrange(0, i as int) =~= slots@);
}

pub(crate) fn encode_counts(buf: &mut Vec<u8>, counts: &[i64])
    ensures
        final(buf)@ == old(buf)@ + counts_encode_spec(counts@),
{
    let mut i: usize = 0;
    while i < counts.len()
        invariant
            i <= counts@.len(),
            buf@ == old(buf)@ + counts_encode_spec(counts@.subrange(0, i as int)),
        decreases counts.len() - i,
    {
        push_bytes(buf, &u64_to_be_bytes(counts[i] as u64));
        proof {
            assert(counts@.subrange(0, i + 1).drop_last() =~= counts@.subrange(0, i as int));
        }
        i += 1;
    }
    assert(counts@.subrange(0, i as int) =~= counts@);
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
pub(crate) fn check_rank(rank: i64, num: usize, allow_end: bool) -> (r: Result<usize>)
    ensures
        r matches Ok(i) ==> i == rank,
        r is Ok <==> 0 <= rank && (rank < num || (allow_end && rank == num)),
{
    if rank < 0 {
        return Err(Error::InvalidBTreeNode);
    }
    if (rank as u64) < (num as u64) || (allow_end && (rank as u64) == (num as u64)) {
        Ok(rank as usize)
    } else {
        Err(Error::InvalidBTreeNode)
    }
}

/// `i64::wrapping_add`, for a sum of two `i64`s.
pub open spec fn wrap_i64(x: int) -> i64 {
    if x > i64::MAX {
        (x - 0x1_0000_0000_0000_0000) as i64
    } else if x < i64::MIN {
        (x + 0x1_0000_0000_0000_0000) as i64
    } else {
        x as i64
    }
}

/// The sum of the first `n` counts, wrapping like `i64::wrapping_add`.
pub open spec fn wrapping_sum(counts: Seq<i64>, n: int) -> i64
    decreases n,
{
    if n <= 0 {
        0
    } else {
        wrap_i64(wrapping_sum(counts, n - 1) as int + counts[n - 1] as int)
    }
}

pub open spec fn node_encode_spec(kind: BTreeNodeKind, num: usize, parts: Seq<u8>) -> Seq<u8> {
    seq![kind_byte_spec(kind), num as u8] + parts
}

impl BTreeNode {
    pub fn empty(kind: BTreeNodeKind, num: usize) -> (r: BTreeNode)
        ensures
            r.kind == kind,
            r.num == num,
            forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] r.counts[i] == 0,
    {
        BTreeNode {
            kind,
            num,
            values: [Slot::default(); BTREE_SLOT_COUNT],
            children: [Slot::default(); BTREE_SLOT_COUNT],
            counts: [0; BTREE_SLOT_COUNT],
        }
    }

    pub fn subtree_count(&self) -> (r: i64)
        requires
            self.num <= BTREE_SLOT_COUNT,
        ensures
            self.kind == BTreeNodeKind::Leaf ==> r == self.num as i64,
            self.kind == BTreeNodeKind::Branch ==> r == wrapping_sum(self.counts@, self.num as int),
    {
        match self.kind {
            BTreeNodeKind::Leaf => self.num as i64,
            BTreeNodeKind::Branch => sum_counts(&self.counts, self.num),
        }
    }

    pub fn to_bytes(self) -> (r: Vec<u8>)
        ensures
            self.kind == BTreeNodeKind::Leaf ==> r@ == node_encode_spec(self.kind, self.num, slots_encode_spec(self.values@)),
            self.kind == BTreeNodeKind::Branch ==> r@ == node_encode_spec(
                self.kind,
                self.num,
                slots_encode_spec(self.children@) + counts_encode_spec(self.counts@),
            ),
    {
        let mut buf = Vec::new();
        buf.push(self.kind.to_u8());
        buf.push(self.num as u8);
        match self.kind {
            BTreeNodeKind::Leaf => encode_slots(&mut buf, &self.values),
            BTreeNodeKind::Branch => {
                encode_slots(&mut buf, &self.children);
                encode_counts(&mut buf, &self.counts);
            },
        }
        proof {
            match self.kind {
                BTreeNodeKind::Leaf => {
                    assert(buf@ =~= node_encode_spec(self.kind, self.num, slots_encode_spec(self.values@)));
                },
                BTreeNodeKind::Branch => {
                    assert(buf@ =~= node_encode_spec(self.kind, self.num, slots_encode_spec(self.children@) + counts_encode_spec(self.counts@)));
                },
            }
        }
        buf
    }
}

fn sum_counts(counts: &[i64; BTREE_SLOT_COUNT], num: usize) -> (r: i64)
    requires
        num <= BTREE_SLOT_COUNT,
    ensures
        r == wrapping_sum(counts@, num as int),
{
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < num
        invariant
            i <= num <= BTREE_SLOT_COUNT,
            sum == wrapping_sum(counts@, i as int),
        decreases num - i,
    {
        sum = sum.wrapping_add(counts[i]);
        i += 1;
    }
    sum
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
    pub fn empty(kind: BTreeNodeKind, num: usize) -> (r: SortedNode)
        ensures
            r.kind == kind,
            r.num == num,
            forall|i: int| 0 <= i < BTREE_SLOT_COUNT ==> #[trigger] r.counts[i] == 0,
    {
        SortedNode {
            kind,
            num,
            entries: [Slot::default(); BTREE_SLOT_COUNT],
            children: [Slot::default(); BTREE_SLOT_COUNT],
            separators: [Slot::default(); BTREE_SLOT_COUNT],
            counts: [0; BTREE_SLOT_COUNT],
        }
    }

    pub fn subtree_count(&self) -> (r: i64)
        requires
            self.num <= BTREE_SLOT_COUNT,
        ensures
            self.kind == BTreeNodeKind::Leaf ==> r == self.num as i64,
            self.kind == BTreeNodeKind::Branch ==> r == wrapping_sum(self.counts@, self.num as int),
    {
        match self.kind {
            BTreeNodeKind::Leaf => self.num as i64,
            BTreeNodeKind::Branch => sum_counts(&self.counts, self.num),
        }
    }

    pub fn to_bytes(self) -> (r: Vec<u8>)
        ensures
            self.kind == BTreeNodeKind::Leaf ==> r@ == node_encode_spec(self.kind, self.num, slots_encode_spec(self.entries@)),
            self.kind == BTreeNodeKind::Branch ==> r@ == node_encode_spec(
                self.kind,
                self.num,
                slots_encode_spec(self.children@) + slots_encode_spec(self.separators@) + counts_encode_spec(self.counts@),
            ),
    {
        let mut buf = Vec::new();
        buf.push(self.kind.to_u8());
        buf.push(self.num as u8);
        match self.kind {
            BTreeNodeKind::Leaf => encode_slots(&mut buf, &self.entries),
            BTreeNodeKind::Branch => {
                encode_slots(&mut buf, &self.children);
                encode_slots(&mut buf, &self.separators);
                encode_counts(&mut buf, &self.counts);
            },
        }
        proof {
            match self.kind {
                BTreeNodeKind::Leaf => {
                    assert(buf@ =~= node_encode_spec(self.kind, self.num, slots_encode_spec(self.entries@)));
                },
                BTreeNodeKind::Branch => {
                    assert(buf@ =~= node_encode_spec(
                        self.kind,
                        self.num,
                        slots_encode_spec(self.children@) + slots_encode_spec(self.separators@) + counts_encode_spec(self.counts@),
                    ));
                },
            }
        }
        buf
    }
}

} // verus!

impl Header {
    /// Reads a header at the core's current position, so the hash size
    /// and hash id of a database can be checked before opening it.
    pub fn read(core: &mut impl crate::Core) -> Result<Header> {
        let mut buf = [0u8; HEADER_LENGTH];
        core.read(&mut buf)?;
        Ok(Header::from_bytes(&buf))
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

    #[test]
    fn constants_match_their_definitions() {
        assert_eq!(MAGIC_NUMBER, *b"xit");
        assert_eq!(SLOT_COUNT, 1 << BIT_COUNT);
        assert_eq!(BTREE_SPLIT_COUNT, BTREE_SLOT_COUNT.div_ceil(2));
    }
}
