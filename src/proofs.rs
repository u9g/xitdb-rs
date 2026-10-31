//! Kani proof harnesses. Run them with `cargo kani` (see the README).
//!
//! The format harnesses hold for every input. The database harnesses are
//! bounded: each builds a small database on a [`CoreMemory`], then makes
//! one change with symbolic keys, values, indexes or corruptions and
//! compares the result against a simple model, so it holds for every choice
//! of those inputs, but only for that database.

use crate::core::CoreMemory;
use crate::database::{Database, hash_nibble, resolve_index};
use crate::format::*;
use crate::slot::{SLOT_LENGTH, Slot, Tag};
use crate::{
    Data, Hasher, ReadArrayList, ReadHashMap, ReadLinkedArrayList, ReadSortedMap, WriteArrayList,
    WriteCountedHashMap, WriteHashMap, WriteLinkedArrayList, WriteSortedMap,
};

fn any_tag() -> Tag {
    let value: u8 = kani::any();
    kani::assume(value <= Tag::SortedKvPair as u8);
    Tag::from_u8(value).unwrap()
}

fn any_slot() -> Slot {
    Slot { value: kani::any(), tag: any_tag(), full: kani::any() }
}

// format

/// A tag byte decodes exactly when it is a known tag, and back to itself.
#[kani::proof]
fn tag_from_u8_is_inverse_of_as_u8() {
    let value: u8 = kani::any();
    match Tag::from_u8(value) {
        Ok(tag) => assert_eq!(tag as u8, value),
        Err(_) => assert!(value > Tag::SortedKvPair as u8),
    }
}

#[kani::proof]
fn slot_roundtrip() {
    let slot = any_slot();
    assert_eq!(Slot::from_bytes(&slot.to_bytes()).unwrap(), slot);
}

/// Decoding any 9 bytes never panics, and a decoded slot encodes back to the
/// same bytes, so there is exactly one encoding of each slot.
#[kani::proof]
fn slot_decoding_is_canonical() {
    let bytes: [u8; SLOT_LENGTH] = kani::any();
    match Slot::from_bytes(&bytes) {
        Ok(slot) => assert_eq!(slot.to_bytes(), bytes),
        Err(_) => assert!(bytes[0] & 0x7f > Tag::SortedKvPair as u8),
    }
}

#[kani::proof]
fn header_roundtrip() {
    let header = Header {
        file_id: kani::any(),
        hash_id: kani::any(),
        hash_size: kani::any(),
        version: kani::any(),
        magic_number: kani::any(),
    };
    let decoded = Header::from_bytes(&header.to_bytes());
    assert_eq!(decoded, header);
    assert_eq!(decoded.validate().is_ok(), header.magic_number == MAGIC_NUMBER && header.version == VERSION);
}

/// Array list and b-tree headers decode only with non-negative fields, and
/// then encode back to the same bytes.
#[kani::proof]
fn collection_headers_roundtrip() {
    let bytes: [u8; 16] = kani::any();
    if let Ok(header) = ArrayListHeader::from_bytes(&bytes) {
        assert!(header.ptr >= 0 && header.size >= 0);
        assert_eq!(header.to_bytes(), bytes);
    }
    if let Ok(header) = BTreeHeader::from_bytes(&bytes) {
        assert!(header.root_ptr >= 0 && header.size >= 0);
        assert_eq!(header.to_bytes(), bytes);
    }
    let header = ArrayListHeader { ptr: kani::any(), size: kani::any() };
    kani::assume(header.ptr >= 0 && header.size >= 0);
    assert_eq!(ArrayListHeader::from_bytes(&header.to_bytes()).unwrap(), header);
}

#[kani::proof]
fn root_header_and_trailer_roundtrip() {
    let header = RootHeader { file_size: kani::any(), root: any_slot() };
    assert_eq!(RootHeader::from_bytes(&header.to_bytes()).unwrap(), header);

    let file_id = kani::any();
    let position = kani::any();
    let trailer = RootTrailer::new(file_id, position, any_slot(), kani::any());
    assert_eq!(RootTrailer::from_bytes(&trailer.to_bytes()).unwrap(), trailer);
    assert_eq!(trailer.checksum, root_trailer_checksum(file_id, position, trailer.root, trailer.commit_id));
}

/// Hash map entries roundtrip with their hash, sorted map entries without
/// one, for hashes of up to 4 bytes.
#[kani::proof]
#[kani::unwind(6)]
fn key_value_pair_roundtrip() {
    let hash_size: usize = kani::any();
    kani::assume(hash_size <= 4);
    let hash: [u8; 4] = kani::any();
    let kv = KeyValuePair { value_slot: any_slot(), key_slot: any_slot(), hash: hash[..hash_size].to_vec() };
    for tag in [Tag::KvPair, Tag::SortedKvPair] {
        let bytes = kv.encode(tag).unwrap();
        assert_eq!(bytes.len(), KeyValuePair::encoded_len(tag, hash_size).unwrap());
        let decoded = KeyValuePair::decode(&bytes, tag, hash_size).unwrap();
        assert_eq!(decoded.key_slot, kv.key_slot);
        assert_eq!(decoded.value_slot, kv.value_slot);
        if tag == Tag::KvPair {
            assert_eq!(decoded.hash, kv.hash);
        } else {
            assert!(decoded.hash.len() == hash_size && decoded.hash.iter().all(|&b| b == 0));
        }
    }
}

/// Any node header decodes without panicking to at most a full node.
#[kani::proof]
fn node_header_is_bounded() {
    let bytes: [u8; BTREE_NODE_HEADER_SIZE] = kani::any();
    if let Ok((kind, num)) = decode_node_header(&bytes) {
        assert_eq!(kind as u8, bytes[0]);
        assert_eq!(num, bytes[1] as usize);
        assert!(num <= BTREE_SLOT_COUNT);
    }
}

fn any_node_len() -> usize {
    let num: usize = kani::any();
    kani::assume(num <= BTREE_SLOT_COUNT);
    num
}

/// Nodes encode to exactly their block size, and the header to what
/// decode_node_header reads back.
#[kani::proof]
#[kani::unwind(17)]
fn btree_leaf_encoding_has_block_size() {
    let num = any_node_len();
    let bytes = BTreeNode::empty(BTreeNodeKind::Leaf, num).to_bytes();
    assert!(bytes.len() == BTREE_LEAF_BLOCK_SIZE);
    assert!(decode_node_header(&bytes).ok() == Some((BTreeNodeKind::Leaf, num)));
}

#[kani::proof]
#[kani::unwind(17)]
fn btree_branch_encoding_has_block_size() {
    let num = any_node_len();
    let bytes = BTreeNode::empty(BTreeNodeKind::Branch, num).to_bytes();
    assert!(bytes.len() == BTREE_BRANCH_BLOCK_SIZE);
    assert!(decode_node_header(&bytes).ok() == Some((BTreeNodeKind::Branch, num)));
}

#[kani::proof]
#[kani::unwind(17)]
fn sorted_leaf_encoding_has_block_size() {
    let num = any_node_len();
    let bytes = SortedNode::empty(BTreeNodeKind::Leaf, num).to_bytes();
    assert!(bytes.len() == SORTED_LEAF_BLOCK_SIZE);
    assert!(decode_node_header(&bytes).ok() == Some((BTreeNodeKind::Leaf, num)));
}

#[kani::proof]
#[kani::unwind(17)]
fn sorted_branch_encoding_has_block_size() {
    let num = any_node_len();
    let bytes = SortedNode::empty(BTreeNodeKind::Branch, num).to_bytes();
    assert!(bytes.len() == SORTED_BRANCH_BLOCK_SIZE);
    assert!(decode_node_header(&bytes).ok() == Some((BTreeNodeKind::Branch, num)));
}

/// The shift of an array list's root block is the integer log16 of its last
/// key, so the trie is exactly tall enough to hold every key.
#[kani::proof]
fn array_list_shift_is_log16() {
    let key: i64 = kani::any();
    let shift = array_list_shift(key) as u32;
    assert!(shift < MAX_BRANCH_LENGTH as u32);
    if key < SLOT_COUNT as i64 {
        assert_eq!(shift, 0);
    } else {
        let key = key as u128;
        assert!(1u128 << (4 * shift) <= key);
        assert!(key < 1u128 << (4 * (shift + 1)));
    }
}

/// hash_nibble is nibble `offset` of the hash read as a big-endian number,
/// or 0 past its end.
#[kani::proof]
#[kani::unwind(6)]
fn hash_nibble_is_nibble_of_big_endian_hash() {
    let len: usize = kani::any();
    kani::assume(len <= 4);
    let bytes: [u8; 4] = kani::any();
    let hash = &bytes[..len];
    let offset: u8 = kani::any();
    let mut number: u64 = 0;
    for &byte in hash {
        number = (number << 8) | byte as u64;
    }
    let expected = if (offset as usize) < 2 * len { (number >> (4 * offset as u32)) & 0xf } else { 0 };
    assert_eq!(hash_nibble(hash, offset) as u64, expected);
}

/// Indexes into a collection of a valid size resolve to an in-range
/// position, counting negatives from the end, without overflowing.
#[kani::proof]
fn resolve_index_is_in_range() {
    let index: i64 = kani::any();
    let size: i64 = kani::any();
    kani::assume(size >= 0);
    let in_range = (index >= 0 && index < size) || (index < 0 && index >= -size);
    match resolve_index(index, size) {
        Ok(resolved) => {
            assert!(in_range);
            assert!(0 <= resolved && resolved < size);
            assert_eq!(resolved, if index < 0 { index + size } else { index });
        }
        Err(_) => assert!(!in_range),
    }
}

#[kani::proof]
fn check_rank_is_in_range() {
    let rank: i64 = kani::any();
    let num: usize = kani::any();
    kani::assume(num <= BTREE_SLOT_COUNT);
    let allow_end: bool = kani::any();
    match check_rank(rank, num, allow_end) {
        Ok(r) => assert!(r as i64 == rank && (r < num || (allow_end && r == num))),
        Err(_) => assert!(rank < 0 || rank as usize > num || (rank as usize == num && !allow_end)),
    }
}

// CRC-64/XZ computed one bit at a time, straight from its definition
fn crc64_bitwise(data: &[u8]) -> u64 {
    let mut crc = !0u64;
    for &byte in data {
        crc ^= byte as u64;
        for _ in 0..8 {
            crc = if crc & 1 == 1 { (crc >> 1) ^ 0xC96C_5795_D787_0F42 } else { crc >> 1 };
        }
    }
    !crc
}

/// The table-driven checksum equals the bitwise definition, for inputs of
/// up to 4 bytes.
#[kani::proof]
#[kani::unwind(9)]
fn crc64_matches_bitwise_definition() {
    let len: usize = kani::any();
    kani::assume(len <= 4);
    let bytes: [u8; 4] = kani::any();
    assert_eq!(crate::crc64::checksum(&bytes[..len]), crc64_bitwise(&bytes[..len]));
}

// database

/// A 1-byte hash, the key's first byte, so every key of one byte has its
/// own hash and keys that share a low nibble collide in the first level.
fn hasher() -> Hasher {
    Hasher::new(|data: &[u8]| vec![data.first().copied().unwrap_or(0)]).with_file_id(1)
}

fn read_uint<C: crate::Core>(cursor: Option<crate::ReadCursor<'_, C>>) -> Option<u8> {
    cursor.map(|cursor| cursor.read_uint().unwrap() as u8)
}

/// A new database reopens with the same header and committed size.
#[kani::proof]
#[kani::unwind(40)]
fn new_database_reopens() {
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    let header = db.header();
    let size = db.committed_size().unwrap();
    let db = Database::new(CoreMemory::from_bytes(db.into_core().into_bytes()), hasher()).unwrap();
    assert_eq!(db.header(), header);
    assert_eq!(db.committed_size().unwrap(), size);
}

/// Opening any 64 bytes as a database never panics.
#[kani::proof]
#[kani::unwind(40)]
fn open_arbitrary_bytes() {
    let bytes: [u8; 64] = kani::any();
    if let Ok(db) = Database::new(CoreMemory::from_bytes(bytes.to_vec()), hasher()) {
        let _ = db.root_cursor().count();
    }
}

// each database harness builds a concrete database, then makes one change
// with symbolic inputs, so symbolic execution doesn't fork on every step of
// every transaction

/// 0x01 and 0x11 share their low nibble, so a map holding both has two
/// levels.
const KEYS: [u8; 2] = [0x01, 0x11];

/// Putting or removing any key, with any value, on a counted hash map with
/// two levels, as its own transaction, leaves every key reading as in a
/// model, and the count matching.
#[kani::proof]
#[kani::unwind(40)]
fn hash_map_matches_model() {
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    db.run_context(|cursor| {
        let mut map = WriteCountedHashMap::new(cursor)?;
        map.put([KEYS[0]], Data::Uint(0))?;
        map.put([KEYS[1]], Data::Uint(1))
    })
    .unwrap();
    let mut model = [Some(0), Some(1)];

    let key: u8 = kani::any();
    let value: u8 = kani::any();
    let put: bool = kani::any();
    let mut map = WriteCountedHashMap::new(&mut db.root_cursor()).unwrap();
    if put {
        map.put([key], Data::Uint(value as u64)).unwrap();
    } else {
        assert_eq!(map.remove([key]).unwrap(), KEYS.contains(&key));
    }
    for (i, &k) in KEYS.iter().enumerate() {
        if k == key {
            model[i] = if put { Some(value) } else { None };
        }
    }

    assert_eq!(read_uint(map.get_cursor([key]).unwrap()), if put { Some(value) } else { None });
    for (i, &k) in KEYS.iter().enumerate() {
        assert_eq!(read_uint(map.get_cursor([k]).unwrap()), model[i]);
    }
    let count = model.iter().filter(|v| v.is_some()).count() + (put && !KEYS.contains(&key)) as usize;
    assert_eq!(map.count().unwrap(), count as i64);
}

/// A transaction never changes committed bytes (besides the root header,
/// which caches the latest commit), so the previous moment reads the same
/// after any put or remove on a copy of it.
#[kani::proof]
#[kani::unwind(40)]
fn transactions_do_not_change_history() {
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    history
        .append_context(None, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            moment.put([KEYS[0]], Data::Uint(0))?;
            moment.put([KEYS[1]], Data::Uint(1))
        })
        .unwrap();
    let committed = db.core().as_bytes().to_vec();

    let key: u8 = kani::any();
    let value: u8 = kani::any();
    let put: bool = kani::any();
    let last = history.get_slot(-1).unwrap();
    history
        .append_context(last, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            if put { moment.put([key], Data::Uint(value as u64)) } else { moment.remove([key]).map(|_| ()) }
        })
        .unwrap();

    {
        let core = db.core();
        let now = core.as_bytes();
        let start = ROOT_HEADER_END as usize;
        assert!(now.len() > committed.len());
        assert!(now[start..committed.len()] == committed[start..]);
    }

    let old = ReadHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(read_uint(old.get_cursor([KEYS[0]]).unwrap()), Some(0));
    assert_eq!(read_uint(old.get_cursor([KEYS[1]]).unwrap()), Some(1));
    let new = ReadHashMap::new(history.get_cursor(1).unwrap().unwrap()).unwrap();
    assert_eq!(read_uint(new.get_cursor([key]).unwrap()), if put { Some(value) } else { None });
}

/// One more item than an index block holds, so an array list's trie has two
/// levels and a linked array list's leaf splits.
const LIST_LEN: usize = 17;

/// Slicing a 17-item array list to any size, then appending, leaves it
/// agreeing with a model at any index.
#[kani::proof]
#[kani::unwind(40)]
fn array_list_matches_model() {
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    db.run_context(|cursor| {
        let mut list = WriteArrayList::new(cursor)?;
        for i in 0..LIST_LEN {
            list.append(Data::Uint(i as u64))?;
        }
        Ok(())
    })
    .unwrap();

    let size: usize = kani::any();
    kani::assume(size <= LIST_LEN);
    db.run_context(|cursor| {
        let mut list = WriteArrayList::new(cursor)?;
        list.slice(size as i64)?;
        list.append(Data::Uint(100))
    })
    .unwrap();

    let index: i64 = kani::any();
    let list = ReadArrayList::new(db.root_cursor()).unwrap();
    let len = size as i64 + 1;
    assert_eq!(list.count().unwrap(), len);
    let expected = resolve_index(index, len).ok().map(|i| if i == size as i64 { 100 } else { i as u8 });
    assert_eq!(read_uint(list.get_cursor(index).unwrap()), expected);
}

/// Inserting into a 16-item linked array list at any index (which splits
/// its leaf), then removing at any index, agrees with a Vec. Like the other
/// implementations, insert puts an item before an existing one, so it
/// can't append.
#[kani::proof]
#[kani::unwind(40)]
fn linked_array_list_matches_model() {
    let n = LIST_LEN - 1;
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    db.run_context(|cursor| {
        let mut list = WriteLinkedArrayList::new(cursor)?;
        for i in 0..n {
            list.append(Data::Uint(i as u64))?;
        }
        Ok(())
    })
    .unwrap();

    let insert_at: usize = kani::any();
    kani::assume(insert_at <= n);
    let remove_at: usize = kani::any();
    kani::assume(remove_at <= n);
    let result = db.run_context(|cursor| {
        let mut list = WriteLinkedArrayList::new(cursor)?;
        list.insert(insert_at as i64, Data::Uint(100))?;
        list.remove(remove_at as i64)
    });
    let mut model: Vec<u8> = (0..n as u8).collect();
    if insert_at == n {
        assert!(matches!(result, Err(crate::Error::KeyNotFound)));
    } else {
        result.unwrap();
        model.insert(insert_at, 100);
        model.remove(remove_at);
    }

    let list = ReadLinkedArrayList::new(db.root_cursor()).unwrap();
    assert_eq!(list.count().unwrap(), model.len() as i64);
    let mut items = Vec::new();
    for item in list.iter().unwrap() {
        items.push(item.unwrap().read_uint().unwrap() as u8);
    }
    assert!(items == model);
}

/// Putting any key into a sorted map leaves it agreeing with a model:
/// iteration is in strictly ascending key order, and get, rank and count
/// match.
#[kani::proof]
#[kani::unwind(40)]
fn sorted_map_matches_model() {
    const SORTED_KEYS: [u8; 2] = [0x10, 0x20];
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    db.run_context(|cursor| {
        let mut map = WriteSortedMap::new(cursor)?;
        for key in SORTED_KEYS {
            map.put([key], Data::Uint(key as u64))?;
        }
        Ok(())
    })
    .unwrap();

    let key: u8 = kani::any();
    let value: u8 = kani::any();
    WriteSortedMap::new(&mut db.root_cursor()).unwrap().put([key], Data::Uint(value as u64)).unwrap();

    let map = ReadSortedMap::new(db.root_cursor()).unwrap();
    let count = 2 + !SORTED_KEYS.contains(&key) as i64;
    assert_eq!(map.count().unwrap(), count);
    assert_eq!(read_uint(map.get_cursor([key]).unwrap()), Some(value));
    assert_eq!(map.rank([key]).unwrap(), SORTED_KEYS.iter().filter(|&&k| k < key).count() as i64);
    for k in SORTED_KEYS {
        if k != key {
            assert_eq!(read_uint(map.get_cursor([k]).unwrap()), Some(k));
        }
    }

    let mut previous: Option<Vec<u8>> = None;
    let mut seen = 0;
    for item in map.iter().unwrap() {
        let key = item.unwrap().read_key_value_pair().unwrap().key_cursor.read_bytes(Some(8)).unwrap();
        if let Some(previous) = previous {
            assert!(previous < key);
        }
        previous = Some(key);
        seen += 1;
    }
    assert_eq!(seen, count);
}

/// Changing any one byte of a database holding a two-level hash map, then
/// opening and reading it, returns errors but never panics or hangs.
#[kani::proof]
#[kani::unwind(40)]
fn corrupt_hash_map_never_panics() {
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    db.run_context(|cursor| {
        let mut map = WriteHashMap::new(cursor)?;
        map.put([KEYS[0]], Data::Uint(0))?;
        map.put([KEYS[1]], Data::Uint(1))
    })
    .unwrap();
    let mut bytes = db.into_core().into_bytes();
    let pos: usize = kani::any();
    kani::assume(pos < bytes.len());
    bytes[pos] = kani::any();

    let Ok(db) = Database::new(CoreMemory::from_bytes(bytes), hasher()) else { return };
    let Ok(map) = ReadHashMap::new(db.root_cursor()) else { return };
    for key in KEYS {
        if let Ok(Some(cursor)) = map.get_cursor([key]) {
            let _ = cursor.read_bytes(Some(16));
        }
    }
    if let Ok(iter) = map.iter() {
        for item in iter {
            let _ = item.and_then(|cursor| cursor.read_key_value_pair().map(|_| ()));
        }
    }
}

/// The same for a sorted map whose root is a branch.
#[kani::proof]
#[kani::unwind(40)]
fn corrupt_sorted_map_never_panics() {
    let db = Database::new(CoreMemory::new(), hasher()).unwrap();
    db.run_context(|cursor| {
        let mut map = WriteSortedMap::new(cursor)?;
        for key in 1..=(BTREE_SLOT_COUNT as u8 + 1) {
            map.put([key], Data::Uint(0))?;
        }
        Ok(())
    })
    .unwrap();
    let mut bytes = db.into_core().into_bytes();
    let pos: usize = kani::any();
    kani::assume(pos < bytes.len());
    bytes[pos] = kani::any();

    let Ok(db) = Database::new(CoreMemory::from_bytes(bytes), hasher()) else { return };
    let Ok(map) = ReadSortedMap::new(db.root_cursor()) else { return };
    let _ = map.get_cursor([1]);
    let _ = map.rank([BTREE_SLOT_COUNT as u8 + 1]);
    if let Ok(iter) = map.iter() {
        for item in iter {
            let _ = item;
        }
    }
}
