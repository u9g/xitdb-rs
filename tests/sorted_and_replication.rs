//! A port of the Go implementation's high_level_test.go, from TestSortedMap
//! to the end: sorted maps, iterating from a start, replication, and the
//! root trailer checksum.

use std::io;

use xitdb::consts::{HEADER_LENGTH, VERSION};
use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

/// The Go tests' `sha1Hasher()`: SHA-1 with a hash ID of 0.
fn sha1_hasher() -> Hasher {
    use sha1::Digest;
    Hasher::new(|data| sha1::Sha1::digest(data).to_vec())
}

fn temp_file() -> std::fs::File {
    tempfile::tempfile().unwrap()
}

/// The Go tests' `errFail`, a custom error returned from a context function.
fn err_fail() -> Error {
    Error::Io(io::Error::other("fail"))
}

fn is_fail(result: Result<()>) -> bool {
    matches!(result, Err(Error::Io(ref err)) if err.to_string() == "fail")
}

// TestSortedMap

#[test]
fn sorted_map() {
    // CoreMemory
    sorted_map_with(CoreMemory::new(), sha1_hasher());
    // CoreFile
    sorted_map_with(CoreFile::new(temp_file()), sha1_hasher());
    // CoreBufferedFile
    sorted_map_with(CoreBufferedFile::with_buffer_size(temp_file(), 1024), sha1_hasher());
}

fn sorted_key(i: i64) -> String {
    format!("k{i:04}")
}

/// The first key yielded by a ranged iterator.
fn first_key<C: Core>(seq: Result<CursorIterator<'_, C>>) -> Result<String> {
    if let Some(c) = seq?.next() {
        let c = c?;
        let kv = c.read_key_value_pair()?;
        let b = kv.key_cursor.read_bytes(MAX_READ)?;
        return Ok(String::from_utf8(b).unwrap());
    }
    Ok(String::new())
}

fn sorted_map_with<C: Core>(mut core: C, hasher: Hasher) {
    core.set_length(0).unwrap();
    let db = Database::new(core, hasher).unwrap();

    // keys "k0000".."k0059" sort lexicographically in numeric order
    const COUNT: i64 = 60;
    let k = sorted_key;

    {
        let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
        let last_slot = history.get_slot(-1).unwrap();
        history
            .append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                let mut map_cursor = moment.put_cursor("map")?;
                let mut m = WriteSortedMap::new(&mut map_cursor)?;

                // insert in reverse order to exercise front-insertions and splits
                for i in (0..COUNT).rev() {
                    m.put(k(i), Data::Uint(i as u64))?;
                }
                assert_eq!(m.count()?, COUNT);

                // dedup: re-putting an existing key replaces the value, not the count
                m.put("k0005", Data::Uint(999))?;
                assert_eq!(m.count()?, COUNT);
                let cur = m.get_cursor("k0005")?.expect("k0005 should be present");
                assert_eq!(cur.read_uint()?, 999);
                m.put("k0005", Data::Uint(5))?;

                // ordered iteration yields k0000..k0059 with intact values
                let mut n = 0;
                for c in m.iter()? {
                    let c = c?;
                    let kv = c.read_key_value_pair()?;
                    let key_bytes = kv.key_cursor.read_bytes(MAX_READ)?;
                    assert_eq!(String::from_utf8(key_bytes).unwrap(), k(n));
                    assert_eq!(kv.value_cursor.read_uint()?, n as u64);
                    n += 1;
                }
                assert_eq!(n, COUNT);

                assert!(m.get_cursor("k0042")?.is_some(), "k0042 should be present");
                assert!(m.get_cursor("nope")?.is_none(), "nope should be absent");

                // getByIndex (positive and negative) and rank are inverses
                for idx in 0..COUNT {
                    let kv = m.get_index_key_value_pair(idx)?.expect("index should be present");
                    let key_bytes = kv.key_cursor.read_bytes(MAX_READ)?;
                    assert_eq!(String::from_utf8(key_bytes.clone()).unwrap(), k(idx));
                    assert_eq!(m.rank(&key_bytes)?, idx);
                }
                let last_kv = m.get_index_key_value_pair(-1)?.expect("index -1 should be present");
                let last_key = last_kv.key_cursor.read_bytes(MAX_READ)?;
                assert_eq!(String::from_utf8(last_key).unwrap(), "k0059");
                assert!(m.get_index_key_value_pair(COUNT)?.is_none(), "index == count should be absent");

                // lower-bound iteration from a present and an absent key
                assert_eq!(first_key(m.iter_from(b"k0030"))?, "k0030");
                // "k00095" sorts between "k0009" and "k0010"
                assert_eq!(first_key(m.iter_from(b"k00095"))?, "k0010");
                assert_eq!(first_key(m.iter_from_index(COUNT - 2))?, "k0058");
                // negative indexes count from the end: -1 is the last entry, -count the first
                assert_eq!(first_key(m.iter_from_index(-1))?, "k0059");
                {
                    // -1 is the last entry, so the iterator yields exactly one
                    let mut n = 0;
                    for c in m.iter_from_index(-1)? {
                        c?;
                        n += 1;
                    }
                    assert_eq!(n, 1);
                }
                assert_eq!(first_key(m.iter_from_index(-COUNT))?, "k0000");
                {
                    // out of range past either end yields nothing
                    let mut n = 0;
                    for c in m.iter_from_index(COUNT)? {
                        c?;
                        n += 1;
                    }
                    for c in m.iter_from_index(-COUNT - 1)? {
                        c?;
                        n += 1;
                    }
                    assert_eq!(n, 0);
                }

                // remove the even keys, then re-verify order, count, and presence
                for j in (0..COUNT).step_by(2) {
                    assert!(m.remove(k(j))?);
                }
                assert_eq!(m.count()?, COUNT / 2);
                assert!(!m.remove("k0000")?);

                let mut expect_i = 1;
                let mut seen = 0;
                for c in m.iter()? {
                    let c = c?;
                    let kv = c.read_key_value_pair()?;
                    let b = kv.key_cursor.read_bytes(MAX_READ)?;
                    assert_eq!(String::from_utf8(b).unwrap(), k(expect_i));
                    expect_i += 2;
                    seen += 1;
                }
                assert_eq!(seen, COUNT / 2);

                // iterating-from on an unwritten (none) map yields nothing
                let none_cursor = ReadCursor::new(SlotPointer::new(None, Slot::default()), &db);
                let empty = ReadSortedMap::new(none_cursor)?;
                let mut empty_count = 0;
                for _ in empty.iter_from(b"anything")? {
                    empty_count += 1;
                }
                for _ in empty.iter_from_index(0)? {
                    empty_count += 1;
                }
                assert_eq!(empty_count, 0);

                // SortedSet with mixed short (inline) and long (external) keys
                let mut set_cursor = moment.put_cursor("set")?;
                let mut set = WriteSortedSet::new(&mut set_cursor)?;
                set.put("short")?;
                set.put("a-much-longer-key-stored-externally")?;
                set.put("mid")?;
                set.put("short")?; // dup is a no-op
                assert_eq!(set.count()?, 3);
                assert!(set.contains("mid")?);
                assert!(!set.contains("nope")?);
                let want = ["a-much-longer-key-stored-externally", "mid", "short"];
                let mut sn = 0;
                for c in set.iter()? {
                    let c = c?;
                    let kv = c.read_key_value_pair()?;
                    let b = kv.key_cursor.read_bytes(MAX_READ)?;
                    assert_eq!(String::from_utf8(b).unwrap(), want[sn]);
                    sn += 1;
                }
                assert_eq!(sn, 3);
                assert!(set.remove("mid")?);
                assert_eq!(set.count()?, 2);

                // immutability guards: positional access is read-only, and keys/entries
                // cannot be overwritten through the low-level path API
                let mut write_cursor = m.write_cursor().clone();
                let result = write_cursor.write_path(&[PathPart::SortedMapGetIndex(0)]);
                assert!(
                    matches!(result, Err(Error::WriteNotAllowed)),
                    "expected WriteNotAllowed, got {result:?}"
                );
                let x = Data::bytes(b"x".as_slice());
                let result = write_cursor.write_path(&[
                    PathPart::SortedMapGet(SortedMapGetTarget::Key(b"k0001")),
                    PathPart::WriteData(&x),
                ]);
                assert!(
                    matches!(result, Err(Error::CursorNotWriteable)),
                    "expected CursorNotWriteable, got {result:?}"
                );

                // a write that fails after the key is inserted (a missing key written
                // through the non-writeable key slot) must still leave the count
                // consistent with the tree, not inserted-but-uncounted
                let count_before_failed_write = m.count()?;
                let result = write_cursor.write_path(&[
                    PathPart::SortedMapGet(SortedMapGetTarget::Key(b"missing-key")),
                    PathPart::WriteData(&x),
                ]);
                assert!(
                    matches!(result, Err(Error::CursorNotWriteable)),
                    "expected CursorNotWriteable, got {result:?}"
                );
                assert_eq!(m.count()?, count_before_failed_write + 1);
                assert!(
                    m.get_key_value_pair("missing-key")?.is_some(),
                    "expected missing-key to be present after failed write"
                );
                m.remove("missing-key")?; // restore the map for the assertions below

                Ok(())
            })
            .unwrap();
    }

    // the map persists in the committed moment
    {
        let history = ReadArrayList::new(db.root_cursor()).unwrap();
        let moment_cursor = history.get_cursor(-1).unwrap().unwrap();
        let moment = ReadHashMap::new(moment_cursor).unwrap();
        let map_cursor = moment.get_cursor("map").unwrap().unwrap();
        let m = ReadSortedMap::new(map_cursor).unwrap();
        assert_eq!(m.count().unwrap(), COUNT / 2);
        let kv = m.get_index_key_value_pair(0).unwrap().unwrap();
        let b = kv.key_cursor.read_bytes(MAX_READ).unwrap();
        assert_eq!(String::from_utf8(b).unwrap(), "k0001");

        // entries have no hash
        let entry = m
            .cursor()
            .read_path_slot(&[PathPart::SortedMapGet(SortedMapGetTarget::KvPair(b"k0001"))])
            .unwrap()
            .unwrap();
        assert_eq!(entry.tag, Tag::SortedKvPair);
    }

    // a second moment that inherits and mutates the map must not disturb the first
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
        let last_slot = history.get_slot(-1).unwrap();
        history
            .append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                let mut map_cursor = moment.put_cursor("map")?;
                let mut m = WriteSortedMap::new(&mut map_cursor)?;
                assert!(m.remove("k0001")?);
                m.put("k0001", Data::Uint(7)) // not in moment 0
            })
            .unwrap();
    }
    {
        let history = ReadArrayList::new(db.root_cursor()).unwrap();
        // moment 0 (original) is unchanged: k0001 still present with value 1
        let m0 = ReadHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();
        let map0 = ReadSortedMap::new(m0.get_cursor("map").unwrap().unwrap()).unwrap();
        assert_eq!(map0.count().unwrap(), COUNT / 2);
        let c0 = map0.get_cursor("k0001").unwrap().unwrap();
        assert_eq!(c0.read_uint().unwrap(), 1);

        // moment 1 reflects the mutation: k0001 re-added with value 7
        let m1 = ReadHashMap::new(history.get_cursor(1).unwrap().unwrap()).unwrap();
        let map1 = ReadSortedMap::new(m1.get_cursor("map").unwrap().unwrap()).unwrap();
        assert_eq!(map1.count().unwrap(), COUNT / 2);
        let c1 = map1.get_cursor("k0001").unwrap().unwrap();
        assert_eq!(c1.read_uint().unwrap(), 7);
    }
}

// TestAllFrom

#[test]
fn all_from() {
    // CoreMemory
    all_from_with(CoreMemory::new(), sha1_hasher());
    // CoreFile
    all_from_with(CoreFile::new(temp_file()), sha1_hasher());
    // CoreBufferedFile
    all_from_with(CoreBufferedFile::with_buffer_size(temp_file(), 1024), sha1_hasher());
}

fn all_from_with<C: Core>(mut core: C, hasher: Hasher) {
    core.set_length(0).unwrap();
    let db = Database::new(core, hasher).unwrap();

    // enough items to force several tiers in both the array-list radix trie
    // (16^2 = 256 > 200) and the linked-array-list b-tree
    const COUNT: i64 = 200;

    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    let last_slot = history.get_slot(-1).unwrap();
    history
        .append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            let mut list_cursor = moment.put_cursor("list")?;
            let mut list = WriteArrayList::new(&mut list_cursor)?;
            for i in 0..COUNT {
                list.append(Data::Uint(i as u64))?;
            }
            let mut linked_cursor = moment.put_cursor("linked")?;
            let mut linked = WriteLinkedArrayList::new(&mut linked_cursor)?;
            for i in 0..COUNT {
                linked.append(Data::Uint(i as u64))?;
            }

            // the write-side structs expose AllFrom too, yielding read-only cursors
            let check_write = |seq: Result<CursorIterator<'_, _>>, want_first: i64, want_n: i64| -> Result<()> {
                let (mut first, mut n) = (-1i64, 0i64);
                for c in seq? {
                    let v = c?.read_uint()?;
                    if first < 0 {
                        first = v as i64;
                    }
                    n += 1;
                }
                assert_eq!(first, want_first);
                assert_eq!(n, want_n);
                Ok(())
            };
            check_write(list.iter_from(COUNT - 3), COUNT - 3, 3)?;
            check_write(linked.iter_from(-2), COUNT - 2, 2)?;
            Ok(())
        })
        .unwrap();

    let moment_cursor = history.get_cursor(-1).unwrap().unwrap();
    let moment = ReadHashMap::new(moment_cursor).unwrap();
    let list = ReadArrayList::new(moment.get_cursor("list").unwrap().unwrap()).unwrap();
    let linked = ReadLinkedArrayList::new(moment.get_cursor("linked").unwrap().unwrap()).unwrap();

    // walk an iterator and assert it yields resolved, resolved+1, .., count-1
    let check_from = |seq: Result<CursorIterator<'_, _>>, resolved: i64| {
        let mut expected = resolved;
        for c in seq.unwrap() {
            let v = c.unwrap().read_uint().unwrap();
            assert_eq!(v, expected as u64);
            expected += 1;
        }
        assert_eq!(expected, COUNT);
    };

    // iteratorFrom(k) yields exactly k, k+1, .., count-1, for both types.
    // negative indexes count from the end: -1 starts at the last element, -count
    // at the first.
    let starts = [0, 1, 15, 16, 17, 100, COUNT - 2, COUNT - 1, -1, -2, -16, -100, -COUNT];
    for start in starts {
        let resolved = if start < 0 { COUNT + start } else { start };
        check_from(list.iter_from(start), resolved);
        check_from(linked.iter_from(start), resolved);
    }

    // a start out of range (past the end, or more negative than -count) yields nothing
    for start in [COUNT, COUNT + 1, COUNT + 1000, -COUNT - 1, -COUNT - 1000] {
        let mut n = 0;
        for c in list.iter_from(start).unwrap() {
            c.unwrap();
            n += 1;
        }
        for c in linked.iter_from(start).unwrap() {
            c.unwrap();
            n += 1;
        }
        assert_eq!(n, 0);
    }
}

// TestReplication

#[test]
fn replication() {
    // CoreMemory
    {
        let mut source_core = CoreMemory::new();
        let mut replica_core = CoreMemory::new();
        replication_with(&mut source_core, &mut replica_core);
        roots_with(&mut source_core, &mut replica_core);
    }

    // CoreFile
    {
        let mut source_core = CoreFile::new(temp_file());
        let mut replica_core = CoreFile::new(temp_file());
        replication_with(&mut source_core, &mut replica_core);
        roots_with(&mut source_core, &mut replica_core);
    }

    // CoreBufferedFile
    {
        let mut source_core = CoreBufferedFile::with_buffer_size(temp_file(), 1024);
        let mut replica_core = CoreBufferedFile::with_buffer_size(temp_file(), 1024);
        replication_with(&mut source_core, &mut replica_core);
        roots_with(&mut source_core, &mut replica_core);
    }

    replica_of_other_file();
}

// TestRootTrailerChecksum

/// A bitwise CRC-64/XZ, independent of the library's table-driven one.
fn reference_crc64_xz(data: &[u8]) -> u64 {
    let mut crc = !0u64;
    for &byte in data {
        crc ^= byte as u64;
        for _ in 0..8 {
            crc = if crc & 1 == 1 { (crc >> 1) ^ 0xC96C_5795_D787_0F42 } else { crc >> 1 };
        }
    }
    !crc
}

#[test]
fn root_trailer_checksum_is_crc64_xz() {
    // trailer checksums are CRC-64/XZ, whose check value is the checksum of "123456789".
    // the crate doesn't expose its CRC function, so check the reference against the
    // check value, then check that root_trailer_checksum is the reference CRC of its
    // big-endian inputs.
    assert_eq!(reference_crc64_xz(b"123456789"), 0x995dc9bbdf1939fa);
    let cases = [
        (0x0102030405060708u64, 37i64, Slot::default(), 0u64),
        (1, 12345, Slot::new(42, Tag::Uint), 0xdeadbeef),
        (u64::MAX, 1 << 40, Slot::new(1000, Tag::ArrayList).with_full(true), u64::MAX),
    ];
    for (file_id, position, root, commit_id) in cases {
        let mut buf = Vec::new();
        buf.extend_from_slice(&file_id.to_be_bytes());
        buf.extend_from_slice(&position.to_be_bytes());
        buf.extend_from_slice(&root.to_bytes());
        buf.extend_from_slice(&commit_id.to_be_bytes());
        assert_eq!(root_trailer_checksum(file_id, position, root, commit_id), reference_crc64_xz(&buf));
    }
}

// replication helpers

fn read_uint<C: Core>(cursor: Result<Option<ReadCursor<'_, C>>>) -> u64 {
    cursor.unwrap().expect("expected a cursor").read_uint().unwrap()
}

/// a replica is never extended with bytes from a file it isn't a replica of
fn replica_of_other_file() {
    let source = Database::new(CoreMemory::new(), sha1_hasher().with_file_id(1)).unwrap();
    let other = Database::new(CoreMemory::new(), sha1_hasher().with_file_id(2)).unwrap();
    let replica = Database::new(CoreMemory::new(), sha1_hasher()).unwrap();

    // the same writes give both files the same layout
    let mut source_root = source.root_cursor();
    source_root.write(Data::Uint(1)).unwrap();
    let mut other_root = other.root_cursor();
    other_root.write(Data::Uint(1)).unwrap();
    replicate(&source, &replica);

    // the other file has a trailer where the replica's committed bytes end,
    // but its checksum covers a different file ID, so the replica is replaced
    other_root.write(Data::Uint(2)).unwrap();
    assert_eq!(other.replication_start(replica.replica_state().unwrap()).unwrap(), 0);

    // and if its bytes are appended anyway, they are rejected
    {
        let start = replica.committed_size().unwrap();
        let end = other.committed_size().unwrap();
        let mut buffer = Vec::new();
        other.read_committed(start, end, &mut buffer).unwrap();
        let result = replica.apply_replicated(start, &mut buffer.as_slice(), end - start);
        assert!(matches!(result, Err(Error::InvalidDatabase)), "expected InvalidDatabase, got {result:?}");
        assert_eq!(replica.committed_size().unwrap(), start);
    }

    // a source restored from an older copy keeps its file ID, but
    // its history diverges, so the replica is replaced too
    let restored = Database::new(CoreMemory::new(), sha1_hasher().with_file_id(1)).unwrap();
    let mut restored_root = restored.root_cursor();
    restored_root.write(Data::Uint(3)).unwrap();
    assert_eq!(restored.replication_start(replica.replica_state().unwrap()).unwrap(), 0);

    // copies of one file that write different data of the same size have the
    // same layout, but every commit has a random ID, so their histories differ
    {
        let copy_a = Database::new(CoreMemory::new(), sha1_hasher().with_file_id(3)).unwrap();
        let copy_b = Database::new(CoreMemory::new(), sha1_hasher().with_file_id(3)).unwrap();
        let copy_replica = Database::new(CoreMemory::new(), sha1_hasher()).unwrap();
        copy_a.root_cursor().write("aaaaaaaaaaaa").unwrap();
        copy_b.root_cursor().write("bbbbbbbbbbbb").unwrap();

        replicate(&copy_a, &copy_replica);
        assert_eq!(copy_b.committed_size().unwrap(), copy_a.committed_size().unwrap());
        assert_eq!(copy_b.replication_start(copy_replica.replica_state().unwrap()).unwrap(), 0);
        replicate(&copy_b, &copy_replica);
        let value = copy_replica.root_cursor().read_bytes(Some(1024)).unwrap();
        assert_eq!(String::from_utf8(value).unwrap(), "bbbbbbbbbbbb");
    }

    // while the real source only sends the new bytes
    source_root.write(Data::Uint(2)).unwrap();
    assert_eq!(
        source.replication_start(replica.replica_state().unwrap()).unwrap(),
        replica.committed_size().unwrap()
    );
    replicate(&source, &replica);
    expect_same_committed_bytes(&source, &replica);
}

fn read_committed_bytes<C: Core>(db: &Database<C>, start: i64) -> Vec<u8> {
    let mut buffer = Vec::new();
    db.read_committed(start, db.committed_size().unwrap(), &mut buffer).unwrap();
    buffer
}

/// the replica sends its state, and the source sends back the bytes it doesn't
/// have yet (or all of them, if it isn't a replica of this source)
fn replicate<S: Core, R: Core>(source: &Database<S>, replica: &Database<R>) {
    let start = source.replication_start(replica.replica_state().unwrap()).unwrap();
    let end = source.committed_size().unwrap();
    let mut buffer = Vec::new();
    source.read_committed(start, end, &mut buffer).unwrap();
    replica.apply_replicated(start, &mut buffer.as_slice(), end - start).unwrap();
}

/// checks that no committed byte has changed since committed was read,
/// except the root header (the root slot and file size after the database
/// header). then replicates and checks that the replica is identical.
fn expect_append_only_and_replicate<S: Core, R: Core>(
    source: &Database<S>,
    replica: &Database<R>,
    committed: &mut Vec<u8>,
) {
    let root_header_start = HEADER_LENGTH;
    let root_header_end = root_header_start + 17;
    {
        let current = read_committed_bytes(source, 0);
        assert!(
            current.len() >= committed.len(),
            "committed bytes shrank from {} to {}",
            committed.len(),
            current.len()
        );
        assert!(
            committed[..root_header_start] == current[..root_header_start],
            "the database header or file ID changed"
        );
        assert!(
            committed[root_header_end..] == current[root_header_end..committed.len()],
            "committed bytes changed"
        );
        *committed = current;
    }

    replicate(source, replica);
    let replica_bytes = read_committed_bytes(replica, 0);
    assert!(*committed == replica_bytes, "the replica differs from the source");
}

fn expect_same_committed_bytes<S: Core, R: Core>(source: &Database<S>, replica: &Database<R>) {
    let source_bytes = read_committed_bytes(source, 0);
    let replica_bytes = read_committed_bytes(replica, 0);
    assert!(source_bytes == replica_bytes, "the replica differs from the source");
}

fn replication_with<C: Core>(source_core: &mut C, replica_core: &mut C) {
    let hasher = sha1_hasher();
    let ctx = |i: u64, fail: bool| {
        move |cursor: &mut WriteCursor<'_, &mut C>| -> Result<()> {
            let mut moment = WriteHashMap::new(cursor)?;
            moment.put(format!("key-{i}"), Data::Uint(i))?;
            let mut list_cursor = moment.put_cursor("list")?;
            let mut list = WriteArrayList::new(&mut list_cursor)?;
            list.append(Data::Uint(i))?;
            if fail {
                return Err(err_fail());
            }
            Ok(())
        }
    };

    source_core.set_length(0).unwrap();
    replica_core.set_length(0).unwrap();

    // a fixed file ID, so the bytes of the new database are known
    let fixed_hasher = hasher.clone().with_file_id(0x0102030405060708);
    let source = Database::new(&mut *source_core, fixed_hasher).unwrap();
    let replica = Database::new(&mut *replica_core, hasher.clone()).unwrap();

    // a new database is its header (which ends with its file ID), its root
    // header, and the trailer for its empty root: the slot (9 zero bytes), the commit ID (0 for
    // the first commit), then the CRC-64/XZ of the file ID, the trailer's position
    // (37), the slot, and the commit ID
    {
        let b = read_committed_bytes(&source, 0);
        assert_eq!(b.len(), 62);
        assert_eq!(&b[12..20], &[0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08], "unexpected file ID bytes");
        assert_eq!(
            &b[37..],
            &[
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, //
                0x00, 0xd6, 0x18, 0x4e, 0x46, 0xb4, 0x7d, 0x29, //
                0x26,
            ],
            "unexpected trailer bytes"
        );
    }

    // new databases have their own random file IDs, so the
    // first sync replaces the replica with a copy of the source
    assert_eq!(source.replication_start(replica.replica_state().unwrap()).unwrap(), 0);
    replicate(&source, &replica);
    expect_same_committed_bytes(&source, &replica);

    assert_eq!(source.header().version, VERSION);

    let mut history = WriteArrayList::new(&mut source.root_cursor()).unwrap();

    let mut committed = read_committed_bytes(&source, 0);

    // enough moments for the top-level array list to grow to three levels
    for i in 0..300u64 {
        if i == 200 {
            // roll back the history
            history.slice(150).unwrap();
        } else if i % 50 == 25 {
            // a failed transaction
            let slot = history.get_slot(-1).unwrap();
            assert!(is_fail(history.append_context(slot, ctx(i, true))));
        } else {
            let slot = history.get_slot(-1).unwrap();
            history.append_context(slot, ctx(i, false)).unwrap();
        }

        expect_append_only_and_replicate(&source, &replica, &mut committed);
    }

    // ApplyReplicated must be given exactly the bytes up to a trailer.
    // a short append fails and is overwritten by the next one.
    {
        let slot = history.get_slot(-1).unwrap();
        history.append_context(slot, ctx(300, false)).unwrap();
        let start = replica.committed_size().unwrap();
        let end = source.committed_size().unwrap();
        let b = read_committed_bytes(&source, start);
        let mut short_reader = &b[..b.len() - 1];
        let result = replica.apply_replicated(start, &mut short_reader, (b.len() - 1) as i64);
        assert!(matches!(result, Err(Error::InvalidDatabase)), "expected InvalidDatabase, got {result:?}");
        assert_eq!(replica.committed_size().unwrap(), start);
        // and only committed bytes can be read, starting at 0 or after the root header
        let result = source.read_committed(start, end + 1, &mut io::sink());
        assert!(matches!(result, Err(Error::InvalidRange)), "expected InvalidRange, got {result:?}");
        let result = source.read_committed(20, end, &mut io::sink());
        assert!(matches!(result, Err(Error::InvalidRange)), "expected InvalidRange, got {result:?}");
        replicate(&source, &replica);
        expect_same_committed_bytes(&source, &replica);
    }

    // the replica can be reopened and read
    drop(replica);
    let replica = Database::new(&mut *replica_core, hasher.clone()).unwrap();
    let source_history = ReadArrayList::new(source.root_cursor()).unwrap();
    let replica_history = ReadArrayList::new(replica.root_cursor()).unwrap();
    assert_eq!(replica_history.count().unwrap(), source_history.count().unwrap());
    let moment_cursor = replica_history.get_cursor(-1).unwrap().unwrap();
    let moment = ReadHashMap::new(moment_cursor).unwrap();
    assert_eq!(read_uint(moment.get_cursor("key-299")), 299);
    // removed by the slice
    assert!(moment.get_cursor("key-180").unwrap().is_none());
    assert_eq!(read_uint(moment.get_cursor("key-149")), 149);

    // a compacted database is a new file, so a replica of it is seeded from byte 0
    {
        let target = source.compact(CoreMemory::new(), &mut MemoryOffsetMap::new()).unwrap();
        let compacted_replica = Database::new(CoreMemory::new(), hasher.clone()).unwrap();
        replicate(&target, &compacted_replica);
        expect_same_committed_bytes(&target, &compacted_replica);

        // and it can keep receiving transactions
        let mut target_history = WriteArrayList::new(&mut target.root_cursor()).unwrap();
        let slot = target_history.get_slot(-1).unwrap();
        target_history.append(slot).unwrap();
        replicate(&target, &compacted_replica);
        expect_same_committed_bytes(&target, &compacted_replica);

        let compacted_history = ReadArrayList::new(compacted_replica.root_cursor()).unwrap();
        assert_eq!(compacted_history.count().unwrap(), 2);
        let compacted_moment_cursor = compacted_history.get_cursor(-1).unwrap().unwrap();
        let compacted_moment = ReadHashMap::new(compacted_moment_cursor).unwrap();
        assert_eq!(read_uint(compacted_moment.get_cursor("key-299")), 299);
    }

    // a database whose trailer doesn't match its header is invalid
    {
        let pos = replica.committed_size().unwrap() - 1;
        {
            let mut core = replica.core();
            core.seek_to(pos as u64).unwrap();
            let mut b = [0u8; 1];
            core.read(&mut b).unwrap();
            core.seek_to(pos as u64).unwrap();
            core.write(&[!b[0]]).unwrap();
            core.flush().unwrap();
        }
        drop(replica);
        let result = Database::new(&mut *replica_core, hasher.clone());
        assert!(matches!(result, Err(Error::InvalidDatabase)), "expected InvalidDatabase, got {result:?}");
    }
}

/// the root can be any type, not just an array list
fn roots_with<C: Core>(source_core: &mut C, replica_core: &mut C) {
    let hasher = sha1_hasher();

    // a hash map root
    {
        source_core.set_length(0).unwrap();
        replica_core.set_length(0).unwrap();

        let source = Database::new(&mut *source_core, hasher.clone()).unwrap();
        let replica = Database::new(&mut *replica_core, hasher.clone()).unwrap();

        let mut m = WriteHashMap::new(&mut source.root_cursor()).unwrap();

        // initializing an initialized root doesn't start a transaction
        let size_after_init = source.committed_size().unwrap();
        WriteHashMap::new(&mut source.root_cursor()).unwrap();
        assert_eq!(source.committed_size().unwrap(), size_after_init);

        // nor can the root be initialized as another type
        let result = WriteArrayList::new(&mut source.root_cursor());
        assert!(matches!(result, Err(Error::UnexpectedTag)), "expected UnexpectedTag");
        assert_eq!(source.committed_size().unwrap(), size_after_init);

        let mut committed = read_committed_bytes(&source, 0);

        for i in 0..100u64 {
            m.put(format!("key-{i}"), Data::Uint(i)).unwrap();
            if i == 50 {
                assert!(m.remove("key-25").unwrap());
            }

            expect_append_only_and_replicate(&source, &replica, &mut committed);
        }

        // a key is written in the same transaction as the lookup, so it works on a root map.
        // (the string-key puts above already wrote their keys, so use an entry without one.)
        let key_hash = {
            use sha1::Digest;
            sha1::Sha1::digest(b"key-only-hashed").to_vec()
        };
        m.put_by_hash(&key_hash, Data::Uint(1)).unwrap();
        m.put_key("key-only-hashed", Data::string("key-only-hashed")).unwrap();
        {
            let kv = m.get_key_value_pair("key-only-hashed").unwrap().unwrap();
            let key = kv.key_cursor.read_bytes(Some(1024)).unwrap();
            assert_eq!(String::from_utf8(key).unwrap(), "key-only-hashed");
            assert_eq!(kv.value_cursor.read_uint().unwrap(), 1);
        }

        // nested collections are written inside one transaction
        let inner_hash = source.digest(b"inner");
        m.write_cursor()
            .clone()
            .write_path_context(&[PathPart::HashMapGet(HashMapGetTarget::Value(&inner_hash))], |cursor| {
                let mut inner = WriteHashMap::new(cursor)?;
                inner.put("foo", Data::string("foo"))?;
                let mut list_cursor = inner.put_cursor("list")?;
                let mut list = WriteArrayList::new(&mut list_cursor)?;
                list.append(Data::Uint(1))?;
                list.append(Data::Uint(2))
            })
            .unwrap();
        replicate(&source, &replica);
        expect_same_committed_bytes(&source, &replica);

        // RunContext groups many writes into one transaction
        {
            let size_before = source.committed_size().unwrap();
            let batch = |fail: bool| {
                move |cursor: &mut WriteCursor<'_, &mut C>| -> Result<()> {
                    let mut root = WriteHashMap::new(cursor)?;
                    for i in 0..100u64 {
                        root.put(format!("batch-{i}"), Data::Uint(i))?;
                    }
                    if fail {
                        return Err(err_fail());
                    }
                    Ok(())
                }
            };

            // a failed transaction leaves nothing behind
            assert!(is_fail(source.run_context(batch(true))));
            assert_eq!(source.committed_size().unwrap(), size_before);
            assert!(m.get_cursor("batch-0").unwrap().is_none());

            // a successful one commits everything at once
            source.run_context(batch(false)).unwrap();
            assert!(source.committed_size().unwrap() > size_before);
            assert_eq!(read_uint(m.get_cursor("batch-0")), 0);
            assert_eq!(read_uint(m.get_cursor("batch-99")), 99);
            replicate(&source, &replica);
            expect_same_committed_bytes(&source, &replica);
        }

        // a nested write cursor can't be written to after its transaction
        let mut late_cursor = m.put_cursor("late").unwrap();
        let result = late_cursor.write(Data::Uint(1));
        assert!(matches!(result, Err(Error::ExpiredTransaction)), "expected ExpiredTransaction, got {result:?}");
        let result = WriteHashMap::new(&mut late_cursor);
        assert!(matches!(result, Err(Error::ExpiredTransaction)), "expected ExpiredTransaction");
        replicate(&source, &replica);
        expect_same_committed_bytes(&source, &replica);

        // the replica can be reopened and read
        drop(replica);
        let replica = Database::new(&mut *replica_core, hasher.clone()).unwrap();
        {
            let replica_map = ReadHashMap::new(replica.root_cursor()).unwrap();
            assert_eq!(read_uint(replica_map.get_cursor("key-99")), 99);
            assert!(replica_map.get_cursor("key-25").unwrap().is_none());
            let inner = ReadHashMap::new(replica_map.get_cursor("inner").unwrap().unwrap()).unwrap();
            let list = ReadArrayList::new(inner.get_cursor("list").unwrap().unwrap()).unwrap();
            assert_eq!(list.count().unwrap(), 2);
            assert_eq!(read_uint(list.get_cursor(-1)), 2);
        }

        // it can be compacted
        {
            let target = replica.compact(CoreMemory::new(), &mut MemoryOffsetMap::new()).unwrap();
            assert!(target.committed_size().unwrap() < replica.committed_size().unwrap());

            let target_map = ReadHashMap::new(target.root_cursor()).unwrap();
            assert_eq!(read_uint(target_map.get_cursor("key-99")), 99);
            assert!(target_map.get_cursor("key-25").unwrap().is_none());
            let inner = ReadHashMap::new(target_map.get_cursor("inner").unwrap().unwrap()).unwrap();
            let list = ReadArrayList::new(inner.get_cursor("list").unwrap().unwrap()).unwrap();
            assert_eq!(list.count().unwrap(), 2);

            // a compacted database is a new file, so a replica of it is seeded from byte 0
            let compacted_replica = Database::new(CoreMemory::new(), hasher.clone()).unwrap();
            replicate(&target, &compacted_replica);
            expect_same_committed_bytes(&target, &compacted_replica);
        }
    }

    // an array list root held by a wrapper stays current
    {
        source_core.set_length(0).unwrap();
        let db = Database::new(&mut *source_core, hasher.clone()).unwrap();

        let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
        history.append(Data::Uint(1)).unwrap();
        history.append(Data::Uint(2)).unwrap();
        assert_eq!(history.count().unwrap(), 2);
        let mut iter_count = 0;
        for c in history.iter().unwrap() {
            c.unwrap();
            iter_count += 1;
        }
        assert_eq!(iter_count, 2);

        // initializing an initialized root doesn't start a transaction
        let size = db.committed_size().unwrap();
        WriteArrayList::new(&mut db.root_cursor()).unwrap();
        assert_eq!(db.committed_size().unwrap(), size);
    }

    // a scalar root
    {
        source_core.set_length(0).unwrap();
        let db = Database::new(&mut *source_core, hasher.clone()).unwrap();

        let retained = db.root_cursor();
        let mut root = db.root_cursor();
        root.write(Data::Uint(42)).unwrap();
        assert_eq!(root.read_uint().unwrap(), 42);
        assert_eq!(db.root_cursor().read_uint().unwrap(), 42);

        // a root cursor kept from before the write sees the new root
        // everywhere it reads its slot, not just in typed reads
        assert_eq!(retained.read_uint().unwrap(), 42);
        assert_eq!(retained.slot().unwrap().value, 42);
        let slot = retained.read_path_slot(&[]).unwrap().unwrap();
        assert_eq!(slot.value, 42);
        let cursor = retained.read_path(&[]).unwrap().unwrap();
        assert_eq!(cursor.read_uint().unwrap(), 42);

        // the cursor stays a root cursor, so it can keep writing
        root.write(Data::string("this is too long to fit in a slot")).unwrap();
        let b = db.root_cursor().read_bytes(Some(64)).unwrap();
        assert_eq!(String::from_utf8(b).unwrap(), "this is too long to fit in a slot");

        // bytes can't be streamed into the root
        assert!(matches!(root.writer(), Err(Error::CursorNotWriteable)), "expected CursorNotWriteable");

        // a scalar root can't be initialized as a collection
        let result = WriteHashMap::new(&mut db.root_cursor());
        assert!(matches!(result, Err(Error::UnexpectedTag)), "expected UnexpectedTag");

        // but once it is cleared, it can
        root.write(Data::None).unwrap();
        let mut m = WriteHashMap::new(&mut db.root_cursor()).unwrap();
        m.put("foo", Data::Uint(1)).unwrap();
        assert_eq!(read_uint(m.get_cursor("foo")), 1);
    }

    // a hash set root
    {
        source_core.set_length(0).unwrap();
        let db = Database::new(&mut *source_core, hasher.clone()).unwrap();

        let mut set = WriteHashSet::new(&mut db.root_cursor()).unwrap();
        set.put("a").unwrap();
        set.put("a").unwrap();
        set.put("b").unwrap();
        for key in ["a", "b"] {
            let cursor = set.get_cursor(key).unwrap().unwrap();
            let value = cursor.read_bytes(Some(1024)).unwrap();
            assert_eq!(String::from_utf8(value).unwrap(), key);
        }
    }

    // a sorted map root
    {
        source_core.set_length(0).unwrap();
        let db = Database::new(&mut *source_core, hasher.clone()).unwrap();

        let mut m = WriteSortedMap::new(&mut db.root_cursor()).unwrap();
        m.put("b", Data::Uint(2)).unwrap();
        m.put("a", Data::Uint(1)).unwrap();
        m.put("c", Data::Uint(3)).unwrap();
        assert!(m.remove("c").unwrap());
        assert_eq!(m.count().unwrap(), 2);
        assert_eq!(m.rank("b").unwrap(), 1);
        assert_eq!(read_uint(m.get_cursor("a")), 1);

        let size = db.committed_size().unwrap();
        WriteSortedMap::new(&mut db.root_cursor()).unwrap();
        assert_eq!(db.committed_size().unwrap(), size);
    }

    // a linked array list root
    {
        source_core.set_length(0).unwrap();
        let db = Database::new(&mut *source_core, hasher.clone()).unwrap();

        let mut list = WriteLinkedArrayList::new(&mut db.root_cursor()).unwrap();
        list.append(Data::Uint(1)).unwrap();
        list.append(Data::Uint(3)).unwrap();
        list.insert(1, Data::Uint(2)).unwrap();
        assert_eq!(list.count().unwrap(), 3);
        assert_eq!(read_uint(list.get_cursor(1)), 2);
        list.remove(0).unwrap();
        assert_eq!(read_uint(list.get_cursor(0)), 2);

        let size = db.committed_size().unwrap();
        WriteLinkedArrayList::new(&mut db.root_cursor()).unwrap();
        assert_eq!(db.committed_size().unwrap(), size);
    }
}
