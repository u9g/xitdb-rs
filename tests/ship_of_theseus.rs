//! "Ship of Theseus" tests: compaction and replication from strange starting
//! points, plus a mutation fuzzer for the reader.
//!
//! * Compaction must be idempotent: compacting a compacted database gives the
//!   same bytes (apart from the random file ID and commit IDs), and both hold
//!   the same data as the original's latest moment.
//! * A database whose every plank was replaced over many transactions must
//!   compact to the same bytes as one built with the final state directly.
//! * Replicas fed skipped, misplaced, truncated, bit-flipped or spliced bytes
//!   must reject them, or be repaired by the next honest sync.
//! * Mutated databases must never make the reader or compactor panic, hang,
//!   or allocate a forged length.
//!
//! The fuzzer's iteration count can be raised with `XITDB_FUZZ_ITERS`.

use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use xitdb::consts::{HEADER_LENGTH, ROOT_HEADER_END, ROOT_TRAILER_LENGTH};
use xitdb::*;

// a small deterministic rng (splitmix64), so failures can be replayed by seed

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn chance(&mut self, one_in: u64) -> bool {
        self.below(one_in) == 0
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }

    /// `min` to `min + spread - 1` random bytes.
    fn some_bytes(&mut self, min: usize, spread: u64) -> Vec<u8> {
        let len = min + self.below(spread) as usize;
        self.bytes(len)
    }
}

fn budget_exceeded() -> Error {
    Error::Io(io::Error::other("dump budget exceeded"))
}

/// A canonical text form of everything reachable from `cursor`. Hash map
/// entries are sorted, so two databases holding the same data dump the same
/// regardless of layout. `budget` bounds the work, so corrupt (e.g. cyclic)
/// data can't make it run forever.
fn dump<C: Core>(cursor: &ReadCursor<'_, C>, depth: usize, budget: &mut u64) -> Result<String> {
    if depth > 64 || *budget == 0 {
        return Err(budget_exceeded());
    }
    *budget -= 1;
    let slot = cursor.slot()?;
    Ok(match slot.tag {
        Tag::None => if slot.full { "null!".into() } else { "null".into() },
        Tag::Uint => format!("u{}", cursor.read_uint()?),
        Tag::Int => format!("i{}", cursor.read_int()?),
        Tag::Float => format!("f{:x}", cursor.read_float()?.to_bits()),
        Tag::Bytes | Tag::ShortBytes => {
            let bytes = cursor.read_bytes_object(Some(1 << 20))?;
            format!("b{:?}{:?}", bytes.format_tag, bytes.value)
        }
        Tag::ArrayList | Tag::LinkedArrayList => {
            let mut items = Vec::new();
            for item in cursor.iter()? {
                items.push(dump(&item?, depth + 1, budget)?);
                if *budget == 0 {
                    return Err(budget_exceeded());
                }
            }
            format!("{:?}[{}; {}]", slot.tag, cursor.count()?, items.join(", "))
        }
        Tag::HashMap | Tag::HashSet | Tag::CountedHashMap | Tag::CountedHashSet | Tag::SortedMap | Tag::SortedSet => {
            let mut entries = Vec::new();
            for item in cursor.iter()? {
                let kv = item?.read_key_value_pair()?;
                let key = dump(&kv.key_cursor, depth + 1, budget)?;
                let value = dump(&kv.value_cursor, depth + 1, budget)?;
                entries.push(format!("{key}: {value}"));
                if *budget == 0 {
                    return Err(budget_exceeded());
                }
            }
            let count = match slot.tag {
                Tag::HashMap | Tag::HashSet => entries.len() as i64,
                _ => cursor.count()?,
            };
            // sorted maps must already iterate in order; hash maps are sorted here
            if !matches!(slot.tag, Tag::SortedMap | Tag::SortedSet) {
                entries.sort();
            }
            format!("{:?}({}){{{}}}", slot.tag, count, entries.join(", "))
        }
        Tag::Index | Tag::KvPair | Tag::SortedKvPair => return Err(Error::UnexpectedTag),
    })
}

fn dump_root<C: Core>(db: &Database<C>) -> String {
    dump(&db.root_cursor().read_cursor(), 0, &mut u64::MAX.clone()).unwrap()
}

/// The dump of the latest moment of a database whose root is a history.
fn dump_last_moment<C: Core>(db: &Database<C>) -> String {
    let history = ReadArrayList::new(db.root_cursor()).unwrap();
    match history.get_cursor(-1).unwrap() {
        Some(moment) => dump(&moment, 0, &mut u64::MAX.clone()).unwrap(),
        None => "no moments".into(),
    }
}

fn random_value(rng: &mut Rng) -> Data<'static> {
    match rng.below(8) {
        // the largest uint the format can store is i64::MAX
        0 => Data::Uint(rng.next() >> 1),
        1 => Data::Int(rng.next() as i64),
        2 => Data::Float(f64::from_bits(rng.next())),
        3 => Data::from(rng.some_bytes(0, 9)),
        4 => Data::from(rng.some_bytes(9, 300)),
        5 => Data::tagged_bytes(rng.some_bytes(0, 40), [b'j', b's']),
        // longer than the 4096 byte chunks compaction and replication copy in
        6 => Data::from(rng.some_bytes(4000, 9000)),
        _ => Data::Uint(rng.below(4)),
    }
}

fn key(rng: &mut Rng, space: u64) -> String {
    format!("key{}", rng.below(space))
}

/// Makes one random change to a moment, covering every collection type.
fn random_op<C: Core>(moment: &mut WriteHashMap<'_, C>, rng: &mut Rng) -> Result<()> {
    match rng.below(9) {
        0 => {
            let mut map = WriteHashMap::new(&mut moment.put_cursor("map")?)?;
            if rng.chance(4) {
                map.remove(key(rng, 40))?;
            } else {
                map.put(key(rng, 40), random_value(rng))?;
            }
        }
        1 => {
            let mut map = WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?;
            if rng.chance(4) {
                map.remove(key(rng, 30))?;
            } else {
                map.put(key(rng, 30), random_value(rng))?;
            }
        }
        2 => {
            let mut set = WriteHashSet::new(&mut moment.put_cursor("set")?)?;
            if rng.chance(3) { set.remove(key(rng, 30))?; } else { set.put(key(rng, 30))?; }
            let mut set = WriteCountedHashSet::new(&mut moment.put_cursor("counted-set")?)?;
            if rng.chance(3) { set.remove(key(rng, 30))?; } else { set.put(key(rng, 30))?; }
        }
        3 => {
            let mut list = WriteArrayList::new(&mut moment.put_cursor("list")?)?;
            let count = list.write_cursor().read_cursor().count()?;
            match rng.below(6) {
                0 if count > 0 => list.slice(rng.below(count as u64) as i64)?,
                1 if count > 0 => list.put(rng.below(count as u64) as i64, random_value(rng))?,
                _ => {
                    for _ in 0..rng.below(20) {
                        list.append(random_value(rng))?;
                    }
                }
            }
        }
        4 => {
            let mut list = WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?;
            let count = list.write_cursor().read_cursor().count()?;
            match rng.below(5) {
                0 if count > 0 => list.remove(rng.below(count as u64) as i64)?,
                1 if count > 0 => list.insert(rng.below(count as u64) as i64, random_value(rng))?,
                2 if count > 1 => {
                    let offset = rng.below(count as u64);
                    list.slice(offset as i64, rng.below(count as u64 - offset) as i64)?
                }
                _ => {
                    for _ in 0..rng.below(20) {
                        list.append(random_value(rng))?;
                    }
                }
            }
        }
        5 => {
            let mut map = WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?;
            for _ in 0..rng.below(10) {
                if rng.chance(4) {
                    map.remove(key(rng, 200))?;
                } else {
                    map.put(key(rng, 200), random_value(rng))?;
                }
            }
        }
        6 => {
            let mut set = WriteSortedSet::new(&mut moment.put_cursor("sorted-set")?)?;
            if rng.chance(4) { set.remove(key(rng, 200))?; } else { set.put(key(rng, 200))?; }
        }
        7 => {
            // a list of nested maps
            let mut list = WriteArrayList::new(&mut moment.put_cursor("nested")?)?;
            let mut map = WriteHashMap::new(&mut list.append_cursor()?)?;
            for _ in 0..rng.below(4) {
                map.put(key(rng, 10), random_value(rng))?;
            }
        }
        _ => moment.put(key(rng, 8), random_value(rng))?,
    }
    Ok(())
}

/// Appends `txs` random transactions to a history. Some end by aliasing an
/// existing collection under another key, so data is shared within moments
/// as well as between them.
fn random_history<C: Core>(db: &Database<C>, seed: u64, txs: usize) -> Result<()> {
    let mut rng = Rng(seed);
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    for _ in 0..txs {
        let last = history.get_slot(-1)?;
        history.append_context(last, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            for _ in 0..1 + rng.below(6) {
                random_op(&mut moment, &mut rng)?;
            }
            // aliasing last, because writing to the original later in the same
            // transaction would change the alias too (see the README on freeze)
            if rng.chance(3) {
                let source = ["map", "list", "sorted", "linked", "nested"][rng.below(5) as usize];
                let slot = ReadHashMap::new(moment.write_cursor().read_cursor())?.get_slot(source)?;
                if let Some(slot) = slot {
                    moment.put(format!("alias-{source}"), slot)?;
                }
            }
            Ok(())
        })?;
    }
    Ok(())
}

fn committed_bytes<C: Core>(db: &Database<C>) -> Vec<u8> {
    let mut buf = Vec::new();
    db.read_committed(0, db.committed_size().unwrap(), &mut buf).unwrap();
    buf
}

/// The committed bytes of a compacted database with the parts that are
/// random by design zeroed: the file ID, and the commit ID and checksum of
/// its two trailers (the one written by `Database::new` and the one ending
/// the compaction's transaction).
fn masked_compacted_bytes<C: Core>(db: &Database<C>) -> Vec<u8> {
    let mut buf = committed_bytes(db);
    buf[12..HEADER_LENGTH].fill(0);
    let trailer_random = SLOT_LENGTH..ROOT_TRAILER_LENGTH;
    for trailer in [ROOT_HEADER_END as usize, buf.len() - ROOT_TRAILER_LENGTH] {
        buf[trailer + trailer_random.start..trailer + trailer_random.end].fill(0);
    }
    buf
}

fn compact<C: Core>(db: &Database<C>) -> Database<CoreMemory> {
    db.compact(CoreMemory::new(), &mut MemoryOffsetMap::new()).unwrap()
}

// compaction

#[test]
fn compaction_keeps_the_last_moment_and_is_idempotent() {
    for seed in 0..12 {
        let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
        random_history(&db, seed, 5 + seed as usize * 6).unwrap();

        let once = compact(&db);
        let twice = compact(&once);
        let thrice = compact(&twice);

        // the same data as the original's latest moment, as the only moment
        let expected = dump_last_moment(&db);
        assert_eq!(ReadArrayList::new(once.root_cursor()).unwrap().count().unwrap(), 1, "seed {seed}");
        assert_eq!(dump_last_moment(&once), expected, "seed {seed}");
        assert_eq!(dump_last_moment(&twice), expected, "seed {seed}");

        // compaction is a fixed point after the first time
        let once_bytes = masked_compacted_bytes(&once);
        assert_eq!(once_bytes, masked_compacted_bytes(&twice), "seed {seed}: compact(compact(db)) != compact(db)");
        assert_eq!(once_bytes, masked_compacted_bytes(&thrice), "seed {seed}");
        assert!(once_bytes.len() <= committed_bytes(&db).len());
    }
}

#[test]
fn compaction_through_a_file_offset_map_matches_memory() {
    for seed in 100..104 {
        let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
        random_history(&db, seed, 30).unwrap();
        let in_memory = compact(&db);

        let scratch = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
        let mut on_disk = None;
        scratch
            .run_context(|cursor| {
                let mut offsets = FileOffsetMap::new(cursor)?;
                on_disk = Some(db.compact(CoreMemory::new(), &mut offsets)?);
                Ok(())
            })
            .unwrap();
        assert_eq!(masked_compacted_bytes(&in_memory), masked_compacted_bytes(&on_disk.unwrap()), "seed {seed}");
    }
}

#[test]
fn compaction_keeps_shared_data_shared() {
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    history
        .append_context(Data::None, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            let mut list = WriteArrayList::new(&mut moment.put_cursor("list")?)?;
            for i in 0..100u64 {
                list.append(i)?;
            }
            moment.put("big", vec![7u8; 10_000])?;
            Ok(())
        })
        .unwrap();
    // in a later transaction, alias both under many keys
    let last = history.get_slot(-1).unwrap();
    history
        .append_context(last, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            let read = ReadHashMap::new(moment.write_cursor().read_cursor())?;
            let (list, big) = (read.get_slot("list")?.unwrap(), read.get_slot("big")?.unwrap());
            for i in 0..50 {
                moment.put(format!("list{i}"), list)?;
                moment.put(format!("big{i}"), big)?;
            }
            Ok(())
        })
        .unwrap();

    let compacted = compact(&db);
    let moment = ReadHashMap::new(ReadArrayList::new(compacted.root_cursor()).unwrap().get_cursor(-1).unwrap().unwrap()).unwrap();
    let list = moment.get_slot("list").unwrap().unwrap();
    let big = moment.get_slot("big").unwrap().unwrap();
    for i in 0..50 {
        assert_eq!(moment.get_slot(format!("list{i}")).unwrap().unwrap(), list);
        assert_eq!(moment.get_slot(format!("big{i}")).unwrap().unwrap(), big);
    }
    // 51 copies of 10 KB would be over 500 KB
    assert!(committed_bytes(&compacted).len() < 30_000);
    assert_eq!(dump_last_moment(&compacted), dump_last_moment(&db));
}

/// Replaces every plank of the ship, one transaction at a time, and checks
/// that the result compacts to exactly the ship built new.
#[test]
fn the_ship_of_theseus() {
    const PLANKS: u64 = 300;
    let plank = |i: u64, version: u64| format!("plank {i} version {version} {}", "x".repeat((i % 20) as usize));

    let old_ship = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut old_ship.root_cursor()).unwrap();
    history
        .append_context(Data::None, |cursor| {
            let mut ship = WriteHashMap::new(cursor)?;
            let mut hull = WriteArrayList::new(&mut ship.put_cursor("hull")?)?;
            let mut rigging = WriteSortedMap::new(&mut ship.put_cursor("rigging")?)?;
            for i in 0..PLANKS {
                ship.put(format!("plank{i}"), plank(i, 0))?;
                hull.append(plank(i, 0))?;
                rigging.put(format!("{i:05}"), plank(i, 0))?;
            }
            Ok(())
        })
        .unwrap();
    let mut rng = Rng(7);
    let mut order: Vec<u64> = (0..PLANKS).collect();
    for i in (1..order.len()).rev() {
        order.swap(i, rng.below(i as u64 + 1) as usize);
    }
    for (n, &i) in order.iter().enumerate() {
        let last = history.get_slot(-1).unwrap();
        history
            .append_context(last, |cursor| {
                let mut ship = WriteHashMap::new(cursor)?;
                // replace it a few times, with a detour through removal
                ship.remove(format!("plank{i}"))?;
                ship.put(format!("plank{i}"), plank(i, 1))?;
                ship.put(format!("plank{i}"), plank(i, 2))?;
                WriteArrayList::new(&mut ship.put_cursor("hull")?)?.put(i as i64, plank(i, 2))?;
                let mut rigging = WriteSortedMap::new(&mut ship.put_cursor("rigging")?)?;
                rigging.remove(format!("{i:05}"))?;
                rigging.put(format!("{i:05}"), plank(i, 2))?;
                // a temporary plank that is thrown away again
                ship.put(format!("scaffold{n}"), n as u64)?;
                ship.remove(format!("scaffold{n}"))?;
                Ok(())
            })
            .unwrap();
    }

    let new_ship = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    WriteArrayList::new(&mut new_ship.root_cursor())
        .unwrap()
        .append_context(Data::None, |cursor| {
            let mut ship = WriteHashMap::new(cursor)?;
            let mut hull = WriteArrayList::new(&mut ship.put_cursor("hull")?)?;
            let mut rigging = WriteSortedMap::new(&mut ship.put_cursor("rigging")?)?;
            for i in 0..PLANKS {
                ship.put(format!("plank{i}"), plank(i, 2))?;
                hull.append(plank(i, 2))?;
                rigging.put(format!("{i:05}"), plank(i, 2))?;
            }
            Ok(())
        })
        .unwrap();

    // every moment of the old ship is still there, and the first is all version 0
    let old_history = ReadArrayList::new(old_ship.root_cursor()).unwrap();
    assert_eq!(old_history.count().unwrap(), PLANKS as i64 + 1);
    let first = ReadHashMap::new(old_history.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(first.get_cursor("plank0").unwrap().unwrap().read_bytes(None).unwrap(), plank(0, 0).as_bytes());

    assert_eq!(dump_last_moment(&old_ship), dump_last_moment(&new_ship));
    // the hash map trie and b-tree shapes depend only on their contents,
    // so the compacted copies are the same ship, byte for byte
    let (old_compacted, new_compacted) = (compact(&old_ship), compact(&new_ship));
    assert_eq!(dump_root(&old_compacted), dump_root(&new_compacted));
    assert_eq!(masked_compacted_bytes(&old_compacted), masked_compacted_bytes(&new_compacted));
}

// replication

/// Brings `replica` up to date with `source` the way the README describes.
fn sync<S: Core, R: Core>(source: &Database<S>, replica: &Database<R>) -> i64 {
    let start = source.replication_start(replica.replica_state().unwrap()).unwrap();
    let end = source.committed_size().unwrap();
    let mut buf = Vec::new();
    source.read_committed(start, end, &mut buf).unwrap();
    replica.apply_replicated(start, &mut buf.as_slice(), end - start).unwrap();
    start
}

fn chunk<C: Core>(db: &Database<C>, start: i64, end: i64) -> Vec<u8> {
    let mut buf = Vec::new();
    db.read_committed(start, end, &mut buf).unwrap();
    buf
}

/// Appends one moment with a fixed-size change, so different histories can
/// have trailers at exactly the same positions.
fn commit_word<C: Core>(db: &Database<C>, word: &str) {
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    let last = history.get_slot(-1).unwrap();
    history
        .append_context(last, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            moment.put("word", word)?;
            let count = moment.write_cursor().read_cursor().count().unwrap_or(0);
            moment.put("n", count as u64)?;
            Ok(())
        })
        .unwrap();
}

fn assert_same_db<S: Core, R: Core>(source: &Database<S>, replica: &Database<R>) {
    assert_eq!(committed_bytes(source), committed_bytes(replica));
    assert_eq!(dump_root(source), dump_root(replica));
}

#[test]
fn replica_rejects_skipped_and_misplaced_bytes() {
    let source = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let replica = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    random_history(&source, 1, 3).unwrap();
    sync(&source, &replica);
    let synced_at = replica.committed_size().unwrap();
    let synced_dump = dump_root(&replica);

    random_history(&source, 2, 1).unwrap();
    let middle = source.committed_size().unwrap();
    random_history(&source, 3, 1).unwrap();
    let end = source.committed_size().unwrap();

    let unchanged = |replica: &Database<CoreMemory>| {
        assert_eq!(replica.committed_size().unwrap(), synced_at);
        assert_eq!(dump_root(replica), synced_dump);
    };

    // only every other chunk: the third chunk, at its real start
    let third = chunk(&source, middle, end);
    assert!(replica.apply_replicated(middle, &mut third.as_slice(), end - middle).is_err());
    unchanged(&replica);

    // the third chunk, claiming to start where the replica ends
    assert!(replica.apply_replicated(synced_at, &mut third.as_slice(), third.len() as i64).is_err());
    unchanged(&replica);

    // the right bytes, shifted by one in either direction
    let both = chunk(&source, synced_at, end);
    for shift in [1usize, 2, 9] {
        let shifted = [vec![0u8; shift], both.clone()].concat();
        assert!(replica.apply_replicated(synced_at, &mut shifted.as_slice(), shifted.len() as i64).is_err());
        unchanged(&replica);
        let shifted = &both[shift..];
        assert!(replica.apply_replicated(synced_at, &mut &shifted[..], shifted.len() as i64).is_err());
        unchanged(&replica);
    }

    // after all that, an honest sync still brings it up to date
    assert_eq!(sync(&source, &replica), synced_at);
    assert_same_db(&source, &replica);
}

/// Interrupts a sync after every possible number of bytes. The replica
/// must stay at its last commit each time, and recover with the next sync.
#[test]
fn replica_survives_a_sync_cut_at_every_byte() {
    struct Cut<'a> {
        data: &'a [u8],
        left: usize,
    }
    impl io::Read for Cut<'_> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.left == 0 {
                return Err(io::Error::new(io::ErrorKind::ConnectionReset, "cut"));
            }
            let n = buf.len().min(self.left).min(self.data.len());
            buf[..n].copy_from_slice(&self.data[..n]);
            self.data = &self.data[n..];
            self.left -= n;
            Ok(n)
        }
    }

    let source = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    random_history(&source, 4, 2).unwrap();
    let replica = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    sync(&source, &replica);
    let synced_at = replica.committed_size().unwrap();
    let synced_dump = dump_root(&replica);

    random_history(&source, 5, 2).unwrap();
    let end = source.committed_size().unwrap();
    let bytes = chunk(&source, synced_at, end);
    for cut in 0..bytes.len() {
        let mut reader = Cut { data: &bytes, left: cut };
        assert!(replica.apply_replicated(synced_at, &mut reader, bytes.len() as i64).is_err());
        assert_eq!(replica.committed_size().unwrap(), synced_at, "cut at {cut}");
        if cut % 97 == 0 {
            assert_eq!(dump_root(&replica), synced_dump, "cut at {cut}");
        }
        // each time, the honest sync starts where the replica committed
        assert_eq!(source.replication_start(replica.replica_state().unwrap()).unwrap(), synced_at);
    }
    sync(&source, &replica);
    assert_same_db(&source, &replica);
}

/// Flips every bit of a sync in transit. Flips in the trailer must always
/// be rejected. Nothing checksums the data itself, so flips there can be
/// accepted, but the replica must never panic reading or compacting them.
#[test]
fn replica_with_a_flipped_bit() {
    let source = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    random_history(&source, 6, 1).unwrap();
    let base = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    sync(&source, &base);
    let synced_at = base.committed_size().unwrap();
    commit_word(&source, "flip");
    let end = source.committed_size().unwrap();
    let bytes = chunk(&source, synced_at, end);
    let base_bytes = committed_bytes(&base);

    let (mut rejected, mut accepted) = (0, 0);
    for bit in 0..bytes.len() * 8 {
        let mut flipped = bytes.clone();
        flipped[bit / 8] ^= 1 << (bit % 8);
        let replica = Database::new(CoreMemory::from_bytes(base_bytes.clone()), Hasher::sha1()).unwrap();
        let in_trailer = bit / 8 >= bytes.len() - ROOT_TRAILER_LENGTH;
        match replica.apply_replicated(synced_at, &mut flipped.as_slice(), flipped.len() as i64) {
            Err(_) => {
                rejected += 1;
                assert_eq!(replica.committed_size().unwrap(), synced_at);
            }
            Ok(()) => {
                accepted += 1;
                assert!(!in_trailer, "a flipped trailer bit {bit} was accepted");
                // whatever the flip did, reading and compacting must not panic
                let mut budget = 1_000_000;
                let _ = dump(&replica.root_cursor().read_cursor(), 0, &mut budget);
                let _ = replica.compact(CoreMemory::new(), &mut MemoryOffsetMap::new());
                // the replica believes it is in sync, so it is never repaired
                assert_eq!(source.replication_start(replica.replica_state().unwrap()).unwrap(), end);
            }
        }
    }
    assert_eq!(rejected + accepted, bytes.len() * 8);
    eprintln!("flipped bits: {rejected} rejected, {accepted} silently accepted");
}

/// Two copies of one file (same file ID) diverge with transactions of
/// exactly the same size, so their trailers sit at the same positions. Only
/// the random commit IDs tell the histories apart.
#[test]
fn glued_histories_force_a_full_copy() {
    let a = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    random_history(&a, 8, 4).unwrap();
    let b = Database::new(CoreMemory::from_bytes(committed_bytes(&a)), Hasher::sha1()).unwrap();
    assert_eq!(a.header().file_id, b.header().file_id);

    let replica = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    assert_eq!(sync(&a, &replica), 0, "a new replica gets a full copy");
    let fork_point = a.committed_size().unwrap();

    commit_word(&a, "alpha");
    commit_word(&b, "bravo");
    assert_eq!(a.committed_size().unwrap(), b.committed_size().unwrap());
    sync(&a, &replica);
    assert_same_db(&a, &replica);

    // the replica of a asks b for an update: b must not extend it
    assert_eq!(b.replication_start(replica.replica_state().unwrap()).unwrap(), 0);
    // even after b grows past it, with trailers at the same positions
    commit_word(&a, "charlie");
    commit_word(&b, "delta");
    commit_word(&b, "echoo");
    assert_eq!(b.replication_start(replica.replica_state().unwrap()).unwrap(), 0);
    // while a fresh replica of the common prefix can still be extended
    let old = Database::new(CoreMemory::from_bytes(chunk(&b, 0, fork_point)), Hasher::sha1()).unwrap();
    assert_eq!(b.replication_start(old.replica_state().unwrap()).unwrap(), fork_point);

    assert_eq!(sync(&b, &replica), 0);
    assert_same_db(&b, &replica);
}

/// The other side of the previous test: `replication_start` is the only
/// check. A source that skips it and sends another history's bytes from
/// the same position produces a replica that mixes both histories, and
/// that replica then looks up to date to the honest source.
///
/// This test documents that behaviour; it is not a guarantee.
#[test]
fn a_dishonest_splice_is_not_detected() {
    let a = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    random_history(&a, 9, 2).unwrap();
    let b = Database::new(CoreMemory::from_bytes(committed_bytes(&a)), Hasher::sha1()).unwrap();
    commit_word(&a, "alpha");
    commit_word(&b, "bravo");
    let replica = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    sync(&a, &replica);

    // b's next commit, sent from the position both histories share
    let from = b.committed_size().unwrap();
    commit_word(&b, "delta");
    let tail = chunk(&b, from, b.committed_size().unwrap());
    assert_eq!(from, replica.committed_size().unwrap());
    let accepted = replica.apply_replicated(from, &mut tail.as_slice(), tail.len() as i64).is_ok();

    if accepted {
        // the replica's latest moment is b's, but its previous one is a's
        let history = ReadArrayList::new(replica.root_cursor()).unwrap();
        let word = |i: i64| {
            let moment = ReadHashMap::new(history.get_cursor(i).unwrap().unwrap()).unwrap();
            moment.get_cursor("word").unwrap().unwrap().read_bytes(None).unwrap()
        };
        assert_eq!(word(-1), b"delta");
        assert_eq!(word(-2), b"alpha");
        // b and the replica now disagree on every byte of the moment
        // before it, but the replica reports the same state as b
        assert_ne!(committed_bytes(&replica), committed_bytes(&b));
        assert_eq!(b.replication_start(replica.replica_state().unwrap()).unwrap(), b.committed_size().unwrap());
        eprintln!("a spliced replica was accepted, and looks in sync with b");
    }
}

// fuzzing the reader

/// Everything a reader might do with an untrusted file. Errors are fine;
/// panics, hangs and huge allocations are not.
/// Returns how far it got: 0 if the file didn't open, 1 if it opened but
/// couldn't be read in full, and 2 if it could.
fn exercise(bytes: Vec<u8>) -> usize {
    let Ok(db) = Database::new(CoreMemory::from_bytes(bytes), Hasher::sha1()) else {
        return 0;
    };
    let mut budget = 20_000;
    let reached = if dump(&db.root_cursor().read_cursor(), 0, &mut budget).is_ok() { 2 } else { 1 };
    if let Ok(history) = ReadArrayList::new(db.root_cursor()) {
        for i in [0, 1, -1, -2] {
            if let Ok(Some(moment)) = history.get_cursor(i)
                && let Ok(map) = ReadHashMap::new(moment)
            {
                for key in ["map", "list", "sorted", "word", "big"] {
                    if let Ok(Some(value)) = map.get_cursor(key)
                        && let Ok(mut reader) = value.reader()
                    {
                        let _ = reader.seek_to(reader.size() / 2);
                        let mut buf = [0u8; 64];
                        let _ = reader.read_fully(&mut buf);
                    }
                }
            }
        }
    }
    let _ = db.replica_state();
    if let Ok(compacted) = db.compact(CoreMemory::new(), &mut MemoryOffsetMap::new()) {
        let mut budget = 20_000;
        let _ = dump(&compacted.root_cursor().read_cursor(), 0, &mut budget);
    }
    // the corrupt file as a replication source
    let replica = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    if let (Ok(start), Ok(end)) = (db.replication_start(replica.replica_state().unwrap()), db.committed_size()) {
        let mut buf = Vec::new();
        if db.read_committed(start, end, &mut buf).is_ok() {
            let _ = replica.apply_replicated(start, &mut buf.as_slice(), buf.len() as i64);
        }
    }
    reached
}

fn mutate(rng: &mut Rng, seed: &[u8]) -> Vec<u8> {
    let mut bytes = seed.to_vec();
    for _ in 0..1 + rng.below(4) {
        let len = bytes.len().max(1);
        let at = rng.below(len as u64) as usize;
        match rng.below(8) {
            0 => {
                if let Some(b) = bytes.get_mut(at) {
                    *b ^= 1 << rng.below(8);
                }
            }
            1 => {
                if let Some(b) = bytes.get_mut(at) {
                    *b = [0, 1, 0x7f, 0x80, 0xff, rng.below(17) as u8][rng.below(6) as usize];
                }
            }
            2 => {
                // an 8 byte value: a pointer somewhere in the file (maybe
                // backwards, making a cycle), a huge length or a negative one
                let value: i64 = match rng.below(4) {
                    0 => rng.below(len as u64) as i64,
                    1 => i64::MAX - rng.below(100) as i64,
                    2 => -(rng.below(100) as i64) - 1,
                    _ => 1 << rng.below(63),
                };
                for (i, b) in value.to_be_bytes().into_iter().enumerate() {
                    if let Some(slot) = bytes.get_mut(at + i) {
                        *slot = b;
                    }
                }
            }
            3 => bytes.truncate(at),
            4 => bytes.extend(rng.some_bytes(0, 64)),
            5 => {
                // copy a run of the file over another place in it
                let from = rng.below(len as u64) as usize;
                let n = (rng.below(64) as usize).min(len - from).min(bytes.len().saturating_sub(at));
                let run = bytes[from..from + n].to_vec();
                bytes[at..at + n].copy_from_slice(&run);
            }
            6 => {
                if at < bytes.len() {
                    bytes.remove(at);
                }
            }
            _ => bytes.insert(at.min(bytes.len()), rng.next() as u8),
        }
    }
    bytes
}

/// Rewrites the last trailer's checksum and the root header to match the
/// file, the way a writer that didn't notice the corruption would, so the
/// corruption gets past `Database::new` and reaches the data structures.
fn reseal(bytes: &mut [u8]) {
    let len = bytes.len();
    if len < ROOT_HEADER_END as usize + ROOT_TRAILER_LENGTH {
        return;
    }
    let trailer = len - ROOT_TRAILER_LENGTH;
    let Ok(root) = Slot::from_bytes(&bytes[trailer..trailer + SLOT_LENGTH]) else {
        return;
    };
    let file_id = u64::from_be_bytes(bytes[12..HEADER_LENGTH].try_into().unwrap());
    let commit_id = u64::from_be_bytes(bytes[trailer + SLOT_LENGTH..trailer + SLOT_LENGTH + 8].try_into().unwrap());
    let checksum = root_trailer_checksum(file_id, trailer as i64, root, commit_id);
    bytes[len - 8..].copy_from_slice(&checksum.to_be_bytes());
    let root_header = HEADER_LENGTH..ROOT_HEADER_END as usize;
    bytes[root_header.start..root_header.start + SLOT_LENGTH].copy_from_slice(&root.to_bytes());
    bytes[root_header.start + SLOT_LENGTH..root_header.end].copy_from_slice(&(len as i64).to_be_bytes());
}

/// Corpus: the Go implementation's database, random histories of every
/// type (and their compactions), and a history with a large value.
fn fuzz_corpus() -> Vec<Vec<u8>> {
    let mut corpus = vec![std::fs::read("tests/testdata/test.db").unwrap()];
    for seed in 0..4 {
        let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
        random_history(&db, 1000 + seed, 3 + seed as usize * 3).unwrap();
        corpus.push(committed_bytes(&compact(&db)));
        corpus.push(committed_bytes(&db));
    }
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    WriteArrayList::new(&mut db.root_cursor()).unwrap().append_context(Data::None, |cursor| {
        let mut map = WriteHashMap::new(cursor)?;
        map.put("big", vec![3u8; 70_000])?;
        map.put("word", "hello")
    }).unwrap();
    corpus.push(committed_bytes(&db));
    corpus
}

#[test]
fn fuzz_the_reader() {
    let iterations: u64 = std::env::var("XITDB_FUZZ_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(3000);
    let corpus = Arc::new(fuzz_corpus());

    // the current case's number (plus one, 0 meaning between cases), so a
    // watchdog can name a case that hangs
    let current = Arc::new(AtomicU64::new(0));
    let worker = {
        let (corpus, current) = (corpus.clone(), current.clone());
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn(move || {
                let (mut failures, mut reached) = (Vec::new(), [0u64; 3]);
                for case in 0..iterations {
                    let mut rng = Rng(case);
                    let seed = &corpus[rng.below(corpus.len() as u64) as usize];
                    let mut bytes = mutate(&mut rng, seed);
                    if !rng.chance(4) {
                        reseal(&mut bytes);
                    }
                    current.store(case + 1, Ordering::SeqCst);
                    match catch_unwind(AssertUnwindSafe(|| exercise(bytes))) {
                        Ok(r) => reached[r] += 1,
                        Err(_) => failures.push(case),
                    }
                    current.store(0, Ordering::SeqCst);
                }
                (failures, reached)
            })
            .unwrap()
    };

    let (mut last_case, mut since) = (0, Instant::now());
    while !worker.is_finished() {
        std::thread::sleep(Duration::from_millis(50));
        let case = current.load(Ordering::SeqCst);
        if case != last_case {
            (last_case, since) = (case, Instant::now());
        } else if case != 0 && since.elapsed() > Duration::from_secs(20) {
            panic!("fuzz case {} hung (replay with Rng({}))", case - 1, case - 1);
        }
    }
    let (failures, [unopened, partial, full]) = worker.join().unwrap();
    eprintln!("fuzz: {unopened} didn't open, {partial} opened with errors, {full} read in full");
    assert!(failures.is_empty(), "fuzz cases panicked: {failures:?}");
    // most mutations must get past the header, or this tests nothing
    assert!(partial + full > iterations / 2);
}
