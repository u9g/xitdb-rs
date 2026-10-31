//! Runs the hash map against deliberately terrible hash functions.
//!
//! With SHA-1, two keys practically never share more than a few trie
//! levels, so the collision and deep-trie paths of the hash map are almost
//! never exercised. These hashers force them: constant hashes, hashes that
//! only differ in their most significant nibble (the last one the trie
//! looks at), tiny and odd-sized hashes, and hashers that lie.
//!
//! xitdb treats equal hashes as equal keys, so the oracle is a map keyed
//! by hash: putting a key whose hash is already present overwrites that
//! entry's value but keeps its original key.

use std::cell::Cell;
use std::collections::{BTreeMap, HashMap};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use sha1::Digest;
use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

fn sha1(data: &[u8]) -> Vec<u8> {
    sha1::Sha1::digest(data).to_vec()
}

/// hash -> (stored key, value)
type Model = BTreeMap<Vec<u8>, (Vec<u8>, u64)>;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// The terrible hashers, each with a name for failure messages.
type HashFn = fn(&[u8]) -> Vec<u8>;

fn terrible_hashers() -> Vec<(&'static str, HashFn)> {
    vec![
        // control
        ("sha1", sha1),
        // every key is the same key
        ("constant", |_| vec![0x42; 20]),
        // a zero-length hash: every key is the same key, and the trie has no levels
        ("empty", |_| Vec::new()),
        // 256 possible hashes, so lots of keys alias, and the trie is two levels deep
        ("one byte", |data| sha1(data)[..1].to_vec()),
        // an odd number of bytes
        ("three bytes", |data| sha1(data)[..3].to_vec()),
        // only the most significant nibble varies, so every pair of keys
        // shares 39 levels of the trie before splitting at the very last one
        ("top nibble only", |data| {
            let mut hash = vec![0u8; 20];
            hash[0] = sha1(data)[0] & 0xf0;
            hash
        }),
        // only the two most significant bytes vary: 65536 hashes, all of
        // them deep, and branching only in the last four levels
        ("top two bytes", |data| {
            let mut hash = vec![0u8; 20];
            hash[..2].copy_from_slice(&sha1(data)[..2]);
            hash
        }),
        // the least significant nibble (the first one the trie looks at) is
        // constant, and the rest is a real hash
        ("stuck low nibble", |data| {
            let mut hash = sha1(data);
            hash[19] &= 0xf0;
            hash
        }),
        // a 64-byte hash, like SHA-512, but mostly zero
        ("wide and deep", |data| {
            let mut hash = vec![0u8; 64];
            hash[0] = sha1(data)[0];
            hash
        }),
    ]
}

fn key(i: u64) -> Vec<u8> {
    // a mix of short (inline) and long keys
    if i % 3 == 0 { format!("key-{i}-{}", "x".repeat(40)).into_bytes() } else { format!("k{i}").into_bytes() }
}

fn model_put(model: &mut Model, hash: Vec<u8>, key: Vec<u8>, value: u64) {
    model.entry(hash).or_insert((key, 0)).1 = value;
}

/// Checks a map against the model through every read path: count,
/// lookups of every key in the pool, by-hash lookups, and iteration.
fn check_map<C: Core>(name: &str, map: &ReadCountedHashMap<'_, C>, model: &Model, hash: HashFn, pool: u64) {
    assert_eq!(map.count().unwrap(), model.len() as i64, "{name}: count");

    for i in 0..pool {
        let k = key(i);
        let h = hash(&k);
        let got = map.get_cursor(&k).unwrap().map(|c| c.read_uint().unwrap());
        assert_eq!(got, model.get(&h).map(|(_, v)| *v), "{name}: value of {}", String::from_utf8_lossy(&k));
        let got_key = map.get_key_cursor(&k).unwrap().map(|c| c.read_bytes(MAX_READ).unwrap());
        assert_eq!(got_key.as_ref(), model.get(&h).map(|(k, _)| k), "{name}: stored key for {}", String::from_utf8_lossy(&k));
    }

    let mut seen = Model::new();
    for kv in map.iter().unwrap() {
        let kv = kv.unwrap().read_key_value_pair().unwrap();
        let k = kv.key_cursor.read_bytes(MAX_READ).unwrap();
        let v = kv.value_cursor.read_uint().unwrap();
        assert_eq!(kv.hash, hash(&k), "{name}: stored hash doesn't match stored key");
        assert!(seen.insert(kv.hash.clone(), (k, v)).is_none(), "{name}: iteration yielded a hash twice");
        let by_hash = map.get_cursor_by_hash(&kv.hash).unwrap().unwrap().read_uint().unwrap();
        assert_eq!(by_hash, v, "{name}: by-hash lookup disagrees with iteration");
    }
    assert_eq!(&seen, model, "{name}: iteration");
}

/// Random puts and removes in many transactions, with the model of every
/// moment kept on the side. At the end, every past moment must still match
/// its model, after reopening the bytes and after compaction.
fn run_oracle(name: &str, hash: HashFn, seed: u64) {
    const POOL: u64 = 300;
    const TRANSACTIONS: usize = 60;

    let mut rng = Rng(seed);
    let db = Database::new(CoreMemory::new(), Hasher::new(hash)).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();

    let mut model = Model::new();
    let mut moments: Vec<Model> = Vec::new();

    for _ in 0..TRANSACTIONS {
        let ops = 1 + rng.below(40);
        let last = history.get_slot(-1).unwrap();
        history
            .append_context(last, |cursor| {
                let mut map = WriteCountedHashMap::new(cursor)?;
                for _ in 0..ops {
                    let k = key(rng.below(POOL));
                    let h = hash(&k);
                    match rng.below(10) {
                        // remove, slightly less often than put so the map grows
                        0..=3 => {
                            let removed = map.remove(&k)?;
                            assert_eq!(removed, model.remove(&h).is_some(), "{name}: remove result");
                        }
                        // put through put_cursor instead of put
                        4 => {
                            let v = rng.next() >> 1;
                            map.put_cursor(&k)?.write(v)?;
                            model_put(&mut model, h, k, v);
                        }
                        _ => {
                            let v = rng.next() >> 1;
                            map.put(&k, v)?;
                            model_put(&mut model, h, k, v);
                        }
                    }
                    assert_eq!(map.count()?, model.len() as i64, "{name}: count during transaction");
                }
                Ok(())
            })
            .unwrap();
        moments.push(model.clone());

        let map = ReadCountedHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
        check_map(name, &map, &model, hash, POOL);
    }

    // every past moment, in a scrambled order, so copy-on-write bugs where a
    // later transaction changed a shared deep index block show up
    let mut order: Vec<usize> = (0..moments.len()).collect();
    for i in (1..order.len()).rev() {
        order.swap(i, rng.below(i as u64 + 1) as usize);
    }
    for &i in &order {
        let map = ReadCountedHashMap::new(history.get_cursor(i as i64).unwrap().unwrap()).unwrap();
        check_map(&format!("{name} (moment {i})"), &map, &moments[i], hash, POOL);
    }

    // reopen the raw bytes
    let bytes = db.into_core().into_bytes();
    let db = Database::new(CoreMemory::from_bytes(bytes), Hasher::new(hash)).unwrap();
    let history = ReadArrayList::new(db.root_cursor()).unwrap();
    for (i, model) in moments.iter().enumerate() {
        let map = ReadCountedHashMap::new(history.get_cursor(i as i64).unwrap().unwrap()).unwrap();
        check_map(&format!("{name} (reopened, moment {i})"), &map, model, hash, POOL);
    }

    // compaction keeps only the last moment
    let compacted = db.compact(CoreMemory::new(), &mut HashMap::<i64, i64>::new()).unwrap();
    let history = ReadArrayList::new(compacted.root_cursor()).unwrap();
    let map = ReadCountedHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
    check_map(&format!("{name} (compacted)"), &map, moments.last().unwrap(), hash, POOL);
}

#[test]
fn oracle_with_terrible_hashers() {
    for (name, hash) in terrible_hashers() {
        for seed in [1, 0xdead_beef] {
            run_oracle(name, hash, seed);
        }
    }
}

/// Insert every key, remove them all in a random order, and check the
/// trie collapses back to an empty map that accepts new keys. With the
/// deep hashers, every removal goes through the code that collapses
/// single-child index blocks.
#[test]
fn fill_and_drain() {
    for (name, hash) in terrible_hashers() {
        let mut rng = Rng(7);
        let db = Database::new(CoreMemory::new(), Hasher::new(hash)).unwrap();
        let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
        let mut model = Model::new();

        let mut keys: Vec<u64> = (0..200).collect();
        history
            .append_context(None, |cursor| {
                let mut map = WriteCountedHashMap::new(cursor)?;
                for &i in &keys {
                    map.put(key(i), i)?;
                    model_put(&mut model, hash(&key(i)), key(i), i);
                }
                Ok(())
            })
            .unwrap();

        for i in (1..keys.len()).rev() {
            keys.swap(i, rng.below(i as u64 + 1) as usize);
        }
        // drain in chunks, one transaction each
        for chunk in keys.chunks(23) {
            let last = history.get_slot(-1).unwrap();
            history
                .append_context(last, |cursor| {
                    let mut map = WriteCountedHashMap::new(cursor)?;
                    for &i in chunk {
                        let removed = map.remove(key(i))?;
                        assert_eq!(removed, model.remove(&hash(&key(i))).is_some(), "{name}: remove {i}");
                    }
                    Ok(())
                })
                .unwrap();
            let map = ReadCountedHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
            check_map(name, &map, &model, hash, 200);
        }
        assert!(model.is_empty());

        // the first moment is untouched by all the draining
        let mut full = Model::new();
        for i in 0..200 {
            model_put(&mut full, hash(&key(i)), key(i), i);
        }
        let map = ReadCountedHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();
        check_map(&format!("{name} (first moment)"), &map, &full, hash, 200);

        // and the drained map still works
        let last = history.get_slot(-1).unwrap();
        history
            .append_context(last, |cursor| {
                let mut map = WriteCountedHashMap::new(cursor)?;
                map.put("again", 1u64)?;
                Ok(())
            })
            .unwrap();
        model_put(&mut model, hash(b"again"), b"again".to_vec(), 1);
        let map = ReadCountedHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
        check_map(name, &map, &model, hash, 0);
    }
}

/// With a constant hash, a map can only ever hold one entry: the first key
/// sticks, and every put overwrites its value.
#[test]
fn constant_hash_aliases_every_key() {
    let db = Database::new(CoreMemory::new(), Hasher::new(|_| vec![0; 20])).unwrap();
    let mut map = WriteCountedHashMap::new(&mut db.root_cursor()).unwrap();
    map.put("apple", 1u64).unwrap();
    map.put("banana", 2u64).unwrap();
    assert_eq!(map.count().unwrap(), 1);
    assert_eq!(map.get_cursor("apple").unwrap().unwrap().read_uint().unwrap(), 2);
    assert_eq!(map.get_cursor("cherry").unwrap().unwrap().read_uint().unwrap(), 2);
    assert_eq!(map.get_key_cursor("banana").unwrap().unwrap().read_bytes(MAX_READ).unwrap(), b"apple");
    assert!(map.remove("durian").unwrap());
    assert_eq!(map.count().unwrap(), 0);
    assert!(map.get_cursor("apple").unwrap().is_none());
    assert!(!map.remove("apple").unwrap());

    // a set behaves the same way
    let db = Database::new(CoreMemory::new(), Hasher::new(|_| vec![0; 20])).unwrap();
    let mut set = WriteCountedHashSet::new(&mut db.root_cursor()).unwrap();
    set.put("apple").unwrap();
    set.put("banana").unwrap();
    assert_eq!(set.count().unwrap(), 1);
    assert!(set.contains("anything at all").unwrap());
}

/// Hashes up to 65535 bytes long can be stored in the header. The trie
/// depth used to be a u8, which can only address 256 nibbles (128 bytes),
/// so two keys whose hashes only differed past the first 128 bytes
/// overflowed it (a panic in debug builds, a wrapped offset in release).
///
/// The trie is walked recursively, one stack frame per level, so this
/// stops at 300 bytes (600 levels) to stay within a debug-build test
/// thread's stack.
#[test]
fn hash_longer_than_128_bytes() {
    for size in [127, 128, 129, 200, 300] {
        let db = Database::new(CoreMemory::new(), Hasher::new(move |data: &[u8]| {
            // keys only differ in the most significant byte, the last one the trie looks at
            let mut hash = vec![0u8; size];
            hash[0] = data.first().copied().unwrap_or(0);
            hash
        }))
        .unwrap();
        let mut map = WriteCountedHashMap::new(&mut db.root_cursor()).unwrap();
        for (i, k) in ["a", "b", "c"].into_iter().enumerate() {
            map.put(k, i as u64).unwrap();
        }
        assert!(map.remove("b").unwrap(), "hash size {size}");
        assert_eq!(map.count().unwrap(), 2, "hash size {size}");
        for (k, v) in [("a", Some(0)), ("b", None), ("c", Some(2))] {
            assert_eq!(map.get_cursor(k).unwrap().map(|c| c.read_uint().unwrap()), v, "hash size {size}: {k}");
        }
    }
}

/// A hasher whose output depends on how many times it has been called.
/// No answer is "right", but the database must not panic, and whatever it
/// wrote must stay a well-formed database: readable, iterable, compactable,
/// and openable with an honest hasher of the same size.
#[test]
fn lying_hasher_never_corrupts_the_file() {
    let calls = Arc::new(AtomicU64::new(0));
    let liar = {
        let calls = calls.clone();
        Hasher::new(move |data| {
            let n = calls.fetch_add(1, Ordering::Relaxed);
            let mut input = data.to_vec();
            // sometimes honest, sometimes not, and sometimes very shallow
            match n % 5 {
                0 | 1 => sha1(data),
                2 => {
                    input.extend_from_slice(&n.to_le_bytes());
                    sha1(&input)
                }
                3 => vec![(n % 3) as u8; 20],
                _ => {
                    let mut hash = vec![0u8; 20];
                    hash[0] = (n as u8) & 0xf0;
                    hash
                }
            }
        })
    };

    let db = Database::new(CoreMemory::new(), liar).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    let mut rng = Rng(99);
    for _ in 0..50 {
        let last = history.get_slot(-1).unwrap();
        history
            .append_context(last, |cursor| {
                let mut map = WriteCountedHashMap::new(cursor)?;
                for _ in 0..20 {
                    let k = key(rng.below(50));
                    if rng.below(3) == 0 {
                        map.remove(&k)?;
                    } else {
                        map.put(&k, rng.next() >> 1)?;
                    }
                    let _ = map.get_cursor(&k)?;
                }
                Ok(())
            })
            .unwrap();
    }
    assert!(calls.load(Ordering::Relaxed) > 1000);

    let check = |history: &ReadArrayList<'_, CoreMemory>| {
        for moment in history.iter().unwrap() {
            let map = ReadCountedHashMap::new(moment.unwrap()).unwrap();
            let mut n = 0;
            for kv in map.iter().unwrap() {
                let kv = kv.unwrap().read_key_value_pair().unwrap();
                kv.key_cursor.read_bytes(MAX_READ).unwrap();
                kv.value_cursor.read_uint().unwrap();
                // whatever hash it was stored under, it can be found by it
                assert!(map.get_cursor_by_hash(&kv.hash).unwrap().is_some());
                n += 1;
            }
            assert_eq!(n, map.count().unwrap(), "count disagrees with iteration");
        }
    };

    let bytes = db.into_core().into_bytes();
    let honest = Database::new(CoreMemory::from_bytes(bytes), Hasher::sha1()).unwrap();
    check(&ReadArrayList::new(honest.root_cursor()).unwrap());
    let compacted = honest.compact(CoreMemory::new(), &mut HashMap::<i64, i64>::new()).unwrap();
    check(&ReadArrayList::new(compacted.root_cursor()).unwrap());
}

/// A hasher that returns hashes of the wrong length is caught, and the
/// transaction it was used in is discarded.
#[test]
fn wrong_length_hash_is_an_error() {
    let long = Arc::new(AtomicU64::new(0));
    let hasher = {
        let long = long.clone();
        Hasher::new(move |data| {
            let mut hash = sha1(data);
            if long.load(Ordering::Relaxed) == 1 {
                hash.push(0);
            }
            hash
        })
    };
    let db = Database::new(CoreMemory::new(), hasher).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    history
        .append_context(None, |cursor| {
            let mut map = WriteHashMap::new(cursor)?;
            map.put("apple", 1u64)
        })
        .unwrap();

    long.store(1, Ordering::Relaxed);
    let last = history.get_slot(-1).unwrap();
    let err = history
        .append_context(last, |cursor| {
            let mut map = WriteHashMap::new(cursor)?;
            map.put("banana", 2u64)
        })
        .unwrap_err();
    assert!(matches!(err, Error::InvalidHashSize), "{err:?}");
    assert!(matches!(history.get_cursor(-1).unwrap().map(ReadHashMap::new).unwrap().unwrap().get_cursor("apple"), Err(Error::InvalidHashSize)));

    long.store(0, Ordering::Relaxed);
    assert_eq!(history.count().unwrap(), 1, "the failed transaction was discarded");
    let map = ReadHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
    assert_eq!(map.get_cursor("apple").unwrap().unwrap().read_uint().unwrap(), 1);
    assert!(map.get_cursor("banana").unwrap().is_none());
}

/// A hasher that panics in the middle of a transaction. The panic unwinds
/// out of the database; afterwards, the bytes must still be the database
/// as of the last committed transaction.
#[test]
fn panicking_hasher_leaves_last_commit_intact() {
    thread_local! {
        static BOMB: Cell<u64> = const { Cell::new(u64::MAX) };
    }
    let hasher = Hasher::new(|data| {
        BOMB.with(|bomb| {
            let left = bomb.get();
            if left == 0 {
                panic!("boom");
            }
            bomb.set(left.saturating_sub(1));
        });
        sha1(data)
    });

    let db = Database::new(CoreMemory::new(), hasher).unwrap();
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
        history
            .append_context(None, |cursor| {
                let mut map = WriteCountedHashMap::new(cursor)?;
                for i in 0..100 {
                    map.put(key(i), i)?;
                }
                Ok(())
            })
            .unwrap();
    }

    BOMB.with(|bomb| bomb.set(37));
    let result = catch_unwind(AssertUnwindSafe(|| {
        let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
        let last = history.get_slot(-1).unwrap();
        history.append_context(last, |cursor| {
            let mut map = WriteCountedHashMap::new(cursor)?;
            for i in 0..100 {
                map.remove(key(i))?;
            }
            Ok(())
        })
    }));
    assert!(result.is_err(), "the hasher should have panicked");
    BOMB.with(|bomb| bomb.set(u64::MAX));

    // reopen from the bytes, as a new process would after a crash
    let bytes = db.into_core().into_bytes();
    let db = Database::new(CoreMemory::from_bytes(bytes), Hasher::sha1()).unwrap();
    let history = ReadArrayList::new(db.root_cursor()).unwrap();
    assert_eq!(history.count().unwrap(), 1);
    let map = ReadCountedHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
    let mut model = Model::new();
    for i in 0..100 {
        model_put(&mut model, sha1(&key(i)), key(i), i);
    }
    check_map("after panic", &map, &model, sha1, 100);
}
