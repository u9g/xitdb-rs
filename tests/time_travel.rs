//! The "time-travel oracle" test. Every moment in a history stays readable,
//! so a history can check itself: run thousands of random transactions
//! against both the database and a plain in-memory model, keep the model's
//! state after each one, and at the end read every past moment back and
//! compare it with the state the model had at that point.
//!
//! This catches copy-on-write bugs, where a later write changes data that
//! an earlier moment shares. To give those bugs chances to happen, the
//! transactions clone collections into each other (with and without
//! freezing, following the rules in the README), revert to old moments and
//! keep writing on top of them, and abort partway through.
//!
//! Set `XITDB_ORACLE_SEED` to replay a failure, and `XITDB_ORACLE_TXNS` to
//! run more transactions than the default.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::OpenOptions;
use std::io::{self, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

use xitdb::*;

const DEFAULT_SEED: u64 = 0x7134_7e1d_0dd1_7135;
const DEFAULT_TXNS: usize = 1500;
const ABORT_MESSAGE: &str = "aborted on purpose";

// splitmix64, so the test needs no dependencies and a seed replays exactly
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            items.swap(i, self.below(i + 1));
        }
    }
}

fn env_or<T: std::str::FromStr>(name: &str, default: T) -> T {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

// the model

/// The kind of a collection in the moment, which decides what the
/// transactions do to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    HashMap,
    CountedHashMap,
    SortedMap,
    HashSet,
    CountedHashSet,
    SortedSet,
    ArrayList,
    LinkedArrayList,
    /// a hash map of hash maps
    Nested,
    /// a large byte array written incrementally
    Blob,
}

/// Each moment is a hash map from these names to collections. Collections
/// of the same kind can be cloned into each other.
const COLLECTIONS: &[(&str, Kind)] = &[
    ("kv", Kind::HashMap),
    ("kv-copy", Kind::HashMap),
    ("counted", Kind::CountedHashMap),
    ("sorted", Kind::SortedMap),
    ("sorted-copy", Kind::SortedMap),
    ("set", Kind::HashSet),
    ("counted-set", Kind::CountedHashSet),
    ("sorted-set", Kind::SortedSet),
    ("list", Kind::ArrayList),
    ("list-copy", Kind::ArrayList),
    ("linked", Kind::LinkedArrayList),
    ("linked-copy", Kind::LinkedArrayList),
    ("nested", Kind::Nested),
    ("nested-copy", Kind::Nested),
    ("blob", Kind::Blob),
];

fn kind_of(name: &str) -> Kind {
    COLLECTIONS.iter().find(|(n, _)| *n == name).map(|(_, k)| *k).unwrap()
}

/// A value as the model sees it. Reading a moment from the database
/// produces the same type, so the two can be compared directly.
#[derive(Debug, Clone, PartialEq)]
enum V {
    Bytes(Vec<u8>, Option<[u8; 2]>),
    Uint(u64),
    Int(i64),
    /// the bits, so that comparing is exact
    Float(u64),
    Map(Tag, BTreeMap<Vec<u8>, V>),
    Set(Tag, BTreeSet<Vec<u8>>),
    List(Tag, Vec<V>),
}

fn empty(kind: Kind) -> V {
    match kind {
        Kind::HashMap | Kind::Nested => V::Map(Tag::HashMap, BTreeMap::new()),
        Kind::CountedHashMap => V::Map(Tag::CountedHashMap, BTreeMap::new()),
        Kind::SortedMap => V::Map(Tag::SortedMap, BTreeMap::new()),
        Kind::HashSet => V::Set(Tag::HashSet, BTreeSet::new()),
        Kind::CountedHashSet => V::Set(Tag::CountedHashSet, BTreeSet::new()),
        Kind::SortedSet => V::Set(Tag::SortedSet, BTreeSet::new()),
        Kind::ArrayList => V::List(Tag::ArrayList, Vec::new()),
        Kind::LinkedArrayList => V::List(Tag::LinkedArrayList, Vec::new()),
        Kind::Blob => V::Bytes(Vec::new(), None),
    }
}

fn to_data(v: &V) -> Data<'_> {
    match v {
        V::Bytes(bytes, None) => Data::bytes(&bytes[..]),
        V::Bytes(bytes, Some(tag)) => Data::tagged_bytes(&bytes[..], *tag),
        V::Uint(n) => Data::Uint(*n),
        V::Int(n) => Data::Int(*n),
        V::Float(bits) => Data::Float(f64::from_bits(*bits)),
        _ => unreachable!("only scalars are written directly"),
    }
}

/// One change to one collection.
#[derive(Debug, Clone)]
enum Action {
    /// maps
    Put(Vec<u8>, V),
    /// maps and sets
    Remove(Vec<u8>),
    /// sets
    Insert(Vec<u8>),
    /// lists
    Append(V),
    /// lists: replace an item
    Set(i64, V),
    /// array lists: keep only the first n items
    Slice(i64),
    /// linked array lists
    InsertAt(i64, V),
    RemoveAt(i64),
    /// nested maps: put a value in an inner map, creating it if needed
    NestedPut(Vec<u8>, Vec<u8>, V),
    /// nested maps: remove an inner map
    NestedRemove(Vec<u8>),
    /// blobs: replace the contents
    Blob(Vec<u8>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Freeze {
    /// only valid when the source wasn't written earlier in the transaction
    None,
    /// `WriteCursor::freeze` on the clone's cursor
    Cursor,
    /// `Database::freeze` before the clone's cursor is made
    Database,
}

#[derive(Debug, Clone)]
enum Op {
    Edit(&'static str, Action),
    Drop(&'static str),
    /// clone `src` into `dst`, then apply `edits` through the clone's cursor
    Clone { src: &'static str, dst: &'static str, freeze: Freeze, edits: Vec<Action> },
}

#[derive(Debug, Clone)]
enum Txn {
    Commit(Vec<Op>),
    /// runs the ops, then fails, so the database must be unchanged
    Abort(Vec<Op>),
    /// appends an earlier moment again
    Revert(usize),
}

fn apply_action_to_model(v: &mut V, action: &Action) {
    match (v, action) {
        (V::Map(_, m), Action::Put(k, val)) => {
            m.insert(k.clone(), val.clone());
        }
        (V::Map(_, m), Action::Remove(k)) => {
            m.remove(k);
        }
        (V::Set(_, s), Action::Remove(k)) => {
            s.remove(k);
        }
        (V::Set(_, s), Action::Insert(k)) => {
            s.insert(k.clone());
        }
        (V::List(_, l), Action::Append(val)) => l.push(val.clone()),
        (V::List(_, l), Action::Set(i, val)) => l[*i as usize] = val.clone(),
        (V::List(_, l), Action::Slice(n)) => l.truncate(*n as usize),
        (V::List(_, l), Action::InsertAt(i, val)) => l.insert(*i as usize, val.clone()),
        (V::List(_, l), Action::RemoveAt(i)) => {
            l.remove(*i as usize);
        }
        (V::Map(_, m), Action::NestedPut(outer, inner, val)) => {
            let inner_map = m.entry(outer.clone()).or_insert_with(|| empty(Kind::HashMap));
            apply_action_to_model(inner_map, &Action::Put(inner.clone(), val.clone()));
        }
        (V::Map(_, m), Action::NestedRemove(outer)) => {
            m.remove(outer);
        }
        (v @ V::Bytes(..), Action::Blob(bytes)) => *v = V::Bytes(bytes.clone(), None),
        (v, action) => panic!("{action:?} doesn't apply to {v:?}"),
    }
}

fn moment_entries(moment: &mut V) -> &mut BTreeMap<Vec<u8>, V> {
    match moment {
        V::Map(_, m) => m,
        _ => unreachable!(),
    }
}

fn apply_op_to_model(moment: &mut V, op: &Op) {
    let entries = moment_entries(moment);
    match op {
        Op::Edit(name, action) => {
            let coll = entries.entry(name.as_bytes().to_vec()).or_insert_with(|| empty(kind_of(name)));
            apply_action_to_model(coll, action);
        }
        Op::Drop(name) => {
            entries.remove(name.as_bytes());
        }
        Op::Clone { src, dst, edits, .. } => {
            let mut coll = entries[src.as_bytes()].clone();
            for action in edits {
                apply_action_to_model(&mut coll, action);
            }
            entries.insert(dst.as_bytes().to_vec(), coll);
        }
    }
}

// generating transactions

fn key(rng: &mut Rng) -> Vec<u8> {
    let n = rng.below(40);
    if n % 7 == 0 {
        // binary keys, including zero bytes, of varying length
        (0..(n % 13 + 1)).map(|i| (i * 37 + n) as u8 % 5).collect()
    } else {
        format!("k{n}").into_bytes()
    }
}

fn random_bytes(rng: &mut Rng, len: usize, allow_zero: bool) -> Vec<u8> {
    (0..len)
        .map(|_| {
            let b = rng.next() as u8;
            if allow_zero || b != 0 { b } else { b'z' }
        })
        .collect()
}

fn scalar(rng: &mut Rng) -> V {
    match rng.below(6) {
        0 => V::Uint(rng.next()),
        1 => V::Int(rng.next() as i64),
        2 => V::Float(((rng.next() as i64 as f64) / 1000.0).to_bits()),
        // fits in a slot
        3 => {
            let len = rng.below(9);
            V::Bytes(random_bytes(rng, len, false), None)
        }
        4 => {
            let len = rng.below(300);
            V::Bytes(random_bytes(rng, len, true), None)
        }
        _ => {
            let len = rng.below(20);
            let tag = [rng.next() as u8, rng.next() as u8];
            let allow_zero = rng.chance(50);
            V::Bytes(random_bytes(rng, len, allow_zero), Some(tag))
        }
    }
}

/// A random action that is valid for `coll`, a collection of `kind`.
fn action(rng: &mut Rng, kind: Kind, coll: Option<&V>) -> Action {
    let len = match coll {
        Some(V::List(_, l)) => l.len(),
        _ => 0,
    };
    match kind {
        Kind::HashMap | Kind::CountedHashMap | Kind::SortedMap => {
            if rng.chance(70) { Action::Put(key(rng), scalar(rng)) } else { Action::Remove(key(rng)) }
        }
        Kind::HashSet | Kind::CountedHashSet | Kind::SortedSet => {
            if rng.chance(70) { Action::Insert(key(rng)) } else { Action::Remove(key(rng)) }
        }
        Kind::ArrayList => match rng.below(10) {
            _ if len == 0 => Action::Append(scalar(rng)),
            0 => Action::Slice(rng.below(len + 1) as i64),
            1..=3 => Action::Set(rng.below(len) as i64, scalar(rng)),
            _ => Action::Append(scalar(rng)),
        },
        Kind::LinkedArrayList => match rng.below(10) {
            _ if len == 0 => Action::Append(scalar(rng)),
            0..=1 => Action::RemoveAt(rng.below(len) as i64),
            2..=3 => Action::InsertAt(rng.below(len) as i64, scalar(rng)),
            4..=5 => Action::Set(rng.below(len) as i64, scalar(rng)),
            _ => Action::Append(scalar(rng)),
        },
        Kind::Nested => {
            let outer = format!("outer{}", rng.below(10)).into_bytes();
            if rng.chance(85) {
                Action::NestedPut(outer, key(rng), scalar(rng))
            } else {
                Action::NestedRemove(outer)
            }
        }
        Kind::Blob => {
            // up to a few times the buffer sizes used by the cursor writer
            let len = if rng.chance(30) { rng.below(64) } else { rng.below(40_000) };
            Action::Blob(random_bytes(rng, len, true))
        }
    }
}

/// The ops for one transaction, applied to `moment` as they're made, so
/// list indexes stay valid.
fn ops(rng: &mut Rng, moment: &mut V) -> Vec<Op> {
    // collections written in this transaction. cloning one of them needs a
    // freeze, or writes to the clone would change the original too
    let mut touched = BTreeSet::new();
    // collections that share data made in this transaction through a
    // cursor-frozen clone. writing to either through a new cursor would
    // change the other, so they are left alone for the rest of the transaction
    let mut locked = BTreeSet::new();

    let mut ops = Vec::new();
    for _ in 0..rng.below(6) + 1 {
        let entries = moment_entries(moment);
        let (name, kind) = COLLECTIONS[rng.below(COLLECTIONS.len())];
        if locked.contains(name) {
            continue;
        }

        let op = if rng.chance(10) {
            // clone another collection of the same kind into this one
            let sources: Vec<&'static str> = COLLECTIONS
                .iter()
                .filter(|(n, k)| *k == kind && *n != name && !locked.contains(n) && entries.contains_key(n.as_bytes()))
                .map(|(n, _)| *n)
                .collect();
            if sources.is_empty() {
                continue;
            }
            let src = sources[rng.below(sources.len())];
            let freeze = match rng.below(3) {
                0 => Freeze::Database,
                1 => Freeze::Cursor,
                _ if touched.contains(src) => Freeze::Cursor,
                _ => Freeze::None,
            };
            let mut coll = entries[src.as_bytes()].clone();
            let mut edits = Vec::new();
            for _ in 0..rng.below(4) {
                let edit = action(rng, kind, Some(&coll));
                apply_action_to_model(&mut coll, &edit);
                edits.push(edit);
            }
            match freeze {
                Freeze::Database => {
                    // everything written so far is now immutable
                    touched.clear();
                    locked.clear();
                }
                Freeze::Cursor if touched.contains(src) => {
                    locked.insert(src);
                    locked.insert(name);
                }
                _ => {}
            }
            touched.insert(name);
            Op::Clone { src, dst: name, freeze, edits }
        } else if rng.chance(3) {
            Op::Drop(name)
        } else {
            touched.insert(name);
            Op::Edit(name, action(rng, kind, entries.get(name.as_bytes())))
        };
        apply_op_to_model(moment, &op);
        ops.push(op);
    }
    ops
}

/// Random transactions and the state of each moment they create.
fn generate(seed: u64, count: usize) -> (Vec<Txn>, Vec<V>) {
    let mut rng = Rng(seed);
    let mut txns = Vec::new();
    let mut moments: Vec<V> = Vec::new();
    for _ in 0..count {
        let last = moments.last().cloned().unwrap_or_else(|| empty(Kind::HashMap));
        if !moments.is_empty() && rng.chance(3) {
            let target = rng.below(moments.len());
            moments.push(moments[target].clone());
            txns.push(Txn::Revert(target));
        } else if !moments.is_empty() && rng.chance(4) {
            let mut scratch = last;
            txns.push(Txn::Abort(ops(&mut rng, &mut scratch)));
        } else {
            let mut next = last;
            txns.push(Txn::Commit(ops(&mut rng, &mut next)));
            moments.push(next);
        }
    }
    (txns, moments)
}

// applying transactions to a database

fn apply_action<'a, C: Core>(cursor: &mut WriteCursor<'a, C>, kind: Kind, action: &Action) -> Result<()> {
    match (kind, action) {
        (Kind::HashMap, Action::Put(k, v)) => WriteHashMap::new(cursor)?.put(k, to_data(v)),
        (Kind::HashMap, Action::Remove(k)) => WriteHashMap::new(cursor)?.remove(k).map(drop),
        (Kind::CountedHashMap, Action::Put(k, v)) => WriteCountedHashMap::new(cursor)?.put(k, to_data(v)),
        (Kind::CountedHashMap, Action::Remove(k)) => WriteCountedHashMap::new(cursor)?.remove(k).map(drop),
        (Kind::SortedMap, Action::Put(k, v)) => WriteSortedMap::new(cursor)?.put(k, to_data(v)),
        (Kind::SortedMap, Action::Remove(k)) => WriteSortedMap::new(cursor)?.remove(k).map(drop),
        (Kind::HashSet, Action::Insert(k)) => WriteHashSet::new(cursor)?.put(k),
        (Kind::HashSet, Action::Remove(k)) => WriteHashSet::new(cursor)?.remove(k).map(drop),
        (Kind::CountedHashSet, Action::Insert(k)) => WriteCountedHashSet::new(cursor)?.put(k),
        (Kind::CountedHashSet, Action::Remove(k)) => WriteCountedHashSet::new(cursor)?.remove(k).map(drop),
        (Kind::SortedSet, Action::Insert(k)) => WriteSortedSet::new(cursor)?.put(k),
        (Kind::SortedSet, Action::Remove(k)) => WriteSortedSet::new(cursor)?.remove(k).map(drop),
        (Kind::ArrayList, Action::Append(v)) => WriteArrayList::new(cursor)?.append(to_data(v)),
        (Kind::ArrayList, Action::Set(i, v)) => WriteArrayList::new(cursor)?.put(*i, to_data(v)),
        (Kind::ArrayList, Action::Slice(n)) => WriteArrayList::new(cursor)?.slice(*n),
        (Kind::LinkedArrayList, Action::Append(v)) => WriteLinkedArrayList::new(cursor)?.append(to_data(v)),
        (Kind::LinkedArrayList, Action::Set(i, v)) => WriteLinkedArrayList::new(cursor)?.put(*i, to_data(v)),
        (Kind::LinkedArrayList, Action::InsertAt(i, v)) => WriteLinkedArrayList::new(cursor)?.insert(*i, to_data(v)),
        (Kind::LinkedArrayList, Action::RemoveAt(i)) => WriteLinkedArrayList::new(cursor)?.remove(*i),
        (Kind::Nested, Action::NestedPut(outer, inner, v)) => {
            let mut nested = WriteHashMap::new(cursor)?;
            WriteHashMap::new(&mut nested.put_cursor(outer)?)?.put(inner, to_data(v))
        }
        (Kind::Nested, Action::NestedRemove(outer)) => WriteHashMap::new(cursor)?.remove(outer).map(drop),
        (Kind::Blob, Action::Blob(bytes)) => {
            // write in uneven chunks to exercise the writer's buffering
            let mut writer = cursor.writer()?;
            for chunk in bytes.chunks(1 + bytes.len() / 7) {
                writer.write_all(chunk)?;
            }
            writer.finish()
        }
        (kind, action) => panic!("{action:?} doesn't apply to {kind:?}"),
    }
}

fn apply_op<'a, C: Core>(db: &'a Database<C>, moment: &mut WriteHashMap<'a, C>, op: &Op) -> Result<()> {
    match op {
        Op::Edit(name, action) => apply_action(&mut moment.put_cursor(name)?, kind_of(name), action),
        Op::Drop(name) => moment.remove(name).map(drop),
        Op::Clone { src, dst, freeze, edits } => {
            let slot = moment.get_slot(src)?.expect("the model says the source exists");
            if *freeze == Freeze::Database {
                db.freeze()?;
            }
            let mut cursor = moment.put_cursor(dst)?;
            cursor.write(slot)?;
            if *freeze == Freeze::Cursor {
                cursor.freeze()?;
            }
            for action in edits {
                apply_action(&mut cursor, kind_of(dst), action)?;
            }
            Ok(())
        }
    }
}

fn is_deliberate_abort(err: &Error) -> bool {
    matches!(err, Error::Io(e) if e.to_string() == ABORT_MESSAGE)
}

fn run_txn<C: Core>(db: &Database<C>, txn: &Txn) -> Result<()> {
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    match txn {
        Txn::Revert(target) => {
            let slot = history.get_slot(*target as i64)?.expect("the moment to revert to exists");
            history.append(slot)
        }
        Txn::Commit(ops) | Txn::Abort(ops) => {
            let last = history.get_slot(-1)?;
            let result = history.append_context(last, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                for op in ops {
                    apply_op(db, &mut moment, op)?;
                }
                if matches!(txn, Txn::Abort(_)) {
                    return Err(Error::Io(io::Error::other(ABORT_MESSAGE)));
                }
                Ok(())
            });
            match result {
                Err(err) if matches!(txn, Txn::Abort(_)) && is_deliberate_abort(&err) => Ok(()),
                Ok(()) if matches!(txn, Txn::Abort(_)) => panic!("an aborted transaction committed"),
                result => result,
            }
        }
    }
}

// reading moments back

fn read_value<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<V> {
    let slot = cursor.slot()?;
    Ok(match slot.tag {
        Tag::ShortBytes | Tag::Bytes => {
            let bytes = cursor.read_bytes_object(None)?;
            V::Bytes(bytes.value.into_owned(), bytes.format_tag)
        }
        Tag::Uint => V::Uint(cursor.read_uint()?),
        Tag::Int => V::Int(cursor.read_int()?),
        Tag::Float => V::Float(cursor.read_float()?.to_bits()),
        Tag::HashMap | Tag::CountedHashMap | Tag::SortedMap => {
            let mut map = BTreeMap::new();
            let mut last_key: Option<Vec<u8>> = None;
            for item in cursor.iter()? {
                let kv = item?.read_key_value_pair()?;
                let key = kv.key_cursor.read_bytes(None)?;
                if slot.tag == Tag::SortedMap {
                    assert!(last_key.as_ref().is_none_or(|last| *last < key), "sorted map out of order");
                    last_key = Some(key.clone());
                }
                let value = read_value(&kv.value_cursor)?;
                assert!(map.insert(key, value).is_none(), "map iterated a key twice");
            }
            if slot.tag != Tag::HashMap {
                assert_eq!(cursor.count()? as usize, map.len(), "{:?} count disagrees with its contents", slot.tag);
            }
            // a lookup goes down the trie (or tree) by key, rather than
            // visiting every node, so it can disagree with iteration
            for (key, value) in &map {
                let found = match slot.tag {
                    Tag::SortedMap => ReadSortedMap::new(cursor.clone())?.get_cursor(key)?,
                    Tag::CountedHashMap => ReadCountedHashMap::new(cursor.clone())?.get_cursor(key)?,
                    _ => ReadHashMap::new(cursor.clone())?.get_cursor(key)?,
                };
                let found = found.expect("an iterated key can't be looked up");
                assert_eq!(read_value(&found)?, *value, "lookup disagrees with iteration");
            }
            V::Map(slot.tag, map)
        }
        Tag::HashSet | Tag::CountedHashSet | Tag::SortedSet => {
            let mut set = BTreeSet::new();
            let mut last_key: Option<Vec<u8>> = None;
            for item in cursor.iter()? {
                let key = item?.read_key_value_pair()?.key_cursor.read_bytes(None)?;
                if slot.tag == Tag::SortedSet {
                    assert!(last_key.as_ref().is_none_or(|last| *last < key), "sorted set out of order");
                    last_key = Some(key.clone());
                }
                assert!(set.insert(key), "set iterated a key twice");
            }
            if slot.tag != Tag::HashSet {
                assert_eq!(cursor.count()? as usize, set.len(), "{:?} count disagrees with its contents", slot.tag);
            }
            V::Set(slot.tag, set)
        }
        Tag::ArrayList | Tag::LinkedArrayList => {
            let mut list = Vec::new();
            for item in cursor.iter()? {
                list.push(read_value(&item?)?);
            }
            assert_eq!(cursor.count()? as usize, list.len(), "{:?} count disagrees with its contents", slot.tag);
            V::List(slot.tag, list)
        }
        tag => panic!("unexpected tag in a moment: {tag:?}"),
    })
}

fn read_moment<C: Core>(db: &Database<C>, index: usize) -> Result<V> {
    let history = ReadArrayList::new(db.root_cursor())?;
    let moment = history.get_cursor(index as i64)?.expect("the moment exists");
    read_value(&moment)
}

/// Where `actual` first differs from `expected`, for a readable failure.
fn first_difference(path: &str, expected: &V, actual: &V) -> Option<String> {
    match (expected, actual) {
        (V::Map(t1, m1), V::Map(t2, m2)) if t1 == t2 => {
            for key in m1.keys().chain(m2.keys()) {
                let path = format!("{path}/{}", String::from_utf8_lossy(key));
                match (m1.get(key), m2.get(key)) {
                    (Some(e), Some(a)) => {
                        if let Some(diff) = first_difference(&path, e, a) {
                            return Some(diff);
                        }
                    }
                    (e, a) => return Some(format!("{path}: expected {e:?}, found {a:?}")),
                }
            }
            None
        }
        (V::List(t1, l1), V::List(t2, l2)) if t1 == t2 => {
            for (i, (e, a)) in l1.iter().zip(l2).enumerate() {
                if let Some(diff) = first_difference(&format!("{path}[{i}]"), e, a) {
                    return Some(diff);
                }
            }
            (l1.len() != l2.len()).then(|| format!("{path}: expected {} items, found {}", l1.len(), l2.len()))
        }
        (e, a) if e == a => None,
        (e, a) => Some(format!("{path}: expected {e:?}, found {a:?}")),
    }
}

fn check_moment<C: Core>(db: &Database<C>, index: usize, expected: &V, seed: u64) {
    let actual = read_moment(db, index).unwrap_or_else(|err| panic!("seed {seed:#x}: reading moment {index}: {err:?}"));
    if let Some(diff) = first_difference("", expected, &actual) {
        panic!("seed {seed:#x}: moment {index} changed: {diff}");
    }
}

fn history_count<C: Core>(db: &Database<C>) -> usize {
    ReadArrayList::new(db.root_cursor()).unwrap().count().unwrap() as usize
}

/// Runs every transaction, checking the newest moment after each one, then
/// reads every moment back in random order.
fn run_and_check<C: Core>(db: &Database<C>, txns: &[Txn], moments: &[V], seed: u64) {
    let mut count = 0;
    for (i, txn) in txns.iter().enumerate() {
        run_txn(db, txn).unwrap_or_else(|err| panic!("seed {seed:#x}: transaction {i} ({txn:?}): {err:?}"));
        if !matches!(txn, Txn::Abort(_)) {
            count += 1;
        }
        assert_eq!(history_count(db), count, "seed {seed:#x}: wrong history length after transaction {i}");
        if count > 0 {
            check_moment(db, count - 1, &moments[count - 1], seed);
        }
    }

    let mut order: Vec<usize> = (0..moments.len()).collect();
    Rng(seed ^ 1).shuffle(&mut order);
    for index in order {
        check_moment(db, index, &moments[index], seed);
    }
}

#[test]
fn every_moment_matches_the_model() {
    let seed = env_or("XITDB_ORACLE_SEED", DEFAULT_SEED);
    let (txns, moments) = generate(seed, env_or("XITDB_ORACLE_TXNS", DEFAULT_TXNS));
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    run_and_check(&db, &txns, &moments, seed);
}

/// Checks random moments until the writer is done, then every moment.
/// Returns how many checks happened while the writer was running.
fn read_while_writing<C: Core>(db: &Database<C>, r: usize, mut rng: Rng, moments: &[V], done: &AtomicBool, seed: u64) -> usize {
    let mut last_count = 0;
    let mut checked = 0;
    loop {
        // read the flag first, so the last pass sees the final history
        let finished = done.load(Ordering::Acquire);
        let count = history_count(db);
        assert!(count >= last_count, "reader {r}: history shrank from {last_count} to {count}");
        assert!(count <= moments.len(), "reader {r}: more moments than transactions");
        last_count = count;
        if finished {
            break;
        }
        if count > 0 {
            let index = rng.below(count);
            check_moment(db, index, &moments[index], seed);
            checked += 1;
        }
    }
    assert_eq!(last_count, moments.len(), "reader {r} didn't see every moment");

    // now every moment, in this reader's own random order
    let mut order: Vec<usize> = (0..moments.len()).collect();
    rng.shuffle(&mut order);
    for index in order {
        check_moment(db, index, &moments[index], seed);
    }
    checked
}

/// Several threads, each with its own `Database` and file handle, read
/// random past moments while another thread is still appending. The README
/// says reads never block writes and need no locks.
#[test]
fn readers_see_every_moment_while_a_writer_appends() {
    const READERS: usize = 4;

    let seed = env_or("XITDB_ORACLE_SEED", DEFAULT_SEED) ^ 2;
    let (txns, moments) = generate(seed, env_or("XITDB_ORACLE_TXNS", DEFAULT_TXNS) / 2);
    let moments = Arc::new(moments);

    let tmp = tempfile::NamedTempFile::new().unwrap();
    let open = |write: bool| OpenOptions::new().read(true).write(write).open(tmp.path()).unwrap();
    // initialize the file before the readers open it
    let writer_db = Database::new(CoreBufferedFile::new(open(true)), Hasher::sha1()).unwrap();
    let done = Arc::new(AtomicBool::new(false));

    let readers: Vec<_> = (0..READERS)
        .map(|r| {
            let file = open(false);
            let moments = Arc::clone(&moments);
            let done = Arc::clone(&done);
            thread::spawn(move || {
                let rng = Rng(seed ^ (r as u64 + 10));
                // half the readers buffer, half don't
                if r % 2 == 0 {
                    let db = Database::new(CoreFile::new(file), Hasher::sha1()).unwrap();
                    read_while_writing(&db, r, rng, &moments, &done, seed)
                } else {
                    let db = Database::new(CoreBufferedFile::with_buffer_size(file, 4096), Hasher::sha1()).unwrap();
                    read_while_writing(&db, r, rng, &moments, &done, seed)
                }
            })
        })
        .collect();

    let writer = {
        let moments = Arc::clone(&moments);
        let done = Arc::clone(&done);
        thread::spawn(move || {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_and_check(&writer_db, &txns, &moments, seed);
            }));
            done.store(true, Ordering::Release);
            if let Err(panic) = result {
                std::panic::resume_unwind(panic);
            }
        })
    };

    writer.join().expect("writer failed");
    for (r, reader) in readers.into_iter().enumerate() {
        let checked = reader.join().unwrap_or_else(|_| panic!("reader {r} failed"));
        assert!(checked > 0, "reader {r} never read a moment");
    }
}


// the freeze rules, checked one at a time. the random transactions above
// follow these rules; these tests check that the rules are real

/// In one transaction, makes a list, clones it, and appends to the clone
/// (or, if `write_original`, to the original). Returns the lengths of the
/// original and the clone in the committed moment.
fn clone_in_one_transaction(freeze: Freeze, write_original: bool) -> (i64, i64) {
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    history
        .append_context(None, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            let mut original = WriteArrayList::new(&mut moment.put_cursor("original")?)?;
            original.append(1u64)?;
            original.append(2u64)?;
            let slot = original.slot()?;

            if freeze == Freeze::Database {
                db.freeze()?;
            }
            let mut clone_cursor = moment.put_cursor("clone")?;
            clone_cursor.write(slot)?;
            if freeze == Freeze::Cursor {
                clone_cursor.freeze()?;
            }
            if write_original {
                WriteArrayList::new(&mut moment.put_cursor("original")?)?.append(3u64)
            } else {
                WriteArrayList::new(&mut clone_cursor)?.append(3u64)
            }
        })
        .unwrap();

    let moment = ReadHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
    let len = |name| ReadArrayList::new(moment.get_cursor(name).unwrap().unwrap()).unwrap().count().unwrap();
    (len("original"), len("clone"))
}

/// The README's warning: without a freeze, changing a clone of data made in
/// the same transaction changes the original too.
#[test]
fn without_freeze_a_clone_shares_writes_with_its_original() {
    assert_eq!(clone_in_one_transaction(Freeze::None, false), (3, 3));
}

#[test]
fn freezing_the_clones_cursor_keeps_the_original_unchanged() {
    assert_eq!(clone_in_one_transaction(Freeze::Cursor, false), (2, 3));
}

/// `WriteCursor::freeze` only affects writes through that cursor. Writing to
/// the original through another cursor still changes the clone. This is
/// why the random transactions leave both alone after such a clone.
#[test]
fn freezing_the_clones_cursor_does_not_protect_the_clone() {
    assert_eq!(clone_in_one_transaction(Freeze::Cursor, true), (3, 3));
}

#[test]
fn freezing_the_database_protects_both_sides() {
    assert_eq!(clone_in_one_transaction(Freeze::Database, false), (2, 3));
    assert_eq!(clone_in_one_transaction(Freeze::Database, true), (3, 2));
}

/// Data from an earlier transaction needs no freeze: it's already immutable,
/// so cloning it and changing the clone leaves the earlier moment alone.
#[test]
fn cloning_earlier_data_needs_no_freeze() {
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    history
        .append_context(None, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            let mut original = WriteArrayList::new(&mut moment.put_cursor("original")?)?;
            original.append(1u64)?;
            original.append(2u64)
        })
        .unwrap();
    let last = history.get_slot(-1).unwrap();
    history
        .append_context(last, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            let slot = moment.get_slot("original")?.unwrap();
            let mut clone_cursor = moment.put_cursor("clone")?;
            clone_cursor.write(slot)?;
            WriteArrayList::new(&mut clone_cursor)?.append(3u64)
        })
        .unwrap();

    let moment = ReadHashMap::new(history.get_cursor(-1).unwrap().unwrap()).unwrap();
    let len = |name| ReadArrayList::new(moment.get_cursor(name).unwrap().unwrap()).unwrap().count().unwrap();
    assert_eq!((len("original"), len("clone")), (2, 3));
}
