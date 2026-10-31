//! Crash consistency: a transaction only becomes visible once the root
//! header points at it, so a crash at any moment must leave a database
//! that opens to either the state before the transaction or the state
//! after it.
//!
//! A random workload runs against a core that journals every write,
//! truncation and sync. The journal is then replayed to rebuild the file as
//! a crash would have left it:
//!
//! * cut after every byte of every write, in order
//! * writes since the last sync persisted in any order, some of them torn,
//!   since only a sync orders writes
//!
//! Every resulting file is opened, its whole history is compared with a
//! model, and a new transaction is written to check the database recovers.

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use xitdb::*;

// journaling core

#[derive(Debug, Clone)]
enum Op {
    Write { pos: u64, data: Vec<u8> },
    SetLength(u64),
    Sync,
}

#[derive(Default)]
struct JournalCore {
    mem: CoreMemory,
    ops: Vec<Op>,
}

impl Core for JournalCore {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        self.mem.read(buf)
    }
    fn write(&mut self, buf: &[u8]) -> io::Result<()> {
        let pos = self.mem.position()?;
        self.ops.push(Op::Write { pos, data: buf.to_vec() });
        self.mem.write(buf)
    }
    fn length(&mut self) -> io::Result<u64> {
        self.mem.length()
    }
    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        self.mem.seek_to(pos)
    }
    fn position(&mut self) -> io::Result<u64> {
        self.mem.position()
    }
    fn set_length(&mut self, len: u64) -> io::Result<()> {
        self.ops.push(Op::SetLength(len));
        self.mem.set_length(len)
    }
    // flushing only empties buffers; it doesn't order writes on disk
    fn flush(&mut self) -> io::Result<()> {
        self.mem.flush()
    }
    fn sync(&mut self) -> io::Result<()> {
        self.ops.push(Op::Sync);
        self.mem.sync()
    }
}

// applies op to a file image, keeping only the first `torn` bytes of a write
fn apply(image: &mut Vec<u8>, op: &Op, torn: Option<usize>) {
    match op {
        Op::Write { pos, data } => {
            let data = &data[..torn.unwrap_or(data.len()).min(data.len())];
            let pos = *pos as usize;
            if image.len() < pos + data.len() {
                image.resize(pos + data.len(), 0);
            }
            image[pos..pos + data.len()].copy_from_slice(data);
        }
        Op::SetLength(len) => image.truncate(*len as usize),
        Op::Sync => {}
    }
}

// rng

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
    fn bytes(&mut self, max_len: u64) -> Vec<u8> {
        let len = self.below(max_len + 1);
        (0..len).map(|_| self.next() as u8).collect()
    }
}

// model

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Bytes(Vec<u8>),
    List(Vec<Vec<u8>>),
}

type Moment = BTreeMap<Vec<u8>, Value>;
type History = Vec<Moment>;

const LOG_KEY: &[u8] = b"log";

fn read_history<C: Core>(db: &Database<C>) -> Result<History> {
    let mut history = Vec::new();
    if db.root_cursor().slot()?.tag == Tag::None {
        return Ok(history);
    }
    for moment_cursor in ReadArrayList::new(db.root_cursor())?.iter()? {
        let mut moment = Moment::new();
        for kv_cursor in ReadHashMap::new(moment_cursor?)?.iter()? {
            let kv = kv_cursor?.read_key_value_pair()?;
            let key = kv.key_cursor.read_bytes(None)?;
            let value = if kv.value_cursor.slot()?.tag == Tag::ArrayList {
                let mut items = Vec::new();
                for item in ReadArrayList::new(kv.value_cursor)?.iter()? {
                    items.push(item?.read_bytes(None)?);
                }
                Value::List(items)
            } else {
                Value::Bytes(kv.value_cursor.read_bytes(None)?)
            };
            moment.insert(key, value);
        }
        history.push(moment);
    }
    Ok(history)
}

// workload

// signals a transaction that the workload aborts on purpose
fn abort() -> Error {
    Error::KeyNotFound
}

// changes a copy of the latest moment, in the database and in `moment`
fn edit_moment<C: Core>(rng: &mut Rng, cursor: &mut WriteCursor<'_, C>, moment: &mut Moment) -> Result<()> {
    let mut map = WriteHashMap::new(cursor)?;
    for _ in 0..1 + rng.below(4) {
        match rng.below(10) {
            // short value, often reusing a key so values get overwritten
            0..=4 => {
                let key = vec![b'k', rng.below(12) as u8];
                let value = rng.bytes(24);
                map.put(&key, value.as_slice())?;
                moment.insert(key, Value::Bytes(value));
            }
            // remove a key, which may not exist
            5..=6 => {
                let key = vec![b'k', rng.below(12) as u8];
                assert_eq!(map.remove(&key)?, moment.remove(&key).is_some());
            }
            // long value written incrementally
            7 => {
                let key = vec![b'b', rng.below(3) as u8];
                let value = rng.bytes(400);
                let mut value_cursor = map.put_cursor(&key)?;
                let mut writer = value_cursor.writer()?;
                for chunk in value.chunks(1 + rng.below(100) as usize) {
                    writer.write_all(chunk)?;
                }
                writer.finish()?;
                moment.insert(key, Value::Bytes(value));
            }
            // append to a nested list
            _ => {
                let item = rng.bytes(16);
                let mut list = WriteArrayList::new(&mut map.put_cursor(LOG_KEY)?)?;
                list.append(item.as_slice())?;
                match moment.entry(LOG_KEY.to_vec()).or_insert(Value::List(Vec::new())) {
                    Value::List(items) => items.push(item),
                    Value::Bytes(_) => unreachable!(),
                }
            }
        }
    }
    Ok(())
}

struct Run {
    ops: Vec<Op>,
    // markers[i] is the journal length once histories[i] was committed and synced
    markers: Vec<usize>,
    histories: Vec<History>,
}

fn run_workload(seed: u64, transactions: usize) -> Run {
    let mut rng = Rng(seed);
    let db = Database::new(JournalCore::default(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    let mut model = History::new();
    let mut markers = vec![db.core().ops.len()];
    let mut histories = vec![model.clone()];

    for _ in 0..transactions {
        match rng.below(10) {
            // a transaction that commits
            0..=5 => {
                let mut moment = model.last().cloned().unwrap_or_default();
                let last = history.get_slot(-1).unwrap();
                history
                    .append_context(last, |cursor| edit_moment(&mut rng, cursor, &mut moment))
                    .unwrap();
                model.push(moment);
            }
            // a transaction that fails after writing, so its data is discarded
            6 => {
                let mut moment = model.last().cloned().unwrap_or_default();
                let last = history.get_slot(-1).unwrap();
                let result = history.append_context(last, |cursor| {
                    edit_moment(&mut rng, cursor, &mut moment)?;
                    Err(abort())
                });
                assert!(matches!(result, Err(Error::KeyNotFound)));
            }
            // a transaction that freezes and then fails, so the frozen bytes
            // are kept but must not be published
            7 => {
                let mut moment = model.last().cloned().unwrap_or_default();
                let last = history.get_slot(-1).unwrap();
                let result = history.append_context(last, |cursor| {
                    edit_moment(&mut rng, cursor, &mut moment)?;
                    db.freeze()?;
                    edit_moment(&mut rng, cursor, &mut moment)?;
                    Err(abort())
                });
                assert!(matches!(result, Err(Error::KeyNotFound)));
            }
            // revert to an earlier moment by appending it again
            8 if !model.is_empty() => {
                let index = rng.below(model.len() as u64) as i64;
                let old = history.get_slot(index).unwrap();
                history.append(old).unwrap();
                model.push(model[index as usize].clone());
            }
            // forget recent moments
            _ if model.len() > 1 => {
                let size = 1 + rng.below(model.len() as u64 - 1);
                history.slice(size as i64).unwrap();
                model.truncate(size as usize);
            }
            _ => {}
        }
        assert_eq!(read_history(&db).unwrap(), model);
        markers.push(db.core().ops.len());
        histories.push(model.clone());
    }

    Run { ops: db.into_core().ops, markers, histories }
}

// checking a crash

#[derive(Default, Debug)]
struct Stats {
    images: usize,
    old_state: usize,
    new_state: usize,
    // images that fail to open, when `allow_error` permits it
    errors: usize,
}

// opens a crashed image, checks its history is the one committed before
// the crash (`index`) or the one in progress (`index + 1`), and that a
// new transaction can be written on top of it. with `allow_error`, failing
// to open is counted rather than a test failure, but opening to any other
// history still is.
fn check_image(
    run: &Run,
    image: Vec<u8>,
    index: usize,
    recover: bool,
    allow_error: bool,
    what: &dyn Fn() -> String,
    stats: &mut Stats,
) {
    let outcome = catch_unwind(AssertUnwindSafe(|| -> Result<usize> {
        let db = Database::new(CoreMemory::from_bytes(image), Hasher::sha1())?;
        let history = read_history(&db)?;
        let state = (index..=index + 1)
            .filter(|&i| i < run.histories.len())
            .find(|&i| run.histories[i] == history)
            .unwrap_or_else(|| panic!("history matches neither committed state {index} nor {}", index + 1));

        if recover {
            let mut list = WriteArrayList::new(&mut db.root_cursor())?;
            list.append_context(None, |cursor| {
                WriteHashMap::new(cursor)?.put("recovered", "yes")?;
                Ok(())
            })?;
            let mut expected = history.clone();
            expected.push(Moment::from([(b"recovered".to_vec(), Value::Bytes(b"yes".to_vec()))]));
            assert_eq!(read_history(&db)?, expected, "recovery transaction");

            // and the recovered file opens again
            let bytes = db.into_core().into_bytes();
            let db = Database::new(CoreMemory::from_bytes(bytes), Hasher::sha1())?;
            assert_eq!(read_history(&db)?, expected, "reopened after recovery");
        }
        Ok(state)
    }));
    match outcome {
        Ok(Ok(state)) => {
            stats.images += 1;
            if state == index {
                stats.old_state += 1;
            } else {
                stats.new_state += 1;
            }
        }
        Ok(Err(_)) if allow_error => stats.errors += 1,
        Ok(Err(err)) => panic!("{}: crashed database fails with {err:?}", what()),
        Err(panic) => {
            let msg = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            panic!("{}: {msg}", what())
        }
    }
}

// the write that commits a transaction by pointing the root header at it.
// it's 17 bytes inside the first sector, which disks write atomically in
// practice, so the main tests never tear it; torn_root_header covers that.
fn is_root_header_write(op: &Op) -> bool {
    use xitdb::consts::{ROOT_HEADER_END, ROOT_HEADER_START};
    matches!(op, Op::Write { pos, data }
        if *pos == ROOT_HEADER_START as u64 && data.len() == (ROOT_HEADER_END - ROOT_HEADER_START) as usize)
}

// the last state committed and synced before journal position `pos`
fn committed_before(run: &Run, pos: usize) -> usize {
    run.markers.iter().rposition(|&m| m <= pos).unwrap()
}

// tests

/// The file as left by a crash after any byte of the journal, with every
/// write before it on disk.
#[test]
fn cut_after_every_byte() {
    for seed in 0..3 {
        let run = run_workload(seed, 30);
        let start = run.markers[0];
        let mut image = Vec::new();
        for op in &run.ops[..start] {
            apply(&mut image, op, None);
        }

        let mut stats = Stats::default();
        for (i, op) in run.ops.iter().enumerate().skip(start) {
            let index = committed_before(&run, i);
            let lengths = match op {
                _ if is_root_header_write(op) => 0..1,
                Op::Write { data, .. } => 0..data.len(),
                _ => 0..1,
            };
            for torn in lengths {
                let mut crashed = image.clone();
                apply(&mut crashed, op, Some(torn));
                let what = || format!("seed {seed}, op {i} ({op:?}) cut after {torn} bytes");
                // recovering is slower than opening, so only do it at a few cut points
                let recover = torn == 0 || torn % 7 == 1;
                check_image(&run, crashed, index, recover, false, &what, &mut stats);
            }
            apply(&mut image, op, None);
        }
        // the whole journal is the final state
        let last = run.histories.len() - 1;
        check_image(&run, image, last, true, false, &|| format!("seed {seed}, end"), &mut stats);
        assert!(stats.old_state > 0 && stats.new_state > 0, "{stats:?}");
        eprintln!("seed {seed}: {} ops, {stats:?}", run.ops.len());
    }
}

/// Since only a sync orders writes, a crash can persist any subset of the
/// writes since the last sync, in any order, and tear any of them.
#[test]
fn unsynced_writes_persist_in_any_order() {
    for seed in 10..14 {
        let run = run_workload(seed, 30);
        let mut rng = Rng(seed ^ 0xdead_beef);
        let mut stats = Stats::default();

        // the image after every sync
        let mut durable = Vec::new();
        let mut epoch_start = 0;
        for (i, op) in run.ops.iter().enumerate() {
            if !matches!(op, Op::Sync) {
                continue;
            }
            let epoch = &run.ops[epoch_start..i];
            if epoch_start >= run.markers[0] && !epoch.is_empty() {
                let index = committed_before(&run, epoch_start);
                let trials = if epoch.len() <= 8 { 1 << epoch.len() } else { 256 };
                for trial in 0..trials {
                    // which ops reach the disk: every subset when there are
                    // few, and random ones otherwise
                    let mut chosen: Vec<usize> = (0..epoch.len())
                        .filter(|&j| if epoch.len() <= 8 { trial >> j & 1 == 1 } else { rng.chance(50) })
                        .collect();
                    // in a random order
                    for j in (1..chosen.len()).rev() {
                        chosen.swap(j, rng.below(j as u64 + 1) as usize);
                    }
                    let mut crashed = durable.clone();
                    let mut torn_ops = Vec::new();
                    for &j in &chosen {
                        let torn = match &epoch[j] {
                            Op::Write { data, .. } if !is_root_header_write(&epoch[j]) && rng.chance(25) => {
                                let torn = rng.below(data.len() as u64 + 1) as usize;
                                torn_ops.push((epoch_start + j, torn));
                                Some(torn)
                            }
                            _ => None,
                        };
                        apply(&mut crashed, &epoch[j], torn);
                    }
                    let what = || {
                        let ops: Vec<usize> = chosen.iter().map(|j| epoch_start + j).collect();
                        format!("seed {seed}, ops {ops:?} persisted in that order, torn (op, bytes) {torn_ops:?}")
                    };
                    check_image(&run, crashed, index, trial % 4 == 0, false, &what, &mut stats);
                }
            }
            for op in &run.ops[epoch_start..=i] {
                apply(&mut durable, op, None);
            }
            epoch_start = i + 1;
        }
        assert!(stats.old_state > 0 && stats.new_state > 0, "{stats:?}");
        eprintln!("seed {seed}: {stats:?}");
    }
}

fn tear_root_header_writes(seed: u64, allow_error: bool) -> Stats {
    let run = run_workload(seed, 30);
    let mut image = Vec::new();
    let mut stats = Stats::default();
    for (i, op) in run.ops.iter().enumerate() {
        if i >= run.markers[0]
            && let Op::Write { data, .. } = op
            && is_root_header_write(op)
        {
            let index = committed_before(&run, i);
            for torn in 1..data.len() {
                let mut crashed = image.clone();
                apply(&mut crashed, op, Some(torn));
                let what = || format!("seed {seed}, root header write (op {i}) cut after {torn} bytes");
                check_image(&run, crashed, index, true, allow_error, &what, &mut stats);
            }
        }
        apply(&mut image, op, None);
    }
    stats
}

/// A torn root header write must never open to the wrong history. Today it
/// can leave a database that doesn't open at all, which this allows; see
/// torn_root_header_opens.
#[test]
fn torn_root_header_never_opens_wrong_history() {
    for seed in 60..63 {
        let stats = tear_root_header_writes(seed, true);
        eprintln!("seed {seed}: {stats:?}");
    }
}

/// A torn root header write leaves the previous transaction's trailer and
/// the new one's on disk, both synced, so the database could open to either
/// of them. Today it fails with InvalidDatabase instead.
#[test]
#[ignore = "a torn root header leaves a database that fails to open with InvalidDatabase"]
fn torn_root_header_opens() {
    tear_root_header_writes(60, false);
}

/// Committed bytes never change, apart from the root header, so a crash
/// can't damage history that was already committed.
#[test]
fn committed_bytes_are_never_overwritten() {
    use xitdb::consts::{ROOT_HEADER_END, ROOT_HEADER_START};
    for seed in 20..30 {
        let run = run_workload(seed, 40);
        let mut image = Vec::new();
        let mut committed_len = 0;
        let mut next_marker = 0;
        for (i, op) in run.ops.iter().enumerate() {
            while next_marker < run.markers.len() && run.markers[next_marker] == i {
                committed_len = image.len();
                next_marker += 1;
            }
            match op {
                Op::Write { pos, data } => {
                    let (start, end) = (*pos as usize, *pos as usize + data.len());
                    let in_root_header = start >= ROOT_HEADER_START as usize && end <= ROOT_HEADER_END as usize;
                    assert!(
                        start >= committed_len || in_root_header,
                        "seed {seed}, op {i}: writes {start}..{end} into committed bytes 0..{committed_len}"
                    );
                }
                Op::SetLength(len) => assert!(
                    *len as usize >= committed_len,
                    "seed {seed}, op {i}: truncates committed bytes to {len}, committed {committed_len}"
                ),
                Op::Sync => {}
            }
            apply(&mut image, op, None);
        }
    }
}

/// Garbage after the committed bytes, such as a half-written transaction
/// whose bytes were scrambled, is ignored and then discarded.
#[test]
fn garbage_after_committed_bytes_is_ignored() {
    let run = run_workload(40, 30);
    let mut image = Vec::new();
    for op in &run.ops {
        apply(&mut image, op, None);
    }
    let last = run.histories.len() - 1;
    let mut rng = Rng(41);
    let mut stats = Stats::default();
    for trial in 0..200 {
        let mut crashed = image.clone();
        let garbage = rng.bytes(2000);
        let len = garbage.len();
        crashed.extend(garbage);
        let what = || format!("trial {trial}: {len} bytes of garbage");
        check_image(&run, crashed, last, true, false, &what, &mut stats);
    }
}

/// Cutting the committed bytes themselves isn't something a crash does,
/// but the database must report it as an error rather than panic or read
/// the wrong data.
#[test]
fn truncated_committed_bytes_fail_cleanly() {
    let run = run_workload(50, 20);
    let mut image = Vec::new();
    for op in &run.ops {
        apply(&mut image, op, None);
    }
    for len in 1..image.len() {
        let cut = image[..len].to_vec();
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            Database::new(CoreMemory::from_bytes(cut), Hasher::sha1()).and_then(|db| read_history(&db))
        }));
        match outcome {
            Ok(Ok(history)) => panic!("cut to {len} bytes of {}: opened with {} moments", image.len(), history.len()),
            Ok(Err(_)) => {}
            Err(_) => panic!("cut to {len} bytes of {}: panicked", image.len()),
        }
    }
}
