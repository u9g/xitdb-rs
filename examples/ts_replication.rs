//! Replicates an in-memory database from this crate to an in-memory replica
//! held by the TypeScript implementation (the `xitdb` npm package), the way
//! a server keeps browser clients in sync, and back. See `interop/ts/run.sh`.
//!
//! `ts_replication <command...>` runs the command (`node client.ts`, in
//! `interop/ts`) and talks to it over its stdin and stdout, one JSON object
//! per line. `interop/ts/client.ts` documents the requests.
//!
//! A replica's `ReplicaState` is sent in its JSON form from the `serde`
//! feature: `{"committedSize":123,"checksum":"456"}`, with the u64 checksum
//! as a decimal string, because JSON numbers can't hold every u64.

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::time::Duration;

use serde_json::{Value, json};
use xitdb::*;

/// How long to wait for each reply from client.ts.
const REPLY_TIMEOUT: Duration = Duration::from_secs(60);

// --- the data written to each moment ---

fn long_bytes(length: usize, seed: usize) -> Vec<u8> {
    (0..length).map(|i| ((i * 31 + seed) % 251) as u8).collect()
}

/// Appends moment `n` to the history in `db`, in one transaction. Moment 0
/// holds every data type, and each later moment changes the previous one
/// (`interop/ts/client.ts` checks the result in `checkMoment`).
fn write_moment<C: Core>(db: &Database<C>, n: u64) -> Result<()> {
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    let last = history.get_slot(-1)?;
    history.append_context(last, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        if n == 0 {
            write_first_moment(&mut moment)?;
        } else {
            change_moment(&mut moment, n)?;
        }
        moment.put("n", n)?;
        moment.put("float-n", n as f64 * 0.25)?;
        Ok(())
    })
}

fn write_first_moment<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<()> {
    moment.put("name", "xitdb-rs")?;
    moment.put("uint", 42u64)?;
    moment.put("uint-max", u64::MAX)?;
    moment.put("uint-2^53+1", (1u64 << 53) + 1)?;
    moment.put("int", -7i64)?;
    moment.put("int-min", i64::MIN)?;
    moment.put("int-max", i64::MAX)?;
    moment.put("float", 3.5f64)?;
    moment.put("float-neg-zero", -0.0f64)?;
    moment.put("float-inf", f64::NEG_INFINITY)?;
    moment.put("float-nan", f64::NAN)?;
    moment.put("float-tiny", 5e-324f64)?;
    moment.put("null", Data::None)?;

    moment.put("short-string", "hi")?;
    moment.put("unicode", "héllo, wörld ✓")?;
    moment.put("empty", Data::bytes(Vec::new()))?;
    moment.put("short-bytes", &[1u8, 2, 255])?;
    moment.put("zero-bytes", &[0u8, 1, 0])?;
    moment.put("eight-bytes", "12345678")?;
    moment.put("nine-bytes", "123456789")?;
    moment.put("long", long_bytes(5000, 0))?;
    moment.put("tagged", Data::tagged_bytes(vec![0xAB; 32], *b"bi"))?;
    moment.put("short-tagged", Data::tagged_string("hi", *b"st"))?;
    moment.put_bytes(Bytes::tagged(&b"key"[..], *b"tk"), 7u64)?;
    moment.put("removed-at-4", "still here")?;

    let mut list = moment.put_list("list")?;
    for i in 0..300u64 {
        list.append(i * 3)?;
    }

    let mut linked = WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?;
    for i in 0..100 {
        linked.append(format!("item-{i}"))?;
    }
    linked.insert(50, "inserted")?;
    linked.remove(0)?;

    let mut sorted = WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?;
    for i in (0..100u64).rev() {
        sorted.put(format!("k{i:03}"), i)?;
    }
    sorted.remove("k050")?;

    let mut set = moment.put_set("set")?;
    for key in ["a", "b", "c"] {
        set.put(key)?;
    }

    let mut counted = WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?;
    counted.put("x", 1u64)?;
    counted.put("y", 2u64)?;

    let mut counted_set = WriteCountedHashSet::new(&mut moment.put_cursor("counted-set")?)?;
    counted_set.put("p")?;
    counted_set.put("q")?;

    let mut sorted_set = WriteSortedSet::new(&mut moment.put_cursor("sorted-set")?)?;
    for key in ["zeta", "alpha", "mid"] {
        sorted_set.put(key)?;
    }

    let mut inner = moment.put_map("nested")?.put_map("inner")?;
    inner.put("version", 0u64)?;
    let mut entry = inner.put_list("deep")?.append_map()?;
    entry.put("x", 0u64)?;
    entry.put("label", "deep-0")?;
    Ok(())
}

fn change_moment<C: Core>(moment: &mut WriteHashMap<'_, C>, n: u64) -> Result<()> {
    moment.put_list("list")?.append((299 + n) * 3)?;
    WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?.append(format!("tx-{n}"))?;
    WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?.put(format!("t{n:03}"), n * 1000)?;
    let mut set = moment.put_set("set")?;
    set.put(format!("s{n}"))?;
    if n == 2 {
        set.remove("b")?;
    }
    WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?.put(format!("z{n}"), n)?;
    let mut inner = moment.put_map("nested")?.put_map("inner")?;
    inner.put("version", n)?;
    let mut entry = inner.put_list("deep")?.append_map()?;
    entry.put("x", n)?;
    entry.put("label", format!("deep-{n}"))?;
    if n == 3 {
        moment.put("big", long_bytes(100_000, 3))?;
    }
    if n == 4 {
        moment.remove("removed-at-4")?;
    }
    Ok(())
}

// --- reading the replies of client.ts ---

fn field<'v>(value: &'v Value, key: &str) -> &'v Value {
    value.get(key).unwrap_or_else(|| panic!("no {key} in {value}"))
}

fn i64_field(value: &Value, key: &str) -> i64 {
    field(value, key).as_i64().unwrap_or_else(|| panic!("{key} isn't an i64 in {value}"))
}

fn str_field<'v>(value: &'v Value, key: &str) -> &'v str {
    field(value, key).as_str().unwrap_or_else(|| panic!("{key} isn't a string in {value}"))
}

fn bool_field(value: &Value, key: &str) -> bool {
    field(value, key).as_bool().unwrap_or_else(|| panic!("{key} isn't a bool in {value}"))
}

// a u64 sent as a decimal string, like a ReplicaState's checksum
fn u64_field(value: &Value, key: &str) -> u64 {
    str_field(value, key).parse().unwrap_or_else(|_| panic!("{key} isn't a decimal u64 in {value}"))
}

fn state_field(value: &Value) -> ReplicaState {
    serde_json::from_value(field(value, "state").clone()).unwrap_or_else(|err| panic!("bad state in {value}: {err}"))
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn from_hex(hex: &str) -> Vec<u8> {
    (0..hex.len()).step_by(2).map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap()).collect()
}

// --- the TypeScript client ---

/// The running client.ts. It is killed when this is dropped, including when
/// a check panics, so a failed run doesn't leave it behind.
struct Client {
    child: Child,
    stdin: Option<ChildStdin>,
    // lines from its stdout, read on another thread, so waiting for one can time out
    lines: Receiver<std::io::Result<String>>,
}

impl Client {
    fn spawn(command: &[String]) -> Client {
        let mut child = Command::new(&command[0])
            .args(&command[1..])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|err| panic!("can't run {command:?}: {err}"));
        let stdin = child.stdin.take();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let (sender, lines) = mpsc::channel();
        std::thread::spawn(move || {
            for line in stdout.lines() {
                if sender.send(line).is_err() {
                    break;
                }
            }
        });
        Client { child, stdin, lines }
    }

    fn request(&mut self, request: Value) -> Value {
        let text = request.to_string();
        let what = &text[..text.len().min(200)];
        let stdin = self.stdin.as_mut().expect("client.ts's stdin is closed");
        writeln!(stdin, "{text}").and_then(|_| stdin.flush()).unwrap_or_else(|err| {
            panic!("can't send {what} to client.ts: {err}");
        });
        let line = match self.lines.recv_timeout(REPLY_TIMEOUT) {
            Ok(line) => line.unwrap_or_else(|err| panic!("can't read the reply to {what}: {err}")),
            Err(RecvTimeoutError::Timeout) => panic!("no reply to {what} from client.ts in {REPLY_TIMEOUT:?}"),
            Err(RecvTimeoutError::Disconnected) => panic!("client.ts exited without replying to {what}"),
        };
        let reply: Value = serde_json::from_str(&line).unwrap_or_else(|err| panic!("bad reply {line:.200}: {err}"));
        if let Some(fatal) = reply.get("fatal") {
            panic!("client.ts failed on {what}:\n{}", fatal.as_str().unwrap_or_default());
        }
        reply
    }

    fn state(&mut self) -> Value {
        self.request(json!({"type": "state"}))
    }

    fn sync(&mut self, start: i64, end: i64, bytes: &[u8]) -> Value {
        self.request(json!({"type": "sync", "start": start, "end": end, "bytes": to_hex(bytes)}))
    }

    fn check(&mut self, moments: &[u64]) {
        self.request(json!({"type": "check", "moments": moments}));
    }

    /// Closes client.ts's stdin, which ends it, and checks that it exited cleanly.
    fn finish(mut self) {
        drop(self.stdin.take());
        let status = self.child.wait().expect("can't wait for client.ts");
        assert!(status.success(), "client.ts exited with {status}");
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        // after finish, it has already exited, and this does nothing
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn read_committed<C: Core>(db: &Database<C>, start: i64, end: i64) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    db.read_committed(start, end, &mut bytes)?;
    Ok(bytes)
}

/// Checks a reply carrying the client's replica state against `db`, which
/// it must now be a replica of, and checks the trailer checksum both ways
/// (see `check_trailer`).
fn check_replica_of<C: Core>(reply: &Value, db: &Database<C>) -> Result<()> {
    let state = state_field(reply);
    assert_eq!(state, db.replica_state()?, "the client's replica state matches the source");
    check_trailer(field(reply, "trailer"), state)?;
    assert_eq!(u64_field(field(reply, "trailer"), "fileId"), db.header().file_id, "file id");
    Ok(())
}

/// Checks the trailer that ends a replica in `state`, as client.ts read it:
/// the checksum xitdb-ts computed for it must equal the stored one and the
/// one this crate computes for the same fields.
fn check_trailer(trailer: &Value, state: ReplicaState) -> Result<()> {
    let file_id = u64_field(trailer, "fileId");
    let position = i64_field(trailer, "position");
    let root = Slot::from_bytes(&from_hex(str_field(trailer, "root")))?;
    let commit_id = u64_field(trailer, "commitId");
    let rust = root_trailer_checksum(file_id, position, root, commit_id);
    assert_eq!(position + consts::ROOT_TRAILER_LENGTH as i64, state.committed_size, "trailer position");
    assert_eq!(u64_field(trailer, "stored"), state.checksum, "stored checksum is the state's");
    assert_eq!(u64_field(trailer, "computed"), rust, "xitdb-ts computes the checksum this crate does");
    assert_eq!(rust, state.checksum, "this crate's checksum of the client's trailer");
    Ok(())
}

/// Sends the committed bytes `[start, end)` of `db` to the client.
fn send<C: Core>(client: &mut Client, db: &Database<C>, start: i64, end: i64) -> Result<Value> {
    let bytes = read_committed(db, start, end)?;
    Ok(client.sync(start, end, &bytes))
}

/// Sends the bytes and checks they were applied.
fn send_applied<C: Core>(client: &mut Client, db: &Database<C>, start: i64, end: i64) -> Result<()> {
    let reply = send(client, db, start, end)?;
    assert!(bool_field(&reply, "applied"), "sync [{start}, {end}) applied: {reply}");
    check_replica_of(&reply, db)
}

/// Commits moment `n` and broadcasts the new bytes to the client.
fn commit_and_broadcast<C: Core>(client: &mut Client, db: &Database<C>, n: u64) -> Result<()> {
    let previous = db.committed_size()?;
    write_moment(db, n)?;
    let end = db.committed_size()?;
    send_applied(client, db, previous, end)?;
    println!("rust: broadcast moment {n} as bytes [{previous}, {end}), applied by ts");
    Ok(())
}

/// Checks that client.ts rejected a sync with `error`, leaving its replica
/// unchanged, still at the committed size `at`.
fn check_rejected(reply: &Value, error: &str, at: i64) {
    assert!(!bool_field(reply, "applied"), "the sync is rejected: {reply}");
    assert_eq!(str_field(reply, "error"), error);
    assert!(bool_field(reply, "unchanged"), "the replica is unchanged: {reply}");
    assert_eq!(state_field(reply).committed_size, at);
}

fn main() -> Result<()> {
    let command: Vec<String> = std::env::args().skip(1).collect();
    if command.is_empty() {
        eprintln!("usage: ts_replication <command to run client.ts...>");
        std::process::exit(2);
    }
    let mut client = Client::spawn(&command);

    // 1. a history with every data type, and a full sync to a new replica.
    // the replica has its own file ID, so replication_start returns 0.
    let server = Database::new(CoreMemory::new(), Hasher::sha1())?;
    write_moment(&server, 0)?;
    write_moment(&server, 1)?;
    let fresh = client.state();
    check_trailer(field(&fresh, "trailer"), state_field(&fresh))?;
    let start = server.replication_start(state_field(&fresh))?;
    assert_eq!(start, 0, "a new replica gets a full copy");
    let end = server.committed_size()?;
    send_applied(&mut client, &server, 0, end)?;
    client.check(&[0, 1]);
    println!("rust: full sync of {end} bytes to a new ts replica; ts read moments 0 and 1");

    // 2. deltas, one per transaction
    for n in 2..=4 {
        commit_and_broadcast(&mut client, &server, n)?;
        client.check(&(0..=n).collect::<Vec<_>>());
    }
    println!("rust: ts applied and read deltas for moments 2 to 4");

    // 3. the client reconnects and sends its state; it missed moment 5
    let before = state_field(&client.state());
    write_moment(&server, 5)?;
    let start = server.replication_start(before)?;
    assert_eq!(start, before.committed_size, "a replica that is a prefix continues where it is");
    let end = server.committed_size()?;
    send_applied(&mut client, &server, start, end)?;
    client.check(&[0, 1, 2, 3, 4, 5]);
    // reconnecting with nothing new sends nothing
    assert_eq!(server.replication_start(state_field(&client.state()))?, end);
    send_applied(&mut client, &server, end, end)?;
    println!("rust: ts sent its state, replication_start returned its committed size {start}, the delta applied");

    // 4. rejected deltas. first, one that doesn't start at the replica's
    // committed size: the client missed moment 6's broadcast, and gets moment 7's
    let at5 = server.committed_size()?;
    write_moment(&server, 6)?;
    let at6 = server.committed_size()?;
    write_moment(&server, 7)?;
    let at7 = server.committed_size()?;
    let reply = send(&mut client, &server, at6, at7)?;
    check_rejected(&reply, "InvalidRangeException", at5);
    client.check(&[0, 1, 2, 3, 4, 5]);
    // so it re-syncs
    let start = server.replication_start(state_field(&reply))?;
    assert_eq!(start, at5);
    send_applied(&mut client, &server, start, at7)?;
    client.check(&[0, 1, 2, 3, 4, 5, 6, 7]);
    println!("rust: ts rejected a delta starting at {at6} (it had {at5}) and re-synced");

    // then bytes that start at the replica's committed size but come from
    // another file, like a stale broadcast: their trailer's checksum covers
    // the other file's ID and position, so close() rejects them
    let other = Database::new(CoreMemory::new(), Hasher::sha1())?;
    write_moment(&other, 0)?;
    let other_start = other.committed_size()?;
    write_moment(&other, 1)?;
    let foreign = read_committed(&other, other_start, other.committed_size()?)?;
    let reply = client.sync(at7, at7 + foreign.len() as i64, &foreign);
    check_rejected(&reply, "InvalidDatabaseException", at7);
    check_replica_of(&reply, &server)?;
    client.check(&[0, 1, 2, 3, 4, 5, 6, 7]);
    // the next delta discards them
    commit_and_broadcast(&mut client, &server, 8)?;
    client.check(&(0..=8).collect::<Vec<_>>());
    println!("rust: ts rejected {} bytes from another file at its committed size", foreign.len());

    // 5. the server compacts its view into a new in-memory database. it has
    // a new file ID, so replication_start returns 0 and the client gets a
    // full copy.
    let uncompacted_size = server.committed_size()?;
    let server = server.compact(CoreMemory::new(), &mut MemoryOffsetMap::new())?;
    let start = server.replication_start(state_field(&client.state()))?;
    assert_eq!(start, 0, "a replica of the old file gets a full copy");
    let end = server.committed_size()?;
    send_applied(&mut client, &server, 0, end)?;
    client.check(&[8]);
    commit_and_broadcast(&mut client, &server, 9)?;
    client.check(&[8, 9]);
    println!("rust: compacted {uncompacted_size} bytes into {end}; ts got a full copy, then a delta");

    // 6. trailer checksums: every sync above compared them, and these are of
    // arbitrary fields
    let slots = [
        Slot::default(),
        Slot::new(1, Tag::ArrayList),
        Slot::new(i64::MAX, Tag::HashMap).with_full(true),
        Slot::new(-1, Tag::Int),
        Slot::new(0x0123_4567_89AB_CDEF, Tag::Bytes),
    ];
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    for (i, slot) in slots.iter().cycle().take(50).enumerate() {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let file_id = if i == 0 { u64::MAX } else { seed };
        let position = (seed >> 20) as i64 % (1 << 40);
        let commit_id = seed.rotate_left(17);
        let reply = client.request(json!({
            "type": "checksum",
            "fileId": file_id.to_string(),
            "position": position,
            "root": to_hex(&slot.to_bytes()),
            "commitId": commit_id.to_string(),
        }));
        let expected = root_trailer_checksum(file_id, position, *slot, commit_id);
        assert_eq!(u64_field(&reply, "checksum"), expected, "checksum of {file_id} {position} {slot:?}");
    }
    println!("rust: ts and rust compute the same checksum for every trailer, and 50 arbitrary ones");

    // 7. the other way: a database written by xitdb-ts, replicated to this crate
    let replica = Database::new(CoreMemory::new(), Hasher::sha1())?;
    for n in 0..3u64 {
        let written = client.request(json!({"type": "source-write", "n": n}));
        let reply = client.request(json!({"type": "source-sync", "state": replica.replica_state()?}));
        let (start, end) = (i64_field(&reply, "start"), i64_field(&reply, "end"));
        assert_eq!(start, if n == 0 { 0 } else { replica.committed_size()? });
        let bytes = from_hex(str_field(&reply, "bytes"));
        replica.apply_replicated(start, &mut bytes.as_slice(), end - start)?;
        assert_eq!(replica.replica_state()?, state_field(&written));
        assert_eq!(replica.replica_state()?, state_field(&reply));
        let history = ReadArrayList::new(replica.root_cursor())?;
        assert_eq!(history.count()?, n as i64 + 1);
        for i in 0..=n {
            let moment = ReadHashMap::new(history.get_cursor(i as i64)?.unwrap())?;
            assert_eq!(moment.get_string("from", None)?.unwrap(), "xitdb-ts");
            assert_eq!(moment.get_uint("n")?, Some(i));
            let values = moment.get_list("values")?.unwrap();
            // each moment copies the previous one and appends to its list
            assert_eq!(values.count()?, i as i64 + 1);
            for (j, value) in values.iter()?.enumerate() {
                assert_eq!(value?.read_uint()?, j as u64);
            }
            assert_eq!(moment.get_bytes("long", None)?.unwrap(), long_bytes(1000, i as usize));
        }
    }
    println!("rust: replicated a database written by ts (a full copy, then 2 deltas) and read it");

    client.finish();
    println!("ts-replication: ok");
    Ok(())
}
