//! Replicates an in-memory database from this crate to an in-memory replica
//! held by the TypeScript implementation (the `xitdb` npm package), the way
//! a server keeps browser clients in sync, and back. See `interop/ts/run.sh`.
//!
//! `ts_replication <command...>` runs the command (`node client.ts`, in
//! `interop/ts`) and talks to it over its stdin and stdout, one JSON object
//! per line. `interop/ts/client.ts` documents the requests.
//!
//! A replica's `ReplicaState` is sent as
//! `{"committedSize":123,"checksum":"456"}`, with the u64 checksum as a
//! decimal string, because JSON numbers can't hold every u64.

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use xitdb::*;

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

// --- a minimal JSON reader, for the replies of client.ts (which hold no arrays) ---

#[derive(Debug, Clone)]
enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Object(BTreeMap<String, Json>),
}

impl Json {
    fn parse(text: &str) -> Json {
        let mut parser = JsonParser { bytes: text.as_bytes(), pos: 0 };
        let value = parser.value();
        parser.skip_whitespace();
        assert_eq!(parser.pos, text.len(), "trailing characters in {text}");
        value
    }

    fn get(&self, key: &str) -> &Json {
        match self {
            Json::Object(map) => map.get(key).unwrap_or_else(|| panic!("no {key} in {self:?}")),
            _ => panic!("not an object: {self:?}"),
        }
    }

    fn has(&self, key: &str) -> bool {
        matches!(self, Json::Object(map) if map.contains_key(key))
    }

    fn i64(&self) -> i64 {
        match self {
            Json::Number(n) => n.parse().unwrap_or_else(|_| panic!("not an i64: {n}")),
            _ => panic!("not a number: {self:?}"),
        }
    }

    fn str(&self) -> &str {
        match self {
            Json::String(s) => s,
            _ => panic!("not a string: {self:?}"),
        }
    }

    fn u64_string(&self) -> u64 {
        self.str().parse().unwrap_or_else(|_| panic!("not a decimal u64: {self:?}"))
    }

    fn bool(&self) -> bool {
        match self {
            Json::Bool(b) => *b,
            _ => panic!("not a bool: {self:?}"),
        }
    }
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl JsonParser<'_> {
    fn skip_whitespace(&mut self) {
        while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
            self.pos += 1;
        }
    }

    fn eat(&mut self, byte: u8) -> bool {
        self.skip_whitespace();
        let found = self.bytes.get(self.pos) == Some(&byte);
        if found {
            self.pos += 1;
        }
        found
    }

    fn expect(&mut self, byte: u8) {
        assert!(self.eat(byte), "expected {:?} at {}", byte as char, self.pos);
    }

    fn literal(&mut self, word: &str, value: Json) -> Json {
        assert!(self.bytes[self.pos..].starts_with(word.as_bytes()), "bad literal at {}", self.pos);
        self.pos += word.len();
        value
    }

    fn value(&mut self) -> Json {
        self.skip_whitespace();
        match self.bytes[self.pos] {
            b'n' => self.literal("null", Json::Null),
            b't' => self.literal("true", Json::Bool(true)),
            b'f' => self.literal("false", Json::Bool(false)),
            b'"' => Json::String(self.string()),
            b'{' => {
                self.pos += 1;
                let mut map = BTreeMap::new();
                if !self.eat(b'}') {
                    loop {
                        self.skip_whitespace();
                        let key = self.string();
                        self.expect(b':');
                        map.insert(key, self.value());
                        if self.eat(b'}') {
                            break;
                        }
                        self.expect(b',');
                    }
                }
                Json::Object(map)
            }
            _ => {
                let start = self.pos;
                while self.pos < self.bytes.len() && b"-+.eE0123456789".contains(&self.bytes[self.pos]) {
                    self.pos += 1;
                }
                assert!(self.pos > start, "unexpected character at {start}");
                Json::Number(String::from_utf8(self.bytes[start..self.pos].to_vec()).unwrap())
            }
        }
    }

    fn string(&mut self) -> String {
        assert_eq!(self.bytes[self.pos], b'"', "expected a string at {}", self.pos);
        self.pos += 1;
        let mut out = String::new();
        loop {
            let rest = std::str::from_utf8(&self.bytes[self.pos..]).unwrap();
            let c = rest.chars().next().expect("unterminated string");
            self.pos += c.len_utf8();
            match c {
                '"' => return out,
                '\\' => {
                    let escape = self.bytes[self.pos];
                    self.pos += 1;
                    match escape {
                        b'n' => out.push('\n'),
                        b't' => out.push('\t'),
                        b'r' => out.push('\r'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'u' => {
                            let hex = std::str::from_utf8(&self.bytes[self.pos..self.pos + 4]).unwrap();
                            self.pos += 4;
                            out.push(char::from_u32(u32::from_str_radix(hex, 16).unwrap()).unwrap_or('?'));
                        }
                        other => out.push(other as char),
                    }
                }
                c => out.push(c),
            }
        }
    }
}

// --- hex, and the ReplicaState wire form ---

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn from_hex(hex: &str) -> Vec<u8> {
    (0..hex.len()).step_by(2).map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap()).collect()
}

fn state_to_json(state: ReplicaState) -> String {
    format!(r#"{{"committedSize":{},"checksum":"{}"}}"#, state.committed_size, state.checksum)
}

fn state_from_json(json: &Json) -> ReplicaState {
    ReplicaState { committed_size: json.get("committedSize").i64(), checksum: json.get("checksum").u64_string() }
}

// --- the TypeScript client ---

struct Client {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
}

impl Client {
    fn spawn(command: &[String]) -> Client {
        let mut child = Command::new(&command[0])
            .args(&command[1..])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap_or_else(|err| panic!("can't run {command:?}: {err}"));
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Client { child, stdin, stdout }
    }

    fn request(&mut self, request: &str) -> Json {
        writeln!(self.stdin, "{request}").unwrap();
        self.stdin.flush().unwrap();
        let mut line = String::new();
        self.stdout.read_line(&mut line).unwrap();
        assert!(!line.is_empty(), "client.ts exited after {request:.200}");
        let reply = Json::parse(&line);
        if reply.has("fatal") {
            panic!("client.ts failed on {request:.200}:\n{}", reply.get("fatal").str());
        }
        reply
    }

    fn state(&mut self) -> Json {
        self.request(r#"{"type":"state"}"#)
    }

    fn sync(&mut self, start: i64, end: i64, bytes: &[u8]) -> Json {
        self.request(&format!(r#"{{"type":"sync","start":{start},"end":{end},"bytes":"{}"}}"#, to_hex(bytes)))
    }

    fn check(&mut self, moments: &[u64]) {
        let list: Vec<String> = moments.iter().map(u64::to_string).collect();
        self.request(&format!(r#"{{"type":"check","moments":[{}]}}"#, list.join(",")));
    }
}

fn read_committed<C: Core>(db: &Database<C>, start: i64, end: i64) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    db.read_committed(start, end, &mut bytes)?;
    Ok(bytes)
}

/// Checks a reply carrying the client's replica state against `db`, which
/// it must now be a replica of, and checks the trailer checksum both ways:
/// the one xitdb-ts computed for the replica's last trailer must equal the
/// stored one and the one this crate computes for the same fields.
fn check_replica_of<C: Core>(reply: &Json, db: &Database<C>) -> Result<ReplicaState> {
    let state = state_from_json(reply.get("state"));
    assert_eq!(state, db.replica_state()?, "the client's replica state matches the source");
    check_trailer(reply.get("trailer"), state)?;
    assert_eq!(reply.get("trailer").get("fileId").u64_string(), db.header().file_id, "file id");
    Ok(state)
}

fn check_trailer(trailer: &Json, state: ReplicaState) -> Result<()> {
    let file_id = trailer.get("fileId").u64_string();
    let position = trailer.get("position").i64();
    let root = Slot::from_bytes(&from_hex(trailer.get("root").str()))?;
    let commit_id = trailer.get("commitId").u64_string();
    let rust = root_trailer_checksum(file_id, position, root, commit_id);
    assert_eq!(position + consts::ROOT_TRAILER_LENGTH as i64, state.committed_size, "trailer position");
    assert_eq!(trailer.get("stored").u64_string(), state.checksum, "stored checksum is the state's");
    assert_eq!(trailer.get("computed").u64_string(), rust, "xitdb-ts computes the checksum this crate does");
    assert_eq!(rust, state.checksum, "this crate's checksum of the client's trailer");
    Ok(())
}

/// Sends the committed bytes `[start, end)` of `db` to the client.
fn send<C: Core>(client: &mut Client, db: &Database<C>, start: i64, end: i64) -> Result<Json> {
    let bytes = read_committed(db, start, end)?;
    Ok(client.sync(start, end, &bytes))
}

/// Sends the bytes and checks they were applied.
fn send_applied<C: Core>(client: &mut Client, db: &Database<C>, start: i64, end: i64) -> Result<ReplicaState> {
    let reply = send(client, db, start, end)?;
    assert!(reply.get("applied").bool(), "sync [{start}, {end}) applied: {reply:?}");
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

fn main() -> Result<()> {
    let command: Vec<String> = std::env::args().skip(1).collect();
    if command.is_empty() {
        eprintln!("usage: ts_replication <command to run client.ts...>");
        std::process::exit(2);
    }
    let mut client = Client::spawn(&command);

    // (a) a history with every data type, and a full sync to a new replica.
    // the replica has its own file ID, so replication_start returns 0.
    let server = Database::new(CoreMemory::new(), Hasher::sha1())?;
    write_moment(&server, 0)?;
    write_moment(&server, 1)?;
    let fresh = client.state();
    check_trailer(fresh.get("trailer"), state_from_json(fresh.get("state")))?;
    let start = server.replication_start(state_from_json(fresh.get("state")))?;
    assert_eq!(start, 0, "a new replica gets a full copy");
    let end = server.committed_size()?;
    send_applied(&mut client, &server, 0, end)?;
    client.check(&[0, 1]);
    println!("rust: full sync of {end} bytes to a new ts replica; ts read moments 0 and 1");

    // (b) deltas, one per transaction
    for n in 2..=4 {
        commit_and_broadcast(&mut client, &server, n)?;
        client.check(&(0..=n).collect::<Vec<_>>());
    }
    println!("rust: ts applied and read deltas for moments 2 to 4");

    // (c) the client reconnects and sends its state; it missed moment 5
    let before = state_from_json(client.state().get("state"));
    write_moment(&server, 5)?;
    let start = server.replication_start(before)?;
    assert_eq!(start, before.committed_size, "a replica that is a prefix continues where it is");
    let end = server.committed_size()?;
    send_applied(&mut client, &server, start, end)?;
    client.check(&[0, 1, 2, 3, 4, 5]);
    // reconnecting with nothing new sends nothing
    let state = state_from_json(client.state().get("state"));
    assert_eq!(server.replication_start(state)?, end);
    send_applied(&mut client, &server, end, end)?;
    println!("rust: ts sent its state, replication_start returned its committed size {start}, the delta applied");

    // (e) a delta that doesn't start at the replica's committed size: the
    // client missed moment 6's broadcast, and gets moment 7's
    let at5 = server.committed_size()?;
    write_moment(&server, 6)?;
    let at6 = server.committed_size()?;
    write_moment(&server, 7)?;
    let at7 = server.committed_size()?;
    let reply = send(&mut client, &server, at6, at7)?;
    assert!(!reply.get("applied").bool(), "a delta past the replica's end is rejected");
    assert_eq!(reply.get("error").str(), "InvalidRangeException");
    assert!(reply.get("unchanged").bool());
    assert_eq!(state_from_json(reply.get("state")).committed_size, at5);
    client.check(&[0, 1, 2, 3, 4, 5]);
    // so it re-syncs
    let start = server.replication_start(state_from_json(reply.get("state")))?;
    assert_eq!(start, at5);
    send_applied(&mut client, &server, start, at7)?;
    client.check(&[0, 1, 2, 3, 4, 5, 6, 7]);
    println!("rust: ts rejected a delta starting at {at6} (it had {at5}) and re-synced");

    // (e) bytes that start at the replica's committed size but come from
    // another file, like a stale broadcast: their trailer's checksum covers
    // the other file's ID and position, so close() rejects them
    let other = Database::new(CoreMemory::new(), Hasher::sha1())?;
    write_moment(&other, 0)?;
    let other_start = other.committed_size()?;
    write_moment(&other, 1)?;
    let foreign = read_committed(&other, other_start, other.committed_size()?)?;
    let reply = client.sync(at7, at7 + foreign.len() as i64, &foreign);
    assert!(!reply.get("applied").bool(), "bytes from another file are rejected");
    assert_eq!(reply.get("error").str(), "InvalidDatabaseException");
    assert!(reply.get("unchanged").bool());
    check_replica_of(&reply, &server)?;
    client.check(&[0, 1, 2, 3, 4, 5, 6, 7]);
    // the next delta discards them
    commit_and_broadcast(&mut client, &server, 8)?;
    client.check(&(0..=8).collect::<Vec<_>>());
    println!("rust: ts rejected {} bytes from another file at its committed size", foreign.len());

    // (d) the server compacts its view into a new in-memory database. it has
    // a new file ID, so replication_start returns 0 and the client gets a
    // full copy.
    let uncompacted_size = server.committed_size()?;
    let server = server.compact(CoreMemory::new(), &mut MemoryOffsetMap::new())?;
    let state = state_from_json(client.state().get("state"));
    assert_eq!(server.replication_start(state)?, 0, "a replica of the uncompacted file gets a full copy");
    let end = server.committed_size()?;
    send_applied(&mut client, &server, 0, end)?;
    client.check(&[8]);
    commit_and_broadcast(&mut client, &server, 9)?;
    client.check(&[8, 9]);
    println!("rust: compacted {uncompacted_size} bytes into {end}; ts got a full copy, then a delta");

    // (f) trailer checksums of arbitrary fields, computed by both
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
        let reply = client.request(&format!(
            r#"{{"type":"checksum","fileId":"{file_id}","position":{position},"root":"{}","commitId":"{commit_id}"}}"#,
            to_hex(&slot.to_bytes())
        ));
        let expected = root_trailer_checksum(file_id, position, *slot, commit_id);
        assert_eq!(reply.get("checksum").u64_string(), expected, "checksum of {file_id} {position} {slot:?}");
    }
    println!("rust: ts and rust compute the same checksum for every trailer, and 50 arbitrary ones");

    // the other way: a database written by xitdb-ts, replicated to this crate
    let replica = Database::new(CoreMemory::new(), Hasher::sha1())?;
    for n in 0..3u64 {
        let written = client.request(&format!(r#"{{"type":"source-write","n":{n}}}"#));
        let reply = client.request(&format!(
            r#"{{"type":"source-sync","state":{}}}"#,
            state_to_json(replica.replica_state()?)
        ));
        let (start, end) = (reply.get("start").i64(), reply.get("end").i64());
        assert_eq!(start, if n == 0 { 0 } else { replica.committed_size()? });
        let bytes = from_hex(reply.get("bytes").str());
        replica.apply_replicated(start, &mut bytes.as_slice(), end - start)?;
        assert_eq!(replica.replica_state()?, state_from_json(written.get("state")));
        assert_eq!(replica.replica_state()?, state_from_json(reply.get("state")));
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

    drop(client.stdin);
    let status = client.child.wait()?;
    assert!(status.success(), "client.ts exited with {status}");
    println!("ts-replication: ok");
    Ok(())
}
