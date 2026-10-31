//! A game of telephone between xitdb implementations, to check that they
//! agree on the file format over a long history. See `interop/telephone.sh`,
//! which runs it with the Go, Java and TypeScript implementations.
//!
//! The implementations ("hops") take turns appending a moment to one
//! database. Each moment applies random edits, which the driver also applies
//! to a model in memory. After every hop, the next hop dumps the whole
//! history and the driver checks every moment against the model. At the end,
//! every hop dumps the file and the dumps must be identical, down to the
//! order hash maps iterate in, and every hop reads a compacted copy.
//!
//! * `telephone run <dir> <rounds> <seed> <hop>...` plays the game in `dir`.
//!   A hop is `rust` (this binary) or `<name>=<command>`, where `command` is
//!   split on whitespace and run as `command apply <db> <ops>` and
//!   `command dump <db>`.
//! * `telephone apply <db> <ops>` and `telephone dump <db>` are the Rust hop.
//!
//! Ops files have one edit per line, and dumps print one value per line,
//! with containers followed by their contents and `end`. Byte strings are
//! hex, or `-` when empty, and floats are their bits in hex. See `Op::line`
//! and `dump`.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::path::{Path, PathBuf};
use std::process::Command;

use xitdb::*;

// values and edits

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
    Uint(u64),
    Int(i64),
    /// the bits of an f64, so NaN payloads and -0.0 compare exactly
    Float(u64),
    Bytes(Vec<u8>, Option<[u8; 2]>),
}

#[derive(Debug, Clone)]
enum Op {
    KvPut(Vec<u8>, Value),
    KvRemove(Vec<u8>),
    CountedPut(Vec<u8>, Value),
    CountedRemove(Vec<u8>),
    SetPut(Vec<u8>),
    SetRemove(Vec<u8>),
    SortedPut(Vec<u8>, Value),
    SortedRemove(Vec<u8>),
    ListAppend(Value),
    ListPut(u64, Value),
    ListSlice(u64),
    LinkedAppend(Value),
    LinkedInsert(u64, Value),
    LinkedRemove(u64),
    LinkedPut(u64, Value),
    LinkedSlice(u64, u64),
}

fn hex(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "-".into();
    }
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    if s == "-" {
        return Vec::new();
    }
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex")).collect()
}

impl Value {
    fn line(&self) -> String {
        match self {
            Value::Uint(v) => format!("uint {v}"),
            Value::Int(v) => format!("int {v}"),
            Value::Float(bits) => format!("float {bits:016x}"),
            Value::Bytes(v, tag) => format!("bytes {} {}", hex(v), tag.map_or("-".into(), |t| hex(&t))),
        }
    }

    fn parse(fields: &[&str]) -> Value {
        match fields {
            ["uint", v] => Value::Uint(v.parse().expect("uint")),
            ["int", v] => Value::Int(v.parse().expect("int")),
            ["float", bits] => Value::Float(u64::from_str_radix(bits, 16).expect("float")),
            ["bytes", v, tag] => {
                let tag = (*tag != "-").then(|| unhex(tag).try_into().expect("2-byte format tag"));
                Value::Bytes(unhex(v), tag)
            }
            _ => panic!("bad value {fields:?}"),
        }
    }

    fn data(&self) -> Data<'_> {
        match self {
            Value::Uint(v) => Data::Uint(*v),
            Value::Int(v) => Data::Int(*v),
            Value::Float(bits) => Data::Float(f64::from_bits(*bits)),
            Value::Bytes(v, tag) => Data::Bytes(Bytes { value: Cow::Borrowed(v), format_tag: *tag }),
        }
    }
}

impl Op {
    fn line(&self) -> String {
        match self {
            Op::KvPut(k, v) => format!("kv_put {} {}", hex(k), v.line()),
            Op::KvRemove(k) => format!("kv_remove {}", hex(k)),
            Op::CountedPut(k, v) => format!("counted_put {} {}", hex(k), v.line()),
            Op::CountedRemove(k) => format!("counted_remove {}", hex(k)),
            Op::SetPut(k) => format!("set_put {}", hex(k)),
            Op::SetRemove(k) => format!("set_remove {}", hex(k)),
            Op::SortedPut(k, v) => format!("sorted_put {} {}", hex(k), v.line()),
            Op::SortedRemove(k) => format!("sorted_remove {}", hex(k)),
            Op::ListAppend(v) => format!("list_append {}", v.line()),
            Op::ListPut(i, v) => format!("list_put {i} {}", v.line()),
            Op::ListSlice(n) => format!("list_slice {n}"),
            Op::LinkedAppend(v) => format!("linked_append {}", v.line()),
            Op::LinkedInsert(i, v) => format!("linked_insert {i} {}", v.line()),
            Op::LinkedRemove(i) => format!("linked_remove {i}"),
            Op::LinkedPut(i, v) => format!("linked_put {i} {}", v.line()),
            Op::LinkedSlice(offset, n) => format!("linked_slice {offset} {n}"),
        }
    }

    fn parse(line: &str) -> Op {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let int = |s: &str| s.parse::<u64>().expect("index");
        match fields[..] {
            ["kv_put", k, ref v @ ..] => Op::KvPut(unhex(k), Value::parse(v)),
            ["kv_remove", k] => Op::KvRemove(unhex(k)),
            ["counted_put", k, ref v @ ..] => Op::CountedPut(unhex(k), Value::parse(v)),
            ["counted_remove", k] => Op::CountedRemove(unhex(k)),
            ["set_put", k] => Op::SetPut(unhex(k)),
            ["set_remove", k] => Op::SetRemove(unhex(k)),
            ["sorted_put", k, ref v @ ..] => Op::SortedPut(unhex(k), Value::parse(v)),
            ["sorted_remove", k] => Op::SortedRemove(unhex(k)),
            ["list_append", ref v @ ..] => Op::ListAppend(Value::parse(v)),
            ["list_put", i, ref v @ ..] => Op::ListPut(int(i), Value::parse(v)),
            ["list_slice", n] => Op::ListSlice(int(n)),
            ["linked_append", ref v @ ..] => Op::LinkedAppend(Value::parse(v)),
            ["linked_insert", i, ref v @ ..] => Op::LinkedInsert(int(i), Value::parse(v)),
            ["linked_remove", i] => Op::LinkedRemove(int(i)),
            ["linked_put", i, ref v @ ..] => Op::LinkedPut(int(i), Value::parse(v)),
            ["linked_slice", offset, n] => Op::LinkedSlice(int(offset), int(n)),
            _ => panic!("bad op {line:?}"),
        }
    }
}

// the model

/// What a moment should contain. Every hop creates all six structures in
/// every moment, under these keys, before applying its edits.
#[derive(Debug, Clone, Default)]
struct Moment {
    kv: BTreeMap<Vec<u8>, Value>,
    counted: BTreeMap<Vec<u8>, Value>,
    set: BTreeSet<Vec<u8>>,
    sorted: BTreeMap<Vec<u8>, Value>,
    list: Vec<Value>,
    linked: Vec<Value>,
}

impl Moment {
    fn apply(&mut self, op: &Op) {
        match op.clone() {
            Op::KvPut(k, v) => drop(self.kv.insert(k, v)),
            Op::KvRemove(k) => drop(self.kv.remove(&k)),
            Op::CountedPut(k, v) => drop(self.counted.insert(k, v)),
            Op::CountedRemove(k) => drop(self.counted.remove(&k)),
            Op::SetPut(k) => drop(self.set.insert(k)),
            Op::SetRemove(k) => drop(self.set.remove(&k)),
            Op::SortedPut(k, v) => drop(self.sorted.insert(k, v)),
            Op::SortedRemove(k) => drop(self.sorted.remove(&k)),
            Op::ListAppend(v) => self.list.push(v),
            Op::ListPut(i, v) => self.list[i as usize] = v,
            Op::ListSlice(n) => self.list.truncate(n as usize),
            Op::LinkedAppend(v) => self.linked.push(v),
            Op::LinkedInsert(i, v) => self.linked.insert(i as usize, v),
            Op::LinkedRemove(i) => drop(self.linked.remove(i as usize)),
            Op::LinkedPut(i, v) => self.linked[i as usize] = v,
            Op::LinkedSlice(offset, n) => {
                self.linked = self.linked[offset as usize..(offset + n) as usize].to_vec();
            }
        }
    }

    fn node(&self) -> Node {
        let key = |k: &Vec<u8>| Node::Value(Value::Bytes(k.clone(), None));
        let map = |kind: &str, m: &BTreeMap<Vec<u8>, Value>| {
            Node::Map(kind.into(), m.iter().map(|(k, v)| (key(k), Node::Value(v.clone()))).collect())
        };
        let seq = |kind: &str, l: &[Value]| Node::Seq(kind.into(), l.iter().cloned().map(Node::Value).collect());
        let fields = [
            ("kv", map("hash_map", &self.kv)),
            ("counted", map("counted_hash_map", &self.counted)),
            ("set", Node::Set("hash_set".into(), self.set.iter().map(key).collect())),
            ("sorted", map("sorted_map", &self.sorted)),
            ("list", seq("array_list", &self.list)),
            ("linked", seq("linked_array_list", &self.linked)),
        ];
        Node::Map("hash_map".into(), fields.into_iter().map(|(k, v)| (key(&k.as_bytes().to_vec()), v)).collect())
    }
}

fn history_node(history: &[Moment]) -> Node {
    canonical(Node::Seq("array_list".into(), history.iter().map(Moment::node).collect()))
}

// random edits

/// splitmix64, so a seed replays the same game without a dependency
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }

    fn bytes(&mut self, len: u64) -> Vec<u8> {
        // printable bytes can be stored inline as short bytes, while
        // arbitrary bytes contain zeroes, which can't
        let printable = self.below(2) == 0;
        (0..len).map(|_| if printable { b'a' + self.below(26) as u8 } else { self.next() as u8 }).collect()
    }

    fn key(&mut self) -> Vec<u8> {
        // mostly from a small pool, so puts overwrite and removes hit
        if self.below(8) == 0 {
            let len = self.below(12);
            self.bytes(len)
        } else {
            format!("k{}", self.below(50)).into_bytes()
        }
    }

    fn existing_key<'k>(&mut self, keys: impl ExactSizeIterator<Item = &'k Vec<u8>>) -> Vec<u8> {
        let len = keys.len() as u64;
        if len == 0 || self.below(4) == 0 {
            return self.key();
        }
        let i = self.below(len) as usize;
        keys.into_iter().nth(i).unwrap().clone()
    }

    fn value(&mut self) -> Value {
        match self.below(10) {
            // no implementation can read a uint above i64::MAX, because they
            // store it in a signed slot
            0 | 1 => Value::Uint(match self.below(3) {
                0 => self.pick(&[0, 1, 255, 256, 1 << 32, (1 << 53) - 1, (1 << 53) + 1, i64::MAX as u64]),
                1 => self.below(1000),
                _ => self.next() >> 1,
            }),
            2 => Value::Int(match self.below(3) {
                0 => self.pick(&[0, -1, 1, i64::MIN, i64::MAX, -(1 << 53) - 1, i32::MIN as i64]),
                1 => self.below(2000) as i64 - 1000,
                _ => self.next() as i64,
            }),
            3 => Value::Float(match self.below(2) {
                0 => self.pick(&[0.0f64, -0.0, 1.5, -2.25, f64::INFINITY, f64::NEG_INFINITY, f64::MIN_POSITIVE, 5e-324, f64::MAX])
                    .to_bits(),
                // any bits except NaN, whose payload a javascript number may not keep
                _ => loop {
                    let bits = self.next();
                    if !f64::from_bits(bits).is_nan() {
                        break bits;
                    }
                },
            }),
            _ => {
                let len = match self.below(20) {
                    0 => 0,
                    1..=7 => 1 + self.below(8),
                    8..=17 => 9 + self.below(92),
                    18 => 200 + self.below(800),
                    _ => 1000 + self.below(4000),
                };
                let value = self.bytes(len);
                let tag = (self.below(3) == 0).then(|| [b'a' + self.below(26) as u8, b'a' + self.below(26) as u8]);
                Value::Bytes(value, tag)
            }
        }
    }

    fn op(&mut self, m: &Moment) -> Op {
        let list = m.list.len() as u64;
        let linked = m.linked.len() as u64;
        loop {
            return match self.below(40) {
                0..=5 => Op::KvPut(self.key(), self.value()),
                6..=7 => Op::KvRemove(self.existing_key(m.kv.keys())),
                8..=11 => Op::CountedPut(self.key(), self.value()),
                12..=13 => Op::CountedRemove(self.existing_key(m.counted.keys())),
                14..=16 => Op::SetPut(self.key()),
                17 => Op::SetRemove(self.existing_key(m.set.iter())),
                18..=22 => Op::SortedPut(self.key(), self.value()),
                23..=24 => Op::SortedRemove(self.existing_key(m.sorted.keys())),
                25..=28 => Op::ListAppend(self.value()),
                29..=30 if list > 0 => Op::ListPut(self.below(list), self.value()),
                31 => Op::ListSlice(self.below(list + 1)),
                32..=33 => Op::LinkedAppend(self.value()),
                // like the other implementations, insert can't append
                34..=36 if linked > 0 => Op::LinkedInsert(self.below(linked), self.value()),
                37 if linked > 0 => Op::LinkedRemove(self.below(linked)),
                38 if linked > 0 => Op::LinkedPut(self.below(linked), self.value()),
                39 => {
                    let offset = self.below(linked + 1);
                    Op::LinkedSlice(offset, self.below(linked - offset + 1))
                }
                _ => continue,
            };
        }
    }
}

// the rust hop

type Db = Database<CoreBufferedFile>;

fn open(path: &Path) -> Result<Db> {
    let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path)?;
    Database::new(CoreBufferedFile::new(file), Hasher::sha1())
}

fn apply(db_path: &Path, ops_path: &Path) -> Result<()> {
    let ops: Vec<Op> = fs::read_to_string(ops_path)?.lines().filter(|l| !l.is_empty()).map(Op::parse).collect();
    let db = open(db_path)?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    let last = history.get_slot(-1)?;
    history.append_context(last, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        WriteHashMap::new(&mut moment.put_cursor("kv")?)?;
        WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?;
        WriteHashSet::new(&mut moment.put_cursor("set")?)?;
        WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?;
        WriteArrayList::new(&mut moment.put_cursor("list")?)?;
        WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?;
        for op in &ops {
            match op {
                Op::KvPut(k, v) => WriteHashMap::new(&mut moment.put_cursor("kv")?)?.put(k, v.data())?,
                Op::KvRemove(k) => drop(WriteHashMap::new(&mut moment.put_cursor("kv")?)?.remove(k)?),
                Op::CountedPut(k, v) => WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?.put(k, v.data())?,
                Op::CountedRemove(k) => drop(WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?.remove(k)?),
                Op::SetPut(k) => WriteHashSet::new(&mut moment.put_cursor("set")?)?.put(k)?,
                Op::SetRemove(k) => drop(WriteHashSet::new(&mut moment.put_cursor("set")?)?.remove(k)?),
                Op::SortedPut(k, v) => WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?.put(k, v.data())?,
                Op::SortedRemove(k) => drop(WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?.remove(k)?),
                Op::ListAppend(v) => WriteArrayList::new(&mut moment.put_cursor("list")?)?.append(v.data())?,
                Op::ListPut(i, v) => WriteArrayList::new(&mut moment.put_cursor("list")?)?.put(*i as i64, v.data())?,
                Op::ListSlice(n) => WriteArrayList::new(&mut moment.put_cursor("list")?)?.slice(*n as i64)?,
                Op::LinkedAppend(v) => WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?.append(v.data())?,
                Op::LinkedInsert(i, v) => {
                    WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?.insert(*i as i64, v.data())?
                }
                Op::LinkedRemove(i) => WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?.remove(*i as i64)?,
                Op::LinkedPut(i, v) => {
                    WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?.put(*i as i64, v.data())?
                }
                Op::LinkedSlice(offset, n) => {
                    WriteLinkedArrayList::new(&mut moment.put_cursor("linked")?)?.slice(*offset as i64, *n as i64)?
                }
            }
        }
        Ok(())
    })?;
    db.core().flush()?;
    Ok(())
}

/// Prints any value, following its tags, in the format `parse` reads.
fn dump<C: Core>(cursor: &ReadCursor<'_, C>, depth: usize, out: &mut String) -> Result<()> {
    let indent = "  ".repeat(depth);
    let container = |kind: &str, count: Option<i64>, out: &mut String, pairs: bool| -> Result<()> {
        let count = count.map_or("-".into(), |n| n.to_string());
        out.push_str(&format!("{indent}{kind} {count}\n"));
        for item in cursor.iter()? {
            let item = item?;
            if pairs {
                let kv = item.read_key_value_pair()?;
                dump(&kv.key_cursor, depth + 1, out)?;
                dump(&kv.value_cursor, depth + 1, out)?;
            } else if matches!(item.slot()?.tag, Tag::KvPair | Tag::SortedKvPair) {
                dump(&item.read_key_value_pair()?.key_cursor, depth + 1, out)?;
            } else {
                dump(&item, depth + 1, out)?;
            }
        }
        out.push_str(&format!("{indent}end\n"));
        Ok(())
    };
    match cursor.slot()?.tag {
        Tag::None => out.push_str(&format!("{indent}none\n")),
        Tag::Uint => out.push_str(&format!("{indent}{}\n", Value::Uint(cursor.read_uint()?).line())),
        Tag::Int => out.push_str(&format!("{indent}{}\n", Value::Int(cursor.read_int()?).line())),
        Tag::Float => out.push_str(&format!("{indent}{}\n", Value::Float(cursor.read_float()?.to_bits()).line())),
        Tag::Bytes | Tag::ShortBytes => {
            let bytes = cursor.read_bytes_object(None)?;
            out.push_str(&format!("{indent}{}\n", Value::Bytes(bytes.value.into_owned(), bytes.format_tag).line()));
        }
        Tag::ArrayList => container("array_list", Some(ReadArrayList::new(cursor.clone())?.count()?), out, false)?,
        Tag::LinkedArrayList => {
            container("linked_array_list", Some(ReadLinkedArrayList::new(cursor.clone())?.count()?), out, false)?
        }
        Tag::HashMap => container("hash_map", None, out, true)?,
        Tag::CountedHashMap => {
            container("counted_hash_map", Some(ReadCountedHashMap::new(cursor.clone())?.count()?), out, true)?
        }
        Tag::SortedMap => container("sorted_map", Some(ReadSortedMap::new(cursor.clone())?.count()?), out, true)?,
        Tag::HashSet => container("hash_set", None, out, false)?,
        Tag::CountedHashSet => {
            container("counted_hash_set", Some(ReadCountedHashSet::new(cursor.clone())?.count()?), out, false)?
        }
        Tag::SortedSet => container("sorted_set", Some(ReadSortedSet::new(cursor.clone())?.count()?), out, false)?,
        tag => panic!("unexpected tag {tag:?}"),
    }
    Ok(())
}

fn dump_file(db_path: &Path) -> Result<String> {
    let db = open(db_path)?;
    let mut out = String::new();
    dump(&db.root_cursor().read_cursor(), 0, &mut out)?;
    Ok(out)
}

// reading dumps

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    None,
    Value(Value),
    Seq(String, Vec<Node>),
    Map(String, Vec<(Node, Node)>),
    Set(String, Vec<Node>),
}

type Tokens<'t> = std::iter::Peekable<std::str::SplitWhitespace<'t>>;

fn parse(tokens: &mut Tokens<'_>) -> std::result::Result<Node, String> {
    fn next<'t>(tokens: &mut Tokens<'t>) -> std::result::Result<&'t str, String> {
        tokens.next().ok_or_else(|| "unexpected end of dump".to_string())
    }
    let kind = next(tokens)?;
    let node = match kind {
        "none" => Node::None,
        "uint" | "int" | "float" => Node::Value(Value::parse(&[kind, next(tokens)?])),
        "bytes" => Node::Value(Value::parse(&[kind, next(tokens)?, next(tokens)?])),
        "array_list" | "linked_array_list" | "hash_map" | "counted_hash_map" | "sorted_map" | "hash_set"
        | "counted_hash_set" | "sorted_set" => {
            let count = next(tokens)?;
            let mut items = Vec::new();
            while tokens.peek() != Some(&"end") {
                items.push(parse(tokens)?);
            }
            tokens.next();
            let pairs = kind.ends_with("map");
            let len = if pairs { items.len() / 2 } else { items.len() };
            if count != "-" && count.parse::<usize>().map_err(|e| e.to_string())? != len {
                return Err(format!("{kind} says its count is {count} but iterates over {len} items"));
            }
            if pairs {
                let mut items = items.into_iter();
                Node::Map(kind.into(), std::iter::from_fn(|| Some((items.next()?, items.next()?))).collect())
            } else if kind.ends_with("set") {
                Node::Set(kind.into(), items)
            } else {
                Node::Seq(kind.into(), items)
            }
        }
        _ => return Err(format!("unexpected token {kind:?}")),
    };
    Ok(node)
}

fn parse_dump(text: &str) -> std::result::Result<Node, String> {
    let mut tokens = text.split_whitespace().peekable();
    let node = parse(&mut tokens)?;
    match tokens.next() {
        Some(extra) => Err(format!("unexpected token {extra:?} after the root")),
        None => Ok(node),
    }
}

/// Sorts hash maps and sets, whose order depends on hashes, not the model.
/// Sorted maps keep their order, since that's what is being tested.
fn canonical(node: Node) -> Node {
    match node {
        Node::Seq(kind, items) => Node::Seq(kind, items.into_iter().map(canonical).collect()),
        Node::Map(kind, pairs) => {
            let mut pairs: Vec<_> = pairs.into_iter().map(|(k, v)| (canonical(k), canonical(v))).collect();
            if kind != "sorted_map" {
                pairs.sort();
            }
            Node::Map(kind, pairs)
        }
        Node::Set(kind, items) => {
            let mut items: Vec<_> = items.into_iter().map(canonical).collect();
            if kind != "sorted_set" {
                items.sort();
            }
            Node::Set(kind, items)
        }
        node => node,
    }
}

fn render(node: &Node, depth: usize, out: &mut String) {
    let indent = "  ".repeat(depth);
    match node {
        Node::None => out.push_str(&format!("{indent}none\n")),
        Node::Value(v) => out.push_str(&format!("{indent}{}\n", v.line())),
        Node::Seq(kind, items) | Node::Set(kind, items) => {
            out.push_str(&format!("{indent}{kind} {}\n", items.len()));
            items.iter().for_each(|item| render(item, depth + 1, out));
            out.push_str(&format!("{indent}end\n"));
        }
        Node::Map(kind, pairs) => {
            out.push_str(&format!("{indent}{kind} {}\n", pairs.len()));
            for (k, v) in pairs {
                render(k, depth + 1, out);
                render(v, depth + 1, out);
            }
            out.push_str(&format!("{indent}end\n"));
        }
    }
}

/// Describes the first place `actual` differs from `expected`.
fn diff(expected: &Node, actual: &Node, path: &str) -> Option<String> {
    let short = |n: &Node| {
        let mut s = String::new();
        render(n, 0, &mut s);
        let first = s.lines().next().unwrap_or_default().to_string();
        if first.len() > 120 { format!("{}...", &first[..120]) } else { first }
    };
    match (expected, actual) {
        (Node::Seq(k1, a), Node::Seq(k2, b)) | (Node::Set(k1, a), Node::Set(k2, b)) if k1 == k2 => {
            for (i, (x, y)) in a.iter().zip(b).enumerate() {
                if let Some(d) = diff(x, y, &format!("{path}[{i}]")) {
                    return Some(d);
                }
            }
            (a.len() != b.len()).then(|| format!("{path}: expected {} items, found {}", a.len(), b.len()))
        }
        (Node::Map(k1, a), Node::Map(k2, b)) if k1 == k2 => {
            for ((xk, xv), (yk, yv)) in a.iter().zip(b) {
                if xk != yk {
                    return Some(format!("{path}: expected key {}, found {}", short(xk), short(yk)));
                }
                let name = match xk {
                    Node::Value(Value::Bytes(k, None)) if k.iter().all(u8::is_ascii_graphic) => {
                        String::from_utf8_lossy(k).into_owned()
                    }
                    _ => short(xk),
                };
                if let Some(d) = diff(xv, yv, &format!("{path}.{name}")) {
                    return Some(d);
                }
            }
            (a.len() != b.len()).then(|| format!("{path}: expected {} entries, found {}", a.len(), b.len()))
        }
        _ => (expected != actual).then(|| format!("{path}: expected {}, found {}", short(expected), short(actual))),
    }
}

// the driver

struct Hop {
    name: String,
    command: Vec<String>,
}

impl Hop {
    fn new(spec: &str) -> Hop {
        match spec.split_once('=') {
            Some((name, command)) => {
                Hop { name: name.into(), command: command.split_whitespace().map(String::from).collect() }
            }
            None if spec == "rust" => {
                let exe = std::env::current_exe().expect("current exe").to_string_lossy().into_owned();
                Hop { name: "rust".into(), command: vec![exe] }
            }
            None => panic!("a hop is `rust` or `<name>=<command>`, not {spec:?}"),
        }
    }

    fn run(&self, args: &[&Path]) -> std::result::Result<String, String> {
        let output = Command::new(&self.command[0])
            .args(&self.command[1..])
            .args(args)
            .output()
            .map_err(|e| format!("{}: couldn't run {:?}: {e}", self.name, self.command))?;
        if !output.status.success() {
            let args: Vec<_> = args.iter().map(|a| a.display().to_string()).collect();
            return Err(format!(
                "{} failed running {}: {}\n{}",
                self.name,
                args.join(" "),
                output.status,
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        String::from_utf8(output.stdout).map_err(|e| e.to_string())
    }

    fn read(&self, db: &Path) -> std::result::Result<Node, String> {
        let text = self.run(&[Path::new("dump"), db])?;
        parse_dump(&text).map_err(|e| format!("{} wrote an unreadable dump of {}: {e}", self.name, db.display()))
    }
}

/// Has `hop` read `db` and compares it to `history`. On a mismatch, writes
/// both to `dir` so they can be diffed.
fn check(hop: &Hop, db: &Path, history: &[Moment], dir: &Path, when: &str) -> std::result::Result<Node, String> {
    let raw = hop.read(db)?;
    let actual = canonical(raw.clone());
    let expected = history_node(history);
    if let Some(d) = diff(&expected, &actual, "history") {
        let (mut e, mut a) = (String::new(), String::new());
        render(&expected, 0, &mut e);
        render(&actual, 0, &mut a);
        let _ = fs::write(dir.join("expected.txt"), e);
        let _ = fs::write(dir.join(format!("actual-{}.txt", hop.name)), a);
        return Err(format!("{when}, {} read {}: {d}", hop.name, db.display()));
    }
    Ok(raw)
}

fn run(dir: &Path, rounds: u64, seed: u64, hops: &[Hop]) -> std::result::Result<(), String> {
    fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    let db = dir.join("telephone.db");
    let compacted = dir.join("compacted.db");
    for path in [&db, &compacted] {
        let _ = fs::remove_file(path);
    }
    let mut rng = Rng(seed);
    let mut history: Vec<Moment> = Vec::new();
    let mut op_count = 0;

    for round in 0..rounds {
        for (i, hop) in hops.iter().enumerate() {
            let step = history.len();
            let mut moment = history.last().cloned().unwrap_or_default();
            let ops: Vec<Op> = (0..1 + rng.below(30))
                .map(|_| {
                    let op = rng.op(&moment);
                    moment.apply(&op);
                    op
                })
                .collect();
            op_count += ops.len();
            let ops_path = dir.join(format!("{step:03}-{}.ops", hop.name));
            let text: String = ops.iter().map(|op| op.line() + "\n").collect();
            fs::write(&ops_path, text).map_err(|e| e.to_string())?;
            hop.run(&[Path::new("apply"), &db, &ops_path])?;
            history.push(moment);

            let reader = &hops[(i + 1) % hops.len()];
            let when = format!("round {round}, after {} wrote moment {step} ({})", hop.name, ops_path.display());
            check(reader, &db, &history, dir, &when)?;
        }
        println!("round {round}: {} moments, all checked", history.len());
    }

    // every hop reads the final file, and they must agree on iteration
    // order too, which depends on how each one lays out its tries
    let mut first: Option<(&str, Node)> = None;
    for hop in hops {
        let raw = check(hop, &db, &history, dir, "at the end")?;
        match &first {
            None => first = Some((&hop.name, raw)),
            Some((name, other)) => {
                if let Some(d) = diff(other, &raw, "history") {
                    return Err(format!("{name} and {} iterate differently: {d}", hop.name));
                }
            }
        }
    }

    compact(&db, &compacted).map_err(|e| e.to_string())?;
    for hop in hops {
        check(hop, &compacted, &history[history.len() - 1..], dir, "after compacting")?;
    }

    let names: Vec<_> = hops.iter().map(|h| h.name.as_str()).collect();
    let size = fs::metadata(&db).map_err(|e| e.to_string())?.len();
    println!(
        "telephone: ok ({} moments, {op_count} edits, {size} bytes, passed around {}, seed {seed})",
        history.len(),
        names.join(" -> ")
    );
    Ok(())
}

fn compact(db_path: &Path, target: &Path) -> Result<()> {
    let db = open(db_path)?;
    let target_file = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(target)?;
    let compacted = db.compact(CoreBufferedFile::new(target_file), &mut MemoryOffsetMap::new())?;
    compacted.core().flush()?;
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let result = match args[..] {
        ["apply", db, ops] => apply(Path::new(db), Path::new(ops)).map_err(|e| e.to_string()),
        ["dump", db] => dump_file(Path::new(db)).map(|out| print!("{out}")).map_err(|e| e.to_string()),
        ["run", dir, rounds, seed, ref hops @ ..] if !hops.is_empty() => {
            let hops: Vec<Hop> = hops.iter().map(|h| Hop::new(h)).collect();
            run(&PathBuf::from(dir), rounds.parse().expect("rounds"), seed.parse().expect("seed"), &hops)
        }
        _ => Err("usage: telephone run <dir> <rounds> <seed> <hop>... | apply <db> <ops> | dump <db>".into()),
    };
    if let Err(e) = result {
        eprintln!("telephone: {e}");
        std::process::exit(1);
    }
}
