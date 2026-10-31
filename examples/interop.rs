//! Exchanges databases with another xitdb implementation, to check that
//! they share a file format. See `interop/run.sh`, which runs this against
//! the Go implementation.
//!
//! * `interop write <path>` creates a database with every data type.
//! * `interop verify <path>` checks it after the other implementation has
//!   appended a moment (see `interop/main.go`).
//! * `interop compact <path> <target>` compacts it into `target`.

use std::fs::{File, OpenOptions};

use xitdb::*;

type Db = Database<CoreBufferedFile>;

fn open(path: &str, truncate: bool) -> Result<Db> {
    let file = OpenOptions::new().read(true).write(true).create(true).truncate(truncate).open(path)?;
    Database::new(CoreBufferedFile::new(file), Hasher::sha1())
}

fn string<C: Core>(cursor: Option<ReadCursor<'_, C>>) -> Result<String> {
    let bytes = cursor.expect("missing value").read_bytes(None)?;
    Ok(String::from_utf8(bytes).expect("utf-8"))
}

fn check(condition: bool, what: &str) {
    if !condition {
        panic!("check failed: {what}");
    }
}

fn long_bytes() -> Vec<u8> {
    (0..5000u32).map(|i| (i % 251) as u8).collect()
}

fn write(path: &str) -> Result<()> {
    let db = open(path, true)?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    let last = history.get_slot(-1)?;
    history.append_context(last, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("name", "xitdb-rs")?;
        moment.put("uint", 42u64)?;
        moment.put("int", -7i64)?;
        moment.put("float", 3.5f64)?;
        moment.put("tagged", Data::tagged_bytes(vec![0xAB; 32], *b"bi"))?;
        moment.put("short-tagged", Data::tagged_string("hi", *b"st"))?;
        moment.put("long", long_bytes())?;

        let mut list = WriteArrayList::new(&mut moment.put_cursor("list")?)?;
        for i in 0..300u64 {
            list.append(i)?;
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

        let mut set = WriteHashSet::new(&mut moment.put_cursor("set")?)?;
        for key in ["a", "b", "c"] {
            set.put(key)?;
        }

        let mut counted = WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?;
        counted.put("x", 1u64)?;
        counted.put("y", 2u64)?;

        let mut sorted_set = WriteSortedSet::new(&mut moment.put_cursor("sorted-set")?)?;
        for key in ["zeta", "alpha", "mid"] {
            sorted_set.put(key)?;
        }
        Ok(())
    })?;
    db.core().flush()?;
    println!("rust: wrote {path}");
    Ok(())
}

/// Checks the moment written by `write`.
fn check_rust_moment<C: Core>(moment: &ReadHashMap<'_, C>) -> Result<()> {
    check(string(moment.get_cursor("name")?)? == "xitdb-rs", "name");
    check(moment.get_cursor("uint")?.unwrap().read_uint()? == 42, "uint");
    check(moment.get_cursor("int")?.unwrap().read_int()? == -7, "int");
    check(moment.get_cursor("float")?.unwrap().read_float()? == 3.5, "float");
    let tagged = moment.get_cursor("tagged")?.unwrap().read_bytes_object(None)?;
    check(tagged.value == vec![0xAB; 32] && tagged.format_tag == Some(*b"bi"), "tagged");
    let short_tagged = moment.get_cursor("short-tagged")?.unwrap().read_bytes_object(None)?;
    check(&*short_tagged.value == b"hi" && short_tagged.format_tag == Some(*b"st"), "short-tagged");
    check(moment.get_cursor("long")?.unwrap().read_bytes(None)? == long_bytes(), "long");

    let set = ReadHashSet::new(moment.get_cursor("set")?.unwrap())?;
    check(set.contains("a")? && set.contains("c")? && !set.contains("d")?, "set");
    let counted = ReadCountedHashMap::new(moment.get_cursor("counted")?.unwrap())?;
    check(counted.get_cursor("y")?.unwrap().read_uint()? == 2, "counted y");

    let sorted_set = ReadSortedSet::new(moment.get_cursor("sorted-set")?.unwrap())?;
    let mut keys = Vec::new();
    for kv in sorted_set.iter()? {
        keys.push(string(Some(kv?.read_key_value_pair()?.key_cursor))?);
    }
    check(keys == ["alpha", "mid", "zeta"], "sorted set order");
    Ok(())
}

fn verify(path: &str) -> Result<()> {
    let db = open(path, false)?;
    let history = ReadArrayList::new(db.root_cursor())?;
    check(history.count()? == 2, "two moments");

    // moment 0 is unchanged by the go transaction
    let moment0 = ReadHashMap::new(history.get_cursor(0)?.unwrap())?;
    check_rust_moment(&moment0)?;
    check(moment0.get_cursor("from-go")?.is_none(), "moment 0 has no go key");
    let list0 = ReadArrayList::new(moment0.get_cursor("list")?.unwrap())?;
    check(list0.count()? == 300, "moment 0 list count");
    let sorted0 = ReadSortedMap::new(moment0.get_cursor("sorted")?.unwrap())?;
    check(sorted0.count()? == 99 && sorted0.get_cursor("k050")?.is_none(), "moment 0 sorted");
    let counted0 = ReadCountedHashMap::new(moment0.get_cursor("counted")?.unwrap())?;
    check(counted0.count()? == 2, "moment 0 counted count");

    // moment 1 was written by go
    let moment1 = ReadHashMap::new(history.get_cursor(1)?.unwrap())?;
    check_rust_moment(&moment1)?;
    check(string(moment1.get_cursor("from-go")?)? == "hello from go", "from-go");
    let list1 = ReadArrayList::new(moment1.get_cursor("list")?.unwrap())?;
    check(list1.count()? == 301, "list count");
    for (i, item) in list1.iter()?.enumerate() {
        check(item?.read_uint()? == i as u64, "list item");
    }
    let sorted1 = ReadSortedMap::new(moment1.get_cursor("sorted")?.unwrap())?;
    check(sorted1.count()? == 100, "sorted count");
    for (i, kv) in sorted1.iter()?.enumerate() {
        let kv = kv?.read_key_value_pair()?;
        check(string(Some(kv.key_cursor))? == format!("k{i:03}"), "sorted key");
        check(kv.value_cursor.read_uint()? == i as u64, "sorted value");
    }
    let linked1 = ReadLinkedArrayList::new(moment1.get_cursor("linked")?.unwrap())?;
    check(linked1.count()? == 101, "linked count");
    check(string(linked1.get_cursor(0)?)? == "item-1", "linked first");
    check(string(linked1.get_cursor(49)?)? == "inserted", "linked inserted");
    check(string(linked1.get_cursor(-1)?)? == "go-item", "linked last");
    let counted1 = ReadCountedHashMap::new(moment1.get_cursor("counted")?.unwrap())?;
    check(counted1.count()? == 3, "counted count after go");
    println!("rust: verified the moment go appended to {path}");
    Ok(())
}

fn compact(path: &str, target: &str) -> Result<()> {
    let db = open(path, false)?;
    let target_file = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(target)?;
    let compacted = db.compact(CoreBufferedFile::new(target_file), &mut MemoryOffsetMap::new())?;
    compacted.core().flush()?;
    let source_len = File::open(path)?.metadata()?.len();
    let target_len = File::open(target)?.metadata()?.len();
    println!("rust: compacted {path} ({source_len} bytes) into {target} ({target_len} bytes)");
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        ["write", path] => write(path),
        ["verify", path] => verify(path),
        ["compact", path, target] => compact(path, target),
        _ => {
            eprintln!("usage: interop write <path> | verify <path> | compact <path> <target>");
            std::process::exit(2);
        }
    }
}
