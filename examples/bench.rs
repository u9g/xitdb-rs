//! A rough benchmark: writes and reads a large hash map, array list and
//! sorted map in a file-backed database.
//!
//! Run with `cargo run --release --example bench`.

use std::time::Instant;

use xitdb::*;

const COUNT: u64 = 100_000;

fn main() -> Result<()> {
    let dir = std::env::temp_dir().join(format!("xitdb-bench-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    let path = dir.join("bench.db");
    let file = std::fs::OpenOptions::new().read(true).write(true).create(true).truncate(true).open(&path)?;
    let db = Database::new(CoreBufferedFile::new(file), Hasher::sha1())?;

    let start = Instant::now();
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append_context(None, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        let step = Instant::now();
        let mut map = WriteHashMap::new(&mut moment.put_cursor("map")?)?;
        for i in 0..COUNT {
            map.put(format!("key-{i}"), i)?;
        }
        println!("  hash map puts: {:?}", step.elapsed());
        let step = Instant::now();
        let mut list = WriteArrayList::new(&mut moment.put_cursor("list")?)?;
        for i in 0..COUNT {
            list.append(i)?;
        }
        println!("  array list appends: {:?}", step.elapsed());
        let step = Instant::now();
        let mut sorted = WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?;
        for i in 0..COUNT {
            sorted.put(format!("key-{:08}", (i * 7919) % COUNT), i)?;
        }
        println!("  sorted map puts: {:?}", step.elapsed());
        Ok(())
    })?;
    println!("write {COUNT} items x 3 structures: {:?}", start.elapsed());

    let start = Instant::now();
    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
    let map = ReadHashMap::new(moment.get_cursor("map")?.unwrap())?;
    for i in 0..COUNT {
        assert_eq!(map.get_cursor(format!("key-{i}"))?.unwrap().read_uint()?, i);
    }
    println!("hash map lookups: {:?}", start.elapsed());

    let start = Instant::now();
    let list = ReadArrayList::new(moment.get_cursor("list")?.unwrap())?;
    let mut sum = 0;
    for item in list.iter()? {
        sum += item?.read_uint()?;
    }
    assert_eq!(sum, COUNT * (COUNT - 1) / 2);
    println!("array list iteration: {:?}", start.elapsed());

    let start = Instant::now();
    let sorted = ReadSortedMap::new(moment.get_cursor("sorted")?.unwrap())?;
    assert_eq!(sorted.count()?, COUNT as i64);
    let mut previous = Vec::new();
    for kv in sorted.entries()? {
        let key = kv?.key_cursor.read_bytes(None)?;
        assert!(key > previous);
        previous = key;
    }
    println!("sorted map ordered iteration: {:?}", start.elapsed());

    drop(db.into_core().close()?);
    println!("file size: {} bytes", std::fs::metadata(&path)?.len());
    std::fs::remove_dir_all(&dir)?;
    Ok(())
}
