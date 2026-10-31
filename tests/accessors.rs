//! Tests for the convenience accessors: `put_map`/`put_set`/`put_list`,
//! `append_map`/`append_set`/`append_list`, the typed getters on
//! `ReadHashMap`, `ReadCursor::read_string`, and `entries`/`keys`.

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

fn memory_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
}

fn assert_unexpected_tag<T>(result: Result<T>) {
    match result {
        Err(Error::UnexpectedTag) => {}
        Err(err) => panic!("expected UnexpectedTag, got {err:?}"),
        Ok(_) => panic!("expected UnexpectedTag, got Ok"),
    }
}

#[test]
fn nested_put_map_round_trips() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put_map("merges")?.put_map("https://example.com")?.put("status", "done")?;
        let mut tags = moment.put_set("tags")?;
        tags.put("a")?;
        tags.put("b")?;
        let mut items = moment.put_list("items")?;
        items.append(1u64)?;
        items.append(2u64)?;
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    let merges = moment.get_map("merges").unwrap().unwrap();
    let merge = merges.get_map("https://example.com").unwrap().unwrap();
    assert_eq!(merge.get_string("status", MAX_READ).unwrap().as_deref(), Some("done"));
    let tags = moment.get_set("tags").unwrap().unwrap();
    assert!(tags.contains("a").unwrap() && tags.contains("b").unwrap());
    let items = moment.get_list("items").unwrap().unwrap();
    assert_eq!(items.count().unwrap(), 2);
    assert_eq!(items.get_cursor(1).unwrap().unwrap().read_uint().unwrap(), 2);
}

#[test]
fn put_map_keeps_existing_contents() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put_map("inner")?.put("a", 1u64)?;
        moment.put_map("inner")?.put("b", 2u64)?;
        moment.put_set("set")?.put("x")?;
        moment.put_set("set")?.put("y")?;
        moment.put_list("list")?.append(1u64)?;
        moment.put_list("list")?.append(2u64)?;
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    let inner = moment.get_map("inner").unwrap().unwrap();
    assert_eq!(inner.get_uint("a").unwrap(), Some(1));
    assert_eq!(inner.get_uint("b").unwrap(), Some(2));
    let set = moment.get_set("set").unwrap().unwrap();
    assert!(set.contains("x").unwrap() && set.contains("y").unwrap());
    assert_eq!(moment.get_list("list").unwrap().unwrap().count().unwrap(), 2);

    // the existing map is kept in a later transaction too
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put_map("inner")?.put("c", 3u64)?;
        Ok(())
    })
    .unwrap();
    let inner = ReadHashMap::new(db.root_cursor()).unwrap().get_map("inner").unwrap().unwrap();
    assert_eq!(inner.get_uint("a").unwrap(), Some(1));
    assert_eq!(inner.get_uint("c").unwrap(), Some(3));
}

#[test]
fn put_map_on_wrong_tag() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("string", "hello")?;
        moment.put("int", 1i64)?;
        moment.put_list("list")?;
        moment.put_map("map")?.put("a", 1u64)?;
        moment.put_set("set")?.put("x")?;
        WriteCountedHashMap::new(&mut moment.put_cursor("counted-map")?)?;
        WriteCountedHashSet::new(&mut moment.put_cursor("counted-set")?)?;
        assert_unexpected_tag(moment.put_map("string"));
        assert_unexpected_tag(moment.put_set("int"));
        assert_unexpected_tag(moment.put_list("string"));
        assert_unexpected_tag(moment.put_map("list"));
        // a map and a set aren't opened as each other, and counted
        // collections aren't opened as plain ones
        assert_unexpected_tag(moment.put_set("map"));
        assert_unexpected_tag(moment.put_map("set"));
        assert_unexpected_tag(moment.put_map("counted-map"));
        assert_unexpected_tag(moment.put_set("counted-set"));
        Ok(())
    })
    .unwrap();

    // nothing was changed by the failed calls
    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    assert_eq!(moment.get_slot("map").unwrap().unwrap().tag, Tag::HashMap);
    assert_eq!(moment.get_map("map").unwrap().unwrap().get_uint("a").unwrap(), Some(1));
    assert_eq!(moment.get_slot("set").unwrap().unwrap().tag, Tag::HashSet);
    assert!(moment.get_set("set").unwrap().unwrap().contains("x").unwrap());
    assert_eq!(moment.get_slot("counted-map").unwrap().unwrap().tag, Tag::CountedHashMap);
    assert_eq!(moment.get_string("string", MAX_READ).unwrap().as_deref(), Some("hello"));

    // counted collections are read with ReadCountedHashMap/Set, not get_map/get_set
    assert_unexpected_tag(moment.get_map("counted-map"));
    assert_unexpected_tag(moment.get_set("counted-set"));
    assert!(ReadCountedHashMap::new(moment.get_cursor("counted-map").unwrap().unwrap()).is_ok());
}

#[test]
fn put_map_on_top_level_map_writes_nothing() {
    // the returned map would belong to an already finished transaction, so
    // put_map needs one to be running, and fails before writing anything
    let db = memory_db();
    let mut moment = WriteHashMap::new(&mut db.root_cursor()).unwrap();
    moment.put("foo", "bar").unwrap();
    let size = db.core().length().unwrap();
    for _ in 0..2 {
        assert!(matches!(moment.put_map("inner"), Err(Error::ExpectedTxStart)));
        assert!(matches!(moment.put_set("inner"), Err(Error::ExpectedTxStart)));
        assert!(matches!(moment.put_list("inner"), Err(Error::ExpectedTxStart)));
    }
    assert_eq!(db.core().length().unwrap(), size);
    assert!(moment.get_cursor("inner").unwrap().is_none());
    assert!(moment.get_map("inner").unwrap().is_none());

    // inside a transaction it works, in the same top-level map
    db.run_context(|cursor| {
        WriteHashMap::new(cursor)?.put_map("inner")?.put("a", 1u64)?;
        Ok(())
    })
    .unwrap();
    let inner = moment.get_map("inner").unwrap().unwrap();
    assert_eq!(inner.get_uint("a").unwrap(), Some(1));
}

#[test]
fn append_map_on_top_level_list_writes_nothing() {
    let db = memory_db();
    let mut list = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    list.append(Data::None).unwrap();
    let size = db.core().length().unwrap();
    for _ in 0..2 {
        assert!(matches!(list.append_map(), Err(Error::ExpectedTxStart)));
        assert!(matches!(list.append_set(), Err(Error::ExpectedTxStart)));
        assert!(matches!(list.append_list(), Err(Error::ExpectedTxStart)));
        assert!(matches!(list.put_map(0), Err(Error::ExpectedTxStart)));
        assert!(matches!(list.put_set(0), Err(Error::ExpectedTxStart)));
        assert!(matches!(list.put_list(0), Err(Error::ExpectedTxStart)));
    }
    assert_eq!(db.core().length().unwrap(), size);
    assert_eq!(list.count().unwrap(), 1);
    assert_eq!(list.get_slot(0).unwrap().unwrap().tag, Tag::None);

    // inside a transaction (here, the usual history pattern) it works
    list.append_context(None, |cursor| {
        WriteHashMap::new(cursor)?.put_list("items")?.append_map()?.put("a", 1u64)?;
        Ok(())
    })
    .unwrap();
    let moment = ReadHashMap::new(list.get_cursor(-1).unwrap().unwrap()).unwrap();
    let items = moment.get_list("items").unwrap().unwrap();
    let item = ReadHashMap::new(items.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(item.get_uint("a").unwrap(), Some(1));
}

#[test]
fn empty_values_read_as_absent() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("empty", Data::None)?;
        moment.put("empty-map", Data::None)?;
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    // the key is there, with an empty value
    assert_eq!(moment.get_slot("empty").unwrap().unwrap().tag, Tag::None);
    assert!(moment.get_map("empty").unwrap().is_none());
    assert!(moment.get_set("empty").unwrap().is_none());
    assert!(moment.get_list("empty").unwrap().is_none());
    assert_eq!(moment.get_bytes("empty", MAX_READ).unwrap(), None);
    assert_eq!(moment.get_string("empty", MAX_READ).unwrap(), None);
    assert_eq!(moment.get_int("empty").unwrap(), None);
    assert_eq!(moment.get_uint("empty").unwrap(), None);
    assert_eq!(moment.get_float("empty").unwrap(), None);

    // put_map initializes an empty value
    db.run_context(|cursor| {
        WriteHashMap::new(cursor)?.put_map("empty-map")?.put("a", 1u64)?;
        Ok(())
    })
    .unwrap();
    let map = moment.get_map("empty-map").unwrap().unwrap();
    assert_eq!(map.get_uint("a").unwrap(), Some(1));
}

#[test]
fn array_list_put_and_append_collections() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut list = WriteArrayList::new(cursor)?;
        list.append_map()?.put("name", "Alice")?;
        list.append_set()?.put("x")?;
        list.append_list()?.append(1u64)?;
        list.append(Data::None)?;

        // put_* keeps an existing collection and initializes an empty slot
        list.put_map(0)?.put("age", 25u64)?;
        list.put_set(1)?.put("y")?;
        list.put_list(2)?.append(2u64)?;
        list.put_map(3)?.put("name", "Bob")?;

        assert_unexpected_tag(list.put_list(0));
        assert_unexpected_tag(list.put_set(2));
        assert!(matches!(list.put_map(10), Err(Error::KeyNotFound)));
        Ok(())
    })
    .unwrap();

    let list = ReadArrayList::new(db.root_cursor()).unwrap();
    let alice = ReadHashMap::new(list.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(alice.get_string("name", MAX_READ).unwrap().as_deref(), Some("Alice"));
    assert_eq!(alice.get_uint("age").unwrap(), Some(25));
    let set = ReadHashSet::new(list.get_cursor(1).unwrap().unwrap()).unwrap();
    assert!(set.contains("x").unwrap() && set.contains("y").unwrap());
    let inner = ReadArrayList::new(list.get_cursor(2).unwrap().unwrap()).unwrap();
    assert_eq!(inner.count().unwrap(), 2);
    let bob = ReadHashMap::new(list.get_cursor(3).unwrap().unwrap()).unwrap();
    assert_eq!(bob.get_string("name", MAX_READ).unwrap().as_deref(), Some("Bob"));
}

#[test]
fn typed_getters() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("bytes", &[0u8, 1, 2][..])?;
        moment.put("string", "héllo")?;
        moment.put("long-string", "a".repeat(100))?;
        moment.put("int", -5i64)?;
        moment.put("uint", 5u64)?;
        moment.put("float", 1.5f64)?;
        moment.put_map("map")?;

        // reads through a WriteHashMap work too, via Deref
        assert_eq!(moment.get_int("int")?, Some(-5));
        assert_eq!(moment.get_string("string", MAX_READ)?.as_deref(), Some("héllo"));
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    assert_eq!(moment.get_bytes("bytes", MAX_READ).unwrap(), Some(vec![0, 1, 2]));
    assert_eq!(moment.get_string("string", MAX_READ).unwrap().as_deref(), Some("héllo"));
    assert_eq!(moment.get_string("long-string", MAX_READ).unwrap(), Some("a".repeat(100)));
    assert_eq!(moment.get_int("int").unwrap(), Some(-5));
    assert_eq!(moment.get_uint("uint").unwrap(), Some(5));
    assert_eq!(moment.get_float("float").unwrap(), Some(1.5));

    // absent keys
    assert!(moment.get_map("missing").unwrap().is_none());
    assert!(moment.get_set("missing").unwrap().is_none());
    assert!(moment.get_list("missing").unwrap().is_none());
    assert_eq!(moment.get_bytes("missing", MAX_READ).unwrap(), None);
    assert_eq!(moment.get_string("missing", MAX_READ).unwrap(), None);
    assert_eq!(moment.get_int("missing").unwrap(), None);
    assert_eq!(moment.get_uint("missing").unwrap(), None);
    assert_eq!(moment.get_float("missing").unwrap(), None);

    // wrong tags
    assert_unexpected_tag(moment.get_map("string"));
    assert_unexpected_tag(moment.get_set("int"));
    assert_unexpected_tag(moment.get_list("map"));
    assert_unexpected_tag(moment.get_bytes("int", MAX_READ));
    assert_unexpected_tag(moment.get_string("map", MAX_READ));
    assert_unexpected_tag(moment.get_int("uint"));
    assert_unexpected_tag(moment.get_uint("int"));
    assert_unexpected_tag(moment.get_float("string"));

    // max size
    assert!(matches!(moment.get_bytes("long-string", Some(10)), Err(Error::StreamTooLong)));
    assert!(matches!(moment.get_string("long-string", Some(10)), Err(Error::StreamTooLong)));
}

#[test]
fn read_string_rejects_invalid_utf8() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("short", &[0xffu8, 0xfe][..])?;
        moment.put("long", [b'a'; 20].iter().chain(&[0xffu8]).copied().collect::<Vec<u8>>())?;
        moment.put("empty", Data::None)?;
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    for key in ["short", "long"] {
        let err = moment.get_string(key, MAX_READ).expect_err("expected an error");
        assert!(matches!(err, Error::InvalidUtf8(_)), "unexpected error: {err:?}");
        assert!(std::error::Error::source(&err).is_some());
        let err = moment.get_cursor(key).unwrap().unwrap().read_string(None).expect_err("expected an error");
        assert!(matches!(err, Error::InvalidUtf8(_)), "unexpected error: {err:?}");
    }
    // the bytes are still readable as bytes
    assert_eq!(moment.get_bytes("short", MAX_READ).unwrap(), Some(vec![0xff, 0xfe]));
    // read_string on an empty slot reads an empty string, like read_bytes
    assert_eq!(moment.get_cursor("empty").unwrap().unwrap().read_string(MAX_READ).unwrap(), "");
}

#[test]
fn hash_map_entries() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("a", 1u64)?;
        moment.put("b", 2u64)?;
        moment.put("c", 3u64)?;
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    let mut entries = moment
        .entries()
        .unwrap()
        .map(|kv| {
            let kv = kv?;
            Ok((kv.key_cursor.read_string(MAX_READ)?, kv.value_cursor.read_uint()?))
        })
        .collect::<Result<Vec<_>>>()
        .unwrap();
    entries.sort();
    assert_eq!(entries, [("a".to_string(), 1), ("b".to_string(), 2), ("c".to_string(), 3)]);

    // entries yields the same pairs as iter + read_key_value_pair
    assert_eq!(moment.entries().unwrap().count(), moment.iter().unwrap().count());

    // an empty map
    let db = memory_db();
    db.run_context(|cursor| {
        WriteArrayList::new(cursor)?.append_map()?;
        Ok(())
    })
    .unwrap();
    let list = ReadArrayList::new(db.root_cursor()).unwrap();
    let empty = ReadHashMap::new(list.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(empty.entries().unwrap().count(), 0);
}

#[test]
fn hash_set_keys() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut set = WriteHashSet::new(cursor)?;
        set.put("x")?;
        set.put("y")?;
        Ok(())
    })
    .unwrap();

    let set = ReadHashSet::new(db.root_cursor()).unwrap();
    let mut keys = set.keys().unwrap().map(|key| key?.read_string(MAX_READ)).collect::<Result<Vec<_>>>().unwrap();
    keys.sort();
    assert_eq!(keys, ["x", "y"]);

    // counted sets get keys through Deref
    let db = memory_db();
    db.run_context(|cursor| {
        let mut set = WriteCountedHashSet::new(cursor)?;
        set.put("z")?;
        Ok(())
    })
    .unwrap();
    let set = ReadCountedHashSet::new(db.root_cursor()).unwrap();
    let keys = set.keys().unwrap().map(|key| key?.read_string(MAX_READ)).collect::<Result<Vec<_>>>().unwrap();
    assert_eq!(keys, ["z"]);
}

#[test]
fn sorted_entries_and_keys() {
    let db = memory_db();
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        let mut map = WriteSortedMap::new(&mut moment.put_cursor("map")?)?;
        map.put("b", 2u64)?;
        map.put("a", 1u64)?;
        let mut set = WriteSortedSet::new(&mut moment.put_cursor("set")?)?;
        set.put("y")?;
        set.put("x")?;
        Ok(())
    })
    .unwrap();

    let moment = ReadHashMap::new(db.root_cursor()).unwrap();
    let map = ReadSortedMap::new(moment.get_cursor("map").unwrap().unwrap()).unwrap();
    let entries = map
        .entries()
        .unwrap()
        .map(|kv| {
            let kv = kv?;
            Ok((kv.key_cursor.read_string(MAX_READ)?, kv.value_cursor.read_uint()?))
        })
        .collect::<Result<Vec<_>>>()
        .unwrap();
    assert_eq!(entries, [("a".to_string(), 1), ("b".to_string(), 2)]);

    let set = ReadSortedSet::new(moment.get_cursor("set").unwrap().unwrap()).unwrap();
    let keys = set.keys().unwrap().map(|key| key?.read_string(MAX_READ)).collect::<Result<Vec<_>>>().unwrap();
    assert_eq!(keys, ["x", "y"]);
}
