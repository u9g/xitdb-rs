//! Tests for writes that are skipped when they wouldn't change anything:
//! `put_if_changed`, `put_path_if_changed`, `write_if_changed` and
//! `ReadCursor::equals`.

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

fn new_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
}

// the length of the file, which grows with every write in a transaction
fn len(db: &Database<CoreMemory>) -> u64 {
    db.core().length().unwrap()
}

/// Commits `stored` at "key", then puts `data` there with `put_if_changed`
/// in a second transaction. Returns whether it wrote and whether the
/// second transaction committed, after checking that a skipped put wrote
/// nothing at all.
fn put_after(stored: Data<'_>, data: Data<'_>) -> (bool, bool) {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("key", stored)).unwrap();
    let (wrote, committed) = history
        .transact_with_status(|moment| {
            let before = len(&db);
            let wrote = moment.put_if_changed("key", data)?;
            if !wrote {
                assert_eq!(len(&db), before, "a skipped put wrote something");
            }
            Ok::<_, Error>(wrote)
        })
        .unwrap();
    assert_eq!(history.count().unwrap(), if committed { 2 } else { 1 });
    (wrote, committed)
}

fn unchanged(stored: Data<'_>, data: Data<'_>) {
    let desc = format!("{stored:?} then {data:?}");
    assert_eq!(put_after(stored, data), (false, false), "{desc}");
}

fn changed(stored: Data<'_>, data: Data<'_>) {
    let desc = format!("{stored:?} then {data:?}");
    assert_eq!(put_after(stored, data), (true, true), "{desc}");
}

fn long(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8 + 1).collect()
}

#[test]
fn inline_values() {
    unchanged(Data::Uint(5), Data::Uint(5));
    changed(Data::Uint(5), Data::Uint(6));
    unchanged(Data::Uint(u64::MAX), Data::Uint(u64::MAX));
    unchanged(Data::Int(-5), Data::Int(-5));
    changed(Data::Int(-5), Data::Int(5));
    unchanged(Data::Float(1.5), Data::Float(1.5));
    changed(Data::Float(1.5), Data::Float(2.5));
    unchanged("abc".into(), "abc".into());
    changed("abc".into(), "abd".into());
    changed("abc".into(), "ab".into());
    unchanged(Data::tagged_string("abc", *b"st"), Data::tagged_string("abc", *b"st"));
    changed(Data::tagged_string("abc", *b"st"), Data::tagged_string("abc", *b"sx"));
}

#[test]
fn floats_compare_by_bits() {
    changed(Data::Float(0.0), Data::Float(-0.0));
    unchanged(Data::Float(f64::NAN), Data::Float(f64::NAN));
    unchanged(Data::Float(f64::INFINITY), Data::Float(f64::INFINITY));
}

#[test]
fn different_types_are_never_equal() {
    changed(Data::Int(1), Data::Uint(1));
    changed(Data::Uint(1), Data::Int(1));
    // the same bits as a different type
    changed(Data::Uint(1.5f64.to_bits()), Data::Float(1.5));
    changed(Data::Uint(0), "".into());
    // a format tag makes it different
    changed("abc".into(), Data::tagged_string("abc", *b"st"));
    changed(Data::tagged_string("abc", *b"st"), "abc".into());
    changed(Data::bytes(long(100)), Data::tagged_bytes(long(100), *b"st"));
    changed(Data::tagged_bytes(long(100), *b"st"), Data::bytes(long(100)));
    // short and long bytes
    changed("abc".into(), Data::bytes(long(100)));
    changed(Data::bytes(long(100)), "abc".into());
    changed(Data::Uint(1), Data::bytes(long(100)));
}

#[test]
fn none_and_empty_bytes() {
    unchanged(Data::None, Data::None);
    unchanged("".into(), "".into());
    changed(Data::None, "".into());
    changed("".into(), Data::None);
    changed(Data::None, Data::Uint(0));
    changed(Data::Uint(0), Data::None);
}

#[test]
fn missing_keys_are_always_changed() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("other", 1u64)).unwrap();

    for data in [Data::None, "".into(), Data::Uint(0), Data::bytes(long(100))] {
        let mut wrote = false;
        let result = history.transact(|moment| {
            wrote = moment.put_if_changed("missing", data.clone())?;
            // the key is there now, even for Data::None
            assert!(moment.get_cursor("missing")?.is_some());
            // discard it, to try the next one
            Err::<(), _>(Error::KeyNotFound)
        });
        assert!(matches!(result, Err(Error::KeyNotFound)));
        assert!(wrote, "{data:?}");
    }
    assert_eq!(history.count().unwrap(), 1);

    // and adding it commits
    let (wrote, committed) = history.transact_with_status(|moment| moment.put_if_changed("missing", Data::None)).unwrap();
    assert!(wrote && committed);
    let (wrote, committed) = history.transact_with_status(|moment| moment.put_if_changed("missing", Data::None)).unwrap();
    assert!(!wrote && !committed);
}

#[test]
fn long_bytes() {
    // longer than the chunks the comparison reads
    let value = long(10_000);
    unchanged(Data::bytes(value.clone()), Data::bytes(value.clone()));
    unchanged(Data::tagged_bytes(value.clone(), *b"bi"), Data::tagged_bytes(value.clone(), *b"bi"));
    changed(Data::tagged_bytes(value.clone(), *b"bi"), Data::tagged_bytes(value.clone(), *b"bj"));

    // differing only in the last byte, or the first
    let mut last = value.clone();
    *last.last_mut().unwrap() += 1;
    changed(Data::bytes(value.clone()), Data::bytes(last.clone()));
    changed(Data::tagged_bytes(value.clone(), *b"bi"), Data::tagged_bytes(last, *b"bi"));
    let mut first = value.clone();
    first[0] += 1;
    changed(Data::bytes(value.clone()), Data::bytes(first));

    // a prefix, or one more byte
    changed(Data::bytes(value.clone()), Data::bytes(value[..9_999].to_vec()));
    let mut longer = value.clone();
    longer.push(1);
    changed(Data::bytes(value.clone()), Data::bytes(longer));

    // just long enough not to be short bytes
    unchanged(Data::bytes(long(9)), Data::bytes(long(9)));
    unchanged(Data::bytes(&b"with\0zero"[..]), Data::bytes(&b"with\0zero"[..]));
    changed(Data::bytes(&b"with\0zero"[..]), Data::bytes(&b"with\0zerp"[..]));
}

#[test]
fn bytes_written_long_differ_from_short_data() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            let mut cursor = moment.put_cursor("key")?;
            let mut writer = cursor.writer()?;
            std::io::Write::write_all(&mut writer, b"abc")?;
            writer.finish()
        })
        .unwrap();
    assert_eq!(history.latest().unwrap().get_slot("key").unwrap().unwrap().tag, Tag::Bytes);

    // the same contents, but writing them stores short bytes instead
    let (wrote, committed) = history.transact_with_status(|moment| moment.put_if_changed("key", "abc")).unwrap();
    assert!(wrote && committed);
    assert_eq!(history.latest().unwrap().get_slot("key").unwrap().unwrap().tag, Tag::ShortBytes);
}

#[test]
fn slots_compare_the_slot_itself() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            moment.put_map("a")?.put("x", 1u64)?;
            moment.put_map("b")?.put("x", 1u64)
        })
        .unwrap();
    let latest = history.latest().unwrap();
    let a = latest.get_slot("a").unwrap().unwrap();
    let b = latest.get_slot("b").unwrap().unwrap();

    let (wrote, committed) = history.transact_with_status(|moment| moment.put_if_changed("a", a)).unwrap();
    assert!(!wrote && !committed);
    // a map with the same contents somewhere else isn't the same slot
    let (wrote, committed) = history.transact_with_status(|moment| moment.put_if_changed("a", b)).unwrap();
    assert!(wrote && committed);
    assert_eq!(history.latest().unwrap().get_slot("a").unwrap().unwrap(), b);

    // an empty slot is written as one marked as written, like Data::None
    unchanged(Data::None, Data::Slot(Slot::default()));
    changed(Data::Uint(1), Data::Slot(Slot::new(1, Tag::Int)));
    unchanged(Data::Uint(1), Data::Slot(Slot::new(1, Tag::Uint)));
}

#[test]
fn history_skips_unchanged_top_level_puts() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            moment.put("status", "idle")?;
            moment.put("question", 3u64)?;
            moment.put("body", Data::bytes(long(5_000)))
        })
        .unwrap();
    let size = db.committed_size().unwrap();

    // a watcher refreshing everything with the same values
    for _ in 0..3 {
        let (wrote, committed) = history
            .transact_with_status(|moment| {
                let mut wrote = moment.put_if_changed("status", "idle")?;
                wrote |= moment.put_if_changed("question", 3u64)?;
                wrote |= moment.put_if_changed("body", Data::bytes(long(5_000)))?;
                Ok::<_, Error>(wrote)
            })
            .unwrap();
        assert!(!wrote && !committed);
    }
    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(db.committed_size().unwrap(), size);

    // one changed value commits
    let (wrote, committed) = history
        .transact_with_status(|moment| {
            let mut wrote = moment.put_if_changed("status", "busy")?;
            wrote |= moment.put_if_changed("question", 3u64)?;
            Ok::<_, Error>(wrote)
        })
        .unwrap();
    assert!(wrote && committed);
    assert_eq!(history.count().unwrap(), 2);
    let latest = history.latest().unwrap();
    assert_eq!(latest.get_string("status", MAX_READ).unwrap().unwrap(), "busy");
    assert_eq!(latest.get_uint("question").unwrap().unwrap(), 3);

    // whereas a plain put of the same value commits
    let (_, committed) = history.transact_with_status(|moment| moment.put("question", 3u64)).unwrap();
    assert!(committed);
}

#[test]
fn history_skips_unchanged_nested_puts() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let url = "https://example.com/pr/1";
    history
        .transact(|moment| {
            let mut merge = moment.put_map("merges")?.put_map(url)?;
            merge.put("question", 3u64)?;
            merge.put("thread_id", "t1")
        })
        .unwrap();

    let (wrote, committed) =
        history.transact_with_status(|moment| moment.put_path_if_changed(&["merges", url, "question"], 3u64)).unwrap();
    assert!(!wrote && !committed);
    assert_eq!(history.count().unwrap(), 1);

    // getting the nested map for writing copies the path to it, so this
    // commits even though the value is the same
    let (wrote, committed) = history
        .transact_with_status(|moment| moment.put_map("merges")?.put_map(url)?.put_if_changed("question", 3u64))
        .unwrap();
    assert!(!wrote && committed);
    assert_eq!(history.count().unwrap(), 2);

    let (wrote, committed) =
        history.transact_with_status(|moment| moment.put_path_if_changed(&["merges", url, "question"], 4u64)).unwrap();
    assert!(wrote && committed);
    let latest = history.latest().unwrap();
    let merge = latest.get_map("merges").unwrap().unwrap().get_map(url).unwrap().unwrap();
    assert_eq!(merge.get_uint("question").unwrap().unwrap(), 4);
    // the rest of the nested map is untouched
    assert_eq!(merge.get_string("thread_id", MAX_READ).unwrap().unwrap(), "t1");

    // a path through maps that don't exist yet creates them
    let (wrote, committed) = history
        .transact_with_status(|moment| moment.put_path_if_changed(&["merges", "https://example.com/pr/2", "question"], 1u64))
        .unwrap();
    assert!(wrote && committed);
    let latest = history.latest().unwrap();
    let merges = latest.get_map("merges").unwrap().unwrap();
    assert_eq!(merges.get_map("https://example.com/pr/2").unwrap().unwrap().get_uint("question").unwrap(), Some(1));

    // and then it's unchanged
    let (wrote, committed) = history
        .transact_with_status(|moment| moment.put_path_if_changed(&["merges", "https://example.com/pr/2", "question"], 1u64))
        .unwrap();
    assert!(!wrote && !committed);
}

#[test]
fn nested_puts_in_many_maps() {
    // the watcher pattern: refresh a field in every nested map, where only
    // some of them differ
    let db = new_db();
    let history = History::new(&db).unwrap();
    let urls: Vec<String> = (0..20).map(|i| format!("https://example.com/pr/{i}")).collect();
    history
        .transact(|moment| {
            let mut merges = moment.put_map("merges")?;
            for url in &urls {
                merges.put_map(url)?.put("question", 1u64)?;
            }
            Ok::<_, Error>(())
        })
        .unwrap();

    let refresh = |question: &dyn Fn(usize) -> u64| {
        history
            .transact_with_status(|moment| {
                let mut wrote = 0;
                for (i, url) in urls.iter().enumerate() {
                    wrote += moment.put_path_if_changed(&["merges", url.as_str(), "question"], question(i))? as usize;
                }
                Ok::<_, Error>(wrote)
            })
            .unwrap()
    };
    assert_eq!(refresh(&|_| 1), (0, false));
    assert_eq!(refresh(&|i| if i == 7 { 2 } else { 1 }), (1, true));
    assert_eq!(refresh(&|i| if i == 7 { 2 } else { 1 }), (0, false));
    assert_eq!(history.count().unwrap(), 2);
}

#[test]
fn put_path_if_changed_checks_the_path() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            moment.put("number", 1u64)?;
            moment.put("empty", Data::None)?;
            moment.put_set("set")?.put("x")
        })
        .unwrap();

    // a value along the path that isn't a map
    for path in [["number", "key"], ["set", "key"]] {
        let result = history.transact_with_status(|moment| moment.put_path_if_changed(&path, 1u64));
        assert!(matches!(result, Err(Error::UnexpectedTag)), "{path:?}: {result:?}");
    }
    let result = history.transact_with_status(|moment| moment.put_path_if_changed::<&str>(&[], 1u64));
    assert!(matches!(result, Err(Error::KeyNotFound)), "{result:?}");
    assert_eq!(history.count().unwrap(), 1);

    // an empty value along the path becomes a map, as with put_map
    let (wrote, committed) =
        history.transact_with_status(|moment| moment.put_path_if_changed(&["empty", "key"], 1u64)).unwrap();
    assert!(wrote && committed);
    let latest = history.latest().unwrap();
    assert_eq!(latest.get_map("empty").unwrap().unwrap().get_uint("key").unwrap(), Some(1));

    // a path of just a key is put_if_changed
    let (wrote, committed) = history.transact_with_status(|moment| moment.put_path_if_changed(&["number"], 1u64)).unwrap();
    assert!(!wrote && !committed);
    let (wrote, committed) = history.transact_with_status(|moment| moment.put_path_if_changed(&["number"], 2u64)).unwrap();
    assert!(wrote && committed);
    assert_eq!(history.latest().unwrap().get_uint("number").unwrap(), Some(2));
}

#[test]
fn unwritten_keys_and_values_are_changed() {
    let db = new_db();
    db.run_context(|root| {
        let mut map = WriteHashMap::new(root)?;

        // a value whose key was never stored: a put stores the key
        let hash = db.digest(b"no-key");
        map.put_cursor_by_hash(&hash)?.write(1u64)?;
        assert!(map.get_key_cursor("no-key")?.is_none());
        assert!(map.put_if_changed("no-key", 1u64)?);
        assert_eq!(map.get_key_cursor("no-key")?.unwrap().read_bytes(MAX_READ)?, b"no-key");
        assert!(!map.put_if_changed("no-key", 1u64)?);

        // a key whose value was never written isn't Data::None
        map.put_cursor("no-value")?;
        assert!(map.put_if_changed("no-value", Data::None)?);
        assert!(!map.put_if_changed("no-value", Data::None)?);
        Ok(())
    })
    .unwrap();
}

#[test]
fn counted_maps() {
    let db = new_db();
    db.run_context(|root| {
        let mut map = WriteCountedHashMap::new(root)?;
        assert!(map.put_if_changed("a", 1u64)?);
        assert!(!map.put_if_changed("a", 1u64)?);
        assert!(map.put_if_changed("a", 2u64)?);
        assert!(map.put_if_changed("b", 2u64)?);
        assert_eq!(map.count()?, 2);
        Ok(())
    })
    .unwrap();
}

#[test]
fn array_lists() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            let mut list = moment.put_list("list")?;
            list.append(1u64)?;
            list.append("two")?;
            list.append(Data::bytes(long(100)))
        })
        .unwrap();

    history
        .transact(|moment| {
            let mut list = moment.put_list("list")?;
            let before = len(&db);
            assert!(!list.put_if_changed(0, 1u64)?);
            assert!(!list.put_if_changed(1, "two")?);
            assert!(!list.put_if_changed(-1, Data::bytes(long(100)))?);
            assert_eq!(len(&db), before);

            assert!(matches!(list.put_if_changed(3, 1u64), Err(Error::KeyNotFound)));
            assert!(list.put_if_changed(0, 1i64)?);
            assert!(list.put_if_changed(-1, Data::bytes(long(101)))?);
            assert!(!list.put_if_changed(0, 1i64)?);
            Ok::<_, Error>(())
        })
        .unwrap();
    let latest = history.latest().unwrap();
    let list = latest.get_list("list").unwrap().unwrap();
    assert_eq!(list.get_cursor(0).unwrap().unwrap().read_int().unwrap(), 1);
    assert_eq!(list.get_cursor(2).unwrap().unwrap().read_bytes(MAX_READ).unwrap(), long(101));
}

#[test]
fn top_level_array_list() {
    let db = new_db();
    let mut list = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    list.append(1u64).unwrap();
    let size = db.committed_size().unwrap();

    // outside a transaction, a skipped put doesn't start one
    assert!(!list.put_if_changed(0, 1u64).unwrap());
    assert_eq!(db.committed_size().unwrap(), size);
    assert!(list.put_if_changed(0, 2u64).unwrap());
    assert!(db.committed_size().unwrap() > size);
}

#[test]
fn linked_array_lists() {
    let db = new_db();
    db.run_context(|root| {
        let mut list = WriteLinkedArrayList::new(root)?;
        list.append(1u64)?;
        list.append(Data::bytes(long(100)))?;
        db.freeze()?;

        let before = len(&db);
        assert!(!list.put_if_changed(0, 1u64)?);
        assert!(!list.put_if_changed(1, Data::bytes(long(100)))?);
        assert_eq!(len(&db), before);
        assert!(list.put_if_changed(1, Data::bytes(long(99)))?);
        assert!(matches!(list.put_if_changed(2, 1u64), Err(Error::KeyNotFound)));
        Ok(())
    })
    .unwrap();
}

#[test]
fn sorted_maps() {
    let db = new_db();
    db.run_context(|root| {
        let mut map = WriteSortedMap::new(root)?;
        map.put("a", 1u64)?;
        map.put("b", "bee")?;
        db.freeze()?;

        let before = len(&db);
        assert!(!map.put_if_changed("a", 1u64)?);
        assert!(!map.put_if_changed("b", "bee")?);
        assert_eq!(len(&db), before);
        assert!(map.put_if_changed("a", 1i64)?);
        assert!(map.put_if_changed("c", Data::None)?);
        assert!(!map.put_if_changed("c", Data::None)?);
        assert_eq!(map.count()?, 3);
        Ok(())
    })
    .unwrap();
}

#[test]
fn cursors() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("key", Data::bytes(long(100)))).unwrap();

    let latest = history.latest().unwrap();
    let cursor = latest.get_cursor("key").unwrap().unwrap();
    assert!(cursor.equals(Data::bytes(long(100))).unwrap());
    assert!(!cursor.equals(Data::bytes(long(101))).unwrap());
    assert!(!cursor.equals(Data::None).unwrap());

    history
        .transact(|moment| {
            let mut cursor = moment.put_cursor("key")?;
            let before = len(&db);
            assert!(!cursor.write_if_changed(Data::bytes(long(100)))?);
            assert_eq!(len(&db), before);
            assert!(cursor.write_if_changed(5u64)?);
            assert!(!cursor.write_if_changed(5u64)?);
            assert!(cursor.equals(5u64)?);
            Ok::<_, Error>(())
        })
        .unwrap();
    assert_eq!(history.latest().unwrap().get_uint("key").unwrap(), Some(5));

    // the root cursor, outside a transaction
    let db = new_db();
    assert!(db.root_cursor().write_if_changed(5u64).unwrap());
    let size = db.committed_size().unwrap();
    assert!(!db.root_cursor().write_if_changed(5u64).unwrap());
    assert_eq!(db.committed_size().unwrap(), size);
    assert!(db.root_cursor().write_if_changed(6u64).unwrap());
    assert_eq!(db.root_cursor().read_uint().unwrap(), 6);
}
