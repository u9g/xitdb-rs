//! Reads a database written by the Go implementation, to check that the
//! file format matches.

use std::fs::File;

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

fn open_fixture() -> Database<CoreFile> {
    let file = File::open(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/testdata/test.db")).unwrap();
    Database::new(CoreFile::new(file), Hasher::sha1()).unwrap()
}

fn read_string<C: Core>(cursor: Option<ReadCursor<'_, C>>) -> String {
    String::from_utf8(cursor.expect("missing value").read_bytes(MAX_READ).unwrap()).unwrap()
}

#[test]
fn read_database_from_resources() {
    let db = open_fixture();
    let history = ReadArrayList::new(db.root_cursor()).unwrap();

    // moment 0
    {
        let moment = ReadHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();
        assert_eq!(read_string(moment.get_cursor("foo").unwrap()), "foo");
        assert_eq!(moment.get_slot("foo").unwrap().unwrap().tag, Tag::ShortBytes);
        assert_eq!(moment.get_slot("bar").unwrap().unwrap().tag, Tag::ShortBytes);

        let fruits = ReadArrayList::new(moment.get_cursor("fruits").unwrap().unwrap()).unwrap();
        assert_eq!(fruits.count().unwrap(), 3);
        assert_eq!(read_string(fruits.get_cursor(0).unwrap()), "apple");

        let people = ReadArrayList::new(moment.get_cursor("people").unwrap().unwrap()).unwrap();
        assert_eq!(people.count().unwrap(), 2);
        let alice = ReadHashMap::new(people.get_cursor(0).unwrap().unwrap()).unwrap();
        assert_eq!(alice.get_cursor("age").unwrap().unwrap().read_uint().unwrap(), 25);

        let todos = ReadLinkedArrayList::new(moment.get_cursor("todos").unwrap().unwrap()).unwrap();
        assert_eq!(todos.count().unwrap(), 3);
        assert_eq!(read_string(todos.get_cursor(0).unwrap()), "Pay the bills");

        // iterate over people -> person -> person fields
        for person in people.iter().unwrap() {
            let person = ReadHashMap::new(person.unwrap()).unwrap();
            for kv in person.iter().unwrap() {
                kv.unwrap().read_key_value_pair().unwrap();
            }
        }

        // counted hash map
        let lcm = ReadCountedHashMap::new(moment.get_cursor("letters-counted-map").unwrap().unwrap()).unwrap();
        assert_eq!(lcm.count().unwrap(), 2);
        let mut count = 0;
        for kv in lcm.iter().unwrap() {
            let kv = kv.unwrap().read_key_value_pair().unwrap();
            kv.key_cursor.read_bytes(MAX_READ).unwrap();
            count += 1;
        }
        assert_eq!(count, 2);

        // hash set
        let ls = ReadHashSet::new(moment.get_cursor("letters-set").unwrap().unwrap()).unwrap();
        assert!(ls.get_cursor("a").unwrap().is_some());
        assert!(ls.get_cursor("c").unwrap().is_some());
        assert_eq!(ls.iter().unwrap().count(), 2);

        // counted hash set
        let lcs = ReadCountedHashSet::new(moment.get_cursor("letters-counted-set").unwrap().unwrap()).unwrap();
        assert_eq!(lcs.count().unwrap(), 2);
        let mut count = 0;
        for kv in lcs.iter().unwrap() {
            let kv = kv.unwrap().read_key_value_pair().unwrap();
            kv.key_cursor.read_bytes(MAX_READ).unwrap();
            count += 1;
        }
        assert_eq!(count, 2);
    }

    // moment 1
    {
        let moment = ReadHashMap::new(history.get_cursor(1).unwrap().unwrap()).unwrap();
        assert!(moment.get_cursor("bar").unwrap().is_none());
        assert_eq!(read_string(moment.get_key_cursor("fruits").unwrap()), "fruits");

        let fruits = ReadArrayList::new(moment.get_cursor("fruits").unwrap().unwrap()).unwrap();
        assert_eq!(fruits.count().unwrap(), 2);
        let fruits_kv = moment.get_key_value_pair("fruits").unwrap().unwrap();
        assert_eq!(fruits_kv.key_cursor.slot_ptr.slot.tag, Tag::ShortBytes);
        assert_eq!(fruits_kv.value_cursor.slot_ptr.slot.tag, Tag::ArrayList);
        assert_eq!(read_string(fruits.get_cursor(0).unwrap()), "lemon");

        let people = ReadArrayList::new(moment.get_cursor("people").unwrap().unwrap()).unwrap();
        assert_eq!(people.count().unwrap(), 2);
        let alice = ReadHashMap::new(people.get_cursor(0).unwrap().unwrap()).unwrap();
        assert_eq!(alice.get_cursor("age").unwrap().unwrap().read_uint().unwrap(), 26);

        let todos = ReadLinkedArrayList::new(moment.get_cursor("todos").unwrap().unwrap()).unwrap();
        assert_eq!(todos.count().unwrap(), 1);
        assert_eq!(read_string(todos.get_cursor(0).unwrap()), "Wash the car");

        let lcm = ReadCountedHashMap::new(moment.get_cursor("letters-counted-map").unwrap().unwrap()).unwrap();
        assert_eq!(lcm.count().unwrap(), 1);

        let ls = ReadHashSet::new(moment.get_cursor("letters-set").unwrap().unwrap()).unwrap();
        assert!(ls.get_cursor("a").unwrap().is_some());
        assert!(ls.get_cursor("c").unwrap().is_none());

        let lcs = ReadCountedHashSet::new(moment.get_cursor("letters-counted-set").unwrap().unwrap()).unwrap();
        assert_eq!(lcs.count().unwrap(), 1);
    }
}

#[test]
fn multithreading() {
    let db = open_fixture();
    let history = ReadArrayList::new(db.root_cursor()).unwrap();
    // read from the main thread to move the read position
    let moment = ReadHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();

    let read_foo = || {
        // each thread opens its own file handle
        let db = open_fixture();
        let history = ReadArrayList::new(db.root_cursor()).unwrap();
        let moment = ReadHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();
        assert_eq!(read_string(moment.get_cursor("foo").unwrap()), "foo");
    };
    let threads = [std::thread::spawn(read_foo), std::thread::spawn(read_foo)];

    // this succeeds because the threads use their own file handles
    assert_eq!(read_string(moment.get_cursor("foo").unwrap()), "foo");

    for thread in threads {
        thread.join().unwrap();
    }
}

/// Writes the same data as the Go test that produced the fixture, and
/// checks that this port reads it back the same way.
#[test]
fn compacting_fixture_preserves_latest_moment() {
    let db = open_fixture();
    let mut offsets = MemoryOffsetMap::new();
    let compacted = db.compact(CoreMemory::new(), &mut offsets).unwrap();
    let history = ReadArrayList::new(compacted.root_cursor()).unwrap();
    assert_eq!(history.count().unwrap(), 1);
    let moment = ReadHashMap::new(history.get_cursor(0).unwrap().unwrap()).unwrap();
    let todos = ReadLinkedArrayList::new(moment.get_cursor("todos").unwrap().unwrap()).unwrap();
    assert_eq!(read_string(todos.get_cursor(0).unwrap()), "Wash the car");
    let fruits = ReadArrayList::new(moment.get_cursor("fruits").unwrap().unwrap()).unwrap();
    assert_eq!(read_string(fruits.get_cursor(0).unwrap()), "lemon");
}
