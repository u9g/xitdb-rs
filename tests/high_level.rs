//! Port of `TestHighLevelApi` and `TestNotUsingArrayListAtTopLevel` from
//! the Go implementation's high_level_test.go.

use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

#[test]
fn high_level_api() {
    // CoreMemory
    {
        let core = CoreMemory::new();
        test_high_level_api(core, Hasher::sha1(), None).unwrap();
    }

    // CoreFile
    {
        let tmp = tempfile::NamedTempFile::new().unwrap();
        let core = CoreFile::new(tmp.as_file().try_clone().unwrap());
        test_high_level_api(core, Hasher::sha1(), Some(tmp.path())).unwrap();
    }

    // CoreBufferedFile
    {
        let tmp = tempfile::NamedTempFile::new().unwrap();
        let core = CoreBufferedFile::with_buffer_size(tmp.as_file().try_clone().unwrap(), 1024);
        test_high_level_api(core, Hasher::sha1(), Some(tmp.path())).unwrap();
    }
}

#[test]
fn not_using_array_list_at_top_level() {
    // hash map
    {
        let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();

        let mut m = WriteHashMap::new(&mut db.root_cursor()).unwrap();
        m.put("foo", Data::string("foo")).unwrap();
        m.put("bar", Data::string("bar")).unwrap();

        // every write to the root is a transaction, so a nested
        // cursor can't be written to after it was returned
        let mut inner_map_cursor = m.put_cursor("inner-map").unwrap();
        let err = WriteHashMap::new(&mut inner_map_cursor).err().expect("expected an error");
        assert!(matches!(err, Error::ExpiredTransaction), "unexpected error: {err:?}");
    }

    // linked array list
    {
        let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();

        let mut list = WriteLinkedArrayList::new(&mut db.root_cursor()).unwrap();
        list.append(Data::Uint(1)).unwrap();
        assert_eq!(list.count().unwrap(), 1);
    }
}

fn read_string<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<String> {
    Ok(String::from_utf8(cursor.read_bytes(MAX_READ)?).unwrap())
}

fn test_high_level_api<C: Core>(mut core: C, hasher: Hasher, file_maybe: Option<&Path>) -> Result<()> {
    // init the db
    core.set_length(0)?;
    let db = Database::new(core, hasher.clone())?;

    // first transaction
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        let last_slot = history.get_slot(-1)?;
        history.append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;

            moment.put("foo", Data::string("foo"))?;
            moment.put("bar", Data::string("bar"))?;

            let mut fruits_cursor = moment.put_cursor("fruits")?;
            let mut fruits = WriteArrayList::new(&mut fruits_cursor)?;
            fruits.append(Data::string("apple"))?;
            fruits.append(Data::string("pear"))?;
            fruits.append(Data::string("grape"))?;

            let mut people_cursor = moment.put_cursor("people")?;
            let mut people = WriteArrayList::new(&mut people_cursor)?;

            let mut alice_cursor = people.append_cursor()?;
            let mut alice = WriteHashMap::new(&mut alice_cursor)?;
            alice.put("name", Data::string("Alice"))?;
            alice.put("age", Data::Uint(25))?;

            let mut bob_cursor = people.append_cursor()?;
            let mut bob = WriteHashMap::new(&mut bob_cursor)?;
            bob.put("name", Data::string("Bob"))?;
            bob.put("age", Data::Uint(42))?;

            let mut todos_cursor = moment.put_cursor("todos")?;
            let mut todos = WriteLinkedArrayList::new(&mut todos_cursor)?;
            todos.append(Data::string("Pay the bills"))?;
            todos.append(Data::string("Get an oil change"))?;
            todos.insert(1, Data::string("Wash the car"))?;

            // make sure insertCursor works
            let mut todo_cursor = todos.insert_cursor(1)?;
            WriteHashMap::new(&mut todo_cursor)?;
            todos.remove(1)?;

            let mut lcm_cursor = moment.put_cursor("letters-counted-map")?;
            let mut lcm = WriteCountedHashMap::new(&mut lcm_cursor)?;
            lcm.put("a", Data::Uint(1))?;
            lcm.put("a", Data::Uint(2))?;
            lcm.put("c", Data::Uint(2))?;

            let mut ls_cursor = moment.put_cursor("letters-set")?;
            let mut ls = WriteHashSet::new(&mut ls_cursor)?;
            ls.put("a")?;
            ls.put("a")?;
            ls.put("c")?;

            let mut lcs_cursor = moment.put_cursor("letters-counted-set")?;
            let mut lcs = WriteCountedHashSet::new(&mut lcs_cursor)?;
            lcs.put("a")?;
            lcs.put("a")?;
            lcs.put("c")?;

            let random_bytes = vec![0xABu8; 32];
            moment.put("random-number", Data::tagged_bytes(random_bytes, *b"bi"))?;

            let mut long_text_cursor = moment.put_cursor("long-text")?;
            let mut cursor_writer = long_text_cursor.writer()?;
            {
                let mut bw = BufWriter::new(&mut cursor_writer);
                for _ in 0..50 {
                    bw.write_all(b"hello, world\n")?;
                }
                bw.flush()?;
            }
            cursor_writer.finish()?;

            Ok(())
        })?;

        // verify moment 0
        let moment_cursor = history.get_cursor(-1)?.unwrap();
        let moment = ReadHashMap::new(moment_cursor)?;

        let foo_cursor = moment.get_cursor("foo")?.unwrap();
        assert_eq!(read_string(&foo_cursor)?, "foo");

        assert_eq!(moment.get_slot("foo")?.unwrap().tag, Tag::ShortBytes);
        assert_eq!(moment.get_slot("bar")?.unwrap().tag, Tag::ShortBytes);

        let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
        assert_eq!(fruits.count()?, 3);

        let apple_cursor = fruits.get_cursor(0)?.unwrap();
        assert_eq!(read_string(&apple_cursor)?, "apple");

        let people = ReadArrayList::new(moment.get_cursor("people")?.unwrap())?;
        assert_eq!(people.count()?, 2);

        let alice = ReadHashMap::new(people.get_cursor(0)?.unwrap())?;
        let alice_age = alice.get_cursor("age")?.unwrap().read_uint()?;
        assert_eq!(alice_age, 25);

        let todos = ReadLinkedArrayList::new(moment.get_cursor("todos")?.unwrap())?;
        assert_eq!(todos.count()?, 3);

        let todo_cursor = todos.get_cursor(0)?.unwrap();
        assert_eq!(read_string(&todo_cursor)?, "Pay the bills");

        // iterate over people
        for person_cursor in people.iter()? {
            let person = ReadHashMap::new(person_cursor?)?;
            for kv_pair_cursor in person.iter()? {
                let kv_pair = kv_pair_cursor?.read_key_value_pair()?;
                kv_pair.key_cursor.read_bytes(MAX_READ)?;
                match kv_pair.value_cursor.slot_ptr.slot.tag {
                    Tag::ShortBytes | Tag::Bytes => {
                        kv_pair.value_cursor.read_bytes(MAX_READ)?;
                    }
                    Tag::Uint => {
                        kv_pair.value_cursor.read_uint()?;
                    }
                    Tag::Int => {
                        kv_pair.value_cursor.read_int()?;
                    }
                    Tag::Float => {
                        kv_pair.value_cursor.read_float()?;
                    }
                    tag => panic!("unexpected tag: {tag:?}"),
                }
            }
        }

        // iterate over fruits
        for fruit in fruits.iter()? {
            fruit?;
        }

        // counted hash map
        {
            let lcm = ReadCountedHashMap::new(moment.get_cursor("letters-counted-map")?.unwrap())?;
            assert_eq!(lcm.count()?, 2);

            let mut count = 0;
            for kv_pair_cursor in lcm.iter()? {
                let kv_pair = kv_pair_cursor?.read_key_value_pair()?;
                kv_pair.key_cursor.read_bytes(MAX_READ)?;
                count += 1;
            }
            assert_eq!(count, 2);
        }

        // hash set
        {
            let ls = ReadHashSet::new(moment.get_cursor("letters-set")?.unwrap())?;
            assert!(ls.get_cursor("a")?.is_some(), "expected non-nil cursor for 'a'");
            assert!(ls.get_cursor("c")?.is_some(), "expected non-nil cursor for 'c'");

            let mut count = 0;
            for kv_pair_cursor in ls.iter()? {
                let kv_pair = kv_pair_cursor?.read_key_value_pair()?;
                kv_pair.key_cursor.read_bytes(MAX_READ)?;
                count += 1;
            }
            assert_eq!(count, 2);
        }

        // counted hash set
        {
            let lcs = ReadCountedHashSet::new(moment.get_cursor("letters-counted-set")?.unwrap())?;
            assert_eq!(lcs.count()?, 2);

            let mut count = 0;
            for kv_pair_cursor in lcs.iter()? {
                let kv_pair = kv_pair_cursor?.read_key_value_pair()?;
                kv_pair.key_cursor.read_bytes(MAX_READ)?;
                count += 1;
            }
            assert_eq!(count, 2);
        }

        // random number format tag
        {
            let rn_cursor = moment.get_cursor("random-number")?.unwrap();
            let rn_obj = rn_cursor.read_bytes_object(MAX_READ)?;
            assert_eq!(rn_obj.format_tag, Some(*b"bi"));
        }

        // long text with reader
        {
            let lt_cursor = moment.get_cursor("long-text")?.unwrap();
            let cursor_reader = lt_cursor.reader()?;
            let mut br = BufReader::new(cursor_reader);
            let mut count = 0;
            let mut line = Vec::new();
            loop {
                line.clear();
                let n = br.read_until(b'\n', &mut line)?;
                // like Go's ReadString, a line without a trailing newline
                // comes back with io.EOF and isn't counted
                if n == 0 || line.last() != Some(&b'\n') {
                    break;
                }
                count += 1;
            }
            assert_eq!(count, 50);
        }
    }

    // second transaction: modify data
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        let last_slot = history.get_slot(-1)?;
        history.append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;

            let removed = moment.remove("bar")?;
            assert!(removed, "expected bar to be removed");
            let removed = moment.remove("doesn't exist")?;
            assert!(!removed, "expected not found");

            let mut fruits_cursor = moment.put_cursor("fruits")?;
            let mut fruits = WriteArrayList::new(&mut fruits_cursor)?;
            fruits.put(0, Data::string("lemon"))?;
            fruits.slice(2)?;

            let mut people_cursor = moment.put_cursor("people")?;
            let mut people = WriteArrayList::new(&mut people_cursor)?;

            let mut alice_cursor = people.put_cursor(0)?;
            let mut alice = WriteHashMap::new(&mut alice_cursor)?;
            alice.put("age", Data::Uint(26))?;

            let mut todos_cursor = moment.put_cursor("todos")?;
            let mut todos = WriteLinkedArrayList::new(&mut todos_cursor)?;
            todos.concat(todos_cursor.slot()?)?;
            todos.slice(1, 2)?;
            todos.remove(1)?;

            // the Go test ignores the results of these removes
            let mut lcm_cursor = moment.put_cursor("letters-counted-map")?;
            let mut lcm = WriteCountedHashMap::new(&mut lcm_cursor)?;
            let _ = lcm.remove("b");
            let _ = lcm.remove("c");

            let mut ls_cursor = moment.put_cursor("letters-set")?;
            let mut ls = WriteHashSet::new(&mut ls_cursor)?;
            let _ = ls.remove("b");
            let _ = ls.remove("c");

            let mut lcs_cursor = moment.put_cursor("letters-counted-set")?;
            let mut lcs = WriteCountedHashSet::new(&mut lcs_cursor)?;
            let _ = lcs.remove("b");
            let _ = lcs.remove("c");

            Ok(())
        })?;

        // verify moment 1
        let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

        assert!(moment.get_cursor("bar")?.is_none(), "expected nil cursor for 'bar'");

        let fruits_key_cursor = moment.get_key_cursor("fruits")?.unwrap();
        assert_eq!(read_string(&fruits_key_cursor)?, "fruits");

        let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
        assert_eq!(fruits.count()?, 2);

        let fruits_kv = moment.get_key_value_pair("fruits")?.unwrap();
        assert_eq!(fruits_kv.key_cursor.slot_ptr.slot.tag, Tag::ShortBytes);
        assert_eq!(fruits_kv.value_cursor.slot_ptr.slot.tag, Tag::ArrayList);

        let lemon_cursor = fruits.get_cursor(0)?.unwrap();
        assert_eq!(read_string(&lemon_cursor)?, "lemon");

        let people = ReadArrayList::new(moment.get_cursor("people")?.unwrap())?;
        assert_eq!(people.count()?, 2);

        let alice = ReadHashMap::new(people.get_cursor(0)?.unwrap())?;
        let alice_age = alice.get_cursor("age")?.unwrap().read_uint()?;
        assert_eq!(alice_age, 26);

        let todos = ReadLinkedArrayList::new(moment.get_cursor("todos")?.unwrap())?;
        assert_eq!(todos.count()?, 1);

        let todo_cursor = todos.get_cursor(0)?.unwrap();
        assert_eq!(read_string(&todo_cursor)?, "Wash the car");

        let lcm = ReadCountedHashMap::new(moment.get_cursor("letters-counted-map")?.unwrap())?;
        assert_eq!(lcm.count()?, 1);

        let ls = ReadHashSet::new(moment.get_cursor("letters-set")?.unwrap())?;
        assert!(ls.get_cursor("a")?.is_some(), "expected non-nil cursor for 'a'");
        assert!(ls.get_cursor("c")?.is_none(), "expected nil cursor for 'c'");

        let lcs = ReadCountedHashSet::new(moment.get_cursor("letters-counted-set")?.unwrap())?;
        assert_eq!(lcs.count()?, 1);
    }

    // old data hasn't changed
    {
        let history = WriteArrayList::new(&mut db.root_cursor())?;

        let moment = ReadHashMap::new(history.get_cursor(0)?.unwrap())?;

        let foo_cursor = moment.get_cursor("foo")?.unwrap();
        assert_eq!(read_string(&foo_cursor)?, "foo");

        assert_eq!(moment.get_slot("foo")?.unwrap().tag, Tag::ShortBytes);
        assert_eq!(moment.get_slot("bar")?.unwrap().tag, Tag::ShortBytes);

        let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
        assert_eq!(fruits.count()?, 3);

        let apple_cursor = fruits.get_cursor(0)?.unwrap();
        assert_eq!(read_string(&apple_cursor)?, "apple");

        let people = ReadArrayList::new(moment.get_cursor("people")?.unwrap())?;
        assert_eq!(people.count()?, 2);

        let alice = ReadHashMap::new(people.get_cursor(0)?.unwrap())?;
        let alice_age = alice.get_cursor("age")?.unwrap().read_uint()?;
        assert_eq!(alice_age, 25);

        let todos = ReadLinkedArrayList::new(moment.get_cursor("todos")?.unwrap())?;
        assert_eq!(todos.count()?, 3);

        let todo_cursor = todos.get_cursor(0)?.unwrap();
        assert_eq!(read_string(&todo_cursor)?, "Pay the bills");
    }

    // remove the last transaction with slice
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        history.slice(1)?;

        let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

        let foo_cursor = moment.get_cursor("foo")?.unwrap();
        assert_eq!(read_string(&foo_cursor)?, "foo");
    }

    // opening the db leaves trailing data alone, because it may
    // belong to another writer's unfinished transaction. the next
    // write transaction truncates it before allocating new data.
    let db = {
        let core_len = db.core().length()?;
        db.core().seek_to(core_len)?;

        db.core().write(b"this is trailing data from an unfinished transaction")?;
        db.core().flush()?;
        let size_with_tail = db.core().length()?;

        // no error is thrown if db file is opened in read-only mode
        if let Some(path) = file_maybe {
            let read_only_file = File::open(path)?;
            let read_only_core = CoreFile::new(read_only_file);
            Database::new(read_only_core, hasher.clone())?;
        }

        let db = Database::new(db.into_core(), hasher.clone())?;

        let size_after = db.core().length()?;
        assert_eq!(size_with_tail, size_after);
        WriteArrayList::new(&mut db.root_cursor())?;
        let size_after = db.core().length()?;
        assert_eq!(core_len, size_after);

        db
    };

    // cloning
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        let last_slot = history.get_slot(-1)?;
        history.append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;

            let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;

            let mut food_cursor = moment.put_cursor("food")?;
            food_cursor.write(fruits.slot()?)?;

            let mut food = WriteArrayList::new(&mut food_cursor)?;
            food.append(Data::string("eggs"))?;
            food.append(Data::string("rice"))?;
            food.append(Data::string("fish"))?;
            Ok(())
        })?;

        let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

        let food = ReadArrayList::new(moment.get_cursor("food")?.unwrap())?;
        assert_eq!(food.count()?, 6);

        let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
        assert_eq!(fruits.count()?, 3);
    }

    // accidental mutation when cloning inside a transaction
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        let history_count = history.count()?;
        let history_index = history_count - 1;

        let last_slot = history.get_slot(-1)?;
        history.append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;

            let mut big_cities_cursor = moment.put_cursor("big-cities")?;
            let mut big_cities = WriteArrayList::new(&mut big_cities_cursor)?;
            big_cities.append(Data::string("New York, NY"))?;
            big_cities.append(Data::string("Los Angeles, CA"))?;

            let mut cities_cursor = moment.put_cursor("cities")?;
            cities_cursor.write(big_cities.slot()?)?;

            let mut cities = WriteArrayList::new(&mut cities_cursor)?;
            cities.append(Data::string("Charleston, SC"))?;
            cities.append(Data::string("Louisville, KY"))?;
            Ok(())
        })?;

        let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

        let cities = ReadArrayList::new(moment.get_cursor("cities")?.unwrap())?;
        assert_eq!(cities.count()?, 4);

        // big-cities also got mutated (accidental)
        let big_cities = ReadArrayList::new(moment.get_cursor("big-cities")?.unwrap())?;
        assert_eq!(big_cities.count()?, 4);

        // revert
        let hist_slot = history.get_slot(history_index)?;
        history.append(hist_slot)?;
    }

    // preventing accidental mutation with freezing
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        let last_slot = history.get_slot(-1)?;
        history.append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;

            let mut big_cities_cursor = moment.put_cursor("big-cities")?;
            let mut big_cities = WriteArrayList::new(&mut big_cities_cursor)?;
            big_cities.append(Data::string("New York, NY"))?;
            big_cities.append(Data::string("Los Angeles, CA"))?;

            let mut cities_cursor = moment.put_cursor("cities")?;
            cities_cursor.write(big_cities.slot()?)?;

            // freeze here, so writes to cities won't mutate big-cities
            // note: you can also freeze globally with `db.freeze()`,
            // but call it before `put_cursor` creates the cities cursor
            cities_cursor.freeze()?;

            let mut cities = WriteArrayList::new(&mut cities_cursor)?;
            cities.append(Data::string("Charleston, SC"))?;
            cities.append(Data::string("Louisville, KY"))?;
            Ok(())
        })?;

        let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

        let cities = ReadArrayList::new(moment.get_cursor("cities")?.unwrap())?;
        assert_eq!(cities.count()?, 4);

        let big_cities = ReadArrayList::new(moment.get_cursor("big-cities")?.unwrap())?;
        assert_eq!(big_cities.count()?, 2);
    }

    // build a secondary index with a SortedMap to sort and paginate,
    // like the "Sorting and Paginating" section of the readme
    {
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;

        struct User {
            id: &'static str,
            username: &'static str,
            name: &'static str,
        }

        // inserted in arbitrary order; the index sorts them alphabetically
        let new_users = [
            User { id: "user000000000001", username: "dave", name: "Dave Smith" },
            User { id: "user000000000002", username: "alice", name: "Alice Jones" },
            User { id: "user000000000003", username: "carol", name: "Carol White" },
            User { id: "user000000000004", username: "dan", name: "Dan Brown" },
            User { id: "user000000000005", username: "bob", name: "Bob Lee" },
            User { id: "user000000000006", username: "eve", name: "Eve Adams" },
        ];

        let last_slot = history.get_slot(-1)?;
        history.append_context(last_slot, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;

            // the primary store: a HashMap from user id to the user's fields
            let mut id_to_user_cursor = moment.put_cursor("id->user")?;
            let mut id_to_user = WriteHashMap::new(&mut id_to_user_cursor)?;

            // the secondary index: a SortedMap ordered alphabetically by username
            let mut username_to_id_cursor = moment.put_cursor("username->id")?;
            let mut username_to_id = WriteSortedMap::new(&mut username_to_id_cursor)?;

            for u in &new_users {
                let mut user_cursor = id_to_user.put_cursor(u.id)?;
                let mut user_map = WriteHashMap::new(&mut user_cursor)?;
                user_map.put("username", Data::string(u.username))?;
                user_map.put("name", Data::string(u.name))?;

                // the key is the username (the sort key); the value is the id
                username_to_id.put(u.username, Data::string(u.id))?;
            }
            Ok(())
        })?;

        let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

        let id_to_user = ReadHashMap::new(moment.get_cursor("id->user")?.unwrap())?;

        let username_to_id = ReadSortedMap::new(moment.get_cursor("username->id")?.unwrap())?;

        let count = username_to_id.count()?;
        assert_eq!(count, new_users.len() as i64);

        // page through the index two at a time and check we get every user back
        // in alphabetical order by username (not the order they were inserted)
        let page_size: i64 = 2;
        let expected_names = ["Alice Jones", "Bob Lee", "Carol White", "Dan Brown", "Dave Smith", "Eve Adams"];

        let mut seen = 0;
        let mut after: i64 = 0;
        while after < count {
            let end = (after + page_size).min(count);
            // seek straight to the start of the page, then walk forward
            for id_cursor in username_to_id.iter_from_index(after)?.take((end - after) as usize) {
                let id_cursor = id_cursor?;

                let id_kv = id_cursor.read_key_value_pair()?;

                // the index entry's value is the user id; use it to read the
                // full user out of the primary map
                let user_id = read_string(&id_kv.value_cursor)?;

                let user_map = ReadHashMap::new(id_to_user.get_cursor(&user_id)?.unwrap())?;
                let name_cursor = user_map.get_cursor("name")?.unwrap();
                assert_eq!(read_string(&name_cursor)?, expected_names[seen]);
                seen += 1;
            }
            after += page_size;
        }
        assert_eq!(seen, new_users.len());

        // autocomplete: seek straight to the first username >= "da", then walk
        // forward only while the prefix matches. this lower-bound seek by key is
        // the thing an ArrayList can't do.
        let prefix = b"da";
        let expected_matches = ["dan", "dave"];
        let mut matches = 0;
        for id_cursor in username_to_id.iter_from(prefix)? {
            let id_kv = id_cursor?.read_key_value_pair()?;

            // the key is the username; stop once we've walked past the prefix
            let username_bytes = id_kv.key_cursor.read_bytes(MAX_READ)?;
            if !username_bytes.starts_with(prefix) {
                break;
            }

            assert_eq!(String::from_utf8(username_bytes).unwrap(), expected_matches[matches]);
            matches += 1;
        }
        assert_eq!(matches, expected_matches.len());
    }

    Ok(())
}
