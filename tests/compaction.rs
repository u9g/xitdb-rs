//! Port of the compaction tests in xitdb-go's high_level_test.go
//! (TestCompaction, TestCompactionWithDiskBackedOffsetsMap and testCompaction).

use std::fs::OpenOptions;

use xitdb::*;

fn read_string<C: Core>(cursor: &ReadCursor<'_, C>, max_read: u64) -> Result<String> {
    Ok(String::from_utf8(cursor.read_bytes(Some(max_read))?).unwrap())
}

#[test]
fn compaction() -> Result<()> {
    let max_read = 1024;
    let mut offset_map = MemoryOffsetMap::new();

    // memory
    {
        let mut source_core = CoreMemory::new();
        let mut target_core = CoreMemory::new();
        let hasher = Hasher::sha1();
        test_compaction(&mut source_core, &mut target_core, &hasher, false, max_read, &mut offset_map)?;
    }

    // file
    {
        let mut source_core = CoreFile::new(tempfile::tempfile()?);
        let mut target_core = CoreFile::new(tempfile::tempfile()?);
        let hasher = Hasher::sha1();
        test_compaction(&mut source_core, &mut target_core, &hasher, true, max_read, &mut offset_map)?;
    }

    // buffered file
    {
        let mut source_core = CoreBufferedFile::new(tempfile::tempfile()?);
        let mut target_core = CoreBufferedFile::new(tempfile::tempfile()?);
        let hasher = Hasher::sha1();
        test_compaction(&mut source_core, &mut target_core, &hasher, true, max_read, &mut offset_map)?;
    }

    Ok(())
}

#[test]
fn compaction_with_disk_backed_offsets_map() -> Result<()> {
    // a FileOffsetMap stores offsets directly as hashes in a separate xitdb hash map,
    // inside one transaction that lasts for the whole compaction, so each put isn't
    // committed separately.
    let temp_dir = tempfile::tempdir()?;
    let create = |name: &str| {
        OpenOptions::new().read(true).write(true).create(true).truncate(true).open(temp_dir.path().join(name))
    };

    let offsets_core = CoreFile::new(create("offsets.db")?);
    let offsets_db = Database::new(offsets_core, Hasher::sha1())?;

    let mut source_core = CoreFile::new(create("source.db")?);
    let mut target_core = CoreFile::new(create("target.db")?);

    offsets_db.run_context(|cursor| {
        let mut offset_map = FileOffsetMap::new(cursor)?;

        // exercise the same data types, cycles, sharing, and reopening checks
        // as the in-memory offsets map, reusing the scratch map between runs.
        // reusing it must discard offsets from previous compactions.
        offset_map.put(0, 123)?;
        test_compaction(&mut source_core, &mut target_core, &Hasher::sha1(), true, 1024, &mut offset_map)?;
        let found = offset_map.get(0)?;
        assert!(found.is_none());
        Ok(())
    })?;

    Ok(())
}

fn test_compaction<S: Core, T: Core>(
    source_core: &mut S,
    target_core: &mut T,
    hasher: &Hasher,
    is_file: bool,
    max_read: u64,
    offset_map: &mut dyn OffsetMap,
) -> Result<()> {
    // empty DB compaction
    {
        source_core.set_length(0)?;
        target_core.set_length(0)?;
        let source = Database::new(&mut *source_core, hasher.clone())?;
        let compacted = source.compact(&mut *target_core, offset_map)?;
        assert!(compacted.root_cursor().slot()?.is_empty());
    }

    // basic compaction with various data types
    {
        source_core.set_length(0)?;
        target_core.set_length(0)?;
        let source = Database::new(&mut *source_core, hasher.clone())?;

        // moment 1
        {
            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                moment.put("key1", Data::string("value1"))?;
                moment.put("key2", Data::Uint(100))?;
                Ok(())
            })?;
        }

        // moment 2
        {
            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                moment.put("key1", Data::string("updated_value1"))?;
                moment.put("key2", Data::Uint(200))?;
                moment.put("key3", Data::Int(-42))?;
                moment.put("key4", Data::Float(2.5))?;
                moment.put("short", Data::string("hi"))?;
                moment.put("tagged", Data::tagged_string("this is a long tagged string!!", *b"bi"))?;

                let mut fruits = WriteArrayList::new(&mut moment.put_cursor("fruits")?)?;
                fruits.append(Data::string("apple"))?;
                fruits.append(Data::string("banana"))?;
                fruits.append(Data::string("cherry"))?;

                let mut todos = WriteLinkedArrayList::new(&mut moment.put_cursor("todos")?)?;
                todos.append(Data::string("task1"))?;
                todos.append(Data::string("task2"))?;
                todos.append(Data::string("task3"))?;

                let mut counted = WriteCountedHashMap::new(&mut moment.put_cursor("counted")?)?;
                counted.put("a", Data::Uint(1))?;
                counted.put_key("a", Data::string("a"))?;
                counted.put("b", Data::Uint(2))?;
                counted.put_key("b", Data::string("b"))?;

                let mut set = WriteHashSet::new(&mut moment.put_cursor("myset")?)?;
                set.put("x")?;
                set.put("y")?;

                let mut cset = WriteCountedHashSet::new(&mut moment.put_cursor("mycset")?)?;
                cset.put("p")?;
                cset.put("q")?;

                // SortedMap
                let mut sorted = WriteSortedMap::new(&mut moment.put_cursor("sorted")?)?;
                sorted.put("apple", Data::Uint(1))?;
                sorted.put("banana", Data::Uint(2))?;
                sorted.put("cherry", Data::Uint(3))?;

                // SortedSet
                let mut sorted_set = WriteSortedSet::new(&mut moment.put_cursor("sortedset")?)?;
                sorted_set.put("foo")?;
                sorted_set.put("bar")?;

                Ok(())
            })?;
        }

        // moment 3
        {
            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                moment.put("key1", Data::string("final_value"))?;

                // cycles must survive compaction rather than causing the
                // remapper to recurse indefinitely.
                let moment_slot = moment.slot()?;
                moment.put("self", moment_slot)?;

                let mut cyclic_list = WriteArrayList::new(&mut moment.put_cursor("cyclic-list")?)?;
                let cyclic_list_slot = cyclic_list.slot()?;
                cyclic_list.append(cyclic_list_slot)?;

                let mut map_a = WriteHashMap::new(&mut moment.put_cursor("map-a")?)?;
                let mut map_b = WriteHashMap::new(&mut moment.put_cursor("map-b")?)?;
                let map_b_slot = map_b.slot()?;
                map_a.put("map-b", map_b_slot)?;
                let map_a_slot = map_a.slot()?;
                map_b.put("map-a", map_a_slot)
            })?;
        }

        let source_size = source.core().length()?;

        let compacted = source.compact(&mut *target_core, offset_map)?;

        let target_size = compacted.core().length()?;
        assert!(target_size < source_size, "target should be smaller: {target_size} >= {source_size}");

        let history = ReadArrayList::new(compacted.root_cursor())?;
        assert_eq!(1, history.count()?);

        let moment_cursor = history.get_cursor(0)?.unwrap();
        let moment = ReadHashMap::new(&moment_cursor)?;

        // self-references and mutual references point back to the same compacted
        // objects rather than duplicate objects or dangling source offsets.
        let self_cursor = moment.get_cursor("self")?.unwrap();
        assert_eq!(moment_cursor.slot()?, self_cursor.slot()?);

        let cyclic_list_cursor = moment.get_cursor("cyclic-list")?.unwrap();
        let cyclic_list = ReadArrayList::new(&cyclic_list_cursor)?;
        let cyclic_slot = cyclic_list.get_slot(0)?;
        assert_eq!(Some(cyclic_list_cursor.slot()?), cyclic_slot);

        let map_a_cursor = moment.get_cursor("map-a")?.unwrap();
        let map_a = ReadHashMap::new(&map_a_cursor)?;
        let map_b_cursor = map_a.get_cursor("map-b")?.unwrap();
        let map_b = ReadHashMap::new(&map_b_cursor)?;
        let map_a_slot = map_b.get_slot("map-a")?;
        assert_eq!(Some(map_a_cursor.slot()?), map_a_slot);

        let key1_cursor = moment.get_cursor("key1")?.unwrap();
        assert_eq!("final_value", read_string(&key1_cursor, max_read)?);

        let key2_cursor = moment.get_cursor("key2")?.unwrap();
        assert_eq!(200u64, key2_cursor.read_uint()?);

        let key3_cursor = moment.get_cursor("key3")?.unwrap();
        assert_eq!(-42i64, key3_cursor.read_int()?);

        let key4_cursor = moment.get_cursor("key4")?.unwrap();
        assert_eq!(2.5f64, key4_cursor.read_float()?);

        let short_cursor = moment.get_cursor("short")?.unwrap();
        assert_eq!("hi", read_string(&short_cursor, max_read)?);

        let tagged_cursor = moment.get_cursor("tagged")?.unwrap();
        let tagged_obj = tagged_cursor.read_bytes_object(Some(max_read))?;
        assert_eq!(b"this is a long tagged string!!".as_slice(), &*tagged_obj.value);
        assert_eq!(Some(*b"bi"), tagged_obj.format_tag);

        let fruits_cursor = moment.get_cursor("fruits")?.unwrap();
        let fruits = ReadArrayList::new(&fruits_cursor)?;
        assert_eq!(3, fruits.count()?);
        let apple_cursor = fruits.get_cursor(0)?.unwrap();
        assert_eq!("apple", read_string(&apple_cursor, max_read)?);
        let cherry_cursor = fruits.get_cursor(2)?.unwrap();
        assert_eq!("cherry", read_string(&cherry_cursor, max_read)?);

        let todos_cursor = moment.get_cursor("todos")?.unwrap();
        let todos = ReadLinkedArrayList::new(&todos_cursor)?;
        assert_eq!(3, todos.count()?);
        let t1_cursor = todos.get_cursor(0)?.unwrap();
        assert_eq!("task1", read_string(&t1_cursor, max_read)?);
        let t3_cursor = todos.get_cursor(2)?.unwrap();
        assert_eq!("task3", read_string(&t3_cursor, max_read)?);

        let counted_cursor = moment.get_cursor("counted")?.unwrap();
        let counted = ReadCountedHashMap::new(&counted_cursor)?;
        assert_eq!(2, counted.count()?);
        let a_cursor = counted.get_cursor("a")?.unwrap();
        assert_eq!(1u64, a_cursor.read_uint()?);
        let b_cursor = counted.get_cursor("b")?.unwrap();
        assert_eq!(2u64, b_cursor.read_uint()?);

        let set_cursor = moment.get_cursor("myset")?.unwrap();
        let set = ReadHashSet::new(&set_cursor)?;
        let x_cursor = set.get_cursor("x")?.unwrap();
        assert_eq!("x", read_string(&x_cursor, max_read)?);

        let cset_cursor = moment.get_cursor("mycset")?.unwrap();
        let cset = ReadCountedHashSet::new(&cset_cursor)?;
        assert_eq!(2, cset.count()?);
        let p_cursor = cset.get_cursor("p")?.unwrap();
        assert_eq!("p", read_string(&p_cursor, max_read)?);

        // SortedMap
        let sorted_cursor = moment.get_cursor("sorted")?.unwrap();
        let sorted = ReadSortedMap::new(&sorted_cursor)?;
        assert_eq!(3, sorted.count()?);
        let banana_cursor = sorted.get_cursor("banana")?.unwrap();
        assert_eq!(2u64, banana_cursor.read_uint()?);
        // lexicographic order is preserved across compaction
        let first_kv = sorted.get_index_key_value_pair(0)?.unwrap();
        assert_eq!("apple", read_string(&first_kv.key_cursor, max_read)?);
        let last_kv = sorted.get_index_key_value_pair(-1)?.unwrap();
        assert_eq!("cherry", read_string(&last_kv.key_cursor, max_read)?);

        // SortedSet
        let sorted_set_cursor = moment.get_cursor("sortedset")?.unwrap();
        let sorted_set = ReadSortedSet::new(&sorted_set_cursor)?;
        assert_eq!(2, sorted_set.count()?);
        assert!(sorted_set.contains("foo")?);
        assert!(sorted_set.contains("bar")?);
        assert!(!sorted_set.contains("baz")?);
    }

    // structural sharing
    {
        source_core.set_length(0)?;
        target_core.set_length(0)?;
        let source = Database::new(&mut *source_core, hasher.clone())?;

        // moment 1: create many keys
        {
            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                for i in 0..20u64 {
                    let key = format!("shared_key_{i}");
                    moment.put(key, Data::Uint(i))?;
                }
                Ok(())
            })?;
        }

        // moments 2-5: change only one key each time
        for round in 0..4u64 {
            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                moment.put("changing_key", Data::Uint(round + 100))
            })?;
        }

        let compacted = source.compact(&mut *target_core, offset_map)?;

        let history = ReadArrayList::new(compacted.root_cursor())?;
        assert_eq!(1, history.count()?);

        let moment_cursor = history.get_cursor(0)?.unwrap();
        let moment = ReadHashMap::new(&moment_cursor)?;

        for i in 0..20u64 {
            let key = format!("shared_key_{i}");
            let cursor = moment.get_cursor(key)?.unwrap();
            assert_eq!(i, cursor.read_uint()?);
        }

        let changing_cursor = moment.get_cursor("changing_key")?.unwrap();
        assert_eq!(103u64, changing_cursor.read_uint()?);
    }

    // re-open after compact and compact-then-continue-writing
    if is_file {
        // re-open after compact
        {
            source_core.set_length(0)?;
            target_core.set_length(0)?;
            let source = Database::new(&mut *source_core, hasher.clone())?;

            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                moment.put("persist", Data::string("persistent_value"))?;
                moment.put("number", Data::Uint(999))
            })?;

            source.compact(&mut *target_core, offset_map)?;

            target_core.seek_to(0)?;
            let reopened = Database::new(&mut *target_core, hasher.clone())?;

            let r_history = ReadArrayList::new(reopened.root_cursor())?;
            assert_eq!(1, r_history.count()?);

            let mc = r_history.get_cursor(0)?.unwrap();
            let m = ReadHashMap::new(&mc)?;
            let p_cursor = m.get_cursor("persist")?.unwrap();
            assert_eq!("persistent_value", read_string(&p_cursor, max_read)?);
            let n_cursor = m.get_cursor("number")?.unwrap();
            assert_eq!(999u64, n_cursor.read_uint()?);
        }

        // compact then continue writing
        {
            source_core.set_length(0)?;
            target_core.set_length(0)?;
            let source = Database::new(&mut *source_core, hasher.clone())?;

            let mut history = WriteArrayList::new(&mut source.root_cursor())?;
            let last_slot = history.get_slot(-1)?;
            history.append_context(last_slot, |cursor| {
                let mut moment = WriteHashMap::new(cursor)?;
                moment.put("original", Data::string("original_data"))
            })?;

            let compacted = source.compact(&mut *target_core, offset_map)?;

            // add new moment to compacted DB
            {
                let mut c_history = WriteArrayList::new(&mut compacted.root_cursor())?;
                let c_last_slot = c_history.get_slot(-1)?;
                c_history.append_context(c_last_slot, |cursor| {
                    let mut moment = WriteHashMap::new(cursor)?;
                    moment.put("new_key", Data::string("new_data"))
                })?;
            }

            let c_history = ReadArrayList::new(compacted.root_cursor())?;
            assert_eq!(2, c_history.count()?);

            let m0_cursor = c_history.get_cursor(0)?.unwrap();
            let m0 = ReadHashMap::new(&m0_cursor)?;
            let orig_cursor = m0.get_cursor("original")?.unwrap();
            assert_eq!("original_data", read_string(&orig_cursor, max_read)?);

            let m1_cursor = c_history.get_cursor(1)?.unwrap();
            let m1 = ReadHashMap::new(&m1_cursor)?;
            let new_cursor = m1.get_cursor("new_key")?.unwrap();
            assert_eq!("new_data", read_string(&new_cursor, max_read)?);

            let orig_cursor2 = m1.get_cursor("original")?.unwrap();
            assert_eq!("original_data", read_string(&orig_cursor2, max_read)?);
        }
    }

    Ok(())
}
