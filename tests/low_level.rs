//! A port of the Go implementation's low_level_test.go.

use std::io::{self, Read, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

use sha1::Digest;
use xitdb::consts::{SLOT_COUNT, VERSION};
use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);
const HASH_MAP_INIT: PathPart<'static> = PathPart::HashMapInit { counted: false, set: false };

// helpers

fn hm_value(hash: &[u8]) -> PathPart<'_> {
    PathPart::HashMapGet(HashMapGetTarget::Value(hash))
}

fn hm_key(hash: &[u8]) -> PathPart<'_> {
    PathPart::HashMapGet(HashMapGetTarget::Key(hash))
}

/// Like Go's ReadPathSlot, which returns an empty slot when the path
/// doesn't exist.
fn last_slot_data<C: Core>(cursor: &ReadCursor<'_, C>) -> Slot {
    cursor.read_path_slot(&[PathPart::ArrayListGet(-1)]).unwrap().unwrap_or_default()
}

fn rollback_error() -> Error {
    Error::Io(io::Error::other("rollback"))
}

fn is_rollback(err: &Error) -> bool {
    matches!(err, Error::Io(e) if e.to_string() == "rollback")
}

/// The xitdb error inside an io::Error returned by a CursorWriter.
fn inner_error(err: &io::Error) -> Option<&Error> {
    err.get_ref().and_then(|e| e.downcast_ref::<Error>())
}

/// Reads the slot stored at `position` straight from the core.
fn read_slot_at<C: Core>(db: &Database<C>, position: i64) -> Slot {
    let mut core = db.core();
    core.seek_to(position as u64).unwrap();
    let mut buf = [0u8; SLOT_LENGTH];
    core.read(&mut buf).unwrap();
    Slot::from_bytes(&buf).unwrap()
}

fn s(bytes: Vec<u8>) -> String {
    String::from_utf8(bytes).unwrap()
}

// TestFrozenWriters

fn read_value_by_key<'a, C: Core + 'a>(cursor: impl Into<ReadCursor<'a, C>>, key: &str) -> i64 {
    let m = ReadHashMap::new(cursor).unwrap();
    let value_cursor = m.get_cursor(key).unwrap().unwrap();
    value_cursor.read_int().unwrap()
}

#[test]
fn frozen_writers() {
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    let result = db
        .root_cursor()
        .write_path_context(&[PathPart::ArrayListAppend, HASH_MAP_INIT], |cursor| {
            let mut m = WriteHashMap::new(cursor).unwrap();
            m.put("v", Data::Int(1)).unwrap();
            let mut child_cursor = m.put_cursor("child").unwrap();
            let mut child = WriteHashMap::new(&mut child_cursor).unwrap();
            child.put("v", Data::Int(2)).unwrap();
            let mut equivalent = m.write_cursor().clone().write_path(&[]).unwrap();
            let frozen = ReadHashMap::new(ReadCursor::new(m.cursor().slot_ptr, &db)).unwrap();
            db.freeze().unwrap();
            assert!(matches!(child.put("v", Data::Int(999)), Err(Error::FrozenSlot)));
            let v_hash = db.digest(b"v");
            equivalent.write_path(&[hm_value(&v_hash), PathPart::WriteData(&Data::Int(999))]).unwrap();
            m.put("v", Data::Int(3)).unwrap();
            let mut child_cursor = m.put_cursor("child").unwrap();
            let mut child = WriteHashMap::new(&mut child_cursor).unwrap();
            child.put("v", Data::Int(4)).unwrap();
            assert_eq!(1, read_value_by_key(frozen.cursor(), "v"));
            let frozen_child = frozen.get_cursor("child").unwrap().unwrap();
            assert_eq!(2, read_value_by_key(frozen_child, "v"));
            assert_eq!(3, read_value_by_key(m.cursor(), "v"));
            Ok(())
        })
        .unwrap();
    assert_eq!(3, read_value_by_key(result.read_cursor(), "v"));
    let slot = history.get_slot(0).unwrap().unwrap_or_default();
    assert_eq!(slot, result.slot().unwrap());

    let mut frozen: Option<ReadCursor<'_, CoreMemory>> = None;
    let err = history
        .append_context(Data::None, |cursor| {
            let position = cursor.slot_ptr().position;
            let mut writer = cursor.writer().unwrap();
            writer.write_all(&[0u8; 16]).unwrap();
            writer.finish().unwrap();
            // the writer borrows the cursor, so read the slot that finish
            // wrote to it (Go reads cursor.SlotPtr here)
            frozen = Some(ReadCursor::new(SlotPointer::new(position, read_slot_at(&db, position.unwrap())), &db));
            db.freeze().unwrap();
            writer.seek_to(0);
            let err = writer.write(&[99]).unwrap_err();
            assert!(matches!(inner_error(&err), Some(Error::FrozenBytes)), "{err:?}");
            assert!(matches!(writer.finish(), Err(Error::FrozenBytes)));
            let mut next = cursor.writer().unwrap();
            next.write_all(&[0u8; 16]).unwrap();
            next.finish().unwrap();
            let value = frozen.as_ref().unwrap().read_bytes(MAX_READ).unwrap();
            assert_eq!(vec![0u8; 16], value, "frozen bytes changed");
            Err(rollback_error())
        })
        .unwrap_err();
    assert!(is_rollback(&err), "{err:?}");
    let frozen = frozen.unwrap();
    let value = frozen.read_bytes(MAX_READ).unwrap();
    assert_eq!(vec![0u8; 16], value, "frozen bytes changed after rollback");
    let appended = history.append_cursor().unwrap();
    assert_eq!(Tag::None, appended.slot().unwrap().tag);
    let slot = history.get_slot(-1).unwrap().unwrap_or_default();
    assert_eq!(Slot::default(), slot);
    {
        let panicked = catch_unwind(AssertUnwindSafe(|| {
            history
                .append_context(Data::bytes(vec![0u8; 16]), |_cursor| std::panic::panic_any("rollback"))
                .unwrap();
        }));
        let payload = panicked.unwrap_err();
        assert_eq!(Some(&"rollback"), payload.downcast_ref::<&str>());
    }
    history.append(Data::string("abcdefghijklmnop")).unwrap();
    let count = history.count().unwrap();
    assert_eq!(3, count);
    let value = frozen.read_bytes(MAX_READ).unwrap();
    assert_eq!(vec![0u8; 16], value, "frozen bytes changed after later writes");
}

// TestExpiredWriters

fn reject<C: Core>(escaped: &mut WriteHashMap<'_, C>, writer: &mut CursorWriter<'_, '_, C>) {
    assert!(matches!(escaped.put("v", Data::Int(999)), Err(Error::ExpiredTransaction)));
    let err = writer.write(&[1]).unwrap_err();
    assert!(matches!(inner_error(&err), Some(Error::ExpiredTransaction)), "{err:?}");
    assert!(matches!(writer.finish(), Err(Error::ExpiredTransaction)));
}

fn read_history_value<C: Core>(history: &WriteArrayList<'_, C>, index: i64) -> i64 {
    let cursor = history.get_cursor(index).unwrap().unwrap();
    let moment = ReadHashMap::new(cursor).unwrap();
    let value_cursor = moment.get_cursor("v").unwrap().unwrap();
    value_cursor.read_int().unwrap()
}

#[test]
fn expired_writers() {
    let db = Database::new(CoreMemory::new(), Hasher::sha1()).unwrap();
    let mut history = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    let err = db.root_cursor().write_path_context(&[], |_cursor| history.append(Data::Int(999))).unwrap_err();
    // the callback runs inside a transaction on the root,
    // so the top-level write inside it is a nested one
    assert!(matches!(err, Error::NestedTopLevelWrite), "{err:?}");
    let count = history.count().unwrap();
    assert_eq!(0, count);

    // Go uses `history` itself inside its own callbacks; Rust's borrow rules
    // need a second handle to the same top-level list for that
    let mut inner_history = WriteArrayList::new(&mut db.root_cursor()).unwrap();

    let mut escaped: Option<WriteHashMap<'_, CoreMemory>> = None;
    let mut bytes_cursor: Option<WriteCursor<'_, CoreMemory>> = None;
    let mut writer: Option<CursorWriter<'_, '_, CoreMemory>> = None;
    {
        let (escaped_ref, bytes_cursor_ref, writer_ref, inner_history) =
            (&mut escaped, &mut bytes_cursor, &mut writer, &mut inner_history);
        history
            .append_context(Data::None, move |cursor| {
                // move the references so the closure is FnOnce and the
                // writer can outlive it, like in Go
                let (escaped_ref, bytes_cursor_ref, writer_ref) = (escaped_ref, bytes_cursor_ref, writer_ref);
                let escaped = escaped_ref.insert(WriteHashMap::new(cursor).unwrap());
                escaped.put("v", Data::Int(1)).unwrap();
                let bytes_cursor = bytes_cursor_ref.insert(escaped.put_cursor("bytes").unwrap());
                let writer = writer_ref.insert(bytes_cursor.writer().unwrap());
                writer.write_all(&[0u8; 16]).unwrap();
                writer.finish().unwrap();
                assert!(matches!(inner_history.append(Data::Int(999)), Err(Error::NestedTopLevelWrite)));
                assert!(matches!(inner_history.slice(0), Err(Error::NestedTopLevelWrite)));
                Ok(())
            })
            .unwrap();
    }
    reject(escaped.as_mut().unwrap(), writer.as_mut().unwrap());
    let slot = history.get_slot(0).unwrap().unwrap_or_default();
    history
        .append_context(slot, |cursor| {
            reject(escaped.as_mut().unwrap(), writer.as_mut().unwrap());
            let mut current = WriteHashMap::new(cursor).unwrap();
            current.put("v", Data::Int(2))
        })
        .unwrap();
    assert_eq!(1, read_history_value(&history, 0));
    assert_eq!(2, read_history_value(&history, 1));
    let err = history
        .append_context(Data::None, |cursor| {
            escaped = Some(WriteHashMap::new(cursor).unwrap());
            Err(rollback_error())
        })
        .unwrap_err();
    assert!(is_rollback(&err), "{err:?}");
    reject(escaped.as_mut().unwrap(), writer.as_mut().unwrap());
    let slot = history.get_slot(1).unwrap().unwrap_or_default();
    history
        .append_context(slot, |_cursor| {
            reject(escaped.as_mut().unwrap(), writer.as_mut().unwrap());
            Ok(())
        })
        .unwrap();
    assert_eq!(2, read_history_value(&history, 2));
}

// TestLowLevelApi

#[test]
fn low_level_api() {
    // CoreMemory
    {
        let mut core = CoreMemory::new();
        let hasher = Hasher::sha1();
        test_low_level_api(&mut core, &hasher);
    }

    // CoreFile
    {
        let file = tempfile::tempfile().unwrap();
        let mut core = CoreFile::new(file);
        let hasher = Hasher::sha1();
        test_low_level_api(&mut core, &hasher);
    }

    // CoreBufferedFile
    {
        let file = tempfile::tempfile().unwrap();
        let mut core = CoreBufferedFile::with_buffer_size(file, 1024);
        let hasher = Hasher::sha1();
        test_low_level_api(&mut core, &hasher);
        core.close().unwrap();
    }
}

// TestLowLevelMemoryOperations

#[test]
fn low_level_memory_operations() {
    let core = CoreMemory::new();
    let hasher = Hasher::sha1();
    let db = Database::new(core, hasher).unwrap();

    // every write to the root is a transaction, so the
    // cursor writer must be used inside one
    let hash_val = db.digest(b"text");
    let mut text_cursor: Option<WriteCursor<'_, CoreMemory>> = None;
    db.run_context(|cursor| {
        let text_cursor = text_cursor.insert(cursor.write_path(&[HASH_MAP_INIT, hm_value(&hash_val)])?);
        let mut writer = text_cursor.writer()?;
        writer.write_all(b"goodbye, world!")?;
        writer.seek_to(9);
        writer.write_all(b"cruel world!")?;
        writer.finish()
    })
    .unwrap();

    let mut reader = text_cursor.as_ref().unwrap().reader().unwrap();
    let all_bytes = reader.read_all().unwrap();
    assert_eq!("goodbye, cruel world!", s(all_bytes));

    let mut core = db.core();
    core.set_length(0).unwrap();
    let data = [1u8, 2, 3, 4];
    core.write(&data).unwrap();
    core.seek_to(1).unwrap();

    // invalid lengths must leave the contents and position alone
    for length in [5i64, -1, i64::MIN] {
        assert!(core.set_length(length as u64).is_err(), "expected invalid length error for {length}");
        let position = core.position().unwrap();
        assert_eq!(1, position);
        assert_eq!(&data[..], core.as_bytes());
    }

    // truncation preserves an earlier position and clamps one past the end
    core.set_length(3).unwrap();
    let position = core.position().unwrap();
    assert_eq!(1, position);
    core.set_length(3).unwrap();
    let position = core.position().unwrap();
    assert_eq!(1, position);
    core.seek_to(3).unwrap();
    core.set_length(2).unwrap();
    let length = core.length().unwrap();
    assert_eq!(2, length);
    let position = core.position().unwrap();
    assert_eq!(2, position);
    assert_eq!(&[1u8, 2][..], core.as_bytes());
    assert!(core.read(&mut [0u8; 1]).is_err(), "expected end of memory error");
    core.write(&[9]).unwrap();
    assert_eq!(&[1u8, 2, 9][..], core.as_bytes());
}

fn test_slice<C: Core>(core: &mut C, hasher: &Hasher, original_size: usize, slice_offset: i64, slice_size: i64) {
    core.set_length(0).unwrap();
    let db = Database::new(&mut *core, hasher.clone()).unwrap();
    let mut root_cursor = db.root_cursor();

    let last_slot = root_cursor.read_path_slot(&[PathPart::ArrayListGet(-1)]).unwrap();
    let last_slot = Data::from(last_slot);
    let even = db.digest(b"even");
    let even_slice = db.digest(b"even-slice");
    let combo = db.digest(b"combo");
    root_cursor
        .write_path_context(
            &[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot), HASH_MAP_INIT],
            |cursor| {
                let mut values: Vec<i64> = Vec::new();

                // create list
                for i in 0..original_size {
                    let n = i as i64 * 2;
                    values.push(n);
                    cursor.write_path(&[
                        hm_value(&even),
                        PathPart::LinkedArrayListInit,
                        PathPart::LinkedArrayListAppend,
                        PathPart::WriteData(&Data::Uint(n as u64)),
                    ])?;
                }

                // slice list
                let even_list_cursor = cursor.read_path(&[hm_value(&even)])?.unwrap();
                let even_list_slice_cursor = cursor.write_path(&[
                    hm_value(&even_slice),
                    PathPart::WriteData(&Data::Slot(even_list_cursor.slot_ptr.slot)),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListSlice { offset: slice_offset, size: slice_size },
                ])?;

                // check all the values in the new slice
                for i in 0..slice_size {
                    let val = values[(slice_offset + i) as usize];
                    let rc = cursor.read_path(&[hm_value(&even_slice), PathPart::LinkedArrayListGet(i)])?.unwrap();
                    let n = rc.slot_ptr.slot.value;
                    assert_eq!(val, n, "expected {val}, got {n}");
                }

                // check all values in the new slice with an iterator
                {
                    let mut i = 0i64;
                    for num_cursor in even_list_slice_cursor.iter()? {
                        let num_cursor = num_cursor?;
                        let uval = num_cursor.read_uint()?;
                        assert_eq!(values[(slice_offset + i) as usize] as u64, uval);
                        i += 1;
                    }
                    assert_eq!(slice_size, i, "expected {slice_size} iterations, got {i}");
                }

                // there are no extra items
                let rc = cursor.read_path(&[hm_value(&even_slice), PathPart::LinkedArrayListGet(slice_size)])?;
                assert!(rc.is_none(), "expected nil cursor");

                // concat the slice with itself
                cursor.write_path(&[
                    hm_value(&combo),
                    PathPart::WriteData(&Data::Slot(even_list_slice_cursor.slot_ptr().slot)),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListConcat(even_list_slice_cursor.slot_ptr().slot),
                ])?;

                // check all values in the combo list
                let range = slice_offset as usize..(slice_offset + slice_size) as usize;
                let mut combo_values: Vec<i64> = Vec::new();
                combo_values.extend_from_slice(&values[range.clone()]);
                combo_values.extend_from_slice(&values[range]);
                for (i, expected) in combo_values.iter().enumerate() {
                    let rc = cursor.read_path(&[hm_value(&combo), PathPart::LinkedArrayListGet(i as i64)])?.unwrap();
                    let n = rc.slot_ptr.slot.value;
                    assert_eq!(*expected, n, "expected {expected}, got {n}");
                }

                // append to the slice
                cursor.write_path(&[
                    hm_value(&even_slice),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListAppend,
                    PathPart::WriteData(&Data::Uint(3)),
                ])?;

                // read the new value from the slice
                let rc = cursor.read_path(&[hm_value(&even_slice), PathPart::LinkedArrayListGet(-1)])?.unwrap();
                assert_eq!(3, rc.slot_ptr.slot.value, "expected 3, got {}", rc.slot_ptr.slot.value);

                Ok(())
            },
        )
        .unwrap();
}

fn test_concat<C: Core>(core: &mut C, hasher: &Hasher, list_a_size: i64, list_b_size: i64) {
    core.set_length(0).unwrap();
    let db = Database::new(&mut *core, hasher.clone()).unwrap();
    let mut root_cursor = db.root_cursor();

    let mut values: Vec<i64> = Vec::new();
    let even = db.digest(b"even");
    let odd = db.digest(b"odd");
    let combo = db.digest(b"combo");

    let last_slot = Data::from(root_cursor.read_path_slot(&[PathPart::ArrayListGet(-1)]).unwrap());
    root_cursor
        .write_path_context(
            &[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot), HASH_MAP_INIT],
            |cursor| {
                // create even list
                cursor.write_path(&[hm_value(&even), PathPart::LinkedArrayListInit])?;
                for i in 0..list_a_size {
                    let n = i * 2;
                    values.push(n);
                    cursor.write_path(&[
                        hm_value(&even),
                        PathPart::LinkedArrayListInit,
                        PathPart::LinkedArrayListAppend,
                        PathPart::WriteData(&Data::Uint(n as u64)),
                    ])?;
                }

                // create odd list
                cursor.write_path(&[hm_value(&odd), PathPart::LinkedArrayListInit])?;
                for i in 0..list_b_size {
                    let n = (i * 2) + 1;
                    values.push(n);
                    cursor.write_path(&[
                        hm_value(&odd),
                        PathPart::LinkedArrayListInit,
                        PathPart::LinkedArrayListAppend,
                        PathPart::WriteData(&Data::Uint(n as u64)),
                    ])?;
                }

                Ok(())
            },
        )
        .unwrap();

    let last_slot2 = Data::from(root_cursor.read_path_slot(&[PathPart::ArrayListGet(-1)]).unwrap());
    root_cursor
        .write_path_context(
            &[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot2), HASH_MAP_INIT],
            |cursor| {
                // get the even list
                let even_list_cursor = cursor.read_path(&[hm_value(&even)])?.unwrap();

                // get the odd list
                let odd_list_cursor = cursor.read_path(&[hm_value(&odd)])?.unwrap();

                // concat the lists
                let combo_list_cursor = cursor.write_path(&[
                    hm_value(&combo),
                    PathPart::WriteData(&Data::Slot(even_list_cursor.slot_ptr.slot)),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListConcat(odd_list_cursor.slot_ptr.slot),
                ])?;

                // check all values in the new list
                for (i, expected) in values.iter().enumerate() {
                    let rc = cursor.read_path(&[hm_value(&combo), PathPart::LinkedArrayListGet(i as i64)])?.unwrap();
                    let n = rc.slot_ptr.slot.value;
                    assert_eq!(*expected, n, "expected {expected}, got {n}");
                }

                // check all values in the new slice with an iterator
                {
                    let mut i = 0usize;
                    for num_cursor in combo_list_cursor.iter()? {
                        let num_cursor = num_cursor?;
                        let uval = num_cursor.read_uint()?;
                        assert_eq!(values[i] as u64, uval);
                        i += 1;
                    }
                    let even_count = even_list_cursor.count()?;
                    let odd_count = odd_list_cursor.count()?;
                    assert_eq!(even_count + odd_count, i as i64, "expected {} iterations, got {i}", even_count + odd_count);
                }

                // there are no extra items
                let rc = cursor.read_path(&[hm_value(&combo), PathPart::LinkedArrayListGet(values.len() as i64)])?;
                assert!(rc.is_none(), "expected nil cursor");

                Ok(())
            },
        )
        .unwrap();
}

fn test_insert_and_remove<C: Core>(core: &mut C, hasher: &Hasher, original_size: usize, insert_index: i64) {
    core.set_length(0).unwrap();
    let db = Database::new(&mut *core, hasher.clone()).unwrap();
    let mut root_cursor = db.root_cursor();

    let insert_value: i64 = 12345;
    let even = db.digest(b"even");
    let even_insert = db.digest(b"even-insert");

    let last_slot = Data::from(root_cursor.read_path_slot(&[PathPart::ArrayListGet(-1)]).unwrap());
    root_cursor
        .write_path_context(
            &[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot), HASH_MAP_INIT],
            |cursor| {
                let mut values: Vec<i64> = Vec::new();

                // create list
                for i in 0..original_size {
                    if i as i64 == insert_index {
                        values.push(insert_value);
                    }
                    let n = i as i64 * 2;
                    values.push(n);
                    cursor.write_path(&[
                        hm_value(&even),
                        PathPart::LinkedArrayListInit,
                        PathPart::LinkedArrayListAppend,
                        PathPart::WriteData(&Data::Uint(n as u64)),
                    ])?;
                }

                // insert into list
                let even_list_cursor = cursor.read_path(&[hm_value(&even)])?.unwrap();
                let mut even_list_insert_cursor = cursor.write_path(&[
                    hm_value(&even_insert),
                    PathPart::WriteData(&Data::Slot(even_list_cursor.slot_ptr.slot)),
                    PathPart::LinkedArrayListInit,
                ])?;
                even_list_insert_cursor.write_path(&[
                    PathPart::LinkedArrayListInsert(insert_index),
                    PathPart::WriteData(&Data::Uint(insert_value as u64)),
                ])?;

                // check all the values in the new list
                for (i, val) in values.iter().enumerate() {
                    let rc =
                        cursor.read_path(&[hm_value(&even_insert), PathPart::LinkedArrayListGet(i as i64)])?.unwrap();
                    let n = rc.slot_ptr.slot.value;
                    assert_eq!(*val, n, "expected {val}, got {n}");
                }

                // check all values in the new list with an iterator
                {
                    let mut i = 0usize;
                    for num_cursor in even_list_insert_cursor.iter()? {
                        let num_cursor = num_cursor?;
                        let uval = num_cursor.read_uint()?;
                        assert_eq!(values[i] as u64, uval);
                        i += 1;
                    }
                    assert_eq!(values.len(), i, "expected {} iterations, got {i}", values.len());
                }

                // there are no extra items
                let rc =
                    cursor.read_path(&[hm_value(&even_insert), PathPart::LinkedArrayListGet(values.len() as i64)])?;
                assert!(rc.is_none(), "expected nil cursor");

                Ok(())
            },
        )
        .unwrap();

    let last_slot2 = Data::from(root_cursor.read_path_slot(&[PathPart::ArrayListGet(-1)]).unwrap());
    root_cursor
        .write_path_context(
            &[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot2), HASH_MAP_INIT],
            |cursor| {
                let mut values: Vec<i64> = Vec::new();

                for i in 0..original_size {
                    let n = i as i64 * 2;
                    values.push(n);
                }

                // remove inserted value from the list
                let even_list_insert_cursor =
                    cursor.write_path(&[hm_value(&even_insert), PathPart::LinkedArrayListRemove(insert_index)])?;

                // check all the values in the new list
                for (i, val) in values.iter().enumerate() {
                    let rc =
                        cursor.read_path(&[hm_value(&even_insert), PathPart::LinkedArrayListGet(i as i64)])?.unwrap();
                    let n = rc.slot_ptr.slot.value;
                    assert_eq!(*val, n, "expected {val}, got {n}");
                }

                // check all values in the new list with an iterator
                {
                    let mut i = 0usize;
                    for num_cursor in even_list_insert_cursor.iter()? {
                        let num_cursor = num_cursor?;
                        let uval = num_cursor.read_uint()?;
                        assert_eq!(values[i] as u64, uval);
                        i += 1;
                    }
                    assert_eq!(values.len(), i, "expected {} iterations, got {i}", values.len());
                }

                // there are no extra items
                let rc =
                    cursor.read_path(&[hm_value(&even_insert), PathPart::LinkedArrayListGet(values.len() as i64)])?;
                assert!(rc.is_none(), "expected nil cursor");

                Ok(())
            },
        )
        .unwrap();
}

/// The tag of the slot for `key` in the index block of the hash map at the
/// end of the history, read straight from the core.
fn hash_map_index_slot_tag<C: Core>(db: &Database<C>, root_cursor: &WriteCursor<'_, C>, key: &[u8]) -> Tag {
    let map_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1)]).unwrap().unwrap();
    let map_slot = map_cursor.slot().unwrap();
    let index_pos = map_slot.value;
    assert_eq!(Tag::HashMap, map_slot.tag);

    // the hash as a big-endian integer, masked with BigMask
    let idx = (key[key.len() - 1] as i64) & (SLOT_COUNT as i64 - 1);
    let slot_pos = index_pos + (SLOT_LENGTH as i64 * idx);
    read_slot_at(db, slot_pos).tag
}

fn read_string<C: Core>(cursor: Option<ReadCursor<'_, C>>) -> String {
    s(cursor.expect("expected non-nil cursor").read_bytes(MAX_READ).unwrap())
}

fn test_low_level_api<C: Core>(core: &mut C, hasher: &Hasher) {
    // open and re-open database
    {
        // make empty database
        core.set_length(0).unwrap();
        Database::new(&mut *core, hasher.clone()).unwrap();

        // re-open without error
        Database::new(&mut *core, hasher.clone()).unwrap();
        core.seek_to(0).unwrap();
        core.write(b"g").unwrap();

        // re-open with error
        let err = Database::new(&mut *core, hasher.clone()).unwrap_err();
        assert!(matches!(err, Error::InvalidDatabase), "expected InvalidDatabase, got {err:?}");

        // modify the version
        core.seek_to(0).unwrap();
        core.write(b"x").unwrap();
        core.seek_to(4).unwrap();
        core.write(&(VERSION + 1).to_be_bytes()).unwrap();

        // re-open with error
        let err = Database::new(&mut *core, hasher.clone()).unwrap_err();
        assert!(matches!(err, Error::InvalidVersion), "expected InvalidVersion, got {err:?}");
    }

    // save hash id in header
    {
        let hasher_with_hash_id = Hasher::new(|data| sha1::Sha1::digest(data).to_vec()).with_id(*b"sha1");

        // make empty database
        core.set_length(0).unwrap();
        Database::new(&mut *core, hasher_with_hash_id).unwrap();

        // read header without initializing database
        core.seek_to(0).unwrap();
        let header = Header::read(core).unwrap();
        assert_eq!(20u16, header.hash_size);
        assert_eq!(*b"sha1", id_to_bytes(header.hash_id));

        // determine the hashing algorithm
        let determined_hasher = match &id_to_bytes(header.hash_id) {
            b"sha1" => {
                let mut h = Hasher::new(|data| sha1::Sha1::digest(data).to_vec());
                h.id = header.hash_id;
                h
            }
            _ => panic!("Invalid hash algorithm"),
        };
        assert_eq!(20, determined_hasher.hash_size());
    }

    // array_list of hash_maps
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        // write foo -> bar with a writer
        let foo_key = db.digest(b"foo");
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path_context(
                &[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&foo_key),
                ],
                |cursor| {
                    assert_eq!(Tag::None, cursor.slot().unwrap().tag);
                    let mut writer = cursor.writer()?;
                    writer.write_all(b"bar")?;
                    writer.finish()
                },
            )
            .unwrap();

        // read foo
        {
            let bar_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap().unwrap();
            let count = bar_cursor.count().unwrap();
            assert_eq!(3, count);
            let bar_value = bar_cursor.read_bytes(MAX_READ).unwrap();
            assert_eq!("bar", s(bar_value));
        }

        // read foo from ctx
        {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path_context(
                    &[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&foo_key),
                    ],
                    |cursor| {
                        assert_ne!(Tag::None, cursor.slot().unwrap().tag, "expected tag != TagNone");

                        let value = cursor.read_bytes(MAX_READ)?;
                        assert_eq!("bar", s(value));

                        let mut bar_reader = cursor.reader()?;

                        // read into buffer
                        let mut bar_bytes = [0u8; 10];
                        let bar_size = bar_reader.read(&mut bar_bytes)?;
                        assert_eq!(b"bar", &bar_bytes[..bar_size]);
                        bar_reader.seek_to(0)?;
                        let bar_size = bar_reader.read(&mut bar_bytes)?;
                        assert_eq!(3, bar_size);
                        assert_eq!(b"bar", &bar_bytes[..3]);

                        // read one char at a time
                        {
                            let mut ch = [0u8; 1];
                            bar_reader.seek_to(0)?;

                            bar_reader.read_fully(&mut ch)?;
                            assert_eq!(b"b", &ch);

                            bar_reader.read_fully(&mut ch)?;
                            assert_eq!(b"a", &ch);

                            bar_reader.read_fully(&mut ch)?;
                            assert_eq!(b"r", &ch);

                            let err = bar_reader.read_fully(&mut ch).unwrap_err();
                            assert!(matches!(err, Error::EndOfStream), "expected EndOfStream, got {err:?}");

                            bar_reader.seek_to(1)?;
                            let b = bar_reader.read_u8()?;
                            assert_eq!(b'a', b);

                            bar_reader.seek_to(0)?;
                            let b = bar_reader.read_u8()?;
                            assert_eq!(b'b', b);
                        }
                        Ok(())
                    },
                )
                .unwrap();
        }

        // overwrite foo -> baz
        {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path_context(
                    &[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&foo_key),
                    ],
                    |cursor| {
                        assert_ne!(Tag::None, cursor.slot().unwrap().tag, "expected tag != TagNone");

                        let mut writer = cursor.writer()?;
                        writer.write_all(b"x")?;
                        writer.write_all(b"x")?;
                        writer.write_all(b"x")?;
                        writer.seek_to(0);
                        writer.write_all(b"b")?;
                        writer.seek_to(2);
                        writer.write_all(b"z")?;
                        writer.seek_to(1);
                        writer.write_all(b"a")?;
                        writer.finish()?;

                        let value = cursor.read_bytes(MAX_READ)?;
                        assert_eq!("baz", s(value));
                        Ok(())
                    },
                )
                .unwrap();
        }

        // if error in ctx, db doesn't change
        {
            let size_before = db.core().length().unwrap();

            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let write_result = root_cursor.write_path_context(
                &[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&foo_key),
                ],
                |cursor| {
                    let mut writer = cursor.writer()?;
                    writer.write_all(b"this value won't be visible")?;
                    writer.finish()?;
                    Err(Error::Io(io::Error::other("intentional error")))
                },
            );
            // we expect an error here
            let _ = write_result;

            // read foo
            let value_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap().unwrap();
            let value = value_cursor.read_bytes(None).unwrap(); // make sure None (no limit) max size works
            assert_eq!("baz", s(value));

            // verify that the db is properly truncated back to its original size after error
            let size_after = db.core().length().unwrap();
            assert_eq!(size_before, size_after);
        }

        // write bar -> longstring
        let bar_key = db.digest(b"bar");
        {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let bar_cursor = root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&bar_key),
                    PathPart::WriteData(&Data::string("longstring")),
                ])
                .unwrap();

            // the slot tag is BYTES because the byte array is > 8 bytes long
            assert_eq!(Tag::Bytes, bar_cursor.slot().unwrap().tag);

            // writing again returns the same slot
            {
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                let next_bar_cursor = root_cursor
                    .write_path_context(
                        &[
                            PathPart::ArrayListInit,
                            PathPart::ArrayListAppend,
                            PathPart::WriteData(&last_slot),
                            HASH_MAP_INIT,
                            hm_value(&bar_key),
                        ],
                        |cursor| cursor.write_if_empty(Data::string("longstring")),
                    )
                    .unwrap();
                assert_eq!(bar_cursor.slot().unwrap().value, next_bar_cursor.slot().unwrap().value);
            }

            // writing with write returns a new slot
            {
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                let next_bar_cursor = root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&bar_key),
                        PathPart::WriteData(&Data::string("longstring")),
                    ])
                    .unwrap();
                assert_ne!(
                    bar_cursor.slot().unwrap().value,
                    next_bar_cursor.slot().unwrap().value,
                    "expected different slot values"
                );
            }
        }

        // read bar
        {
            let read_bar_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&bar_key)]).unwrap();
            assert_eq!("longstring", read_string(read_bar_cursor));
        }

        // write bar -> shortstr
        {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let bar_cursor = root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&bar_key),
                    PathPart::WriteData(&Data::string("shortstr")),
                ])
                .unwrap();

            // the slot tag is SHORT_BYTES because the byte array is <= 8 bytes long
            assert_eq!(Tag::ShortBytes, bar_cursor.slot().unwrap().tag);
            let count = bar_cursor.count().unwrap();
            assert_eq!(8, count);

            // make sure that SHORT_BYTES can be read with a reader
            let mut bar_reader = bar_cursor.reader().unwrap();
            let mut bar_value = vec![0u8; count as usize];
            bar_reader.read_fully(&mut bar_value).unwrap();
            assert_eq!("shortstr", s(bar_value));
        }

        // write bytes with a format tag
        {
            // (value, expected tag, expected count)
            let cases: [(&str, Tag, i64); 3] = [
                // the slot tag is BYTES because the byte array is > 8 bytes long including the format tag
                ("shortstr", Tag::Bytes, 8),
                // the slot tag is SHORT_BYTES because the byte array is <= 8 bytes long including the format tag
                ("shorts", Tag::ShortBytes, 6),
                ("short", Tag::ShortBytes, 5),
            ];
            for (value, expected_tag, expected_count) in cases {
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                let bar_cursor = root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&bar_key),
                        PathPart::WriteData(&Data::tagged_string(value, *b"st")),
                    ])
                    .unwrap();

                assert_eq!(expected_tag, bar_cursor.slot().unwrap().tag, "{value}");
                let count = bar_cursor.count().unwrap();
                assert_eq!(expected_count, count, "{value}");

                // read bar
                let read_bar_cursor =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&bar_key)]).unwrap().unwrap();
                let bar_bytes_obj = read_bar_cursor.read_bytes_object(MAX_READ).unwrap();
                assert_eq!(value.as_bytes(), &bar_bytes_obj.value[..]);
                assert_eq!(Some(*b"st"), bar_bytes_obj.format_tag);

                // make sure that BYTES / SHORT_BYTES can be read with a reader
                let mut bar_reader = bar_cursor.reader().unwrap();
                let mut bar_value = vec![0u8; count as usize];
                bar_reader.read_fully(&mut bar_value).unwrap();
                assert_eq!(value, s(bar_value));
            }
        }

        // read foo into buffer
        {
            let bar_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap();
            assert_eq!("baz", read_string(bar_cursor));
        }

        // write bar and get a pointer to it
        {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let bar_slot_cursor = root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&bar_key),
                    PathPart::WriteData(&Data::string("bar")),
                ])
                .unwrap();
            let bar_slot = bar_slot_cursor.slot().unwrap();

            // overwrite foo -> bar using the bar pointer
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&foo_key),
                    PathPart::WriteData(&Data::Slot(bar_slot)),
                ])
                .unwrap();
            let bar_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap();
            assert_eq!("bar", read_string(bar_cursor));

            // can still read the old value
            let baz_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-2), hm_value(&foo_key)]).unwrap();
            assert_eq!("baz", read_string(baz_cursor));

            // key not found
            let not_found_key = db.digest(b"this doesn't exist");
            let not_found_cursor =
                root_cursor.read_path(&[PathPart::ArrayListGet(-2), hm_value(&not_found_key)]).unwrap();
            assert!(not_found_cursor.is_none(), "expected nil cursor");

            // write key that conflicts with foo the first two bytes
            let mut small_conflict_key = db.digest(b"small conflict");
            let n = small_conflict_key.len();
            small_conflict_key[n - 1] = foo_key[n - 1];
            small_conflict_key[n - 2] = foo_key[n - 2];
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&small_conflict_key),
                    PathPart::WriteData(&Data::string("small")),
                ])
                .unwrap();

            // write key that conflicts with foo the first four bytes
            let mut conflict_key = db.digest(b"conflict");
            let n = conflict_key.len();
            conflict_key[n - 1] = foo_key[n - 1];
            conflict_key[n - 2] = foo_key[n - 2];
            conflict_key[n - 3] = foo_key[n - 3];
            conflict_key[n - 4] = foo_key[n - 4];
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&conflict_key),
                    PathPart::WriteData(&Data::string("hello")),
                ])
                .unwrap();

            // read conflicting key
            let hello_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&conflict_key)]).unwrap();
            assert_eq!("hello", read_string(hello_cursor));

            // we can still read foo
            let bar_cursor2 = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap();
            assert_eq!("bar", read_string(bar_cursor2));

            // overwrite conflicting key
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&conflict_key),
                    PathPart::WriteData(&Data::string("goodbye")),
                ])
                .unwrap();
            let goodbye_cursor =
                root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&conflict_key)]).unwrap();
            assert_eq!("goodbye", read_string(goodbye_cursor));

            // we can still read the old conflicting key
            let hello_cursor2 = root_cursor.read_path(&[PathPart::ArrayListGet(-2), hm_value(&conflict_key)]).unwrap();
            assert_eq!("hello", read_string(hello_cursor2));

            // remove the conflicting keys
            {
                // foo's slot is an INDEX slot due to the conflict
                assert_eq!(Tag::Index, hash_map_index_slot_tag(&db, &root_cursor, &foo_key));

                // remove the small conflict key
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        PathPart::HashMapRemove(&small_conflict_key),
                    ])
                    .unwrap();

                // the conflict key still exists in history
                let sc_cursor =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-2), hm_value(&small_conflict_key)]).unwrap();
                assert!(sc_cursor.is_some(), "expected non-nil cursor");

                // the conflict key doesn't exist in the latest moment
                let sc_cursor2 =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&small_conflict_key)]).unwrap();
                assert!(sc_cursor2.is_none(), "expected nil cursor");

                // the other conflict key still exists
                let ck_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&conflict_key)]).unwrap();
                assert!(ck_cursor.is_some(), "expected non-nil cursor");

                // foo's slot is still an INDEX slot due to the other conflicting key
                assert_eq!(Tag::Index, hash_map_index_slot_tag(&db, &root_cursor, &foo_key));

                // remove the conflict key
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        PathPart::HashMapRemove(&conflict_key),
                    ])
                    .unwrap();

                // the conflict keys don't exist in the latest moment
                let sc_cursor3 =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&small_conflict_key)]).unwrap();
                assert!(sc_cursor3.is_none(), "expected nil cursor");
                let ck_cursor2 =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&conflict_key)]).unwrap();
                assert!(ck_cursor2.is_none(), "expected nil cursor");

                // foo's slot is now a KV_PAIR slot, because the branch was shortened
                assert_eq!(Tag::KvPair, hash_map_index_slot_tag(&db, &root_cursor, &foo_key));
            }

            {
                // overwrite foo with a uint
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&foo_key),
                        PathPart::WriteData(&Data::Uint(42)),
                    ])
                    .unwrap();

                // read foo
                let uint_cursor =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap().unwrap();
                let uint_value = uint_cursor.read_uint().unwrap();
                assert_eq!(42u64, uint_value);
            }

            {
                // overwrite foo with a int
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&foo_key),
                        PathPart::WriteData(&Data::Int(-42)),
                    ])
                    .unwrap();

                // read foo
                let int_cursor =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap().unwrap();
                let int_value = int_cursor.read_int().unwrap();
                assert_eq!(-42i64, int_value);
            }

            {
                // overwrite foo with a float
                let last_slot = Data::Slot(last_slot_data(&root_cursor));
                root_cursor
                    .write_path(&[
                        PathPart::ArrayListInit,
                        PathPart::ArrayListAppend,
                        PathPart::WriteData(&last_slot),
                        HASH_MAP_INIT,
                        hm_value(&foo_key),
                        PathPart::WriteData(&Data::Float(42.5)),
                    ])
                    .unwrap();

                // read foo
                let float_cursor =
                    root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap().unwrap();
                let float_value = float_cursor.read_float().unwrap();
                assert_eq!(42.5, float_value);
            }

            // remove foo
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    PathPart::HashMapRemove(&foo_key),
                ])
                .unwrap();

            // remove key that does not exist
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let doesnt_exist = db.digest(b"doesn't exist");
            let remove_err = root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    PathPart::HashMapRemove(&doesnt_exist),
                ])
                .unwrap_err();
            assert!(matches!(remove_err, Error::KeyNotFound), "expected KeyNotFound, got {remove_err:?}");

            // make sure foo doesn't exist anymore
            let foo_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&foo_key)]).unwrap();
            assert!(foo_cursor.is_none(), "expected nil cursor");

            // non-top-level list
            {
                let fruits = db.digest(b"fruits");
                let write_fruit = |root_cursor: &mut WriteCursor<'_, &mut C>, fruit: &str| {
                    let last_slot = Data::Slot(last_slot_data(root_cursor));
                    root_cursor
                        .write_path(&[
                            PathPart::ArrayListInit,
                            PathPart::ArrayListAppend,
                            PathPart::WriteData(&last_slot),
                            HASH_MAP_INIT,
                            hm_value(&fruits),
                            PathPart::ArrayListInit,
                            PathPart::ArrayListAppend,
                            PathPart::WriteData(&Data::string(fruit)),
                        ])
                        .unwrap();
                };

                // write apple
                write_fruit(&mut root_cursor, "apple");

                // read apple
                let apple_cursor = root_cursor
                    .read_path(&[PathPart::ArrayListGet(-1), hm_value(&fruits), PathPart::ArrayListGet(-1)])
                    .unwrap();
                assert_eq!("apple", read_string(apple_cursor));

                // write banana
                write_fruit(&mut root_cursor, "banana");

                // read banana
                let banana_cursor = root_cursor
                    .read_path(&[PathPart::ArrayListGet(-1), hm_value(&fruits), PathPart::ArrayListGet(-1)])
                    .unwrap();
                assert_eq!("banana", read_string(banana_cursor));

                // can't read banana in older array_list
                let no_cursor = root_cursor
                    .read_path(&[PathPart::ArrayListGet(-2), hm_value(&fruits), PathPart::ArrayListGet(1)])
                    .unwrap();
                assert!(no_cursor.is_none(), "expected nil cursor");

                // write pear
                write_fruit(&mut root_cursor, "pear");

                // write grape
                write_fruit(&mut root_cursor, "grape");

                // read pear
                let pear_cursor = root_cursor
                    .read_path(&[PathPart::ArrayListGet(-1), hm_value(&fruits), PathPart::ArrayListGet(-2)])
                    .unwrap();
                assert_eq!("pear", read_string(pear_cursor));

                // read grape
                let grape_cursor = root_cursor
                    .read_path(&[PathPart::ArrayListGet(-1), hm_value(&fruits), PathPart::ArrayListGet(-1)])
                    .unwrap();
                assert_eq!("grape", read_string(grape_cursor));
            }
        }
    }

    // append to top-level array_list many times, filling up the array_list until a root overflow occurs
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        let wat_key = db.digest(b"wat");
        for i in 0..SLOT_COUNT + 1 {
            let value = format!("wat{i}");
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&wat_key),
                    PathPart::WriteData(&Data::string(&value)),
                ])
                .unwrap();
        }

        for i in 0..SLOT_COUNT + 1 {
            let value = format!("wat{i}");
            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(i as i64), hm_value(&wat_key)]).unwrap();
            assert_eq!(value, read_string(cursor));
        }

        // add more slots to cause a new index block to be created.
        for i in SLOT_COUNT + 1..SLOT_COUNT * 2 + 1 {
            let value = format!("wat{i}");
            let index = i;

            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let write_result = root_cursor.write_path_context(
                &[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&wat_key),
                    PathPart::WriteData(&Data::string(&value)),
                ],
                |_cursor| {
                    if index == 32 {
                        return Err(Error::Io(io::Error::other("intentional error")));
                    }
                    Ok(())
                },
            );
            let _ = write_result;
        }

        // try another append to make sure we still can.
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                HASH_MAP_INIT,
                hm_value(&wat_key),
                PathPart::WriteData(&Data::string("wat32")),
            ])
            .unwrap();

        // slice so it contains exactly SLOT_COUNT
        root_cursor.write_path(&[PathPart::ArrayListInit, PathPart::ArrayListSlice(SLOT_COUNT as i64)]).unwrap();

        // we can iterate over the remaining slots
        for i in 0..SLOT_COUNT {
            let value = format!("wat{i}");
            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(i as i64), hm_value(&wat_key)]).unwrap();
            assert_eq!(value, read_string(cursor));
        }

        // but we can't get the value that we sliced out of the array list
        let nil_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(SLOT_COUNT as i64 + 1)]).unwrap();
        assert!(nil_cursor.is_none(), "expected nil cursor");
    }

    // append to inner array_list many times, filling up the array_list until a root overflow occurs
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        for i in 0..SLOT_COUNT + 1 {
            let value = format!("wat{i}");
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&Data::string(&value)),
                ])
                .unwrap();
        }

        for i in 0..SLOT_COUNT + 1 {
            let value = format!("wat{i}");
            let cursor =
                root_cursor.read_path(&[PathPart::ArrayListGet(-1), PathPart::ArrayListGet(i as i64)]).unwrap();
            assert_eq!(value, read_string(cursor));
        }

        // slice the inner array list so it contains exactly SLOT_COUNT
        let last_moment = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_moment),
                PathPart::ArrayListInit,
                PathPart::ArrayListSlice(SLOT_COUNT as i64),
            ])
            .unwrap();

        // we can iterate over the remaining slots
        for i in 0..SLOT_COUNT {
            let value = format!("wat{i}");
            let cursor =
                root_cursor.read_path(&[PathPart::ArrayListGet(-1), PathPart::ArrayListGet(i as i64)]).unwrap();
            assert_eq!(value, read_string(cursor));
        }

        // but we can't get the value that we sliced out of the array list
        let nil_cursor = root_cursor
            .read_path(&[PathPart::ArrayListGet(-1), PathPart::ArrayListGet(SLOT_COUNT as i64 + 1)])
            .unwrap();
        assert!(nil_cursor.is_none(), "expected nil cursor");

        // overwrite the last value with hello
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                PathPart::ArrayListInit,
                PathPart::ArrayListGet(-1),
                PathPart::WriteData(&Data::string("hello")),
            ])
            .unwrap();

        // read last value
        {
            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), PathPart::ArrayListGet(-1)]).unwrap();
            assert_eq!("hello", read_string(cursor));
        }

        // overwrite the last value with goodbye
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                PathPart::ArrayListInit,
                PathPart::ArrayListGet(-1),
                PathPart::WriteData(&Data::string("goodbye")),
            ])
            .unwrap();

        // read last value
        {
            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), PathPart::ArrayListGet(-1)]).unwrap();
            assert_eq!("goodbye", read_string(cursor));
        }

        // previous last value is still hello
        {
            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-2), PathPart::ArrayListGet(-1)]).unwrap();
            assert_eq!("hello", read_string(cursor));
        }
    }

    // iterate over inner array_list
    {
        core.set_length(0).unwrap();
        Database::new(&mut *core, hasher.clone()).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        // add wats
        for i in 0..10 {
            let value = format!("wat{i}");
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&Data::string(&value)),
                ])
                .unwrap();

            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), PathPart::ArrayListGet(-1)]).unwrap();
            assert_eq!(value, read_string(cursor));
        }

        // iterate over array_list
        {
            let inner_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1)]).unwrap().unwrap();
            let mut i = 0;
            for next_cursor in inner_cursor.iter().unwrap() {
                let next_cursor = next_cursor.unwrap();
                let value = format!("wat{i}");
                let value2 = next_cursor.read_bytes(MAX_READ).unwrap();
                assert_eq!(value, s(value2));
                i += 1;
            }
            assert_eq!(10, i);
        }

        // set first slot to .none and make sure iteration still works
        {
            let last_moment = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_moment),
                    PathPart::ArrayListInit,
                    PathPart::ArrayListGet(0),
                    PathPart::WriteData(&Data::None),
                ])
                .unwrap();
            let inner_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1)]).unwrap().unwrap();
            let mut i = 0;
            for next_cursor in inner_cursor.iter().unwrap() {
                next_cursor.unwrap();
                i += 1;
            }
            assert_eq!(10, i);
        }

        // get list slot
        let list_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1)]).unwrap().unwrap();
        let list_count = list_cursor.count().unwrap();
        assert_eq!(10, list_count);
    }

    // iterate over inner hash_map
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        // add wats
        for i in 0..10 {
            let value = format!("wat{i}");
            let wat_key = db.digest(value.as_bytes());
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    HASH_MAP_INIT,
                    hm_value(&wat_key),
                    PathPart::WriteData(&Data::string(&value)),
                ])
                .unwrap();

            let cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1), hm_value(&wat_key)]).unwrap();
            assert_eq!(value, read_string(cursor));
        }

        // add foo
        let foo_key = db.digest(b"foo");
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                HASH_MAP_INIT,
                hm_key(&foo_key),
                PathPart::WriteData(&Data::string("foo")),
            ])
            .unwrap();
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                HASH_MAP_INIT,
                hm_value(&foo_key),
                PathPart::WriteData(&Data::Uint(42)),
            ])
            .unwrap();

        // remove a wat
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        let wat0 = db.digest(b"wat0");
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                HASH_MAP_INIT,
                PathPart::HashMapRemove(&wat0),
            ])
            .unwrap();

        // iterate over hash_map
        {
            let inner_cursor = root_cursor.read_path(&[PathPart::ArrayListGet(-1)]).unwrap().unwrap();
            let mut i = 0;
            for kv_pair_cursor in inner_cursor.iter().unwrap() {
                let kv_pair_cursor = kv_pair_cursor.unwrap();
                let kv_pair = kv_pair_cursor.read_key_value_pair().unwrap();
                if kv_pair.hash == foo_key {
                    let key = kv_pair.key_cursor.read_bytes(MAX_READ).unwrap();
                    assert_eq!("foo", s(key));
                    assert_eq!(42i64, kv_pair.value_cursor.slot_ptr.slot.value);
                } else {
                    let value = kv_pair.value_cursor.read_bytes(MAX_READ).unwrap();
                    assert_eq!(kv_pair.hash, db.digest(&value), "hash mismatch");
                }
                i += 1;
            }
            assert_eq!(10, i);
        }

        // iterate over hash_map with writeable cursor
        {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            let inner_cursor = root_cursor
                .write_path(&[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot)])
                .unwrap();
            let mut i = 0;
            for kv_pair_cursor in inner_cursor.iter().unwrap() {
                let kv_pair_cursor = kv_pair_cursor.unwrap();
                let kv_pair = kv_pair_cursor.read_key_value_pair().unwrap();
                if kv_pair.hash == foo_key {
                    let value = kv_pair.value_cursor.read_uint().unwrap();
                    assert_eq!(42u64, value);
                }
                i += 1;
            }
            assert_eq!(10, i);
        }
    }

    {
        // slice linked_array_list
        test_slice(core, hasher, SLOT_COUNT * 5 + 1, 10, 5);
        test_slice(core, hasher, SLOT_COUNT * 5 + 1, 0, (SLOT_COUNT * 2) as i64);
        test_slice(core, hasher, SLOT_COUNT * 5, (SLOT_COUNT * 3) as i64, SLOT_COUNT as i64);
        test_slice(core, hasher, SLOT_COUNT * 5, (SLOT_COUNT * 3) as i64, (SLOT_COUNT * 2) as i64);
        test_slice(core, hasher, SLOT_COUNT * 2, 10, SLOT_COUNT as i64);
        test_slice(core, hasher, 2, 0, 2);
        test_slice(core, hasher, 2, 1, 1);
        test_slice(core, hasher, 1, 0, 0);

        // concat linked_array_list
        test_concat(core, hasher, (SLOT_COUNT * 5 + 1) as i64, (SLOT_COUNT + 1) as i64);
        test_concat(core, hasher, SLOT_COUNT as i64, SLOT_COUNT as i64);
        test_concat(core, hasher, 1, 1);
        test_concat(core, hasher, 0, 0);

        // insert linked_array_list
        test_insert_and_remove(core, hasher, 1, 0);
        test_insert_and_remove(core, hasher, 10, 0);
        test_insert_and_remove(core, hasher, 10, 5);
        test_insert_and_remove(core, hasher, 10, 9);
        test_insert_and_remove(core, hasher, SLOT_COUNT * 5, (SLOT_COUNT * 2) as i64);
    }

    // concat linked_array_list multiple times
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        let even = db.digest(b"even");
        let combo = db.digest(b"combo");
        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path_context(
                &[PathPart::ArrayListInit, PathPart::ArrayListAppend, PathPart::WriteData(&last_slot), HASH_MAP_INIT],
                |cursor| {
                    let mut values: Vec<i64> = Vec::new();

                    // create list
                    for i in 0..SLOT_COUNT + 1 {
                        let n = i as i64 * 2;
                        values.push(n);
                        cursor.write_path(&[
                            hm_value(&even),
                            PathPart::LinkedArrayListInit,
                            PathPart::LinkedArrayListAppend,
                            PathPart::WriteData(&Data::Uint(n as u64)),
                        ])?;
                    }

                    // get list slot
                    let even_list_cursor = cursor.read_path(&[hm_value(&even)])?.unwrap();
                    let even_count = even_list_cursor.count()?;
                    assert_eq!((SLOT_COUNT + 1) as i64, even_count);

                    // check all values in the new slice with an iterator
                    {
                        let inner_cursor = cursor.read_path(&[hm_value(&even)])?.unwrap();
                        let mut i = 0;
                        for item in inner_cursor.iter()? {
                            item?;
                            i += 1;
                        }
                        assert_eq!(SLOT_COUNT + 1, i);
                    }

                    // concat the list with itself multiple times
                    let mut combo_list_cursor = cursor.write_path(&[
                        hm_value(&combo),
                        PathPart::WriteData(&Data::Slot(even_list_cursor.slot_ptr.slot)),
                        PathPart::LinkedArrayListInit,
                    ])?;
                    for _ in 0..16 {
                        combo_list_cursor = combo_list_cursor
                            .write_path(&[PathPart::LinkedArrayListConcat(even_list_cursor.slot_ptr.slot)])?;
                    }

                    // append to the new list
                    cursor.write_path(&[
                        hm_value(&combo),
                        PathPart::LinkedArrayListAppend,
                        PathPart::WriteData(&Data::Uint(3)),
                    ])?;

                    // read the new value from the list
                    let rc = cursor.read_path(&[hm_value(&combo), PathPart::LinkedArrayListGet(-1)])?.unwrap();
                    assert_eq!(3, rc.slot_ptr.slot.value, "expected 3, got {}", rc.slot_ptr.slot.value);

                    // append more to the new list
                    for _ in 0..500 {
                        cursor.write_path(&[
                            hm_value(&combo),
                            PathPart::LinkedArrayListAppend,
                            PathPart::WriteData(&Data::Uint(1)),
                        ])?;
                    }

                    Ok(())
                },
            )
            .unwrap();
    }

    // append items to linked_array_list without setting their value
    {
        core.set_length(0).unwrap();
        Database::new(&mut *core, hasher.clone()).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        // appending without setting any value should work
        for _ in 0..8 {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListAppend,
                ])
                .unwrap();
        }

        // explicitly writing a null slot should also work
        for _ in 0..8 {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListAppend,
                    PathPart::WriteData(&Data::None),
                ])
                .unwrap();
        }
    }

    // insert at beginning of linked_array_list many times
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                PathPart::LinkedArrayListInit,
                PathPart::LinkedArrayListAppend,
                PathPart::WriteData(&Data::Uint(42)),
            ])
            .unwrap();

        for i in 0..1000u64 {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListInsert(0),
                    PathPart::WriteData(&Data::Uint(i)),
                ])
                .unwrap();
        }
    }

    // insert at end of linked_array_list many times
    {
        core.set_length(0).unwrap();
        let db = Database::new(&mut *core, hasher.clone()).unwrap();
        let mut root_cursor = db.root_cursor();

        let last_slot = Data::Slot(last_slot_data(&root_cursor));
        root_cursor
            .write_path(&[
                PathPart::ArrayListInit,
                PathPart::ArrayListAppend,
                PathPart::WriteData(&last_slot),
                PathPart::LinkedArrayListInit,
                PathPart::LinkedArrayListAppend,
                PathPart::WriteData(&Data::Uint(42)),
            ])
            .unwrap();

        for i in 0..1000u64 {
            let last_slot = Data::Slot(last_slot_data(&root_cursor));
            root_cursor
                .write_path(&[
                    PathPart::ArrayListInit,
                    PathPart::ArrayListAppend,
                    PathPart::WriteData(&last_slot),
                    PathPart::LinkedArrayListInit,
                    PathPart::LinkedArrayListInsert(i as i64),
                    PathPart::WriteData(&Data::Uint(i)),
                ])
                .unwrap();
        }
    }
}
