//! Bugs found while porting, which the Go implementation shares.

use std::io::Write;

use xitdb::*;

/// Iterating an array list must not yield items that a slice removed, even
/// when an appended slot is left empty.
#[test]
fn array_list_iteration_skips_sliced_items() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    db.run_context(|cursor| {
        let mut list = WriteArrayList::new(cursor)?;
        for item in ["a", "b", "c", "d"] {
            list.append(item)?;
        }
        // the slice keeps the same index block, so "c" and "d" are still in it
        list.slice(2)?;
        // append without writing: the new item's slot is empty
        list.append_cursor()?;
        Ok(())
    })?;

    let list = ReadArrayList::new(db.root_cursor())?;
    assert_eq!(list.count()?, 3);
    assert!(list.get_cursor(2)?.is_none());
    let mut items = Vec::new();
    for item in list.iter()? {
        items.push(item?.read_bytes(None)?);
    }
    assert_eq!(items, [b"a", b"b"]);
    // the same for an iterator that seeks into the list
    let mut items = Vec::new();
    for item in list.iter_from(1)? {
        items.push(item?.read_bytes(None)?);
    }
    assert_eq!(items, [b"b"]);
    Ok(())
}

/// A byte writer can't seek before the start of its byte array.
#[test]
fn writer_cannot_seek_before_its_bytes() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append("committed data")?;
    let committed = db.core().as_bytes().to_vec();

    history.append_context(None, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        let mut text_cursor = moment.put_cursor("text")?;
        let mut writer = text_cursor.writer()?;
        writer.write_all(b"0123456789")?;
        // a position past the bytes written so far is ignored
        writer.seek_to(u64::MAX - 99);
        writer.write_all(&[0xff; 50])?;
        writer.finish()?;
        let text = text_cursor.read_bytes(None)?;
        assert_eq!(&text[..10], b"0123456789");
        assert_eq!(text.len(), 60);
        Ok(())
    })?;

    // the committed bytes, except the root header, are unchanged
    let start = xitdb::consts::ROOT_HEADER_END as usize;
    assert_eq!(&db.core().as_bytes()[start..committed.len()], &committed[start..]);
    Ok(())
}

/// A corrupt byte array length is an error, not a huge allocation.
#[test]
fn corrupt_bytes_length_is_an_error() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut map = WriteHashMap::new(&mut db.root_cursor())?;
    map.put("long", "longer than eight bytes")?;
    let slot = map.get_slot("long")?.unwrap();
    assert_eq!(slot.tag, Tag::Bytes);

    // the slot points at the byte array's length
    db.core().seek_to(slot.value as u64)?;
    db.core().write(&(1i64 << 50).to_be_bytes())?;

    let cursor = map.get_cursor("long")?.unwrap();
    assert!(matches!(cursor.read_bytes(None), Err(Error::InvalidDatabase)));
    assert!(matches!(cursor.reader(), Err(Error::InvalidDatabase)));
    Ok(())
}

/// A b-tree whose header claims more items than it has can't send an
/// iterator into a near-endless loop or index out of bounds.
#[test]
fn corrupt_btree_size_is_an_error() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut list = WriteLinkedArrayList::new(&mut db.root_cursor())?;
    for i in 0..3u64 {
        list.append(i)?;
    }
    let slot = list.slot()?;

    // the header starts with the size
    db.core().seek_to(slot.value as u64)?;
    db.core().write(&(1i64 << 40).to_be_bytes())?;

    let list = ReadLinkedArrayList::new(db.root_cursor())?;
    assert_eq!(list.count()?, 1 << 40);
    assert_eq!(list.iter()?.count(), 3);
    assert!(matches!(list.get_cursor(100), Err(Error::InvalidBTreeNode)));
    assert!(matches!(list.iter_from(100), Err(Error::InvalidBTreeNode)));
    Ok(())
}

/// A uint above i64::MAX was written as a negative slot value, which every
/// implementation reads as an error, so it could be written but never read
/// back. Writing one is now the error.
#[test]
fn uint_above_i64_max_is_rejected_when_written() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut map = WriteHashMap::new(&mut db.root_cursor())?;
    map.put("max", i64::MAX as u64)?;
    assert_eq!(map.get_cursor("max")?.unwrap().read_uint()?, i64::MAX as u64);
    for value in [i64::MAX as u64 + 1, u64::MAX] {
        let result = map.put("too big", value);
        assert!(matches!(result, Err(Error::ExpectedUnsignedLong)), "{value}: {result:?}");
    }
    assert!(map.get_cursor("too big")?.is_none());
    Ok(())
}
