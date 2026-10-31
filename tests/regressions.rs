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

/// Points the first child slot of the index block or b-tree node body at
/// `block` back at `target`, so following it loops.
fn corrupt_child(db: &Database<CoreMemory>, block: i64, target: i64) -> Result<()> {
    let mut core = db.core();
    let mut tag = [0u8];
    core.seek_to(block as u64)?;
    core.read(&mut tag)?;
    assert_eq!(tag[0] & 0x7f, Tag::Index as u8);
    core.write(&target.to_be_bytes())?;
    Ok(())
}

/// The position of a b-tree's root node, from the header its slot points at.
fn btree_root(db: &Database<CoreMemory>, slot: Slot) -> Result<i64> {
    let mut buf = [0u8; 8];
    let mut core = db.core();
    core.seek_to(slot.value as u64 + 8)?;
    core.read(&mut buf)?;
    Ok(i64::from_be_bytes(buf))
}

/// A hash map index slot that points back at its own block is an error
/// when iterating, not an endless descent. Found by Kani.
#[test]
fn cyclic_hash_map_iteration_is_an_error() -> Result<()> {
    // a 1-byte hash, so 0x01 and 0x11 share the first level's nibble
    let hasher = Hasher::new(|data: &[u8]| vec![data.first().copied().unwrap_or(0)]);
    let db = Database::new(CoreMemory::new(), hasher)?;
    let mut map = WriteHashMap::new(&mut db.root_cursor())?;
    map.put([0x01], 1u64)?;
    map.put([0x11], 2u64)?;
    let root = map.slot()?.value;
    corrupt_child(&db, root + SLOT_LENGTH as i64, root)?;

    let map = ReadHashMap::new(db.root_cursor())?;
    let results: Vec<_> = map.iter()?.collect();
    assert!(matches!(results.last(), Some(Err(Error::InvalidDatabase))));
    Ok(())
}

/// A sorted map branch whose child points back at it is an error, not an
/// endless descent. Found by Kani.
#[test]
fn cyclic_sorted_map_is_an_error() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    db.run_context(|cursor| {
        let mut map = WriteSortedMap::new(cursor)?;
        // one more than a leaf holds, so the root is a branch
        for key in 1..=17u8 {
            map.put([key], key as u64)?;
        }
        Ok(())
    })?;
    let root = btree_root(&db, db.root_cursor().slot()?)?;
    corrupt_child(&db, root + 2, root)?;

    let map = ReadSortedMap::new(db.root_cursor())?;
    assert!(matches!(map.get_cursor([1]), Err(Error::InvalidBTreeNode)));
    assert!(matches!(map.rank([1]), Err(Error::InvalidBTreeNode)));
    assert!(matches!(map.iter_from([1]), Err(Error::InvalidBTreeNode)));
    assert!(matches!(map.iter_from_index(0), Err(Error::InvalidBTreeNode)));
    assert!(matches!(map.iter()?.last(), Some(Err(Error::InvalidDatabase))));
    let mut map = WriteSortedMap::new(&mut db.root_cursor())?;
    assert!(matches!(map.put([1], 0u64), Err(Error::InvalidBTreeNode)));
    assert!(matches!(map.remove([1]), Err(Error::InvalidBTreeNode)));
    Ok(())
}

/// The same for a linked array list.
#[test]
fn cyclic_linked_array_list_is_an_error() -> Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    db.run_context(|cursor| {
        let mut list = WriteLinkedArrayList::new(cursor)?;
        for i in 0..17u64 {
            list.append(i)?;
        }
        Ok(())
    })?;
    let root = btree_root(&db, db.root_cursor().slot()?)?;
    corrupt_child(&db, root + 2, root)?;

    let list = ReadLinkedArrayList::new(db.root_cursor())?;
    assert!(matches!(list.get_cursor(0), Err(Error::InvalidBTreeNode)));
    assert!(matches!(list.iter_from(0), Err(Error::InvalidBTreeNode)));
    assert!(matches!(list.iter()?.last(), Some(Err(Error::InvalidDatabase))));
    let mut list = WriteLinkedArrayList::new(&mut db.root_cursor())?;
    assert!(matches!(list.insert(0, 0u64), Err(Error::InvalidBTreeNode)));
    assert!(matches!(list.remove(0), Err(Error::InvalidBTreeNode)));
    assert!(matches!(list.put(0, 0u64), Err(Error::InvalidBTreeNode)));
    assert!(matches!(list.slice(1, 1), Err(Error::InvalidBTreeNode)));
    Ok(())
}
