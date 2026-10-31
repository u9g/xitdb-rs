//! Tests for the convenience constructors and for closing cores, including
//! through a `DynCore`.

use std::path::Path;

use xitdb::*;

fn append_moment<C: Core>(db: &Database<C>, value: &str) -> Result<()> {
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append(value)
}

fn last_moment<C: Core>(db: &Database<C>) -> Result<Option<Vec<u8>>> {
    let history = ReadArrayList::new(db.root_cursor())?;
    match history.get_cursor(-1)? {
        Some(cursor) => Ok(Some(cursor.read_bytes(Some(1024))?)),
        None => Ok(None),
    }
}

fn moment_count(path: &Path) -> Result<i64> {
    let db = Database::open_read_only(path)?;
    ReadArrayList::new(db.root_cursor())?.count()
}

#[test]
fn open_creates_and_reopens() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("test.db");

    let db = Database::open(&path)?;
    assert_eq!(db.header().hash_id, bytes_to_id(*b"sha1"));
    append_moment(&db, "first")?;
    db.close()?;

    // reopening keeps the existing data
    let db = Database::open(&path)?;
    assert_eq!(last_moment(&db)?.as_deref(), Some(&b"first"[..]));
    append_moment(&db, "second")?;
    db.close()?;

    assert_eq!(moment_count(&path)?, 2);
    Ok(())
}

#[test]
fn in_memory() -> Result<()> {
    let db = Database::in_memory()?;
    append_moment(&db, "hello")?;
    assert_eq!(last_moment(&db)?.as_deref(), Some(&b"hello"[..]));
    db.close()?;
    Ok(())
}

#[test]
fn open_read_only() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("test.db");

    // a missing file isn't created
    assert!(matches!(Database::open_read_only(&path), Err(Error::Io(_))));
    assert!(!path.exists());

    let db = Database::open(&path)?;
    append_moment(&db, "first")?;
    let len = std::fs::metadata(&path)?.len();

    // reading works alongside the writer
    let reader = Database::open_read_only(&path)?;
    assert_eq!(last_moment(&reader)?.as_deref(), Some(&b"first"[..]));

    // writing fails, and the file is unchanged
    assert!(matches!(append_moment(&reader, "second"), Err(Error::Io(_))));
    drop(reader);
    assert_eq!(std::fs::metadata(&path)?.len(), len);

    // the writer still works
    append_moment(&db, "second")?;
    db.close()?;
    assert_eq!(moment_count(&path)?, 2);
    Ok(())
}

#[test]
fn finish_flushes_boxed_buffered_file() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("raw.bin");

    // raw writes stay in the buffer until it is flushed
    let mut core: DynCore = Box::new(CoreBufferedFile::open(&path)?);
    core.seek_to(0)?;
    core.write(b"hello")?;
    assert_eq!(std::fs::metadata(&path)?.len(), 0);
    core.finish()?;
    assert_eq!(std::fs::read(&path)?, b"hello");
    drop(core);

    // and a database closed through a DynCore can be reopened
    let db_path = dir.path().join("test.db");
    let db = Database::open(&db_path)?.into_dyn();
    append_moment(&db, "boxed")?;
    db.close()?;
    let db = Database::open(&db_path)?;
    assert_eq!(last_moment(&db)?.as_deref(), Some(&b"boxed"[..]));
    Ok(())
}

#[test]
fn finish_reports_flush_errors_through_dyn_core() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("raw.bin");
    std::fs::write(&path, b"")?;

    // buffered writes to a read-only file only fail when flushed, which
    // used to be impossible to observe once the core was boxed
    let mut core: DynCore = Box::new(CoreBufferedFile::open_read_only(&path)?);
    core.seek_to(0)?;
    core.write(b"hello")?;
    assert!(core.finish().is_err());
    Ok(())
}

#[test]
fn mixed_dyn_cores() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("test.db");

    let dbs: Vec<Database<DynCore>> = vec![
        Database::open(&path)?.into_dyn(),
        Database::in_memory()?.into_dyn(),
        Database::new(Box::new(CoreFile::new(tempfile::tempfile()?)) as DynCore, Hasher::sha1())?,
    ];
    for (i, db) in dbs.iter().enumerate() {
        append_moment(db, &format!("db {i}"))?;
    }
    for (i, db) in dbs.iter().enumerate() {
        assert_eq!(last_moment(db)?, Some(format!("db {i}").into_bytes()));
    }
    for db in dbs {
        db.close()?;
    }

    assert_eq!(moment_count(&path)?, 1);
    Ok(())
}

#[test]
fn into_dyn_keeps_state() -> Result<()> {
    let db = Database::in_memory()?;
    append_moment(&db, "before")?;
    let header = db.header();

    let db = db.into_dyn();
    assert_eq!(db.header(), header);
    assert_eq!(last_moment(&db)?.as_deref(), Some(&b"before"[..]));
    append_moment(&db, "after")?;
    assert_eq!(ReadArrayList::new(db.root_cursor())?.count()?, 2);
    Ok(())
}

#[test]
fn close_read_only() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("test.db");
    let db = Database::open(&path)?;
    append_moment(&db, "first")?;
    db.close()?;

    // finishing a core that wrote nothing never needs write access
    let reader = Database::open_read_only(&path)?;
    assert_eq!(last_moment(&reader)?.as_deref(), Some(&b"first"[..]));
    reader.close()?;
    Database::open_read_only(&path)?.into_dyn().close()?;
    Ok(())
}

#[test]
fn open_read_only_empty_file() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("test.db");
    std::fs::write(&path, b"")?;

    // a read-only open never initializes the file
    assert!(matches!(Database::open_read_only(&path), Err(Error::InvalidDatabase)));
    assert_eq!(std::fs::metadata(&path)?.len(), 0);
    Ok(())
}
