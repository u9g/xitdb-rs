//! Tests for Database::compact_file, which compacts a database file in place.

use std::fs::{File, OpenOptions};
use std::path::Path;

use xitdb::*;

fn open_rw(path: &Path) -> std::io::Result<File> {
    OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path)
}

/// Appends `count` moments, each setting "n" to its index and adding a
/// large value, so the history takes much more space than the last moment.
fn append_moments<C: Core>(db: &Database<C>, start: u64, count: u64) -> Result<()> {
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    for i in start..start + count {
        let last = history.get_slot(-1)?;
        history.append_context(last, |cursor| {
            let mut moment = WriteHashMap::new(cursor)?;
            moment.put("n", i)?;
            moment.put("blob", vec![i as u8; 1000])?;
            Ok(())
        })?;
    }
    Ok(())
}

fn last_n<C: Core>(db: &Database<C>) -> Result<(i64, u64)> {
    let history = ReadArrayList::new(db.root_cursor())?;
    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
    Ok((history.count()?, moment.get_cursor("n")?.unwrap().read_uint()?))
}

#[test]
fn compact_file_shrinks_and_keeps_data() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let mut db = Database::new(CoreBufferedFile::new(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&db, 0, 50)?;
    let before = std::fs::metadata(&path)?.len();
    let file_id = db.header().file_id;

    db.compact_file(&path, &mut MemoryOffsetMap::new(), CoreBufferedFile::new)?;

    assert!(std::fs::metadata(&path)?.len() < before / 10);
    assert!(!dir.path().join("db.compacting").exists());
    // the compacted file is a new database with its own file id
    assert_ne!(db.header().file_id, file_id);
    assert_eq!(last_n(&db)?, (1, 49));

    // the compacted database keeps writing to the file at path
    append_moments(&db, 50, 3)?;
    assert_eq!(last_n(&db)?, (4, 52));
    drop(db);
    let reopened = Database::new(CoreBufferedFile::new(open_rw(&path)?), Hasher::sha1())?;
    assert_eq!(last_n(&reopened)?, (4, 52));
    Ok(())
}

#[test]
fn compact_file_with_dyn_core_and_file_offset_map() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let open = |file| Box::new(CoreBufferedFile::new(file)) as Box<dyn Core + Send>;
    let mut db = Database::new(open(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&db, 0, 10)?;

    let scratch = Database::new(CoreFile::new(tempfile::tempfile()?), Hasher::sha1())?;
    scratch.run_context(|cursor| {
        let mut offsets = FileOffsetMap::new(cursor)?;
        db.compact_file(&path, &mut offsets, open)
    })?;

    assert_eq!(last_n(&db)?, (1, 9));
    append_moments(&db, 10, 1)?;
    assert_eq!(last_n(&db)?, (2, 10));
    Ok(())
}

#[test]
fn readers_see_commits_and_reopen_after_compaction() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let mut writer = Database::new(CoreBufferedFile::new(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&writer, 0, 5)?;

    // a long-lived reader sees new commits, since the root is re-read
    let reader = Database::new(CoreFile::new(File::open(&path)?), Hasher::sha1())?;
    assert_eq!(last_n(&reader)?, (5, 4));
    append_moments(&writer, 5, 1)?;
    assert_eq!(last_n(&reader)?, (6, 5));

    // the file can be replaced while the reader holds it open
    writer.compact_file(&path, &mut MemoryOffsetMap::new(), CoreBufferedFile::new)?;
    append_moments(&writer, 6, 1)?;

    // the reader's handle still points at the old file...
    assert_eq!(last_n(&reader)?, (6, 5));
    // ...which it can detect by comparing file ids with the file at path
    let header = Header::read(&mut CoreFile::new(File::open(&path)?))?;
    assert_ne!(header.file_id, reader.header().file_id);

    // a reader that opens the file per read sees the compacted data
    let reader = Database::new(CoreFile::new(File::open(&path)?), Hasher::sha1())?;
    assert_eq!(last_n(&reader)?, (2, 6));
    Ok(())
}

#[test]
fn compact_file_failure_keeps_original() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let mut db = Database::new(CoreBufferedFile::new(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&db, 0, 5)?;
    let file_id = db.header().file_id;

    // the temporary file can't be created where a directory is in the way
    std::fs::create_dir(dir.path().join("db.compacting"))?;
    assert!(db.compact_file(&path, &mut MemoryOffsetMap::new(), CoreBufferedFile::new).is_err());

    // the original is still open, unchanged and writable
    assert_eq!(db.header().file_id, file_id);
    assert_eq!(last_n(&db)?, (5, 4));
    append_moments(&db, 5, 1)?;
    assert_eq!(last_n(&db)?, (6, 5));
    Ok(())
}

#[cfg(windows)]
#[test]
fn compact_file_rename_failure_reopens_original() -> Result<()> {
    use std::os::windows::fs::OpenOptionsExt;

    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let mut db = Database::new(CoreBufferedFile::new(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&db, 0, 5)?;
    let file_id = db.header().file_id;

    // a handle opened without FILE_SHARE_DELETE makes the rename fail
    const FILE_SHARE_READ: u32 = 1;
    const FILE_SHARE_WRITE: u32 = 2;
    let blocker = OpenOptions::new().read(true).share_mode(FILE_SHARE_READ | FILE_SHARE_WRITE).open(&path)?;
    assert!(db.compact_file(&path, &mut MemoryOffsetMap::new(), CoreBufferedFile::new).is_err());
    drop(blocker);

    // the original was reopened, and the temporary file removed
    assert!(!dir.path().join("db.compacting").exists());
    assert_eq!(db.header().file_id, file_id);
    assert_eq!(last_n(&db)?, (5, 4));
    append_moments(&db, 5, 1)?;
    assert_eq!(last_n(&db)?, (6, 5));
    Ok(())
}
