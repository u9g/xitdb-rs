//! Tests for Database::compact_file, which compacts a database file in place.

use std::fs::{File, OpenOptions};
use std::io;
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

/// The names of the files in `dir`, sorted.
fn file_names(dir: &Path) -> io::Result<Vec<String>> {
    let mut names = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        names.push(entry?.file_name().into_string().unwrap());
    }
    names.sort();
    Ok(names)
}

/// A core whose writes, or reads too, fail, to make compaction or
/// reopening fail.
struct FailingCore {
    inner: CoreBufferedFile,
    fail_reads: bool,
}

impl Core for FailingCore {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        if self.fail_reads {
            return Err(io::Error::other("injected read failure"));
        }
        self.inner.read(buf)
    }
    fn write(&mut self, _buf: &[u8]) -> io::Result<()> {
        Err(io::Error::other("injected write failure"))
    }
    fn length(&mut self) -> io::Result<u64> {
        self.inner.length()
    }
    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        self.inner.seek_to(pos)
    }
    fn position(&mut self) -> io::Result<u64> {
        self.inner.position()
    }
    fn set_length(&mut self, len: u64) -> io::Result<()> {
        self.inner.set_length(len)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
    fn sync(&mut self) -> io::Result<()> {
        self.inner.sync()
    }
}

type DynCore = Box<dyn Core + Send>;

fn buffered(file: File) -> DynCore {
    Box::new(CoreBufferedFile::new(file))
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
    assert_eq!(file_names(dir.path())?, ["db"]);
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
fn compact_file_keeps_hasher_and_follows_symlinks() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    // the file id only applies when a database is created, and compaction
    // gives the new file its own, but self keeps the caller's hasher
    let hasher = Hasher::sha1().with_id(*b"sha1").with_file_id(42);
    let mut db = Database::new(CoreBufferedFile::new(open_rw(&path)?), hasher)?;
    append_moments(&db, 0, 5)?;

    let link = dir.path().join("link");
    #[cfg(unix)]
    let linked = std::os::unix::fs::symlink(&path, &link).is_ok();
    // creating symlinks needs a privilege on Windows
    #[cfg(windows)]
    let linked = std::os::windows::fs::symlink_file(&path, &link).is_ok();
    let target = if linked { &link } else { &path };

    db.compact_file(target, &mut MemoryOffsetMap::new(), CoreBufferedFile::new)?;
    assert_eq!(db.hasher().id, bytes_to_id(*b"sha1"));
    assert_eq!(db.hasher().file_id, 42);
    assert_ne!(db.header().file_id, 42);
    assert_eq!(db.header().hash_id, bytes_to_id(*b"sha1"));
    if linked {
        // the file behind the link was replaced, not the link
        assert!(std::fs::symlink_metadata(&link)?.file_type().is_symlink());
    }
    assert_eq!(last_n(&db)?, (1, 4));
    Ok(())
}

#[test]
fn compact_file_failure_keeps_original() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let mut db = Database::new(buffered(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&db, 0, 5)?;
    let file_id = db.header().file_id;

    // the compacted copy can't be written
    let failing = |file| Box::new(FailingCore { inner: CoreBufferedFile::new(file), fail_reads: false }) as DynCore;
    assert!(db.compact_file(&path, &mut MemoryOffsetMap::new(), failing).is_err());

    // the original is still open, unchanged and writable, and the
    // temporary file was removed
    assert_eq!(file_names(dir.path())?, ["db"]);
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
    assert_eq!(file_names(dir.path())?, ["db"]);
    assert_eq!(db.header().file_id, file_id);
    assert_eq!(last_n(&db)?, (5, 4));
    append_moments(&db, 5, 1)?;
    assert_eq!(last_n(&db)?, (6, 5));
    Ok(())
}

#[cfg(windows)]
#[test]
fn compact_file_reopen_failure_reports_temp_path() -> Result<()> {
    use std::os::windows::fs::OpenOptionsExt;

    let dir = tempfile::tempdir()?;
    let path = dir.path().join("db");
    let mut db = Database::new(buffered(open_rw(&path)?), Hasher::sha1())?;
    append_moments(&db, 0, 5)?;

    // the rename fails, and so does reopening the original (the second open)
    const FILE_SHARE_READ: u32 = 1;
    const FILE_SHARE_WRITE: u32 = 2;
    let blocker = OpenOptions::new().read(true).share_mode(FILE_SHARE_READ | FILE_SHARE_WRITE).open(&path)?;
    let mut opens = 0;
    let open = |file| {
        opens += 1;
        if opens == 1 {
            buffered(file)
        } else {
            Box::new(FailingCore { inner: CoreBufferedFile::new(file), fail_reads: true }) as DynCore
        }
    };
    let err = db.compact_file(&path, &mut MemoryOffsetMap::new(), open).unwrap_err();
    drop(blocker);
    let Error::CompactFileReopenFailed { temp_path, .. } = err else {
        panic!("unexpected error: {err:?}");
    };

    // the database is the compacted copy at temp_path, which is kept
    assert!(temp_path.exists());
    assert_eq!(last_n(&db)?, (1, 4));
    append_moments(&db, 5, 1)?;

    // retrying puts the copy, with the new moment, at path, and doesn't
    // touch the file the database was using
    db.compact_file(&path, &mut MemoryOffsetMap::new(), buffered)?;
    assert!(temp_path.exists());
    assert_eq!(last_n(&db)?, (1, 5));
    std::fs::remove_file(&temp_path)?;
    assert_eq!(file_names(dir.path())?, ["db"]);
    drop(db);
    let reopened = Database::new(CoreFile::new(File::open(&path)?), Hasher::sha1())?;
    assert_eq!(last_n(&reopened)?, (1, 5));
    Ok(())
}
