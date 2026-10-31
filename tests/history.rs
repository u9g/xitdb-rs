//! Tests for `History`, a root array list of hash map moments.

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

fn new_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
}

fn read(moment: &ReadHashMap<'_, impl Core>, key: &str) -> Option<Vec<u8>> {
    moment.get_cursor(key).unwrap().map(|cursor| cursor.read_bytes(MAX_READ).unwrap())
}

#[derive(Debug)]
enum AppError {
    Db(Error),
    Rejected(&'static str),
}

impl From<Error> for AppError {
    fn from(err: Error) -> Self {
        AppError::Db(err)
    }
}

#[test]
fn latest_on_new_database() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    assert_eq!(history.count().unwrap(), 0);
    assert!(history.moment(-1).unwrap().is_none());

    // an empty map, not an error
    let latest = history.latest().unwrap();
    assert!(read(&latest, "foo").is_none());
    assert_eq!(latest.iter().unwrap().count(), 0);

    // opening it again doesn't commit anything
    let size = db.committed_size().unwrap();
    History::new(&db).unwrap();
    assert_eq!(db.committed_size().unwrap(), size);
}

#[test]
fn transact_returns_value() {
    let db = new_db();
    let history = History::new(&db).unwrap();

    let n = history
        .transact(|moment| {
            moment.put("n", 1u64)?;
            Ok::<_, Error>(41)
        })
        .unwrap();
    assert_eq!(n, 41);

    let (n, committed) = history
        .transact_with_status(|moment| {
            let n = moment.get_cursor("n")?.unwrap().read_uint()?;
            moment.put("n", n + 1)?;
            Ok::<_, Error>(n + 1)
        })
        .unwrap();
    assert_eq!(n, 2);
    assert!(committed);
    assert_eq!(history.count().unwrap(), 2);
    assert_eq!(history.latest().unwrap().get_cursor("n").unwrap().unwrap().read_uint().unwrap(), 2);
}

#[test]
fn transact_copies_latest_moment() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("a", "1")).unwrap();
    history.transact(|moment| moment.put("b", "2")).unwrap();

    let latest = history.latest().unwrap();
    assert_eq!(read(&latest, "a").unwrap(), b"1");
    assert_eq!(read(&latest, "b").unwrap(), b"2");

    // past moments stay readable
    let first = history.moment(0).unwrap().unwrap();
    assert_eq!(read(&first, "a").unwrap(), b"1");
    assert!(read(&first, "b").is_none());

    // the latest moment is a snapshot
    history.transact(|moment| moment.put("a", "3")).unwrap();
    assert_eq!(read(&latest, "a").unwrap(), b"1");
    assert_eq!(read(&history.latest().unwrap(), "a").unwrap(), b"3");
}

#[test]
fn custom_error_aborts_transaction() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    let size = db.committed_size().unwrap();
    let len = db.core().length().unwrap();

    let result: Result<(), AppError> = history.transact(|moment| {
        moment.put("foo", "changed")?;
        moment.put("bar", "bar")?;
        Err(AppError::Rejected("nope"))
    });
    assert!(matches!(result, Err(AppError::Rejected("nope"))));

    // nothing was committed, and the discarded data is gone
    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(db.committed_size().unwrap(), size);
    assert_eq!(db.core().length().unwrap(), len);
    let latest = history.latest().unwrap();
    assert_eq!(read(&latest, "foo").unwrap(), b"foo");
    assert!(read(&latest, "bar").is_none());

    // xitdb errors inside the callback convert into the custom type
    let result: Result<(), AppError> = history.transact(|moment| {
        ReadArrayList::new(moment.get_cursor("foo")?.unwrap())?;
        Ok(())
    });
    assert!(matches!(result, Err(AppError::Db(Error::UnexpectedTag))));
    assert_eq!(history.count().unwrap(), 1);

    // the history still works afterwards
    history.transact(|moment| moment.put("bar", "bar")).unwrap();
    assert_eq!(history.count().unwrap(), 2);
}

#[test]
fn no_op_transaction_does_not_grow_history() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let db = Database::new(CoreFile::new(tmp.as_file().try_clone().unwrap()), Hasher::sha1()).unwrap();
    let history = History::new(&db).unwrap();

    // on a new database, a no-op transaction doesn't create a moment
    let (_, committed) = history.transact_with_status(|_| Ok::<_, Error>(())).unwrap();
    assert!(!committed);
    assert_eq!(history.count().unwrap(), 0);

    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    assert_eq!(history.count().unwrap(), 1);
    let size = db.committed_size().unwrap();
    let file_len = tmp.as_file().metadata().unwrap().len();

    for _ in 0..10 {
        // reading only
        let (foo, committed) =
            history.transact_with_status(|moment| moment.get_cursor("foo")?.unwrap().read_bytes(MAX_READ)).unwrap();
        assert_eq!(foo, b"foo");
        assert!(!committed);

        // writing only when the value differs
        let (_, committed) = history
            .transact_with_status(|moment| {
                if moment.get_cursor("foo")?.unwrap().read_bytes(MAX_READ)? != b"foo" {
                    moment.put("foo", "foo")?;
                }
                Ok::<_, Error>(())
            })
            .unwrap();
        assert!(!committed);
    }

    // a put that's undone leaves the moment unchanged
    let (_, committed) = history
        .transact_with_status(|moment| {
            moment.put("tmp", "tmp")?;
            moment.remove("tmp")?;
            Ok::<_, Error>(())
        })
        .unwrap();
    assert!(!committed);

    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(db.committed_size().unwrap(), size);
    assert_eq!(tmp.as_file().metadata().unwrap().len(), file_len);

    // a real change still commits
    let (_, committed) = history.transact_with_status(|moment| moment.put("foo", "bar").map(|_| ())).unwrap();
    assert!(committed);
    assert_eq!(history.count().unwrap(), 2);
}

#[test]
fn reads_own_writes_inside_transact() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("count", 1u64)).unwrap();

    let seen = history
        .transact(|moment| {
            moment.put("count", 2u64)?;
            let mut fruits = WriteArrayList::new(&mut moment.put_cursor("fruits")?)?;
            fruits.append("apple")?;
            fruits.append("pear")?;

            let count = moment.get_cursor("count")?.unwrap().read_uint()?;
            let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
            Ok::<_, Error>((count, fruits.count()?))
        })
        .unwrap();
    assert_eq!(seen, (2, 2));

    // the previous moment is unaffected
    let first = history.moment(0).unwrap().unwrap();
    assert_eq!(first.get_cursor("count").unwrap().unwrap().read_uint().unwrap(), 1);
    assert!(first.get_cursor("fruits").unwrap().is_none());
}

#[test]
fn reopens_existing_history() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    {
        let db = Database::open(tmp.path()).unwrap();
        History::new(&db).unwrap().transact(|moment| moment.put("foo", "foo")).unwrap();
        db.close().unwrap();
    }
    let db = Database::open(tmp.path()).unwrap();
    let history = History::new(&db).unwrap();
    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(read(&history.latest().unwrap(), "foo").unwrap(), b"foo");
}

#[test]
fn rejects_other_roots() {
    let db = new_db();
    WriteHashMap::new(&mut db.root_cursor()).unwrap();
    assert!(matches!(History::new(&db), Err(Error::UnexpectedTag)));
}

#[test]
fn rewriting_same_value_counts_as_change() {
    // documented limitation: a put copies what it writes to, so even an
    // identical value gives the moment a new top-level block
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    let (_, committed) = history.transact_with_status(|moment| moment.put("foo", "foo")).unwrap();
    assert!(committed);
    assert_eq!(history.count().unwrap(), 2);
}

#[test]
fn rejects_moments_that_are_not_hash_maps() {
    let db = new_db();
    let mut list = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    list.append_context(None::<Slot>, |cursor| WriteCountedHashMap::new(cursor)?.put("foo", "foo")).unwrap();
    assert!(matches!(History::new(&db), Err(Error::UnexpectedTag)));

    // a counted map appended after opening is rejected by transact
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    let mut list = WriteArrayList::new(&mut db.root_cursor()).unwrap();
    list.append_context(None::<Slot>, |cursor| WriteCountedHashMap::new(cursor).map(|_| ())).unwrap();
    let size = db.committed_size().unwrap();
    let result = history.transact(|moment| moment.put("bar", "bar"));
    assert!(matches!(result, Err(Error::UnexpectedTag)));
    assert_eq!(db.committed_size().unwrap(), size);
    assert_eq!(history.count().unwrap(), 2);
}

#[test]
fn sees_commits_from_other_handles() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let open = || Database::new(CoreFile::new(tmp.as_file().try_clone().unwrap()), Hasher::sha1()).unwrap();
    let (db1, db2) = (open(), open());
    let (h1, h2) = (History::new(&db1).unwrap(), History::new(&db2).unwrap());

    h1.transact(|moment| moment.put("a", "1")).unwrap();
    h2.transact(|moment| moment.put("b", "2")).unwrap();
    h1.transact(|moment| moment.put("c", "3")).unwrap();

    let latest = h2.latest().unwrap();
    assert_eq!(h2.count().unwrap(), 3);
    for (key, value) in [("a", "1"), ("b", "2"), ("c", "3")] {
        assert_eq!(read(&latest, key).unwrap(), value.as_bytes());
    }
}

#[test]
fn values_from_transact_are_independent_of_the_moment() {
    // the moment is discarded when nothing changes, so values that outlive
    // the transaction must be owned (borrowing it doesn't compile, see the
    // compile_fail doctest on History::transact)
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    let (foo, committed) =
        history.transact_with_status(|moment| moment.get_cursor("foo")?.unwrap().read_bytes(MAX_READ)).unwrap();
    assert!(!committed);
    history.transact(|moment| moment.put("foo", "changed-value!!")).unwrap();
    assert_eq!(foo, b"foo");
    assert_eq!(read(&history.latest().unwrap(), "foo").unwrap(), b"changed-value!!");
}

// Opens `path` read-only and checks that opening its history and reading it leaves the file
// byte for byte as it was.
fn read_only_history(path: &std::path::Path, check: impl FnOnce(&History<'_, CoreBufferedFile>)) {
    let before = std::fs::read(path).unwrap();
    let db = Database::open_read_only(path).unwrap();
    check(&History::new(&db).unwrap());
    drop(db);
    assert_eq!(std::fs::read(path).unwrap(), before);
}

#[test]
fn opens_a_read_only_history_without_writing() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let db = Database::open(tmp.path()).unwrap();
    History::new(&db).unwrap().transact(|moment| moment.put("foo", "foo")).unwrap();
    db.close().unwrap();
    read_only_history(tmp.path(), |history| {
        assert_eq!(read(&history.latest().unwrap(), "foo").unwrap(), b"foo");
        assert_eq!(history.count().unwrap(), 1);
    });
}

#[test]
fn opens_a_read_only_empty_history_without_writing() {
    // a writer created the file but has not transacted yet
    let tmp = tempfile::NamedTempFile::new().unwrap();
    Database::open(tmp.path()).unwrap().close().unwrap();
    read_only_history(tmp.path(), |history| {
        assert_eq!(history.count().unwrap(), 0);
        assert!(history.moment(-1).unwrap().is_none());
        assert!(read(&history.latest().unwrap(), "foo").is_none());
    });
}

#[test]
fn transact_initializes_an_empty_history() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    assert_eq!(history.count().unwrap(), 0);
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    assert_eq!(history.count().unwrap(), 1);
}
