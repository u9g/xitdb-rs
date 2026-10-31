//! Tests for versioned layouts and `History::migrate`.

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

fn new_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
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

fn add_proposals<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<()> {
    let mut proposals = moment.put_map("proposals")?;
    proposals.put("https://example.com/pr/1", "open")?;
    proposals.put("https://example.com/pr/2", "merged")?;
    Ok(())
}

// renames "proposals" to "merges", and reshapes each value from a status string into a map
// with a "status" key
fn proposals_to_merges<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<()> {
    let mut entries = Vec::new();
    if let Some(proposals) = moment.get_map("proposals")? {
        for kv in proposals.entries()? {
            let kv = kv?;
            entries.push((kv.key_cursor.read_string(MAX_READ)?, kv.value_cursor.read_string(MAX_READ)?));
        }
    }
    moment.remove("proposals")?;
    let mut merges = moment.put_map("merges")?;
    for (url, status) in entries {
        merges.put_map(url)?.put("status", status)?;
    }
    Ok(())
}

fn add_tokens<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<()> {
    moment.put_set("agent-tokens")?;
    Ok(())
}

fn migrations<C: Core + 'static>(count: usize) -> Migrations<C> {
    let all = [
        Migration::new(1, "add proposals", add_proposals),
        Migration::new(2, "proposals to merges", proposals_to_merges),
        Migration::new(3, "add agent tokens", add_tokens),
    ];
    Migrations::new(all.into_iter().take(count)).unwrap()
}

// the recorded version under the default key
fn version<C: Core + 'static>(history: &History<'_, C>) -> Result<u64> {
    history.version(&migrations::<C>(0))
}

fn merge_status(moment: &ReadHashMap<'_, impl Core>, url: &str) -> Option<String> {
    moment.get_map("merges").unwrap()?.get_map(url).unwrap()?.get_string("status", MAX_READ).unwrap()
}

#[test]
fn fresh_database_runs_all_migrations() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    assert_eq!(version(&history).unwrap(), 0);

    let migrated = history.migrate(&migrations(3)).unwrap();
    assert_eq!(
        migrated,
        Migrated { from: 0, to: 3, ran: vec!["add proposals", "proposals to merges", "add agent tokens"] }
    );

    // all in one moment
    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(version(&history).unwrap(), 3);
    let latest = history.latest().unwrap();
    assert_eq!(latest.get_uint(LAYOUT_VERSION_KEY).unwrap(), Some(3));
    assert!(latest.get_set("agent-tokens").unwrap().is_some());
}

#[test]
fn reopening_runs_none() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    {
        let db = Database::open(tmp.path()).unwrap();
        History::new(&db).unwrap().migrate(&migrations(3)).unwrap();
        db.close().unwrap();
    }

    let db = Database::open(tmp.path()).unwrap();
    let history = History::new(&db).unwrap();
    let size = db.committed_size().unwrap();
    let migrated = history.migrate(&migrations(3)).unwrap();
    assert_eq!(migrated, Migrated { from: 3, to: 3, ran: vec![] });

    // nothing was committed
    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(db.committed_size().unwrap(), size);
}

#[test]
fn adding_a_migration_runs_only_the_new_one() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.migrate(&migrations(1)).unwrap();
    assert_eq!(version(&history).unwrap(), 1);

    // the app writes data in the version 1 layout
    history.transact(|moment| moment.put_map("proposals")?.put("https://example.com/pr/3", "open")).unwrap();

    let migrated = history.migrate(&migrations(2)).unwrap();
    assert_eq!(migrated, Migrated { from: 1, to: 2, ran: vec!["proposals to merges"] });
    let migrated = history.migrate(&migrations(3)).unwrap();
    assert_eq!(migrated, Migrated { from: 2, to: 3, ran: vec!["add agent tokens"] });

    assert_eq!(history.count().unwrap(), 4);
    let latest = history.latest().unwrap();
    assert_eq!(merge_status(&latest, "https://example.com/pr/3").as_deref(), Some("open"));
}

#[test]
fn renames_a_key_and_reshapes_values() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.migrate(&migrations(1)).unwrap();
    let before = history.latest().unwrap();
    assert!(before.get_map("merges").unwrap().is_none());

    history.migrate(&migrations(2)).unwrap();
    let after = history.latest().unwrap();
    assert!(after.get_cursor("proposals").unwrap().is_none());
    assert_eq!(merge_status(&after, "https://example.com/pr/1").as_deref(), Some("open"));
    assert_eq!(merge_status(&after, "https://example.com/pr/2").as_deref(), Some("merged"));
    assert_eq!(after.get_map("merges").unwrap().unwrap().entries().unwrap().count(), 2);

    // the moment before the migration still has the old layout
    let first = history.moment(0).unwrap().unwrap();
    let proposals = first.get_map("proposals").unwrap().unwrap();
    assert_eq!(proposals.get_string("https://example.com/pr/1", MAX_READ).unwrap().as_deref(), Some("open"));
}

fn rename_foo<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<(), AppError> {
    let value = moment.get_string("foo", MAX_READ)?.unwrap_or_default();
    moment.remove("foo")?;
    moment.put("bar", value)?;
    Ok(())
}

fn reject<C: Core>(_: &mut WriteHashMap<'_, C>) -> Result<(), AppError> {
    Err(AppError::Rejected("nope"))
}

fn add_baz<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<(), AppError> {
    moment.put("baz", "baz")?;
    Ok(())
}

#[test]
fn failing_migration_changes_nothing() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    history.migrate(&Migrations::new([Migration::new(1, "add baz", add_baz)]).unwrap()).unwrap();
    let size = db.committed_size().unwrap();
    let len = db.core().length().unwrap();

    // the second migration fails after the first changed the moment
    let migrations = Migrations::new([
        Migration::new(1, "add baz", add_baz),
        Migration::new(2, "rename foo", rename_foo),
        Migration::new(3, "reject", reject),
    ])
    .unwrap();
    let result = history.migrate(&migrations);
    assert!(matches!(result, Err(AppError::Rejected("nope"))));

    // nothing was committed, and the discarded data is gone
    assert_eq!(history.count().unwrap(), 2);
    assert_eq!(db.committed_size().unwrap(), size);
    assert_eq!(db.core().length().unwrap(), len);
    assert_eq!(version(&history).unwrap(), 1);
    let latest = history.latest().unwrap();
    assert_eq!(latest.get_string("foo", MAX_READ).unwrap().as_deref(), Some("foo"));
    assert!(latest.get_cursor("bar").unwrap().is_none());

    // xitdb errors inside a migration convert into the custom type
    fn not_a_list<C: Core>(moment: &mut WriteHashMap<'_, C>) -> Result<(), AppError> {
        ReadArrayList::new(moment.get_cursor("foo")?.unwrap())?;
        Ok(())
    }
    let migrations = Migrations::new([
        Migration::new(1, "add baz", add_baz),
        Migration::new(2, "not a list", not_a_list),
    ])
    .unwrap();
    let result = history.migrate(&migrations);
    assert!(matches!(result, Err(AppError::Db(Error::UnexpectedTag))));
    assert_eq!(version(&history).unwrap(), 1);
    assert_eq!(db.committed_size().unwrap(), size);
}

#[test]
fn too_new_version_is_an_error() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.migrate(&migrations(3)).unwrap();
    let size = db.committed_size().unwrap();

    // an older binary that only knows two migrations
    let result = history.migrate(&migrations(2));
    assert!(matches!(result, Err(Error::LayoutTooNew { found: 3, known: 2 })));
    let result = history.migrate(&migrations(0));
    assert!(matches!(result, Err(Error::LayoutTooNew { found: 3, known: 0 })));
    assert_eq!(db.committed_size().unwrap(), size);
    assert_eq!(history.count().unwrap(), 1);
    assert_eq!(version(&history).unwrap(), 3);

    let err = history.migrate(&migrations(2)).unwrap_err();
    assert_eq!(err.to_string(), "layout version 3 is newer than the newest known version 2");
}

#[test]
fn rejects_invalid_lists() {
    fn check(versions: &[u64]) -> Result<Migrations<CoreMemory>> {
        Migrations::new(versions.iter().map(|&version| Migration::new(version, "add tokens", add_tokens)))
    }
    assert!(matches!(check(&[1, 1]), Err(Error::MigrationOutOfOrder { version: 1, previous: 1 })));
    assert!(matches!(check(&[1, 3, 2]), Err(Error::MigrationOutOfOrder { version: 2, previous: 3 })));
    assert!(matches!(check(&[0]), Err(Error::MigrationOutOfOrder { version: 0, previous: 0 })));

    // gaps are fine
    let migrations = check(&[2, 5, 10]).unwrap();
    assert_eq!(migrations.latest(), 10);
    assert_eq!(migrations.as_slice().len(), 3);
    assert_eq!(check(&[]).unwrap().latest(), 0);
}

#[test]
fn version_on_empty_and_migrated_databases() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    assert_eq!(version(&history).unwrap(), 0);

    // data without a recorded version is at version 0
    history.transact(|moment| moment.put("foo", "foo")).unwrap();
    assert_eq!(version(&history).unwrap(), 0);

    history.migrate(&migrations(2)).unwrap();
    assert_eq!(version(&history).unwrap(), 2);

    // a version that isn't a Uint is an error
    history.transact(|moment| moment.put(LAYOUT_VERSION_KEY, "two")).unwrap();
    assert!(matches!(version(&history), Err(Error::UnexpectedTag)));
    assert!(matches!(history.migrate(&migrations(3)), Err(Error::UnexpectedTag)));
    assert!(matches!(history.check_version(&migrations(3)), Err(Error::UnexpectedTag)));

    // so is an empty value: it reads as version 0
    history.transact(|moment| moment.put(LAYOUT_VERSION_KEY, Data::None)).unwrap();
    assert_eq!(version(&history).unwrap(), 0);
}

#[test]
fn reads_an_int_version() {
    // another implementation may write the version as an Int
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.migrate(&migrations(1)).unwrap();
    history.transact(|moment| moment.put(LAYOUT_VERSION_KEY, 1i64)).unwrap();
    assert_eq!(version(&history).unwrap(), 1);
    assert_eq!(history.check_version(&migrations(1)).unwrap(), 1);

    // migrating reads it, and records the new version as a Uint
    let migrated = history.migrate(&migrations(2)).unwrap();
    assert_eq!(migrated, Migrated { from: 1, to: 2, ran: vec!["proposals to merges"] });
    let slot = history.latest().unwrap().get_slot(LAYOUT_VERSION_KEY).unwrap().unwrap();
    assert_eq!(slot.tag, Tag::Uint);

    // a negative Int isn't a version
    history.transact(|moment| moment.put(LAYOUT_VERSION_KEY, -1i64)).unwrap();
    assert!(matches!(version(&history), Err(Error::ExpectedUnsignedLong)));
    assert!(matches!(history.migrate(&migrations(3)), Err(Error::ExpectedUnsignedLong)));
}

#[test]
fn unknown_version_is_an_error() {
    fn check(versions: &[u64]) -> Migrations<CoreMemory> {
        Migrations::new(versions.iter().map(|&version| Migration::new(version, "add tokens", add_tokens))).unwrap()
    }
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.migrate(&check(&[1, 4])).unwrap();
    let size = db.committed_size().unwrap();

    // version 4 was made by a migration that [1, 3, 5] doesn't have, so 5 can't run on it
    let result = history.migrate(&check(&[1, 3, 5]));
    assert!(matches!(result, Err(Error::UnknownLayoutVersion { found: 4 })));
    assert!(matches!(history.check_version(&check(&[1, 3, 5])), Err(Error::UnknownLayoutVersion { found: 4 })));
    assert!(matches!(history.check_version(&check(&[5])), Err(Error::UnknownLayoutVersion { found: 4 })));
    assert_eq!(db.committed_size().unwrap(), size);
    assert_eq!(version(&history).unwrap(), 4);
    assert_eq!(
        history.migrate(&check(&[5])).unwrap_err().to_string(),
        "layout version 4 isn't the version of any known migration"
    );

    // a list that has 4 runs only what comes after it, even with gaps
    let migrated = history.migrate(&check(&[2, 4, 7])).unwrap();
    assert_eq!(migrated, Migrated { from: 4, to: 7, ran: vec!["add tokens"] });
    assert_eq!(history.check_version(&check(&[2, 4, 7])).unwrap(), 7);
}

#[test]
fn migrations_can_capture() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let default_status = String::from("open");
    let migrations = Migrations::new([
        Migration::new(1, "add proposals", add_proposals),
        Migration::new(2, "default status", move |moment: &mut WriteHashMap<'_, CoreMemory>| {
            moment.put("default-status", default_status.as_str())
        }),
    ])
    .unwrap();
    history.migrate(&migrations).unwrap();
    let latest = history.latest().unwrap();
    assert_eq!(latest.get_string("default-status", MAX_READ).unwrap().as_deref(), Some("open"));
    assert!(latest.get_map("proposals").unwrap().is_some());

    // a migration list can be shared between threads
    fn assert_send_sync<T: Send + Sync>(_: &T) {}
    assert_send_sync(&migrations);
}

#[test]
fn no_migrations_on_new_database_commits_nothing() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let migrated = history.migrate(&migrations(0)).unwrap();
    assert_eq!(migrated, Migrated { from: 0, to: 0, ran: vec![] });
    assert_eq!(history.count().unwrap(), 0);
}

#[test]
fn custom_key() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let migrations = migrations(3).with_key("schema");
    assert_eq!(migrations.key(), "schema");
    history.migrate(&migrations).unwrap();

    let latest = history.latest().unwrap();
    assert_eq!(latest.get_uint("schema").unwrap(), Some(3));
    assert!(latest.get_cursor(LAYOUT_VERSION_KEY).unwrap().is_none());
    assert_eq!(history.version(&migrations).unwrap(), 3);
    assert_eq!(version(&history).unwrap(), 0);
    assert_eq!(history.check_version(&migrations).unwrap(), 3);
    assert_eq!(history.migrate(&migrations).unwrap().ran.len(), 0);
}

#[test]
fn read_only_reader_checks_version() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    {
        let db = Database::open(tmp.path()).unwrap();
        let history = History::new(&db).unwrap();
        // before the writer migrates, a reader sees an old layout
        assert!(matches!(history.check_version(&migrations(2)), Err(Error::LayoutTooOld { found: 0, expected: 2 })));
        history.migrate(&migrations(2)).unwrap();
        db.close().unwrap();
    }

    let before = std::fs::read(tmp.path()).unwrap();
    let db = Database::open_read_only(tmp.path()).unwrap();
    let history = History::new(&db).unwrap();
    assert_eq!(version(&history).unwrap(), 2);
    assert_eq!(history.check_version(&migrations(2)).unwrap(), 2);
    // an older reader refuses newer data, and a newer one waits for the writer to migrate
    assert!(matches!(history.check_version(&migrations(1)), Err(Error::LayoutTooNew { found: 2, known: 1 })));
    assert!(matches!(history.check_version(&migrations(3)), Err(Error::LayoutTooOld { found: 2, expected: 3 })));

    // migrating through a read-only database fails without writing
    assert!(history.migrate(&migrations(3)).is_err());
    drop(db);
    assert_eq!(std::fs::read(tmp.path()).unwrap(), before);
}
