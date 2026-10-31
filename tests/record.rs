//! Tests for records: `#[derive(Record)]` and `Map::update`.
#![cfg(feature = "derive")]

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

/// A merge, as gem's server stores it by hand.
#[derive(Record, Debug, Clone, PartialEq, Default)]
struct Merge {
    title: String,
    #[xitdb(rename = "started-at")]
    started_at: i64,
    question: bool,
    #[xitdb(rename = "thread")]
    thread_id: Option<String>,
}

const MERGES: Map<str, Merge> = Map::new("merges");
const URL: &str = "https://example.com/pr/1";

fn new_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
}

/// Runs `f` in a transaction on a new history and returns the database.
fn with_moment(f: impl for<'t> FnOnce(&mut WriteHashMap<'t, CoreMemory>) -> Result<()>) -> Database<CoreMemory> {
    let db = new_db();
    History::new(&db).unwrap().transact(f).unwrap();
    db
}

fn latest(db: &Database<CoreMemory>) -> ReadHashMap<'_, CoreMemory> {
    History::new(db).unwrap().latest().unwrap()
}

/// The stored map of the merge at `URL`.
fn stored<'a>(moment: &ReadHashMap<'a, CoreMemory>) -> ReadHashMap<'a, CoreMemory> {
    moment.get_map("merges").unwrap().unwrap().get_map(URL).unwrap().unwrap()
}

fn decode_error<T: std::fmt::Debug>(result: Result<T>) -> DecodeError {
    match result {
        Err(Error::Decode(err)) => *err,
        other => panic!("expected a decode error, got {other:?}"),
    }
}

fn merge() -> Merge {
    Merge { title: "Add records".into(), started_at: 1700000000, question: true, thread_id: Some("thread-0001".into()) }
}

#[test]
fn records_round_trip_as_maps_of_their_fields() {
    let merge = merge();
    let db = with_moment(|moment| MERGES.put(moment, URL, &merge));
    let moment = latest(&db);
    assert_eq!(MERGES.get(&moment, URL).unwrap(), Some(merge.clone()));
    assert_eq!(MERGES.iter(&moment).unwrap().collect::<Result<Vec<_>>>().unwrap(), [(URL.to_string(), merge)]);

    // stored under the renamed keys, the way gem writes it by hand
    let map = stored(&moment);
    assert_eq!(map.get_string("title", MAX_READ).unwrap().as_deref(), Some("Add records"));
    assert_eq!(map.get_int("started-at").unwrap(), Some(1700000000));
    assert_eq!(map.get_uint("question").unwrap(), Some(1));
    assert_eq!(map.get_string("thread", MAX_READ).unwrap().as_deref(), Some("thread-0001"));
    assert!(map.get_slot("started_at").unwrap().is_none());
    assert_eq!(<Merge as Record>::FIELDS, ["title", "started-at", "question", "thread"]);
}

#[test]
fn reads_data_written_by_hand() {
    let db = with_moment(|moment| {
        let mut merge = moment.put_map("merges")?.put_map(URL)?;
        merge.put("title", "By hand")?;
        merge.put("started-at", 1700000000i64)?;
        merge.put("question", 0u64)?;
        // gem writes "thread" later, so it's absent here
        Ok(())
    });
    let moment = latest(&db);
    let expected = Merge { title: "By hand".into(), started_at: 1700000000, question: false, thread_id: None };
    assert_eq!(MERGES.get(&moment, URL).unwrap(), Some(expected));

    // and what gem's hand-written reader reads from a derived record
    let db = with_moment(|moment| MERGES.put(moment, URL, &merge()));
    let map = stored(&latest(&db));
    assert_eq!(map.get_string("thread", None).unwrap().as_deref(), Some("thread-0001"));
    assert_eq!(map.get_string("title", None).unwrap().unwrap_or_default(), "Add records");
    assert_eq!(map.get_int("started-at").unwrap().unwrap_or_default(), 1700000000);
    assert!(map.get_uint("question").unwrap().is_some_and(|q| q != 0));
}

#[test]
fn missing_and_empty_fields_read_as_defaults() {
    let db = with_moment(|moment| {
        let mut merges = moment.put_map("merges")?;
        merges.put_map("empty")?;
        let mut nones = merges.put_map("nones")?;
        nones.put("title", Data::None)?;
        nones.put("thread", Data::None)?;
        Ok(())
    });
    let moment = latest(&db);
    assert_eq!(MERGES.get(&moment, "empty").unwrap(), Some(Merge::default()));
    assert_eq!(MERGES.get(&moment, "nones").unwrap(), Some(Merge::default()));
}

#[test]
fn required_fields_must_be_present() {
    #[derive(Record, Debug, Clone, PartialEq)]
    struct User {
        #[xitdb(required)]
        id: u64,
        name: String,
    }
    const USERS: Map<str, User> = Map::new("users");

    let db = with_moment(|moment| {
        USERS.put(moment, "a", &User { id: 0, name: String::new() })?;
        moment.put_map("users")?.put_map("b")?.put("name", "bob")?;
        Ok(())
    });
    let moment = latest(&db);
    assert_eq!(USERS.get(&moment, "a").unwrap(), Some(User { id: 0, name: String::new() }));
    let err = decode_error(USERS.get(&moment, "b"));
    assert_eq!(err.to_string(), r#"couldn't decode "users" at key "b" field "id": the field is missing"#);
}

#[test]
fn none_is_a_missing_field_and_writing_it_removes_the_field() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| MERGES.put(moment, URL, &merge())).unwrap();
    assert!(stored(&history.latest().unwrap()).get_slot("thread").unwrap().is_some());

    history.transact(|moment| MERGES.put(moment, URL, &Merge { thread_id: None, ..merge() })).unwrap();
    let moment = history.latest().unwrap();
    // removed, not stored as an empty value
    assert!(stored(&moment).get_slot("thread").unwrap().is_none());
    assert_eq!(MERGES.get(&moment, URL).unwrap().unwrap().thread_id, None);

    // put a record with None into a new key: the field is never written
    history.transact(|moment| MERGES.put(moment, "new", &Merge::default())).unwrap();
    let moment = history.latest().unwrap();
    let new = moment.get_map("merges").unwrap().unwrap().get_map("new").unwrap().unwrap();
    assert!(new.get_slot("thread").unwrap().is_none());
    assert_eq!(new.get_string("title", MAX_READ).unwrap().as_deref(), Some(""));
}

#[test]
fn unknown_fields_are_ignored_on_read_and_kept_on_write() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            MERGES.put(moment, URL, &merge())?;
            // written by newer code
            moment.put_map("merges")?.put_map(URL)?.put("reviewer", "ann")?;
            Ok::<_, Error>(())
        })
        .unwrap();
    assert_eq!(MERGES.get(&history.latest().unwrap(), URL).unwrap(), Some(merge()));

    history.transact(|moment| MERGES.update(moment, URL, |merge| merge.title = "Renamed".into())).unwrap();
    let map = stored(&history.latest().unwrap());
    assert_eq!(map.get_string("reviewer", MAX_READ).unwrap().as_deref(), Some("ann"));
    assert_eq!(map.get_string("title", MAX_READ).unwrap().as_deref(), Some("Renamed"));

    history.transact(|moment| MERGES.put(moment, URL, &Merge::default())).unwrap();
    let map = stored(&history.latest().unwrap());
    assert_eq!(map.get_string("reviewer", MAX_READ).unwrap().as_deref(), Some("ann"));
    assert_eq!(MERGES.get(&history.latest().unwrap(), URL).unwrap(), Some(Merge::default()));
}

#[test]
fn put_replaces_a_value_that_isnt_a_map() {
    let db = with_moment(|moment| {
        moment.put_map("merges")?.put(URL, "not a record")?;
        MERGES.put(moment, URL, &merge())
    });
    assert_eq!(MERGES.get(&latest(&db), URL).unwrap(), Some(merge()));
}

#[test]
fn update_writes_only_the_fields_that_changed() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| MERGES.put(moment, URL, &merge())).unwrap();
    let before = stored(&history.latest().unwrap());

    let updated = history
        .transact(|moment| MERGES.update(moment, URL, |merge| merge.started_at = 1800000000))
        .unwrap();
    assert_eq!(updated, Some(Merge { started_at: 1800000000, ..merge() }));
    let after = stored(&history.latest().unwrap());
    assert_eq!(MERGES.get(&history.latest().unwrap(), URL).unwrap(), updated);
    // unchanged fields keep their slots, so their bytes weren't written
    // again (both strings are too long to be stored in the slot)
    for field in ["title", "question", "thread"] {
        assert_eq!(before.get_slot(field).unwrap(), after.get_slot(field).unwrap(), "{field}");
    }
    assert_eq!(after.get_int("started-at").unwrap(), Some(1800000000));
    assert_eq!(updated.unwrap().changed_fields(&merge()), ["started-at"]);

    // Some to None removes the field
    history.transact(|moment| MERGES.update(moment, URL, |merge| merge.thread_id = None)).unwrap();
    assert!(stored(&history.latest().unwrap()).get_slot("thread").unwrap().is_none());
}

#[test]
fn update_that_changes_nothing_doesnt_commit() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| MERGES.put(moment, URL, &merge())).unwrap();
    let count = history.count().unwrap();

    // f runs but sets the values that are already there
    let (updated, committed) = history
        .transact_with_status(|moment| {
            MERGES.update(moment, URL, |merge| {
                merge.question = true;
                merge.title = "Add records".into();
            })
        })
        .unwrap();
    assert_eq!(updated, Some(merge()));
    assert!(!committed);

    // a missing key or collection isn't created, and f isn't called
    let (updated, committed) = history
        .transact_with_status(|moment| {
            let a = MERGES.update(moment, "missing", |_| panic!("f is only called for a stored record"))?;
            const OTHER: Map<str, Merge> = Map::new("other");
            let b = OTHER.update(moment, URL, |_| panic!("f is only called for a stored record"))?;
            Ok::<_, Error>((a, b))
        })
        .unwrap();
    assert_eq!(updated, (None, None));
    assert!(!committed);
    assert_eq!(history.count().unwrap(), count);

    // and a field that's missing in storage but default in the struct stays
    // missing
    history.transact(|moment| moment.put_map("merges")?.put_map("bare")?.put("title", "t")).unwrap();
    let (_, committed) = history
        .transact_with_status(|moment| MERGES.update(moment, "bare", |merge| merge.started_at = 0))
        .unwrap();
    assert!(!committed);
}

#[test]
fn upsert_starts_from_the_default() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let created = history.transact(|moment| MERGES.upsert(moment, URL, |merge| merge.question = true)).unwrap();
    assert_eq!(created, Merge { question: true, ..Merge::default() });
    let map = stored(&history.latest().unwrap());
    assert_eq!(map.get_string("title", MAX_READ).unwrap().as_deref(), Some(""));
    assert_eq!(map.get_uint("question").unwrap(), Some(1));

    let updated = history.transact(|moment| MERGES.upsert(moment, URL, |merge| merge.title = "t".into())).unwrap();
    assert_eq!(updated, Merge { title: "t".into(), question: true, ..Merge::default() });

    let (_, committed) =
        history.transact_with_status(|moment| MERGES.upsert(moment, URL, |merge| merge.question = true)).unwrap();
    assert!(!committed);
}

#[derive(Record, Debug, Clone, PartialEq, Default)]
struct Moment {
    #[xitdb(rename = "merge")]
    current: Merge,
    previous: Option<Merge>,
    count: u64,
    ratio: f64,
    data: Vec<u8>,
}

const MOMENTS: Map<u64, Moment> = Map::new("moments");

#[test]
fn records_nest() {
    let value = Moment { current: merge(), previous: None, count: 3, ratio: 0.5, data: vec![1, 2] };
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| MOMENTS.put(moment, &1, &value)).unwrap();
    let moment = history.latest().unwrap();
    assert_eq!(MOMENTS.get(&moment, &1).unwrap(), Some(value.clone()));
    let stored = moment.get_map("moments").unwrap().unwrap().get_map(1u64.to_be_bytes()).unwrap().unwrap();
    let merge_map = stored.get_map("merge").unwrap().unwrap();
    assert_eq!(merge_map.get_int("started-at").unwrap(), Some(1700000000));
    assert!(stored.get_slot("previous").unwrap().is_none());

    // a changed nested record is changed in place, keeping its unknown
    // keys, and only its changed fields are written
    let title = merge_map.get_slot("title").unwrap();
    history
        .transact(|moment| {
            MOMENTS.collection_mut(moment)?.put_map(1u64.to_be_bytes())?.put_map("merge")?.put("x", 1u64)
        })
        .unwrap();
    let updated = history
        .transact(|moment| {
            MOMENTS.update(moment, &1, |value| {
                value.current.question = false;
                value.previous = Some(Merge::default());
            })
        })
        .unwrap()
        .unwrap();
    let moment = history.latest().unwrap();
    assert_eq!(MOMENTS.get(&moment, &1).unwrap(), Some(updated));
    let stored = moment.get_map("moments").unwrap().unwrap().get_map(1u64.to_be_bytes()).unwrap().unwrap();
    let merge_map = stored.get_map("merge").unwrap().unwrap();
    assert_eq!((merge_map.get_uint("question").unwrap(), merge_map.get_uint("x").unwrap()), (Some(0), Some(1)));
    assert_eq!(merge_map.get_slot("title").unwrap(), title);
    // a nested record that was missing is written whole, defaults included
    let previous = stored.get_map("previous").unwrap().unwrap();
    assert_eq!(previous.get_string("title", MAX_READ).unwrap().as_deref(), Some(""));
}

#[test]
fn decode_errors_name_the_field() {
    let db = with_moment(|moment| {
        let mut merges = moment.put_map("merges")?;
        merges.put_map("text-time")?.put("started-at", "today")?;
        merges.put_map("two")?.put("question", 2u64)?;
        merges.put_map("int-thread")?.put("thread", 5i64)?;
        merges.put("not-a-map", "x")?;
        let mut moments = moment.put_map("moments")?;
        moments.put_map(1u64.to_be_bytes())?.put_map("merge")?.put("title", 1u64)?;
        moments.put_map(2u64.to_be_bytes())?.put("merge", "x")?;
        Ok(())
    });
    let moment = latest(&db);

    let err = decode_error(MERGES.get(&moment, "text-time"));
    assert_eq!(
        (err.collection.as_deref(), err.key.as_deref(), err.field.as_deref()),
        (Some("merges"), Some("\"text-time\""), Some("started-at"))
    );
    assert_eq!(
        err.to_string(),
        r#"couldn't decode "merges" at key "text-time" field "started-at": expected an integer, found ShortBytes"#
    );
    assert_eq!(decode_error(MERGES.get(&moment, "two")).message, "expected 0 or 1 for a bool, found 2");
    let err = decode_error(MERGES.get(&moment, "int-thread"));
    assert_eq!((err.field.as_deref(), err.message.as_str()), (Some("thread"), "expected bytes, found Int"));

    let err = decode_error(MERGES.get(&moment, "not-a-map"));
    assert_eq!((err.field, err.message.as_str()), (None, "expected a hash map, found ShortBytes"));

    // a nested record's field is a path
    let err = decode_error(MOMENTS.get(&moment, &1));
    assert_eq!((err.key.as_deref(), err.field.as_deref()), (Some("1"), Some("merge.title")));
    let err = decode_error(MOMENTS.get(&moment, &2));
    assert_eq!((err.field.as_deref(), err.message.as_str()), (Some("merge"), "expected a hash map, found ShortBytes"));

    // and update returns the error without writing
    let history = History::new(&db).unwrap();
    let result = history.transact_with_status(|moment| MERGES.update(moment, "two", |_| unreachable!()));
    assert!(matches!(result, Err(Error::Decode(_))));
}

#[test]
fn records_work_as_plain_value_codecs() {
    // a record is a ValueCodec, so it can be written through any cursor
    let db = with_moment(|moment| Merge::write(&merge(), &mut moment.put_cursor("merge")?));
    let cursor = latest(&db).get_cursor("merge").unwrap().unwrap();
    assert_eq!(Merge::read(&cursor).unwrap(), merge());
    assert_eq!(Merge::read_fields(&ReadHashMap::new(&cursor).unwrap()).unwrap(), merge());
}

#[cfg(feature = "serde")]
mod json {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Default)]
    struct Progress {
        done: u64,
        total: u64,
    }

    #[derive(Record, Debug, Clone, PartialEq, Default)]
    struct Job {
        #[xitdb(codec = Json<Progress>)]
        progress: Progress,
        #[xitdb(codec = Option<Json<Vec<String>>>, rename = "log")]
        lines: Option<Vec<String>>,
    }

    const JOBS: Map<str, Job> = Map::new("jobs");

    #[test]
    fn json_fields() {
        let job = Job { progress: Progress { done: 1, total: 2 }, lines: Some(vec!["a".into()]) };
        let db = new_db();
        let history = History::new(&db).unwrap();
        history.transact(|moment| JOBS.put(moment, "j", &job)).unwrap();
        let moment = history.latest().unwrap();
        assert_eq!(JOBS.get(&moment, "j").unwrap(), Some(job.clone()));
        let map = moment.get_map("jobs").unwrap().unwrap().get_map("j").unwrap().unwrap();
        let progress = map.get_cursor("progress").unwrap().unwrap().read_bytes_object(MAX_READ).unwrap();
        assert_eq!(progress.format_tag, Some(JSON_FORMAT_TAG));
        assert_eq!(&*progress.value, br#"{"done":1,"total":2}"#);
        assert_eq!(map.get_string("log", MAX_READ).unwrap().as_deref(), Some(r#"["a"]"#));

        let (_, committed) = history
            .transact_with_status(|moment| JOBS.update(moment, "j", |job| job.progress.total = 2))
            .unwrap();
        assert!(!committed);

        history.transact(|moment| moment.put_map("jobs")?.put_map("bad")?.put("log", "[1]")).unwrap();
        let err = decode_error(JOBS.get(&history.latest().unwrap(), "bad"));
        assert_eq!(err.field.as_deref(), Some("log"));
        assert!(err.message.starts_with("invalid json"), "{}", err.message);
    }
}

#[test]
fn floats_change_by_their_bits() {
    #[derive(Record, Debug, Clone, PartialEq, Default)]
    struct Reading {
        value: f64,
    }
    const READINGS: Map<str, Reading> = Map::new("readings");

    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| READINGS.put(moment, "a", &Reading { value: 0.0 })).unwrap();

    // -0.0 == 0.0, but it's stored differently, so it's written
    let (_, committed) =
        history.transact_with_status(|moment| READINGS.update(moment, "a", |r| r.value = -0.0)).unwrap();
    assert!(committed);
    let value = READINGS.get(&history.latest().unwrap(), "a").unwrap().unwrap().value;
    assert!(value == 0.0 && value.is_sign_negative());

    // NaN != NaN, but the same NaN is stored the same, so it isn't
    history.transact(|moment| READINGS.update(moment, "a", |r| r.value = f64::NAN)).unwrap();
    let (_, committed) =
        history.transact_with_status(|moment| READINGS.update(moment, "a", |r| r.value = f64::NAN)).unwrap();
    assert!(!committed);
    assert!(READINGS.get(&history.latest().unwrap(), "a").unwrap().unwrap().value.is_nan());
}

/// An `Option` by another name is still a missing field when it's `None`.
type Thread = Option<String>;

#[derive(Record, Debug, Clone, PartialEq, Default)]
struct Aliased {
    thread: Thread,
}

#[test]
fn option_aliases_are_missing_fields_when_none() {
    const ALIASED: Map<str, Aliased> = Map::new("aliased");
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| ALIASED.put(moment, "a", &Aliased { thread: Some("t".into()) })).unwrap();
    history.transact(|moment| ALIASED.update(moment, "a", |a| a.thread = None)).unwrap();
    history.transact(|moment| ALIASED.put(moment, "b", &Aliased { thread: None })).unwrap();
    let moment = history.latest().unwrap();
    let aliased = moment.get_map("aliased").unwrap().unwrap();
    for key in ["a", "b"] {
        let map = aliased.get_map(key).unwrap().unwrap();
        // missing, not an empty value
        assert!(map.get_slot("thread").unwrap().is_none(), "{key}");
        assert_eq!(ALIASED.get(&moment, key).unwrap(), Some(Aliased { thread: None }));
    }
}

/// Names that the generated code mustn't collide with: a type named like
/// a generic, and constants named like its variables.
#[allow(non_upper_case_globals, dead_code)]
mod collisions {
    use xitdb::*;

    pub type C = String;
    pub type F = u64;
    const map: u8 = 0;
    const old: u8 = 0;
    const value: u8 = 0;
    const cursor: u8 = 0;
    const changed: u8 = 0;

    #[derive(Record, Debug, Clone, PartialEq, Default)]
    pub struct Named {
        pub r#type: C,
        pub count: F,
    }
}

#[test]
fn raw_identifiers_and_colliding_names() {
    use collisions::Named;
    const NAMED: Map<str, Named> = Map::new("named");
    assert_eq!(<Named as Record>::FIELDS, ["type", "count"]);

    let named = Named { r#type: "kind".into(), count: 2 };
    let db = with_moment(|moment| NAMED.put(moment, "a", &named));
    let moment = latest(&db);
    let map = moment.get_map("named").unwrap().unwrap().get_map("a").unwrap().unwrap();
    assert_eq!(map.get_string("type", MAX_READ).unwrap().as_deref(), Some("kind"));
    assert!(map.get_slot("r#type").unwrap().is_none());
    assert_eq!(NAMED.get(&moment, "a").unwrap(), Some(named));
}

/// xitdb, re-exported, as a crate that wraps it would.
mod reexport {
    pub use xitdb as db;
}

#[derive(reexport::db::Record, Debug, Clone, PartialEq, Default)]
#[xitdb(crate = "crate::reexport::db")]
struct Reexported {
    name: String,
}

#[test]
fn the_crate_path_can_be_given() {
    const REEXPORTED: Map<str, Reexported> = Map::new("reexported");
    let value = Reexported { name: "n".into() };
    let db = with_moment(|moment| REEXPORTED.put(moment, "a", &value));
    assert_eq!(REEXPORTED.get(&latest(&db), "a").unwrap(), Some(value));
}

#[test]
fn write_changed_fields_opens_the_map_only_for_a_change() {
    let db = with_moment(|moment| MERGES.put(moment, URL, &merge()));
    let history = History::new(&db).unwrap();
    let (opened, committed) = history
        .transact_with_status(|moment| {
            let old = MERGES.get(moment, URL)?.unwrap();
            let mut map = LazyMap::new(|| -> Result<WriteHashMap<'_, CoreMemory>> { panic!("nothing changed") });
            let wrote = old.clone().write_changed_fields(&old, &mut map)?;
            Ok::<_, Error>(wrote || map.is_open())
        })
        .unwrap();
    assert!(!opened && !committed);
}

#[test]
fn update_at_writes_nothing_along_the_path_if_nothing_changed() {
    let path = ["rooms", "lobby"];
    let db = with_moment(|moment| {
        let mut lobby = moment.put_map("rooms")?.put_map("lobby")?;
        MERGES.put(&mut lobby, URL, &merge())
    });
    let history = History::new(&db).unwrap();

    let (updated, committed) = history
        .transact_with_status(|moment| MERGES.update_at(moment, &path, URL, |merge| merge.question = true))
        .unwrap();
    assert_eq!(updated, Some(merge()));
    assert!(!committed);

    // getting the parent with put_map copies the path, so that commits
    let (_, committed) = history
        .transact_with_status(|moment| {
            let mut lobby = moment.put_map("rooms")?.put_map("lobby")?;
            MERGES.update(&mut lobby, URL, |merge| merge.question = true)
        })
        .unwrap();
    assert!(committed);

    let (updated, committed) = history
        .transact_with_status(|moment| MERGES.update_at(moment, &path, URL, |merge| merge.question = false))
        .unwrap();
    assert!(committed);
    let lobby = history.latest().unwrap().get_map("rooms").unwrap().unwrap().get_map("lobby").unwrap().unwrap();
    assert_eq!(MERGES.get(&lobby, URL).unwrap(), updated);
    assert!(!updated.unwrap().question);

    // a missing map along the path is a missing key
    let (updated, committed) = history
        .transact_with_status(|moment| MERGES.update_at(moment, &["rooms", "hall"], URL, |_| unreachable!()))
        .unwrap();
    assert!(updated.is_none() && !committed);
}
