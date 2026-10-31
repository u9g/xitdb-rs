//! Tests for typed collections (`Map` and `Set`) and their codecs.

use xitdb::*;

const MAX_READ: Option<u64> = Some(1024);

const NAMES: Map<str, String> = Map::new("names");
const STARTED: Set<str> = Set::new("started");

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

fn decode_error<T: std::fmt::Debug>(result: Result<T>) -> DecodeError {
    match result {
        Err(Error::Decode(err)) => *err,
        other => panic!("expected a decode error, got {other:?}"),
    }
}

#[test]
fn map_round_trips_in_transact() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            NAMES.put(moment, "a", "alice")?;
            NAMES.put(moment, "b", "bob")?;
            // reads inside the transaction see its writes
            assert_eq!(NAMES.get(moment, "a")?.as_deref(), Some("alice"));
            NAMES.put(moment, "a", "amy")?;
            Ok::<_, Error>(())
        })
        .unwrap();

    let moment = history.latest().unwrap();
    assert_eq!(NAMES.get(&moment, "a").unwrap().as_deref(), Some("amy"));
    assert_eq!(NAMES.get(&moment, "b").unwrap().as_deref(), Some("bob"));
    assert_eq!(NAMES.get(&moment, "c").unwrap(), None);
    assert!(NAMES.contains(&moment, "b").unwrap());
    assert!(!NAMES.contains(&moment, "c").unwrap());

    let mut entries: Vec<(String, String)> = NAMES.iter(&moment).unwrap().collect::<Result<_>>().unwrap();
    entries.sort();
    assert_eq!(entries, [("a".to_string(), "amy".to_string()), ("b".to_string(), "bob".to_string())]);

    let removed = history.transact(|moment| Ok::<_, Error>((NAMES.remove(moment, "a")?, NAMES.remove(moment, "a")?)));
    assert_eq!(removed.unwrap(), (true, false));
    let moment = history.latest().unwrap();
    assert_eq!(NAMES.get(&moment, "a").unwrap(), None);
    assert_eq!(NAMES.iter(&moment).unwrap().count(), 1);

    // the first moment is unchanged
    let first = history.moment(0).unwrap().unwrap();
    assert_eq!(NAMES.get(&first, "a").unwrap().as_deref(), Some("amy"));
}

#[test]
fn typed_and_untyped_are_the_same_data() {
    let db = with_moment(|moment| {
        NAMES.put(moment, "a", "alice")?;
        moment.put_map("names")?.put("b", "bob")?;
        STARTED.insert(moment, "x")?;
        moment.put_set("started")?.put("y")?;
        Ok(())
    });
    let moment = latest(&db);
    let names = moment.get_map("names").unwrap().unwrap();
    assert_eq!(names.get_string("a", MAX_READ).unwrap().as_deref(), Some("alice"));
    assert_eq!(NAMES.get(&moment, "b").unwrap().as_deref(), Some("bob"));
    assert!(moment.get_set("started").unwrap().unwrap().contains("x").unwrap());
    assert!(STARTED.contains(&moment, "y").unwrap());
    assert_eq!(NAMES.collection(&moment).unwrap().unwrap().slot().unwrap(), names.slot().unwrap());
    assert_eq!(NAMES.name(), "names");
}

#[test]
fn missing_collections_read_as_empty() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let moment = history.latest().unwrap();
    assert_eq!(NAMES.get(&moment, "a").unwrap(), None);
    assert!(!NAMES.contains(&moment, "a").unwrap());
    assert_eq!(NAMES.iter(&moment).unwrap().count(), 0);
    assert!(!STARTED.contains(&moment, "a").unwrap());
    assert_eq!(STARTED.iter(&moment).unwrap().count(), 0);
    assert!(NAMES.collection(&moment).unwrap().is_none());

    // removing from a missing collection doesn't create it, so nothing is
    // committed
    let (removed, committed) = history
        .transact_with_status(|moment| Ok::<_, Error>(NAMES.remove(moment, "a")? || STARTED.remove(moment, "a")?))
        .unwrap();
    assert!(!removed && !committed);
    assert_eq!(history.count().unwrap(), 0);
}

#[test]
fn removing_a_missing_key_writes_nothing() {
    let db = with_moment(|moment| NAMES.put(moment, "a", "alice"));
    let history = History::new(&db).unwrap();
    let (removed, committed) = history.transact_with_status(|moment| NAMES.remove(moment, "zzz")).unwrap();
    assert!(!removed && !committed);
}

#[test]
fn sets() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let inserted = history
        .transact(|moment| {
            Ok::<_, Error>([STARTED.insert(moment, "a")?, STARTED.insert(moment, "b")?, STARTED.insert(moment, "a")?])
        })
        .unwrap();
    assert_eq!(inserted, [true, true, false]);

    let moment = history.latest().unwrap();
    assert!(STARTED.contains(&moment, "a").unwrap());
    assert!(!STARTED.contains(&moment, "c").unwrap());
    let mut keys: Vec<String> = STARTED.iter(&moment).unwrap().collect::<Result<_>>().unwrap();
    keys.sort();
    assert_eq!(keys, ["a", "b"]);

    // inserting a key that's already there writes nothing
    let (inserted, committed) = history.transact_with_status(|moment| STARTED.insert(moment, "a")).unwrap();
    assert!(!inserted && !committed);

    let removed =
        history.transact(|moment| Ok::<_, Error>((STARTED.remove(moment, "a")?, STARTED.remove(moment, "a")?)));
    assert_eq!(removed.unwrap(), (true, false));
    let moment = history.latest().unwrap();
    assert_eq!(STARTED.iter(&moment).unwrap().collect::<Result<Vec<_>>>().unwrap(), ["b"]);

    let numbers: Set<u64> = Set::new("numbers");
    let db = with_moment(|moment| {
        numbers.insert(moment, &7)?;
        Ok(())
    });
    assert_eq!(numbers.iter(&latest(&db)).unwrap().collect::<Result<Vec<_>>>().unwrap(), [7]);
}

#[test]
fn key_codecs() {
    const STRINGS: Map<String, u64> = Map::new("strings");
    const BYTES: Map<[u8], u64> = Map::new("bytes");
    const BYTE_VECS: Map<Vec<u8>, u64> = Map::new("byte-vecs");
    const U8: Map<u8, u64> = Map::new("u8");
    const U16: Map<u16, u64> = Map::new("u16");
    const U32: Map<u32, u64> = Map::new("u32");
    const U64: Map<u64, u64> = Map::new("u64");
    const I8: Map<i8, u64> = Map::new("i8");
    const I16: Map<i16, u64> = Map::new("i16");
    const I32: Map<i32, u64> = Map::new("i32");
    const I64: Map<i64, u64> = Map::new("i64");

    let db = with_moment(|moment| {
        STRINGS.put(moment, &"s".to_string(), &1)?;
        BYTES.put(moment, b"\x00\xff", &2)?;
        BYTE_VECS.put(moment, &vec![1, 2, 3], &3)?;
        U8.put(moment, &u8::MAX, &4)?;
        U16.put(moment, &0x0102, &5)?;
        U32.put(moment, &7, &6)?;
        U64.put(moment, &u64::MAX, &7)?;
        I8.put(moment, &-1, &8)?;
        I16.put(moment, &i16::MIN, &9)?;
        I32.put(moment, &-2, &10)?;
        I64.put(moment, &-3, &11)?;
        Ok(())
    });
    let moment = latest(&db);

    fn only<K: KeyCodec + ?Sized>(map: Map<K, u64>, moment: &ReadHashMap<'_, CoreMemory>) -> (K::Owned, u64) {
        let mut entries: Vec<_> = map.iter(moment).unwrap().collect::<Result<_>>().unwrap();
        assert_eq!(entries.len(), 1);
        entries.remove(0)
    }
    assert_eq!(only(STRINGS, &moment), ("s".to_string(), 1));
    assert_eq!(only(BYTES, &moment), (vec![0, 0xff], 2));
    assert_eq!(only(BYTE_VECS, &moment), (vec![1, 2, 3], 3));
    assert_eq!(only(U8, &moment), (u8::MAX, 4));
    assert_eq!(only(U16, &moment), (0x0102, 5));
    assert_eq!(only(U32, &moment), (7, 6));
    assert_eq!(only(U64, &moment), (u64::MAX, 7));
    assert_eq!(only(I8, &moment), (-1, 8));
    assert_eq!(only(I16, &moment), (i16::MIN, 9));
    assert_eq!(only(I32, &moment), (-2, 10));
    assert_eq!(only(I64, &moment), (-3, 11));

    // a `String` key and a `str` key are the same bytes
    assert_eq!(Map::<str, u64>::new("strings").get(&moment, "s").unwrap(), Some(1));

    // integer keys are big-endian at their full width, two's complement
    let raw = |name: &str, key: &[u8]| moment.get_map(name).unwrap().unwrap().get_uint(key).unwrap();
    assert_eq!(raw("u16", &[1, 2]), Some(5));
    assert_eq!(raw("u32", &[0, 0, 0, 7]), Some(6));
    assert_eq!(raw("i32", &[0xff, 0xff, 0xff, 0xfe]), Some(10));
    assert_eq!(raw("i64", &(-3i64).to_be_bytes()), Some(11));
    assert_eq!(U32.get(&moment, &7).unwrap(), Some(6));
    assert_eq!(I16.get(&moment, &i16::MIN).unwrap(), Some(9));
}

#[test]
fn value_codecs() {
    const STRINGS: Map<str, String> = Map::new("strings");
    const BYTES: Map<str, Vec<u8>> = Map::new("bytes");
    const INTS: Map<str, i64> = Map::new("ints");
    const UINTS: Map<str, u64> = Map::new("uints");
    const FLOATS: Map<str, f64> = Map::new("floats");
    const BOOLS: Map<str, bool> = Map::new("bools");
    const OPTIONS: Map<str, Option<String>> = Map::new("options");

    let long = "a string too long to fit in a slot".to_string();
    let db = with_moment(|moment| {
        STRINGS.put(moment, "short", "hi")?;
        STRINGS.put(moment, "long", &long)?;
        STRINGS.put(moment, "empty", "")?;
        BYTES.put(moment, "zeroes", &[0, 0, 1])?;
        INTS.put(moment, "min", &i64::MIN)?;
        UINTS.put(moment, "max", &(i64::MAX as u64))?;
        FLOATS.put(moment, "pi", &3.5)?;
        BOOLS.put(moment, "yes", &true)?;
        BOOLS.put(moment, "no", &false)?;
        OPTIONS.put(moment, "some", &Some("x".to_string()))?;
        OPTIONS.put(moment, "none", &None)?;
        Ok(())
    });
    let moment = latest(&db);

    assert_eq!(STRINGS.get(&moment, "short").unwrap().as_deref(), Some("hi"));
    assert_eq!(STRINGS.get(&moment, "long").unwrap(), Some(long));
    assert_eq!(STRINGS.get(&moment, "empty").unwrap().as_deref(), Some(""));
    assert_eq!(BYTES.get(&moment, "zeroes").unwrap(), Some(vec![0, 0, 1]));
    assert_eq!(INTS.get(&moment, "min").unwrap(), Some(i64::MIN));
    assert_eq!(UINTS.get(&moment, "max").unwrap(), Some(i64::MAX as u64));
    assert_eq!(FLOATS.get(&moment, "pi").unwrap(), Some(3.5));
    assert_eq!(BOOLS.get(&moment, "yes").unwrap(), Some(true));
    assert_eq!(BOOLS.get(&moment, "no").unwrap(), Some(false));
    assert_eq!(OPTIONS.get(&moment, "some").unwrap(), Some(Some("x".to_string())));
    // `None` is an empty value, which a map reads as missing
    assert_eq!(OPTIONS.get(&moment, "none").unwrap(), None);
    assert!(!OPTIONS.contains(&moment, "none").unwrap());
    assert_eq!(OPTIONS.iter(&moment).unwrap().count(), 1);

    // how they're stored, as untyped code reads them
    let ints = moment.get_map("ints").unwrap().unwrap();
    assert_eq!(ints.get_int("min").unwrap(), Some(i64::MIN));
    let bools = moment.get_map("bools").unwrap().unwrap();
    assert_eq!(bools.get_uint("yes").unwrap(), Some(1));
    assert_eq!(bools.get_uint("no").unwrap(), Some(0));
    let options = moment.get_map("options").unwrap().unwrap();
    assert_eq!(options.get_slot("none").unwrap().unwrap().tag, Tag::None);
    let strings = moment.get_map("strings").unwrap().unwrap();
    assert_eq!(strings.get_cursor("short").unwrap().unwrap().read_bytes_object(MAX_READ).unwrap().format_tag, None);
}

#[test]
fn integers_read_across_signedness() {
    const INTS: Map<str, i64> = Map::new("ints");
    const UINTS: Map<str, u64> = Map::new("uints");
    let db = with_moment(|moment| {
        let mut ints = moment.put_map("ints")?;
        ints.put("from-uint", 5u64)?;
        ints.put("too-big", u64::MAX >> 1)?;
        let mut uints = moment.put_map("uints")?;
        uints.put("from-int", 6i64)?;
        uints.put("negative", -1i64)?;
        Ok(())
    });
    let moment = latest(&db);
    assert_eq!(INTS.get(&moment, "from-uint").unwrap(), Some(5));
    assert_eq!(INTS.get(&moment, "too-big").unwrap(), Some(i64::MAX));
    assert_eq!(UINTS.get(&moment, "from-int").unwrap(), Some(6));
    let err = decode_error(UINTS.get(&moment, "negative"));
    assert_eq!(err.message, "-1 doesn't fit in a u64");
}

#[test]
fn decode_errors_have_context() {
    const UINTS: Map<str, u64> = Map::new("uints");
    const FLOATS: Map<str, f64> = Map::new("floats");
    const BOOLS: Map<str, bool> = Map::new("bools");
    const BYTES: Map<str, Vec<u8>> = Map::new("names");
    const BY_ID: Map<u64, String> = Map::new("names");
    const IDS: Set<u32> = Set::new("ids");

    let db = with_moment(|moment| {
        let mut names = moment.put_map("names")?;
        names.put("int", 5u64)?;
        names.put("bad-utf8", &[0xff, 0xfe][..])?;
        moment.put_map("uints")?.put("text", "five")?;
        moment.put_map("floats")?.put("int", 1i64)?;
        moment.put_map("bools")?.put("two", 2u64)?;
        moment.put_set("ids")?.put("abc")?;
        Ok(())
    });
    let moment = latest(&db);

    let err = decode_error(NAMES.get(&moment, "int"));
    assert_eq!(err.collection.as_deref(), Some("names"));
    assert_eq!(err.key.as_deref(), Some("\"int\""));
    assert_eq!(err.message, "expected bytes, found Uint");
    assert_eq!(err.to_string(), "couldn't decode \"names\" at key \"int\": expected bytes, found Uint");

    let err = decode_error(NAMES.get(&moment, "bad-utf8"));
    assert!(err.message.starts_with("invalid utf-8"), "{}", err.message);
    // the same bytes decode as bytes
    assert_eq!(BYTES.get(&moment, "bad-utf8").unwrap(), Some(vec![0xff, 0xfe]));

    assert_eq!(decode_error(UINTS.get(&moment, "text")).message, "expected an integer, found ShortBytes");
    assert_eq!(decode_error(FLOATS.get(&moment, "int")).message, "expected a float, found Int");
    assert_eq!(decode_error(BOOLS.get(&moment, "two")).message, "expected 0 or 1 for a bool, found 2");

    // iteration yields the error for that entry, and continues
    let results: Vec<_> = NAMES.iter(&moment).unwrap().collect();
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|result| matches!(result, Err(Error::Decode(_)))));

    // keys that don't decode are shown as lossy strings
    let err = decode_error(BY_ID.iter(&moment).unwrap().next().unwrap());
    assert_eq!(err.collection.as_deref(), Some("names"));
    assert!(err.message.starts_with("expected a 8-byte u64 key, found"), "{}", err.message);
    let err = decode_error(IDS.iter(&moment).unwrap().next().unwrap());
    assert_eq!(err.key.as_deref(), Some("\"abc\""));
    assert_eq!(err.message, "expected a 4-byte u32 key, found 3 bytes");

    // a collection of the wrong type isn't a decode error
    let db = with_moment(|moment| moment.put("names", "not a map"));
    assert!(matches!(NAMES.get(&latest(&db), "a"), Err(Error::UnexpectedTag)));
}

#[test]
fn empty_values_read_as_missing() {
    let db = with_moment(|moment| {
        let mut names = moment.put_map("names")?;
        names.put("empty", Data::None)?;
        names.put("a", "alice")?;
        Ok(())
    });
    let moment = latest(&db);
    assert_eq!(NAMES.get(&moment, "empty").unwrap(), None);
    assert!(!NAMES.contains(&moment, "empty").unwrap());
    let entries: Vec<_> = NAMES.iter(&moment).unwrap().collect::<Result<_>>().unwrap();
    assert_eq!(entries, [("a".to_string(), "alice".to_string())]);
}

#[test]
fn definitions_work_on_nested_maps() {
    const ROOMS: &str = "rooms";
    const MESSAGES: Map<u64, String> = Map::new("messages");
    const MEMBERS: Set<str> = Set::new("members");

    let db = with_moment(|moment| {
        for (room, text) in [("lobby", "hi"), ("games", "gg")] {
            let mut room = moment.put_map(ROOMS)?.put_map(room)?;
            MESSAGES.put(&mut room, &1, text)?;
            MEMBERS.insert(&mut room, "alice")?;
        }
        // the same definition on the moment is a different collection
        MESSAGES.put(moment, &1, "top level")?;
        Ok(())
    });
    let moment = latest(&db);
    let rooms = moment.get_map(ROOMS).unwrap().unwrap();
    let lobby = rooms.get_map("lobby").unwrap().unwrap();
    assert_eq!(MESSAGES.get(&lobby, &1).unwrap().as_deref(), Some("hi"));
    assert!(MEMBERS.contains(&lobby, "alice").unwrap());
    let games = rooms.get_map("games").unwrap().unwrap();
    assert_eq!(MESSAGES.get(&games, &1).unwrap().as_deref(), Some("gg"));
    assert_eq!(MESSAGES.get(&moment, &1).unwrap().as_deref(), Some("top level"));
    assert!(!MEMBERS.contains(&moment, "alice").unwrap());

    // a typed collection's map can be the parent of another
    const THREADS: Map<str, String> = Map::new("threads");
    let db = with_moment(|moment| {
        let mut threads = THREADS.collection_mut(moment)?;
        MEMBERS.insert(&mut threads, "bob")?;
        Ok(())
    });
    let moment = latest(&db);
    let threads = THREADS.collection(&moment).unwrap().unwrap();
    assert!(MEMBERS.contains(&threads, "bob").unwrap());
}

/// A value stored as a nested hash map of its fields, the way a derived
/// record would be.
#[derive(Debug, PartialEq)]
struct Point {
    x: i64,
    label: Option<String>,
}

const X: &str = "x";
const LABEL: &str = "label";

impl ValueCodec for Point {
    type Owned = Point;
    type Borrowed = Point;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Point> {
        let map = ReadHashMap::new(cursor)?;
        let field = |name: &str| map.get_cursor(name);
        let x = match field(X)? {
            Some(cursor) => i64::read(&cursor)?,
            None => return Err(Error::decode("missing field x")),
        };
        let label = match field(LABEL)? {
            Some(cursor) => <Option<String>>::read(&cursor)?,
            None => None,
        };
        Ok(Point { x, label })
    }

    fn write<C: Core>(value: &Point, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        let mut map = WriteHashMap::new(cursor)?;
        i64::write(&value.x, &mut map.put_cursor(X)?)?;
        <Option<String>>::write(&value.label, &mut map.put_cursor(LABEL)?)
    }
}

#[test]
fn values_can_be_nested_structures() {
    const POINTS: Map<str, Point> = Map::new("points");
    let a = Point { x: -4, label: Some("a".into()) };
    let b = Point { x: 9, label: None };
    let db = with_moment(|moment| {
        POINTS.put(moment, "a", &a)?;
        POINTS.put(moment, "b", &b)?;
        moment.put_map("points")?.put_map("no-x")?.put(LABEL, "c")?;
        moment.put_map("points")?.put("not-a-map", 1u64)?;
        Ok(())
    });
    let moment = latest(&db);
    assert_eq!(POINTS.get(&moment, "a").unwrap(), Some(a));
    assert_eq!(POINTS.get(&moment, "b").unwrap(), Some(b));

    // stored as a nested map, with None as an empty value
    let b = moment.get_map("points").unwrap().unwrap().get_map("b").unwrap().unwrap();
    assert_eq!(b.get_int(X).unwrap(), Some(9));
    assert_eq!(b.get_slot(LABEL).unwrap().unwrap().tag, Tag::None);

    let err = decode_error(POINTS.get(&moment, "no-x"));
    assert_eq!((err.collection.as_deref(), err.key.as_deref()), (Some("points"), Some("\"no-x\"")));
    assert_eq!(err.message, "missing field x");

    // an unexpected tag from a codec gets the same context
    let err = decode_error(POINTS.get(&moment, "not-a-map"));
    assert_eq!(err.key.as_deref(), Some("\"not-a-map\""));
    assert_eq!(err.message, "unexpected tag");
}

#[cfg(feature = "serde")]
mod json {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
    struct Proposal {
        id: String,
        votes: u64,
    }

    const PROPOSALS: Map<str, Json<Proposal>> = Map::new("proposals");

    #[test]
    fn json_round_trips_with_a_format_tag() {
        let proposal = Proposal { id: "p1".into(), votes: 2 };
        let db = with_moment(|moment| PROPOSALS.put(moment, &proposal.id, &proposal));
        let moment = latest(&db);
        assert_eq!(PROPOSALS.get(&moment, "p1").unwrap(), Some(proposal.clone()));
        let entries: Vec<_> = PROPOSALS.iter(&moment).unwrap().collect::<Result<_>>().unwrap();
        assert_eq!(entries, [("p1".to_string(), proposal)]);

        let stored = moment.get_map("proposals").unwrap().unwrap().get_cursor("p1").unwrap().unwrap();
        let bytes = stored.read_bytes_object(MAX_READ).unwrap();
        assert_eq!(bytes.format_tag, Some(JSON_FORMAT_TAG));
        assert_eq!(&*bytes.value, br#"{"id":"p1","votes":2}"#);
    }

    #[test]
    fn json_reads_untagged_and_rejects_other_tags() {
        let db = with_moment(|moment| {
            let mut proposals = moment.put_map("proposals")?;
            // written as a plain string, as before the codec existed
            proposals.put("untagged", r#"{"id":"u","votes":1}"#)?;
            proposals.put("other-tag", Data::tagged_string(r#"{"id":"o","votes":1}"#, *b"xx"))?;
            proposals.put("invalid", "{not json")?;
            proposals.put("wrong-shape", r#"{"id":1}"#)?;
            proposals.put("number", 5u64)?;
            Ok(())
        });
        let moment = latest(&db);
        assert_eq!(PROPOSALS.get(&moment, "untagged").unwrap(), Some(Proposal { id: "u".into(), votes: 1 }));

        let err = decode_error(PROPOSALS.get(&moment, "other-tag"));
        assert_eq!(err.key.as_deref(), Some("\"other-tag\""));
        assert_eq!(err.message, "expected format tag \"js\" or none, found \"xx\"");
        let err = decode_error(PROPOSALS.get(&moment, "invalid"));
        assert!(err.message.starts_with("invalid json"), "{}", err.message);
        let err = decode_error(PROPOSALS.get(&moment, "wrong-shape"));
        assert!(err.message.starts_with("invalid json"), "{}", err.message);
        let err = decode_error(PROPOSALS.get(&moment, "number"));
        assert_eq!(err.message, "expected json bytes, found Uint");

        // every bad entry is an error, not dropped
        let results: Vec<_> = PROPOSALS.iter(&moment).unwrap().collect();
        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
        assert_eq!(results.len(), 5);
    }

    #[test]
    fn json_serialize_errors_are_io_errors() {
        type ByPair = std::collections::HashMap<(u8, u8), u8>;
        const BY_PAIR: Map<str, Json<ByPair>> = Map::new("by-pair");
        let db = new_db();
        let result = History::new(&db)
            .unwrap()
            .transact(|moment| BY_PAIR.put(moment, "a", &[((1, 2), 3)].into_iter().collect()));
        assert!(matches!(result, Err(Error::Io(_))));
    }
}
