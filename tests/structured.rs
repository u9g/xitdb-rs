//! Tests for `Structured`, `put_structured` and friends: serde types stored
//! as nested maps, lists and scalars, written with only what changed.

#![cfg(feature = "serde")]

use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use xitdb::*;

fn new_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
}

// the length of the file, which grows with every write in a transaction
fn len(db: &Database<CoreMemory>) -> u64 {
    db.core().length().unwrap()
}

/// Puts `value` under "value", reads it back, and checks that putting it
/// again writes nothing.
fn round_trip<T: Serialize + DeserializeOwned + Debug>(value: &T) -> T {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let wrote = history.transact(|moment| put_structured(moment, "value", value)).unwrap();
    assert!(wrote, "{value:?}");
    let (wrote, committed) =
        history.transact_with_status(|moment| put_structured(moment, "value", value)).unwrap();
    assert!(!wrote && !committed, "putting {value:?} again wrote something");
    get_structured(&history.latest().unwrap(), "value").unwrap().unwrap()
}

fn assert_round_trip<T: Serialize + DeserializeOwned + Debug + PartialEq>(value: T) {
    assert_eq!(round_trip(&value), value);
}

/// Bytes serialized with `serialize_bytes`, as `serde_bytes` does.
#[derive(Debug, PartialEq, Clone)]
struct ByteBuf(Vec<u8>);

impl Serialize for ByteBuf {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.0)
    }
}

impl<'de> Deserialize<'de> for ByteBuf {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct Visitor;
        impl serde::de::Visitor<'_> for Visitor {
            type Value = ByteBuf;
            fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.write_str("bytes")
            }
            fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<ByteBuf, E> {
                Ok(ByteBuf(v))
            }
            fn visit_bytes<E>(self, v: &[u8]) -> Result<ByteBuf, E> {
                Ok(ByteBuf(v.to_vec()))
            }
            fn visit_str<E>(self, v: &str) -> Result<ByteBuf, E> {
                Ok(ByteBuf(v.as_bytes().to_vec()))
            }
        }
        deserializer.deserialize_byte_buf(Visitor)
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
enum State {
    Pending,
    Passed,
    Failed { reason: String, retries: u32 },
    Skipped(String),
    Moved(u32, String),
    Maybe(Option<u32>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct Check {
    name: String,
    state: State,
    #[serde(skip_serializing_if = "Option::is_none", default)]
    url: Option<String>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct Comment {
    author: String,
    body: String,
    reactions: BTreeMap<String, u64>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct PullRequest {
    number: u64,
    title: String,
    draft: bool,
    checks: Vec<Check>,
    comments: Vec<Comment>,
    labels: Vec<String>,
    merged_at: Option<i64>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct Cluster {
    id: String,
    pull_requests: Vec<PullRequest>,
    proposals: HashMap<String, Vec<String>>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
struct View {
    clusters: Vec<Cluster>,
    generated_at: i64,
}

fn text(seed: usize, len: usize) -> String {
    let words = ["fix", "the", "flaky", "build", "of", "gem", "and", "xitdb", "replication", "überprüfen"];
    let mut out = String::new();
    let mut i = seed;
    while out.len() < len {
        out.push_str(words[i % words.len()]);
        out.push(' ');
        i = i.wrapping_mul(31).wrapping_add(7);
    }
    out
}

/// A view like gem's, about `clusters` * 12 KB as JSON.
fn view(clusters: usize) -> View {
    View {
        generated_at: 1_700_000_000,
        clusters: (0..clusters)
            .map(|c| Cluster {
                id: format!("cluster-{c}"),
                proposals: (0..3).map(|p| (format!("proposal-{p}"), vec![text(c + p, 40), text(c * p, 20)])).collect(),
                pull_requests: (0..4)
                    .map(|p| PullRequest {
                        number: (c * 10 + p) as u64,
                        title: text(c * 7 + p, 60),
                        draft: p % 3 == 0,
                        checks: (0..8)
                            .map(|k| Check {
                                name: format!("check-{k}"),
                                state: if k % 4 == 0 { State::Pending } else { State::Passed },
                                url: (k % 2 == 0).then(|| format!("https://ci.example.com/{c}/{p}/{k}")),
                            })
                            .collect(),
                        comments: (0..4)
                            .map(|k| Comment {
                                author: format!("user-{}", (c + k) % 9),
                                body: text(c + p + k, 300),
                                reactions: [("+1".to_string(), k as u64), ("heart".to_string(), 1)].into(),
                            })
                            .collect(),
                        labels: vec!["review".into(), format!("area-{}", p)],
                        merged_at: (p == 3).then_some(1_700_000_123),
                    })
                    .collect(),
            })
            .collect(),
    }
}

#[test]
fn nested_structs_maps_and_lists_round_trip() {
    assert_round_trip(view(3));
    let mut map = HashMap::new();
    map.insert("a".to_string(), vec![vec![1u8, 2], vec![]]);
    map.insert("".to_string(), vec![]);
    assert_round_trip(map);
    assert_round_trip(BTreeMap::from([(1u64, "one".to_string()), (u64::MAX, "max".to_string())]));
    assert_round_trip(BTreeMap::from([(-5i32, true), (7, false)]));
    assert_round_trip(BTreeMap::from([('x', 1u8)]));
    assert_round_trip(BTreeMap::from([(true, 1u8), (false, 0)]));
    assert_round_trip(BTreeMap::from([(State::Pending, 1u8)].map(|(k, v)| (format!("{k:?}"), v))));
    assert_round_trip((1u8, "two".to_string(), [3i16, -4]));
    assert_round_trip(Vec::<String>::new());
    assert_round_trip(HashMap::<String, u64>::new());
}

#[test]
fn options_round_trip() {
    assert_round_trip(Some(5u32));
    assert_round_trip(vec![Some(1u32), None, Some(3)]);
    assert_round_trip(vec![None::<String>, None]);
    assert_round_trip(Some(vec![Some("a".to_string())]));
    assert_round_trip(Check { name: "build".into(), state: State::Passed, url: None });

    #[derive(Serialize, Deserialize, Debug, PartialEq)]
    struct Optional {
        a: Option<u64>,
        b: Option<Vec<Option<bool>>>,
    }
    assert_round_trip(Optional { a: None, b: Some(vec![None, Some(true), Some(false)]) });
    assert_round_trip(Optional { a: Some(0), b: None });
}

#[test]
fn enums_round_trip() {
    for state in [
        State::Pending,
        State::Failed { reason: "timeout".into(), retries: 2 },
        State::Skipped("not needed".into()),
        State::Moved(3, "elsewhere".into()),
        State::Maybe(None),
        State::Maybe(Some(4)),
    ] {
        assert_round_trip(state.clone());
        assert_round_trip(vec![state.clone(), State::Passed]);
        assert_round_trip(Some(state));
    }
}

#[test]
fn numbers_at_the_edges_round_trip() {
    assert_round_trip(u64::MAX);
    assert_round_trip(i64::MIN);
    assert_round_trip(i64::MAX);
    assert_round_trip(0u64);
    assert_round_trip((u8::MAX, i8::MIN, u16::MAX, i16::MIN, u32::MAX, i32::MIN));
    assert_round_trip((i128::from(i64::MIN), u128::from(u64::MAX)));
    assert_round_trip(f64::MAX);
    assert_round_trip(f64::MIN_POSITIVE);
    assert_round_trip(f64::INFINITY);
    assert_round_trip(1.5f32);
    assert_round_trip(true);
    assert_round_trip('é');

    // -0.0 and NaN, compared by their bits
    assert_eq!(round_trip(&-0.0f64).to_bits(), (-0.0f64).to_bits());
    let nan = f64::from_bits(0x7ff8_0000_0000_1234);
    assert_eq!(round_trip(&nan).to_bits(), nan.to_bits());

    // -0.0 is a change from 0.0
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| put_structured(moment, "x", &0.0f64)).unwrap();
    let (wrote, committed) = history.transact_with_status(|moment| put_structured(moment, "x", &-0.0f64)).unwrap();
    assert!(wrote && committed);

    // 128-bit integers that don't fit are an error
    let err = history.transact(|moment| put_structured(moment, "x", &u128::MAX)).unwrap_err();
    assert!(matches!(err, Error::Io(_)), "{err:?}");
}

#[test]
fn bytes_and_unicode_round_trip() {
    assert_round_trip(ByteBuf(vec![0, 1, 2, 255]));
    assert_round_trip(ByteBuf(vec![]));
    assert_round_trip(ByteBuf((0..=255).collect()));
    assert_round_trip("héllo wörld, 日本語, 🦀".to_string());
    assert_round_trip(String::new());
    assert_round_trip("x".repeat(10_000));
    assert_round_trip(BTreeMap::from([("ключ".to_string(), "значение".to_string()), ("🔑".into(), "🦀".into())]));
}

#[test]
fn stored_shape_is_plain() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let pr = PullRequest {
        number: 7,
        title: "Add structured values".into(),
        draft: true,
        checks: vec![
            Check { name: "build".into(), state: State::Passed, url: Some("https://ci/1".into()) },
            Check { name: "lint".into(), state: State::Failed { reason: "fmt".into(), retries: 1 }, url: None },
            Check { name: "doc".into(), state: State::Skipped("no docs".into()), url: None },
        ],
        comments: vec![],
        labels: vec!["a".into()],
        merged_at: None,
    };
    history.transact(|moment| put_structured(moment, "pr", &pr)).unwrap();
    history.transact(|moment| put_structured(moment, "nested", &vec![Some(1i64), None, Some(-3)])).unwrap();

    let moment = history.latest().unwrap();
    let stored = moment.get_map("pr").unwrap().unwrap();
    assert_eq!(stored.get_uint("number").unwrap(), Some(7));
    assert_eq!(stored.get_string("title", None).unwrap().as_deref(), Some("Add structured values"));
    assert_eq!(stored.get_uint("draft").unwrap(), Some(1));
    // None is a missing key
    assert!(stored.get_cursor("merged_at").unwrap().is_none());
    assert_eq!(stored.get_list("comments").unwrap().unwrap().count().unwrap(), 0);

    let checks = stored.get_list("checks").unwrap().unwrap();
    assert_eq!(checks.count().unwrap(), 3);
    let build = ReadHashMap::new(checks.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(build.get_string("name", None).unwrap().as_deref(), Some("build"));
    // a unit variant is its name
    assert_eq!(build.get_string("state", None).unwrap().as_deref(), Some("Passed"));
    assert_eq!(build.get_string("url", None).unwrap().as_deref(), Some("https://ci/1"));
    // a struct variant is a map from its name to a map of its fields
    let lint = ReadHashMap::new(checks.get_cursor(1).unwrap().unwrap()).unwrap();
    assert!(lint.get_cursor("url").unwrap().is_none());
    let failed = lint.get_map("state").unwrap().unwrap().get_map("Failed").unwrap().unwrap();
    assert_eq!(failed.get_string("reason", None).unwrap().as_deref(), Some("fmt"));
    assert_eq!(failed.get_uint("retries").unwrap(), Some(1));
    // a newtype variant is a map from its name to its value
    let doc = ReadHashMap::new(checks.get_cursor(2).unwrap().unwrap()).unwrap();
    let skipped = doc.get_map("state").unwrap().unwrap();
    assert_eq!(skipped.get_string("Skipped", None).unwrap().as_deref(), Some("no docs"));

    // None in a list is an empty slot; signed integers are Ints
    let nested = moment.get_list("nested").unwrap().unwrap();
    assert_eq!(nested.get_cursor(0).unwrap().unwrap().read_int().unwrap(), 1);
    assert_eq!(nested.get_slot(1).unwrap().unwrap().tag, Tag::None);
    assert_eq!(nested.get_cursor(2).unwrap().unwrap().read_int().unwrap(), -3);

    // integer map keys are their text, like JSON
    history.transact(|moment| put_structured(moment, "ids", &BTreeMap::from([(42u64, "x".to_string())]))).unwrap();
    let ids = history.latest().unwrap().get_map("ids").unwrap().unwrap();
    assert_eq!(ids.get_string("42", None).unwrap().as_deref(), Some("x"));

    // and data written by hand reads as the type
    history
        .transact(|moment| {
            let mut check = moment.put_map("hand")?;
            check.put("name", "by hand")?;
            check.put("state", "Pending")?;
            check.put("extra", "ignored")?;
            Ok::<_, Error>(())
        })
        .unwrap();
    let check: Check = get_structured(&history.latest().unwrap(), "hand").unwrap().unwrap();
    assert_eq!(check, Check { name: "by hand".into(), state: State::Pending, url: None });
}

#[test]
fn an_identical_value_writes_nothing_at_any_depth() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let view = view(5);
    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    let count = history.count().unwrap();

    // view.clusters[i].pull_requests[j].checks[k].state is 7 levels deep
    let copy = view.clone();
    let (wrote, committed) = history
        .transact_with_status(|moment| {
            let before = len(&db);
            let wrote = put_structured(moment, "view", &copy)?;
            assert_eq!(len(&db), before, "an identical value wrote something");
            Ok::<_, Error>(wrote)
        })
        .unwrap();
    assert!(!wrote && !committed);
    assert_eq!(history.count().unwrap(), count);

    // the same through a typed map
    const VIEWS: Map<str, Structured<View>> = Map::new("views");
    history.transact(|moment| VIEWS.put(moment, "main", &view)).unwrap();
    assert_eq!(VIEWS.get(&history.latest().unwrap(), "main").unwrap().as_ref(), Some(&view));
    let before = db.committed_size().unwrap();
    history.transact(|moment| VIEWS.put(moment, "main", &view)).unwrap();
    // Map::put opens the collection and the key, so it copies the path, but
    // nothing of the value
    assert!(db.committed_size().unwrap() - before < 2048);
}

#[test]
fn changing_one_leaf_appends_little() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let mut view = view(50);
    let json_size = serde_json::to_vec(&view).unwrap().len();
    assert!(json_size > 400_000, "the view is {json_size} bytes of JSON");

    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    let stored_size = db.committed_size().unwrap();

    // one check flipping state, 7 levels deep
    assert_eq!(view.clusters[20].pull_requests[2].checks[4].state, State::Pending);
    view.clusters[20].pull_requests[2].checks[4].state = State::Passed;
    let before = db.committed_size().unwrap();
    let (wrote, committed) = history.transact_with_status(|moment| put_structured(moment, "view", &view)).unwrap();
    assert!(wrote && committed);
    let delta = db.committed_size().unwrap() - before;
    println!("json {json_size} bytes, stored {stored_size} bytes, one-leaf delta {delta} bytes");
    assert!(delta < 2048, "changing one leaf appended {delta} bytes");

    // a string leaf
    view.clusters[3].pull_requests[1].checks[2].name = "renamed".into();
    let before = db.committed_size().unwrap();
    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    let delta = db.committed_size().unwrap() - before;
    assert!(delta < 2048, "changing one leaf appended {delta} bytes");

    // a leaf that becomes a struct variant: two new maps
    view.clusters[40].pull_requests[0].checks[1].state = State::Failed { reason: "flaky".into(), retries: 1 };
    let before = db.committed_size().unwrap();
    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    let delta = db.committed_size().unwrap() - before;
    println!("unit to struct variant delta {delta} bytes");
    assert!(delta < 4096, "changing one leaf appended {delta} bytes");
    assert_eq!(get_structured::<_, View>(&history.latest().unwrap(), "view").unwrap(), Some(view.clone()));

    // the same change to the view as one JSON blob rewrites all of it
    const JSON: Map<str, Json<View>> = Map::new("json");
    history.transact(|moment| JSON.put(moment, "view", &view)).unwrap();
    view.clusters[3].pull_requests[1].checks[2].name = "renamed again".into();
    let before = db.committed_size().unwrap();
    history.transact(|moment| JSON.put(moment, "view", &view)).unwrap();
    assert!(db.committed_size().unwrap() - before > json_size as i64);
}

#[test]
fn removed_keys_are_removed() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let mut map = BTreeMap::from([("a".to_string(), 1u64), ("b".into(), 2), ("c".into(), 3)]);
    history.transact(|moment| put_structured(moment, "map", &map)).unwrap();
    map.remove("b");
    map.insert("d".into(), 4);
    history.transact(|moment| put_structured(moment, "map", &map)).unwrap();
    let moment = history.latest().unwrap();
    let stored = moment.get_map("map").unwrap().unwrap();
    assert!(stored.get_cursor("b").unwrap().is_none());
    assert_eq!(stored.get_uint("d").unwrap(), Some(4));
    assert_eq!(stored.iter().unwrap().count(), 3);
    assert_eq!(get_structured(&moment, "map").unwrap(), Some(map));

    // a field set to None is removed
    let mut check = Check { name: "build".into(), state: State::Pending, url: Some("https://ci".into()) };
    history.transact(|moment| put_structured(moment, "check", &check)).unwrap();
    check.url = None;
    history.transact(|moment| put_structured(moment, "check", &check)).unwrap();
    let stored = history.latest().unwrap().get_map("check").unwrap().unwrap();
    assert!(stored.get_cursor("url").unwrap().is_none());

    // changing a variant removes the old one
    check.state = State::Failed { reason: "x".into(), retries: 0 };
    history.transact(|moment| put_structured(moment, "check", &check)).unwrap();
    check.state = State::Skipped("y".into());
    history.transact(|moment| put_structured(moment, "check", &check)).unwrap();
    let state = history.latest().unwrap().get_map("check").unwrap().unwrap().get_map("state").unwrap().unwrap();
    assert!(state.get_cursor("Failed").unwrap().is_none());
    assert_eq!(state.iter().unwrap().count(), 1);
    assert_eq!(get_structured(&history.latest().unwrap(), "check").unwrap(), Some(check.clone()));

    // a value that's None removes its key
    let (wrote, _) = history.transact_with_status(|moment| put_structured(moment, "check", &None::<Check>)).unwrap();
    assert!(wrote);
    assert!(history.latest().unwrap().get_cursor("check").unwrap().is_none());
    let (wrote, committed) =
        history.transact_with_status(|moment| put_structured(moment, "check", &None::<Check>)).unwrap();
    assert!(!wrote && !committed);
}

#[test]
fn lists_shrink_and_grow() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let mut list: Vec<String> = (0..100).map(|i| text(i, 200)).collect();
    history.transact(|moment| put_structured(moment, "list", &list)).unwrap();

    list.truncate(40);
    history.transact(|moment| put_structured(moment, "list", &list)).unwrap();
    let stored = history.latest().unwrap().get_list("list").unwrap().unwrap();
    assert_eq!(stored.count().unwrap(), 40);
    assert_eq!(get_structured(&history.latest().unwrap(), "list").unwrap(), Some(list.clone()));

    // appending writes the new items, not the old ones
    list.push("new".into());
    list.push("newer".into());
    let before = db.committed_size().unwrap();
    history.transact(|moment| put_structured(moment, "list", &list)).unwrap();
    assert!(db.committed_size().unwrap() - before < 2048);
    assert_eq!(get_structured(&history.latest().unwrap(), "list").unwrap(), Some(list.clone()));

    list.clear();
    history.transact(|moment| put_structured(moment, "list", &list)).unwrap();
    assert_eq!(history.latest().unwrap().get_list("list").unwrap().unwrap().count().unwrap(), 0);
    assert_eq!(get_structured(&history.latest().unwrap(), "list").unwrap(), Some(list));

    // lists of options, and lists in lists
    let mut nested = vec![vec![Some(1u64), None], vec![], vec![None]];
    history.transact(|moment| put_structured(moment, "nested", &nested)).unwrap();
    nested[0].push(Some(3));
    nested[1].push(None);
    nested[2].clear();
    nested.push(vec![Some(4)]);
    history.transact(|moment| put_structured(moment, "nested", &nested)).unwrap();
    assert_eq!(get_structured(&history.latest().unwrap(), "nested").unwrap(), Some(nested.clone()));
    nested.truncate(1);
    nested[0][2] = None;
    history.transact(|moment| put_structured(moment, "nested", &nested)).unwrap();
    assert_eq!(get_structured(&history.latest().unwrap(), "nested").unwrap(), Some(nested));
}

#[test]
fn other_kinds_are_replaced() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("value", "a string")).unwrap();
    let check = Check { name: "build".into(), state: State::Passed, url: None };
    history.transact(|moment| put_structured(moment, "value", &check)).unwrap();
    assert_eq!(get_structured(&history.latest().unwrap(), "value").unwrap(), Some(check));
    history.transact(|moment| put_structured(moment, "value", &vec![1u64, 2])).unwrap();
    assert_eq!(get_structured(&history.latest().unwrap(), "value").unwrap(), Some(vec![1u64, 2]));
    history.transact(|moment| put_structured(moment, "value", &5u64)).unwrap();
    assert_eq!(get_structured(&history.latest().unwrap(), "value").unwrap(), Some(5u64));
    history.transact(|moment| put_structured(moment, "value", &vec![vec![1u64]])).unwrap();
    history.transact(|moment| put_structured(moment, "value", &vec![BTreeMap::from([("k", 1u64)])])).unwrap();
    assert_eq!(
        get_structured(&history.latest().unwrap(), "value").unwrap(),
        Some(vec![BTreeMap::from([("k".to_string(), 1u64)])])
    );
}

#[test]
fn writing_twice_in_one_transaction() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let mut view = view(2);
    history
        .transact(|moment| {
            put_structured(moment, "view", &view)?;
            view.clusters[1].pull_requests.pop();
            view.clusters[0].id = "renamed".into();
            put_structured(moment, "view", &view)
        })
        .unwrap();
    assert_eq!(get_structured(&history.latest().unwrap(), "view").unwrap(), Some(view));
}

#[test]
fn write_at_a_cursor() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let value = BTreeMap::from([("a".to_string(), vec![1i64, 2]), ("b".into(), vec![])]);
    history
        .transact(|moment| {
            let mut list = moment.put_list("list")?;
            let mut cursor = list.append_cursor()?;
            assert!(write_structured(&mut cursor, &value)?);
            // the cursor sees what was written
            assert_eq!(read_structured::<_, BTreeMap<String, Vec<i64>>>(&cursor)?, value);
            assert!(!write_structured(&mut cursor, &value)?);
            Ok::<_, Error>(())
        })
        .unwrap();
    let list = history.latest().unwrap().get_list("list").unwrap().unwrap();
    let read: BTreeMap<String, Vec<i64>> = read_structured(&list.get_cursor(0).unwrap().unwrap()).unwrap();
    assert_eq!(read, value);
}

#[test]
fn errors() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let view = view(1);
    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    history
        .transact(|moment| {
            let mut prs = moment.put_map("view")?.put_list("clusters")?.put_map(0)?.put_list("pull_requests")?;
            prs.put_map(1)?.put("number", "seven")
        })
        .unwrap();
    let err = get_structured::<_, View>(&history.latest().unwrap(), "view").unwrap_err();
    let Error::Decode(decode) = &err else { panic!("{err:?}") };
    assert_eq!(decode.field.as_deref(), Some("clusters.0.pull_requests.1.number"));

    const VIEWS: Map<str, Structured<View>> = Map::new("views");
    history.transact(|moment| VIEWS.collection_mut(moment)?.put("main", 5u64)).unwrap();
    let err = VIEWS.get(&history.latest().unwrap(), "main").unwrap_err();
    let Error::Decode(decode) = &err else { panic!("{err:?}") };
    assert_eq!(decode.collection.as_deref(), Some("views"));

    // keys that aren't text are an error
    let err = history.transact(|moment| put_structured(moment, "x", &HashMap::from([((1, 2), 3)]))).unwrap_err();
    assert!(matches!(err, Error::Io(_)), "{err:?}");
    assert!(err.to_string().contains("map key"), "{err}");
}

#[test]
fn a_change_writes_what_writing_its_path_by_hand_does() {
    let mut view = view(10);
    let by_hand = {
        let db = new_db();
        let history = History::new(&db).unwrap();
        history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
        let before = db.committed_size().unwrap();
        history
            .transact(|moment| {
                let mut clusters = moment.put_map("view")?.put_list("clusters")?;
                let mut prs = clusters.put_map(7)?.put_list("pull_requests")?;
                prs.put_map(2)?.put_list("checks")?.put_map(4)?.put("state", "Passed")
            })
            .unwrap();
        db.committed_size().unwrap() - before
    };

    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    view.clusters[7].pull_requests[2].checks[4].state = State::Passed;
    let before = db.committed_size().unwrap();
    history.transact(|moment| put_structured(moment, "view", &view)).unwrap();
    assert_eq!(db.committed_size().unwrap() - before, by_hand);
}
