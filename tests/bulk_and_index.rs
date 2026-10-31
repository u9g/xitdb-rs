//! Tests for the bulk operations on typed collections (`retain`,
//! `remove_all`, `update_where` and the `_where` reads) and for secondary
//! indexes (`Index` and `IndexedMap`).

use xitdb::*;

const NAMES: Map<str, String> = Map::new("names");
const SCORES: Map<u64, u64> = Map::new("scores");
const STARTED: Set<str> = Set::new("started");

/// A merge, stored as a nested hash map with a `status` and an optional
/// `thread-id`.
#[derive(Debug, Clone, PartialEq)]
struct Merge {
    status: String,
    thread_id: Option<String>,
}

fn merge(status: &str, thread_id: Option<&str>) -> Merge {
    Merge { status: status.to_string(), thread_id: thread_id.map(str::to_string) }
}

impl ValueCodec for Merge {
    type Owned = Merge;
    type Borrowed = Merge;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Merge> {
        let map = ReadHashMap::new(cursor)?;
        let status = map.get_string("status", Some(1024))?.ok_or_else(|| Error::decode("missing status"))?;
        Ok(Merge { status, thread_id: map.get_string("thread-id", Some(1024))? })
    }

    fn write<C: Core>(value: &Merge, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        let mut map = WriteHashMap::new(cursor)?;
        map.put("status", value.status.as_str())?;
        match &value.thread_id {
            Some(thread_id) => map.put("thread-id", thread_id.as_str())?,
            None => {
                map.remove("thread-id")?;
            }
        }
        Ok(())
    }
}

const MERGES: Map<str, Merge> = Map::new("merges");
const BY_THREAD: Index<str, Merge, str> = Index::new(MERGES, "merges-by-thread", |merge| merge.thread_id.clone());
const BY_STATUS: Index<str, Merge, str> = Index::new(MERGES, "merges-by-status", |merge| Some(merge.status.clone()));
const INDEXED_MERGES: IndexedMap<str, Merge> = IndexedMap::new(MERGES, &[&BY_THREAD, &BY_STATUS]);

// names, indexed by their first letter
const BY_INITIAL: Index<str, String, str> =
    Index::new(NAMES, "names-by-initial", |name| name.get(..1).map(str::to_owned));
const INDEXED_NAMES: IndexedMap<str, String> = IndexedMap::new(NAMES, &[&BY_INITIAL]);

fn new_db() -> Database<CoreMemory> {
    Database::in_memory().unwrap()
}

/// Runs `f` in a transaction, returning what it returns and whether it
/// committed.
fn transact<T>(
    history: &History<'_, CoreMemory>,
    f: impl for<'t> FnOnce(&mut WriteHashMap<'t, CoreMemory>) -> Result<T>,
) -> (T, bool) {
    history.transact_with_status(f).unwrap()
}

fn sorted<T: Ord>(mut items: Vec<T>) -> Vec<T> {
    items.sort();
    items
}

fn put_names(history: &History<'_, CoreMemory>) {
    history
        .transact(|moment| {
            NAMES.put(moment, "a", "alice")?;
            NAMES.put(moment, "b", "bob")?;
            NAMES.put(moment, "c", "carol")?;
            NAMES.put(moment, "d", "dave")
        })
        .unwrap();
}

fn names(history: &History<'_, CoreMemory>) -> Vec<(String, String)> {
    sorted(NAMES.iter(&history.latest().unwrap()).unwrap().collect::<Result<_>>().unwrap())
}

fn pairs(pairs: &[(&str, &str)]) -> Vec<(String, String)> {
    pairs.iter().map(|(key, value)| (key.to_string(), value.to_string())).collect()
}

// Bulk operations

#[test]
fn keys_and_entries_where() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    let moment = history.latest().unwrap();
    assert!(NAMES.keys_where(&moment, |_, _| true).unwrap().is_empty());

    put_names(&history);
    let moment = history.latest().unwrap();
    let keys = NAMES.keys_where(&moment, |_, name| name.len() > 3).unwrap();
    assert_eq!(sorted(keys), ["a", "c", "d"]);
    let entries = NAMES.entries_where(&moment, |key, _| key.as_str() < "c").unwrap();
    assert_eq!(sorted(entries), pairs(&[("a", "alice"), ("b", "bob")]));
}

#[test]
fn map_retain() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_names(&history);

    let (removed, committed) = transact(&history, |moment| NAMES.retain(moment, |_, name| name.starts_with('a')));
    assert_eq!((removed, committed), (3, true));
    assert_eq!(names(&history), pairs(&[("a", "alice")]));

    // keeping everything writes nothing
    let count = history.count().unwrap();
    let (removed, committed) = transact(&history, |moment| NAMES.retain(moment, |_, _| true));
    assert_eq!((removed, committed), (0, false));
    assert_eq!(history.count().unwrap(), count);

    // and removing everything leaves an empty collection
    let (removed, _) = transact(&history, |moment| NAMES.retain(moment, |_, _| false));
    assert_eq!(removed, 1);
    assert!(names(&history).is_empty());
}

#[test]
fn bulk_ops_on_a_missing_collection_write_nothing() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history.transact(|moment| moment.put("other", "value")).unwrap();

    let (counts, committed) = transact(&history, |moment| {
        Ok((
            NAMES.retain(moment, |_, _| false)?,
            NAMES.remove_all(moment, ["a", "b"])?,
            NAMES.update_where(moment, |_, _| true, |name| name.push('!'))?,
            STARTED.retain(moment, |_| false)?,
            STARTED.remove_all(moment, ["a"])?,
            INDEXED_MERGES.retain(moment, |_, _| false)?,
            INDEXED_MERGES.remove_all(moment, ["a"])?,
            INDEXED_MERGES.update_where(moment, |_, _| true, |merge| merge.status.push('!'))?,
        ))
    });
    assert_eq!(counts, (0, 0, 0, 0, 0, 0, 0, 0));
    assert!(!committed);

    let moment = history.latest().unwrap();
    for name in ["names", "started", "merges", "merges-by-thread", "merges-by-status"] {
        assert!(moment.get_cursor(name).unwrap().is_none(), "{name} was created");
    }
}

#[test]
fn map_remove_all() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_names(&history);

    // owned strings, a missing key, and a key given twice
    let keys = vec!["a".to_string(), "x".to_string(), "b".to_string(), "a".to_string()];
    let (removed, committed) = transact(&history, |moment| NAMES.remove_all(moment, keys));
    assert_eq!((removed, committed), (2, true));
    assert_eq!(names(&history), pairs(&[("c", "carol"), ("d", "dave")]));

    let (removed, committed) = transact(&history, |moment| NAMES.remove_all(moment, ["a", "x"]));
    assert_eq!((removed, committed), (0, false));

    // integer keys, by value
    history
        .transact(|moment| {
            SCORES.put(moment, &1, &10)?;
            SCORES.put(moment, &2, &20)
        })
        .unwrap();
    let (removed, _) = transact(&history, |moment| SCORES.remove_all(moment, [1, 3]));
    assert_eq!(removed, 1);
    assert_eq!(SCORES.keys_where(&history.latest().unwrap(), |_, _| true).unwrap(), [2]);
}

#[test]
fn map_update_where() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_names(&history);

    // String values: the closure gets a String, and it's written as a str
    let (changed, committed) = transact(&history, |moment| {
        NAMES.update_where(moment, |key, _| key != "d", |name| *name = name.to_uppercase())
    });
    assert_eq!((changed, committed), (3, true));
    assert_eq!(names(&history), pairs(&[("a", "ALICE"), ("b", "BOB"), ("c", "CAROL"), ("d", "dave")]));

    // a change that leaves the values as they were writes nothing
    let (changed, committed) =
        transact(&history, |moment| NAMES.update_where(moment, |_, _| true, |name| *name = name.to_uppercase()));
    assert_eq!((changed, committed), (1, true));
    let (changed, committed) =
        transact(&history, |moment| NAMES.update_where(moment, |_, _| true, |name| *name = name.to_uppercase()));
    assert_eq!((changed, committed), (0, false));

    // as does matching nothing
    let (changed, committed) =
        transact(&history, |moment| NAMES.update_where(moment, |_, _| false, |name| name.clear()));
    assert_eq!((changed, committed), (0, false));

    // integer values
    history.transact(|moment| SCORES.put(moment, &1, &10)).unwrap();
    let (changed, _) = transact(&history, |moment| SCORES.update_where(moment, |_, _| true, |score| *score += 1));
    assert_eq!(changed, 1);
    assert_eq!(SCORES.get(&history.latest().unwrap(), &1).unwrap(), Some(11));
}

#[test]
fn set_retain_and_remove_all() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            for key in ["a", "b", "c", "d"] {
                STARTED.insert(moment, key)?;
            }
            Ok::<_, Error>(())
        })
        .unwrap();
    let keys = |history: &History<'_, CoreMemory>| -> Vec<String> {
        sorted(STARTED.iter(&history.latest().unwrap()).unwrap().collect::<Result<_>>().unwrap())
    };

    let (removed, committed) = transact(&history, |moment| STARTED.retain(moment, |key| key != "a"));
    assert_eq!((removed, committed), (1, true));
    assert_eq!(keys(&history), ["b", "c", "d"]);

    let (removed, committed) = transact(&history, |moment| STARTED.retain(moment, |_| true));
    assert_eq!((removed, committed), (0, false));

    let (removed, committed) = transact(&history, |moment| STARTED.remove_all(moment, ["b", "x", "c"]));
    assert_eq!((removed, committed), (2, true));
    assert_eq!(keys(&history), ["d"]);

    let (removed, committed) = transact(&history, |moment| STARTED.remove_all(moment, ["b", "x"]));
    assert_eq!((removed, committed), (0, false));
}

#[test]
fn retain_with_an_undecodable_value_removes_nothing() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_names(&history);
    history.transact(|moment| moment.put_map("names")?.put("e", 5u64)).unwrap();

    let result = history.transact(|moment| NAMES.retain(moment, |_, _| false));
    assert!(matches!(result, Err(Error::Decode(_))));
    assert_eq!(History::new(&db).unwrap().count().unwrap(), 2);
}

#[cfg(feature = "serde")]
mod json {
    use serde::{Deserialize, Serialize};
    use xitdb::*;

    #[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
    struct Proposal {
        votes: u64,
        thread_id: Option<String>,
    }

    const PROPOSALS: Map<str, Json<Proposal>> = Map::new("proposals");
    const BY_THREAD: Index<str, Json<Proposal>, str> =
        Index::new(PROPOSALS, "proposals-by-thread", |proposal| proposal.thread_id.clone());
    const INDEXED: IndexedMap<str, Json<Proposal>> = IndexedMap::new(PROPOSALS, &[&BY_THREAD]);

    #[test]
    fn json_values() {
        let db = Database::in_memory().unwrap();
        let history = History::new(&db).unwrap();
        history
            .transact(|moment| {
                INDEXED.put(moment, "p1", &Proposal { votes: 1, thread_id: Some("t1".into()) })?;
                INDEXED.put(moment, "p2", &Proposal { votes: 5, thread_id: None })
            })
            .unwrap();

        let (changed, committed) = history
            .transact_with_status(|moment| {
                INDEXED.update_where(moment, |_, proposal| proposal.votes < 5, |proposal| {
                    proposal.votes += 1;
                    proposal.thread_id = Some("t2".into());
                })
            })
            .unwrap();
        assert_eq!((changed, committed), (1, true));

        let moment = history.latest().unwrap();
        assert_eq!(PROPOSALS.get(&moment, "p1").unwrap().unwrap().votes, 2);
        assert!(BY_THREAD.get(&moment, "t1").unwrap().is_empty());
        assert_eq!(BY_THREAD.get(&moment, "t2").unwrap(), ["p1"]);
        assert_eq!(PROPOSALS.keys_where(&moment, |_, proposal| proposal.votes == 5).unwrap(), ["p2"]);
    }
}

// Indexes

fn thread(history: &History<'_, CoreMemory>, thread_id: &str) -> Vec<String> {
    sorted(BY_THREAD.get(&history.latest().unwrap(), thread_id).unwrap())
}

fn status(history: &History<'_, CoreMemory>, status: &str) -> Vec<String> {
    sorted(BY_STATUS.get(&history.latest().unwrap(), status).unwrap())
}

fn put_merges(history: &History<'_, CoreMemory>) {
    history
        .transact(|moment| {
            INDEXED_MERGES.put(moment, "pr/1", &merge("open", Some("t1")))?;
            INDEXED_MERGES.put(moment, "pr/2", &merge("open", Some("t1")))?;
            INDEXED_MERGES.put(moment, "pr/3", &merge("merged", Some("t2")))?;
            INDEXED_MERGES.put(moment, "pr/4", &merge("open", None))
        })
        .unwrap();
}

#[test]
fn index_put_is_one_to_many_and_skips_none() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    assert!(thread(&history, "t1").is_empty());
    put_merges(&history);

    assert_eq!(thread(&history, "t1"), ["pr/1", "pr/2"]);
    assert_eq!(thread(&history, "t2"), ["pr/3"]);
    assert!(thread(&history, "t3").is_empty());
    assert_eq!(status(&history, "open"), ["pr/1", "pr/2", "pr/4"]);

    // pr/4 has no thread, so it isn't in that index, and the keys are distinct
    let moment = history.latest().unwrap();
    assert_eq!(sorted(BY_THREAD.keys(&moment).unwrap()), ["t1", "t2"]);
    assert_eq!(sorted(BY_STATUS.keys(&moment).unwrap()), ["merged", "open"]);

    let entries = BY_THREAD.entries(&moment, "t2").unwrap();
    assert_eq!(entries, [("pr/3".to_string(), merge("merged", Some("t2")))]);

    // the index is plain data: a map from index key to a set of primary keys
    let by_thread = moment.get_map("merges-by-thread").unwrap().unwrap();
    assert!(by_thread.get_set("t1").unwrap().unwrap().contains("pr/2").unwrap());
}

#[test]
fn index_follows_puts_and_removes() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_merges(&history);

    history
        .transact(|moment| {
            // a new thread, an unchanged one, and no thread
            INDEXED_MERGES.put(moment, "pr/1", &merge("open", Some("t2")))?;
            INDEXED_MERGES.put(moment, "pr/3", &merge("merged", Some("t2")))?;
            INDEXED_MERGES.put(moment, "pr/2", &merge("closed", None))?;
            // reads in the transaction see the index's writes
            assert_eq!(sorted(BY_THREAD.get(moment, "t2")?), ["pr/1", "pr/3"]);
            Ok::<_, Error>(())
        })
        .unwrap();
    assert!(thread(&history, "t1").is_empty());
    assert_eq!(thread(&history, "t2"), ["pr/1", "pr/3"]);
    assert_eq!(status(&history, "closed"), ["pr/2"]);
    assert_eq!(status(&history, "open"), ["pr/1", "pr/4"]);

    // an index key without entries is gone, not an empty set
    let moment = history.latest().unwrap();
    assert_eq!(BY_THREAD.keys(&moment).unwrap(), ["t2"]);
    assert!(moment.get_map("merges-by-thread").unwrap().unwrap().get_cursor("t1").unwrap().is_none());

    let (removed, committed) = transact(&history, |moment| {
        Ok((INDEXED_MERGES.remove(moment, "pr/1")?, INDEXED_MERGES.remove(moment, "pr/1")?))
    });
    assert_eq!((removed, committed), ((true, false), true));
    assert_eq!(thread(&history, "t2"), ["pr/3"]);
    assert_eq!(status(&history, "open"), ["pr/4"]);
    assert!(!INDEXED_MERGES.contains(&history.latest().unwrap(), "pr/1").unwrap());
}

#[test]
fn index_follows_bulk_ops() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_merges(&history);

    // merge every open merge in t1
    let (changed, committed) = transact(&history, |moment| {
        INDEXED_MERGES.update_where(
            moment,
            |_, merge| merge.thread_id.as_deref() == Some("t1"),
            |merge| merge.status = "merged".to_string(),
        )
    });
    assert_eq!((changed, committed), (2, true));
    assert_eq!(status(&history, "merged"), ["pr/1", "pr/2", "pr/3"]);
    assert_eq!(status(&history, "open"), ["pr/4"]);
    assert_eq!(thread(&history, "t1"), ["pr/1", "pr/2"]);

    let (removed, _) = transact(&history, |moment| INDEXED_MERGES.retain(moment, |key, _| key != "pr/3"));
    assert_eq!(removed, 1);
    assert!(thread(&history, "t2").is_empty());
    assert_eq!(status(&history, "merged"), ["pr/1", "pr/2"]);

    let (removed, _) = transact(&history, |moment| INDEXED_MERGES.remove_all(moment, ["pr/1", "pr/9"]));
    assert_eq!(removed, 1);
    assert_eq!(thread(&history, "t1"), ["pr/2"]);
    assert_eq!(status(&history, "merged"), ["pr/2"]);

    // what's left matches a rebuild
    assert!(!history.transact(|moment| INDEXED_MERGES.rebuild(moment)).unwrap());
}

#[test]
fn indexed_writes_that_change_nothing_dont_commit() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_merges(&history);
    let count = history.count().unwrap();

    let (results, committed) = transact(&history, |moment| {
        Ok((
            INDEXED_MERGES.remove(moment, "pr/9")?,
            INDEXED_MERGES.remove_all(moment, ["pr/8", "pr/9"])?,
            INDEXED_MERGES.retain(moment, |_, _| true)?,
            // matches, but leaves the value as it was
            INDEXED_MERGES.update_where(moment, |_, _| true, |merge| merge.status = merge.status.clone())?,
            INDEXED_MERGES.rebuild(moment)?,
        ))
    });
    assert_eq!(results, (false, 0, 0, 0, false));
    assert!(!committed);
    assert_eq!(history.count().unwrap(), count);
}

#[test]
fn index_with_string_values() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    history
        .transact(|moment| {
            INDEXED_NAMES.put(moment, "a", "alice")?;
            INDEXED_NAMES.put(moment, "b", "amy")?;
            // an empty name has no initial, so it isn't indexed
            INDEXED_NAMES.put(moment, "c", "")
        })
        .unwrap();
    let moment = history.latest().unwrap();
    assert_eq!(sorted(BY_INITIAL.get(&moment, "a").unwrap()), ["a", "b"]);
    assert_eq!(BY_INITIAL.keys(&moment).unwrap(), ["a"]);
    assert_eq!(INDEXED_NAMES.get(&moment, "c").unwrap().as_deref(), Some(""));

    history
        .transact(|moment| INDEXED_NAMES.update_where(moment, |key, _| key == "b", |name| *name = "bea".into()))
        .unwrap();
    let moment = history.latest().unwrap();
    assert_eq!(BY_INITIAL.get(&moment, "a").unwrap(), ["a"]);
    assert_eq!(BY_INITIAL.get(&moment, "b").unwrap(), ["b"]);
}

#[test]
fn rebuild_indexes_existing_data() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    // written before the index existed
    history
        .transact(|moment| {
            MERGES.put(moment, "pr/1", &merge("open", Some("t1")))?;
            MERGES.put(moment, "pr/2", &merge("open", Some("t1")))?;
            MERGES.put(moment, "pr/3", &merge("open", None))
        })
        .unwrap();
    assert!(thread(&history, "t1").is_empty());

    // rebuilding one index only creates that one
    let (changed, committed) = transact(&history, |moment| BY_THREAD.rebuild(moment));
    assert!(changed && committed);
    assert_eq!(thread(&history, "t1"), ["pr/1", "pr/2"]);
    assert!(history.latest().unwrap().get_cursor("merges-by-status").unwrap().is_none());

    let (changed, committed) = transact(&history, |moment| INDEXED_MERGES.rebuild(moment));
    assert!(changed && committed);
    assert_eq!(status(&history, "open"), ["pr/1", "pr/2", "pr/3"]);

    // an index that's up to date writes nothing
    let (changed, committed) = transact(&history, |moment| INDEXED_MERGES.rebuild(moment));
    assert!(!changed && !committed);

    // a missing map is an empty index, so rebuilding writes nothing either
    let (changed, committed) = transact(&history, |moment| INDEXED_NAMES.rebuild(moment));
    assert!(!changed && !committed);
}

#[test]
fn bypassing_the_index_leaves_it_stale_until_rebuilt() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_merges(&history);

    // writes through the plain map don't touch the index
    history
        .transact(|moment| {
            MERGES.put(moment, "pr/1", &merge("open", Some("t3")))?;
            MERGES.put(moment, "pr/5", &merge("open", Some("t3")))?;
            MERGES.remove(moment, "pr/3")?;
            Ok::<_, Error>(())
        })
        .unwrap();
    assert_eq!(thread(&history, "t1"), ["pr/1", "pr/2"]);
    assert_eq!(thread(&history, "t2"), ["pr/3"]);
    assert!(thread(&history, "t3").is_empty());
    // entries skips primary keys that are gone from the map
    assert!(BY_THREAD.entries(&history.latest().unwrap(), "t2").unwrap().is_empty());

    let (changed, committed) = transact(&history, |moment| INDEXED_MERGES.rebuild(moment));
    assert!(changed && committed);
    assert_eq!(thread(&history, "t1"), ["pr/2"]);
    assert!(thread(&history, "t2").is_empty());
    assert_eq!(thread(&history, "t3"), ["pr/1", "pr/5"]);
    assert_eq!(status(&history, "open"), ["pr/1", "pr/2", "pr/4", "pr/5"]);
    assert!(status(&history, "merged").is_empty());
    assert_eq!(sorted(BY_THREAD.keys(&history.latest().unwrap()).unwrap()), ["t1", "t3"]);
}

#[test]
#[should_panic(expected = "is of another map")]
fn an_index_of_another_map_panics() {
    const WRONG: IndexedMap<str, String> = IndexedMap::new(Map::new("other-names"), &[&BY_INITIAL]);
    let db = new_db();
    let history = History::new(&db).unwrap();
    let _ = history.transact(|moment| WRONG.put(moment, "a", "alice"));
}

#[test]
fn removing_every_entry_of_an_index_key_removes_its_set() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_merges(&history);

    // both entries of t1 in one call, so its set is emptied in one write
    let (removed, _) = transact(&history, |moment| INDEXED_MERGES.remove_all(moment, ["pr/1", "pr/2"]));
    assert_eq!(removed, 2);
    let moment = history.latest().unwrap();
    assert_eq!(BY_THREAD.keys(&moment).unwrap(), ["t2"]);
    assert!(moment.get_map("merges-by-thread").unwrap().unwrap().get_cursor("t1").unwrap().is_none());
    assert!(!history.transact(|moment| INDEXED_MERGES.rebuild(moment)).unwrap());
}

#[test]
fn empty_index_sets_read_as_missing_and_rebuild_removes_them() {
    let db = new_db();
    let history = History::new(&db).unwrap();
    put_merges(&history);
    // an empty set, as untyped code could leave one
    history
        .transact(|moment| {
            moment.put_map("merges-by-thread")?.put_set("t9")?;
            Ok::<_, Error>(())
        })
        .unwrap();

    let moment = history.latest().unwrap();
    assert!(BY_THREAD.get(&moment, "t9").unwrap().is_empty());
    assert_eq!(sorted(BY_THREAD.keys(&moment).unwrap()), ["t1", "t2"]);

    let (changed, committed) = transact(&history, |moment| BY_THREAD.rebuild(moment));
    assert!(changed && committed);
    let moment = history.latest().unwrap();
    assert!(moment.get_map("merges-by-thread").unwrap().unwrap().get_cursor("t9").unwrap().is_none());
    let (changed, committed) = transact(&history, |moment| BY_THREAD.rebuild(moment));
    assert!(!changed && !committed);
}

#[test]
#[should_panic(expected = "an index can't be stored under the name of the map it indexes")]
fn an_index_under_its_maps_name_panics() {
    let _ = Index::<str, Merge, str>::new(MERGES, "merges", |merge| merge.thread_id.clone());
}

#[test]
#[should_panic(expected = "two indexes of \"merges\" are stored under \"merges-by-thread\"")]
fn two_indexes_under_one_name_panic() {
    const BY_THREAD_AGAIN: Index<str, Merge, str> =
        Index::new(MERGES, "merges-by-thread", |merge| Some(merge.status.clone()));
    const WRONG: IndexedMap<str, Merge> = IndexedMap::new(MERGES, &[&BY_THREAD, &BY_THREAD_AGAIN]);
    let db = new_db();
    let history = History::new(&db).unwrap();
    let _ = history.transact(|moment| WRONG.put(moment, "pr/1", &merge("open", None)));
}
