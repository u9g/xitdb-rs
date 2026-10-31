<p align="center">
  xitdb is an immutable database written in Rust
  <br/>
  <br/>
  <b>Choose your flavor:</b>
  <a href="https://github.com/xit-vcs/xitdb">Zig</a> |
  <a href="https://github.com/xit-vcs/xitdb-java">Java</a> |
  <a href="https://github.com/codeboost/xitdb-clj">Clojure</a> |
  <a href="https://github.com/xit-vcs/xitdb-ts">TypeScript</a> |
  <a href="https://github.com/xit-vcs/xitdb-go">Go</a> |
  Rust
</p>

This is a Rust port of [xitdb](https://github.com/xit-vcs/xitdb). It reads and writes the same file format as the other implementations, so a database written by one can be read and extended by another.

* Each transaction efficiently creates a new "copy" of the database, and past copies can still be read from and reverted to.
* Supports storing in a single file as well as purely in-memory use.
* Runs as a library (embedded in process).
* Incrementally reads and writes, so file-based databases can contain larger-than-memory datasets.
* Reads never block writes, and a database can be read from multiple threads/processes without locks.
* No query engine of any kind. You just write data structures (primarily an `ArrayList` and `HashMap`) that can be nested arbitrarily.
* Dependencies: `getrandom` (for file and commit IDs) and, behind the default `sha1` feature, `sha1`. The optional `serde` feature adds `serde` and `serde_json`, and the optional `derive` feature adds `xitdb-derive`, the crate with `#[derive(Record)]`.

* [Example](#example)
* [Initializing a Database](#initializing-a-database)
* [Types](#types)
* [Cloning and Undoing](#cloning-and-undoing)
* [Sorting and Paginating](#sorting-and-paginating)
* [Large Byte Arrays](#large-byte-arrays)
* [Iterators](#iterators)
* [Accessors](#accessors)
* [Typed Collections](#typed-collections)
* [Records](#records)
* [Hashing](#hashing)
* [Compaction](#compaction)
* [Replication](#replication)
* [Thread Safety](#thread-safety)
* [Compatibility](#compatibility)

## Example

In this example, we create a new database, write some data in a transaction, and read the data afterwards.

```rust
use std::fs::OpenOptions;
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let path = std::env::temp_dir().join("xitdb-readme-example.db");
    let file = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(&path)?;

    // when writing from multiple processes, take an exclusive lock on a
    // separate lock file first (see "Initializing a Database")

    // init the db
    let db = Database::new(CoreBufferedFile::new(file), Hasher::sha1())?;

    // the top-level data structure is an ArrayList, so each transaction is
    // stored as an item in it, and past copies of the db stay readable
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;

    // this is how a transaction is executed. we call history.append_context,
    // providing it with the most recent copy of the db and a context
    // function. the function will run before the transaction has completed.
    // this is where we can write changes to the db. if any error happens
    // in it, the transaction will not complete and the db will be unaffected.
    //
    // after this transaction, the db will look like this if represented
    // as JSON (in reality the format is binary):
    //
    // {"foo": "foo",
    //  "bar": "bar",
    //  "fruits": ["apple", "pear", "grape"],
    //  "people": [
    //    {"name": "Alice", "age": 25},
    //    {"name": "Bob", "age": 42}
    //  ]}
    let last = history.get_slot(-1)?;
    history.append_context(last, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;

        moment.put("foo", "foo")?;
        moment.put("bar", "bar")?;

        let mut fruits = WriteArrayList::new(&mut moment.put_cursor("fruits")?)?;
        fruits.append("apple")?;
        fruits.append("pear")?;
        fruits.append("grape")?;

        let mut people = WriteArrayList::new(&mut moment.put_cursor("people")?)?;

        let mut alice = WriteHashMap::new(&mut people.append_cursor()?)?;
        alice.put("name", "Alice")?;
        alice.put("age", 25u64)?;

        let mut bob = WriteHashMap::new(&mut people.append_cursor()?)?;
        bob.put("name", "Bob")?;
        bob.put("age", 42u64)?;

        Ok(())
    })?;

    // get the most recent copy of the database, like a moment
    // in time. the -1 index will return the last index in the list.
    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

    // we can read the value of "foo" from the map by getting
    // the cursor to "foo" and then calling read_bytes on it
    let foo_value = moment.get_cursor("foo")?.unwrap().read_bytes(Some(1024))?;
    assert_eq!(foo_value, b"foo");

    // to get the "fruits" list, we get the cursor to it and
    // then pass it to the ArrayList constructor
    let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
    assert_eq!(fruits.count()?, 3);

    // now we can get the first item from the fruits list and read it
    let apple_value = fruits.get_cursor(0)?.unwrap().read_bytes(Some(1024))?;
    assert_eq!(apple_value, b"apple");

    Ok(())
}
```

Lookups that can miss, like `get_cursor`, return `Ok(None)` when the key or index doesn't exist.

## Initializing a Database

A `Database` is initialized with an implementation of the `Core` trait, which determines how the i/o is done. There are three implementations of `Core` in this library: `CoreBufferedFile`, `CoreFile`, and `CoreMemory`.

* `CoreBufferedFile` databases, like in the example above, write to a file while using an in-memory buffer to dramatically improve performance. This is highly recommended if you want to create a file-based database. Initialize with `CoreBufferedFile::new(file)`.
* `CoreFile` databases use no buffering when reading and writing data. Initialize with `CoreFile::new(file)`. This is almost never necessary but it's useful as a benchmark comparison with `CoreBufferedFile` databases.
* `CoreMemory` databases work completely in memory. Initialize with `CoreMemory::new()`.

The database owns its core. Get it back with `Database::into_core`, or borrow it with `Database::core`. `CoreBufferedFile` flushes its buffer when dropped; call `CoreBufferedFile::close` if you want to see errors from that flush.

With the default `sha1` feature, there are shortcuts that use `Hasher::sha1()`: `Database::open(path)` opens a `CoreBufferedFile` database for reading and writing, creating it if it doesn't exist; `Database::open_read_only(path)` opens an existing one for reading only, which is how another process reads a database while it's being written to (writes through it fail); and `Database::in_memory()` creates a `CoreMemory` database. For another hasher, pass `CoreBufferedFile::open(path)?` to `Database::new`.

None of these lock the file. Only one process may write at a time, so when writing from multiple processes, hold an exclusive lock on a separate lock file, such as `<path>.lock`, from before opening the database (which may initialize a new file) until you're done writing, for example with `File::lock` (Rust 1.89+). Don't lock the database file itself: on some platforms, such as Windows, file locks are mandatory, so that would block readers. Readers need no lock.

To choose the core at runtime, such as a file in production and memory in tests, use `Database<DynCore>`, where `DynCore` is a `Box<dyn Core + Send>`. `Database::into_dyn` boxes the core of any database. `Database::close` writes out the core's buffer and returns any error from it, even when the core is boxed; it calls `Core::finish`, which by default calls `Core::flush`.

```rust
use xitdb::*;

fn open_db(path: Option<&std::path::Path>) -> xitdb::Result<Database<DynCore>> {
    Ok(match path {
        Some(path) => Database::open(path)?.into_dyn(),
        None => Database::in_memory()?.into_dyn(),
    })
}

fn main() -> xitdb::Result<()> {
    let path = std::env::temp_dir().join("xitdb-readme-dyn-core.db");
    // start from a new file each time this example runs
    let _ = std::fs::remove_file(&path);
    for path in [Some(path.as_path()), None] {
        let db = open_db(path)?;
        let mut history = WriteArrayList::new(&mut db.root_cursor())?;
        history.append("hello")?;
        db.close()?;
    }

    // the file still has the data, and other processes can read it
    let db = Database::open_read_only(&path)?;
    let history = ReadArrayList::new(db.root_cursor())?;
    assert_eq!(history.get_cursor(-1)?.unwrap().read_bytes(Some(1024))?, b"hello");
    Ok(())
}
```

Since xitdb is an append-only database, the data you are writing is invisible to any reader until the very last step, when a small header at the start of the file is updated to point at it. This is how it supports transactions, despite not having any rollback journal or write-ahead log: if a transaction fails, the data it appended is simply discarded.

Usually, you want to use a top-level `ArrayList` like in the example above, because that allows you to store a reference to each copy of the database (which I call a "moment"), so past copies stay readable and can be reverted to. If you don't need to keep past copies, you can also use a top-level `HashMap`. Keep in mind that each write to a top-level `HashMap` is its own transaction, so if you make many writes, group them into one transaction with `Database::run_context`.

Since xitdb supports in-memory databases, you could use it as an over-the-wire serialization format. Much like "Cap'n Proto", xitdb has no encoding/decoding step: you just give the buffer to xitdb and it can immediately read from it (`CoreMemory::from_bytes`).

## History

`History` wraps a database whose root is a history of `HashMap` moments, like the example above, without the boilerplate. `History::transact` appends a copy of the latest moment, runs your function on it, and commits it. Whatever the function returns is returned. If it returns an error, which can be any type that `xitdb::Error` converts into, nothing is committed. If it leaves the moment unchanged, nothing is committed either, so the history only grows when the data changes:

```rust
use xitdb::*;

#[derive(Debug)]
enum AppError {
    Db(xitdb::Error),
    Overdrawn,
}

impl From<xitdb::Error> for AppError {
    fn from(err: xitdb::Error) -> Self {
        AppError::Db(err)
    }
}

fn main() -> Result<(), AppError> {
    let db = Database::in_memory()?;
    let history = History::new(&db)?;

    // a new database has no moments, and latest() is an empty map
    assert!(history.latest()?.get_cursor("balance")?.is_none());

    history.transact(|moment| moment.put("balance", 100u64))?;

    // transactions can return a value, and read their own writes
    let balance = history.transact(|moment| {
        let balance = moment.get_uint("balance")?.unwrap();
        moment.put("balance", balance - 30)?;
        Ok::<_, AppError>(moment.get_uint("balance")?.unwrap())
    })?;
    assert_eq!(balance, 70);

    // an error aborts the transaction
    let result = history.transact(|moment| {
        let balance = moment.get_uint("balance")?.unwrap();
        if balance < 500 {
            return Err(AppError::Overdrawn);
        }
        moment.put("balance", balance - 500)?;
        Ok(())
    });
    assert!(matches!(result, Err(AppError::Overdrawn)));

    // a transaction that changes nothing isn't committed
    let (_, committed) = history.transact_with_status(|moment| {
        Ok::<_, AppError>(moment.get_cursor("balance")?.is_some())
    })?;
    assert!(!committed);

    assert_eq!(history.count()?, 2);
    let first = history.moment(0)?.unwrap();
    assert_eq!(first.get_uint("balance")?.unwrap(), 100);
    Ok(())
}
```

The function can't return anything that borrows the moment, since an unchanged moment is discarded; read what you need into owned values. A moment counts as unchanged when its top-level index block ends up byte-for-byte the same as the previous moment's, which is cheap to check. That's always the case if the function made no writes, but a write usually counts as a change even when it stores the value that was already there, because writes copy what they write to.

### Writing only what changed

To refresh values that rarely change, such as state polled on a timer, write them with `put_if_changed`. It compares first and writes nothing at all if the value is the same, so the moment stays unchanged and isn't committed. For a value in nested maps, use `put_path_if_changed` with the keys leading to it: getting a nested map with `put_map` already copies the path to it, which counts as a change, so it reads along the path first and only writes along it if the value differs. Both return whether they wrote:

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::in_memory()?;
    let history = History::new(&db)?;
    let url = "https://example.com/pr/1";

    history.transact(|moment| {
        moment.put("status", "idle")?;
        moment.put_map("merges")?.put_map(url)?.put("question", 3u64)
    })?;

    // the same values: nothing is written, and nothing is committed
    let (wrote, committed) = history.transact_with_status(|moment| {
        let status = moment.put_if_changed("status", "idle")?;
        let question = moment.put_path_if_changed(&["merges", url, "question"], 3u64)?;
        Ok::<_, xitdb::Error>(status || question)
    })?;
    assert!(!wrote && !committed);
    assert_eq!(history.count()?, 1);

    // one changed value commits a moment
    let (wrote, committed) = history.transact_with_status(|moment| {
        let status = moment.put_if_changed("status", "idle")?;
        let question = moment.put_path_if_changed(&["merges", url, "question"], 4u64)?;
        Ok::<_, xitdb::Error>(status || question)
    })?;
    assert!(wrote && committed);
    assert_eq!(history.count()?, 2);
    Ok(())
}
```

Values compare exactly, as they would be stored: the type, value and format tag must match, so `Int` 1 isn't `Uint` 1, and floats compare by their bits. A missing key always counts as changed, even when writing `Data::None`, and `Data::None` and empty bytes are different values. A `Data::Slot` equals only the slot it writes, which is that slot, except that an empty one is written marked as written, like `Data::None`. Long byte arrays compare their length and format tag first, then their contents, which are read in chunks. `WriteArrayList`, `WriteLinkedArrayList` and `WriteSortedMap` have `put_if_changed` too, and `ReadCursor::equals` does the comparison without writing.

These are all built on `WriteCursor::write_path_if_changed`, which takes a path like `write_path` and works through any mix of collections, such as a list in a counted map, at any depth. On the root cursor outside a transaction, the comparison and the write run in one transaction of their own, which is discarded if the value is the same.

## Migrations

When the layout of the moment changes, such as a renamed key or a value with a new shape, existing data has to be converted. `Migrations` is an ordered list of `Migration`s, each a version, a name and a function or closure that changes the moment, and `History::migrate` brings the latest moment up to date: it reads the layout version recorded in the moment, runs each newer migration in order, and records the newest version, all in one transaction. If a migration returns an error, nothing is committed, so the data is never partly migrated. If there's nothing to run, nothing is committed either, so calling it on every start is cheap.

The version is stored as a `Uint` under the key `LAYOUT_VERSION_KEY` (`"xitdb/layout-version"`); `Migrations::with_key` picks another. A non-negative `Int` there, as another implementation might write, is read as the same version. A moment without it, such as on a new database, is at version 0, so the first `migrate` runs everything. `Migrations::new` returns `Error::MigrationOutOfOrder` unless the versions start above 0 and strictly increase; gaps are fine. The recorded version must be 0 or one of the migrations' versions, or `migrate` changes nothing and returns an error: `Error::LayoutTooNew` if it's newer than every migration, so an old binary doesn't run against data written by a newer one, and `Error::UnknownLayoutVersion` if it's between them, since then it was made by a migration this code doesn't have.

```rust
use xitdb::*;

// version 1 stored each proposal's status as a string
fn add_proposals<C: Core>(moment: &mut WriteHashMap<'_, C>) -> xitdb::Result<()> {
    moment.put_map("proposals")?.put("https://example.com/pr/1", "open")?;
    Ok(())
}

// version 2 renames "proposals" to "merges", and makes each value a map
fn proposals_to_merges<C: Core>(moment: &mut WriteHashMap<'_, C>) -> xitdb::Result<()> {
    let mut entries = Vec::new();
    if let Some(proposals) = moment.get_map("proposals")? {
        for kv in proposals.entries()? {
            let kv = kv?;
            entries.push((kv.key_cursor.read_string(Some(1024))?, kv.value_cursor.read_string(Some(1024))?));
        }
    }
    moment.remove("proposals")?;
    let mut merges = moment.put_map("merges")?;
    for (url, status) in entries {
        merges.put_map(url)?.put("status", status)?;
    }
    Ok(())
}

fn migrations(default_owner: &str) -> xitdb::Result<Migrations<CoreMemory>> {
    let default_owner = default_owner.to_string();
    Migrations::new([
        Migration::new(1, "add proposals", add_proposals),
        Migration::new(2, "proposals to merges", proposals_to_merges),
        // a closure can capture configuration
        Migration::new(3, "add default owner", move |moment| moment.put("default-owner", default_owner.as_str())),
    ])
}

fn main() -> xitdb::Result<()> {
    let db = Database::in_memory()?;
    let history = History::new(&db)?;
    let migrations = migrations("jason")?;
    assert_eq!(history.version(&migrations)?, 0);

    let migrated = history.migrate(&migrations)?;
    assert_eq!(migrated.ran, ["add proposals", "proposals to merges", "add default owner"]);
    assert_eq!((migrated.from, migrated.to), (0, 3));
    assert_eq!(history.version(&migrations)?, 3);

    // the next start has nothing to do
    assert!(history.migrate(&migrations)?.ran.is_empty());

    let merge = history.latest()?.get_map("merges")?.unwrap().get_map("https://example.com/pr/1")?.unwrap();
    assert_eq!(merge.get_string("status", Some(1024))?.as_deref(), Some("open"));
    Ok(())
}
```

Migrations can fail with the application's own error type, like `History::transact`: `Migration<C, E>` takes functions returning `Result<(), E>`, and `migrate` returns `E`. A migration function that's generic over the core needs `C: Core + 'static` where the list is built, since it's stored as a boxed closure.

A writer should open the database, take the write lock, `migrate`, and only then start serving. A reader, such as another process with `Database::open_read_only`, shouldn't migrate: `History::check_version` takes the same `Migrations` and, without writing, returns the version if it's the newest one, `Error::LayoutTooNew` if the data was written by newer code, and `Error::LayoutTooOld` if the writer hasn't migrated it yet. Check it on startup, and again after the writer may have restarted with new code, since a reader's `Database` sees new commits as they happen. `History::version` returns the recorded version on its own, without checking it.

## Types

In xitdb there are a variety of immutable data structures that you can nest arbitrarily:

* `HashMap` contains key-value pairs stored with a hash
* `HashSet` is like a `HashMap` that only sets the keys; it is useful when only checking for membership
* `CountedHashMap` and `CountedHashSet` are just a `HashMap` and `HashSet` that maintain a count of their contents
* `ArrayList` is a growable array
* `LinkedArrayList` is like an `ArrayList` that can also be efficiently sliced, concatenated, and inserted into
* `SortedMap` and `SortedSet` are like a `HashMap` and `HashSet` where the keys are byte arrays kept in lexicographic order

Each has a `Read` and a `Write` type, such as `ReadHashMap` and `WriteHashMap`. A `Write` type dereferences to its `Read` type.

The `Hash`-based data structures and the `ArrayList` use the hash array mapped trie, invented by Phil Bagwell. The `LinkedArrayList`, `SortedMap`, and `SortedSet` are based on a B-tree.

There are also scalar types you can store in the above-mentioned data structures. They are all variants of the `Data` enum, and most Rust values convert into it:

* `Data::Bytes` is a byte array (from `&str`, `String`, `&[u8]` and `Vec<u8>`)
* `Data::Uint` is an unsigned 64-bit int (from `u64`)
* `Data::Int` is a signed 64-bit int (from `i64`)
* `Data::Float` is a 64-bit float (from `f64`)

You may also want to define custom types. For example, you may want to store a big integer that can't fit in 64 bits. You could just store this with `Bytes`, but when reading the byte array there wouldn't be any indication that it should be interpreted as a big integer.

In xitdb, you can optionally store a format tag with a byte array. A format tag is a 2 byte tag that is stored alongside the byte array. Readers can use it to decide how to interpret the byte array. Here's an example of storing a 256-bit number with `bi` as the format tag:

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut moment = WriteHashMap::new(&mut db.root_cursor())?;

    let big_int = [0xAB; 32];
    moment.put("random-number", Data::tagged_bytes(&big_int[..], *b"bi"))?;

    let random_number = moment.get_cursor("random-number")?.unwrap().read_bytes_object(Some(1024))?;
    assert_eq!(random_number.format_tag, Some(*b"bi"));
    assert_eq!(&*random_number.value, &big_int[..]);
    Ok(())
}
```

There are many types you may want to store this way. Maybe an ISO-8601 date like `2026-01-01T18:55:48Z` could be stored with `dt` as the format tag. It's also great for storing custom structs. Just define the struct, serialize it as a byte array using whatever mechanism you wish, and store it with a format tag. Keep in mind that format tags can be *any* 2 bytes, so there are 65536 possible format tags.

## Cloning and Undoing

A powerful feature of immutable data is fast cloning. Any data structure can be instantly cloned and changed without affecting the original. Here we make a "food" list based on an existing "fruits" list:

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append_context(None, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        let mut fruits = WriteArrayList::new(&mut moment.put_cursor("fruits")?)?;
        for fruit in ["apple", "pear", "grape"] {
            fruits.append(fruit)?;
        }
        Ok(())
    })?;

    let last = history.get_slot(-1)?;
    history.append_context(last, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;

        // create a new key called "food" whose initial value is
        // based on the "fruits" list
        let mut food_cursor = moment.put_cursor("food")?;
        food_cursor.write(fruits.slot()?)?;

        let mut food = WriteArrayList::new(&mut food_cursor)?;
        for item in ["eggs", "rice", "fish"] {
            food.append(item)?;
        }
        Ok(())
    })?;

    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;

    // the food list includes the fruits
    let food = ReadArrayList::new(moment.get_cursor("food")?.unwrap())?;
    assert_eq!(food.count()?, 6);

    // ...but the fruits list hasn't been changed
    let fruits = ReadArrayList::new(moment.get_cursor("fruits")?.unwrap())?;
    assert_eq!(fruits.count()?, 3);

    // to undo a transaction, append the moment you want to go back to
    let first = history.get_slot(0)?;
    history.append(first)?;
    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
    assert!(moment.get_cursor("food")?.is_none());
    Ok(())
}
```

There's one catch you'll run into when cloning. All data in a given transaction is temporarily mutable, which is a very important optimization. So if you clone a data structure that was created *in the same transaction*, changing the clone also changes the original. To prevent that, call `freeze` on the cursor of the clone. This tells xitdb that writes through that cursor must treat all data made so far in the transaction as immutable, so they copy it instead of changing it. Writes through other cursors aren't affected.

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append_context(None, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;

        let mut big_cities = WriteArrayList::new(&mut moment.put_cursor("big-cities")?)?;
        big_cities.append("New York, NY")?;
        big_cities.append("Los Angeles, CA")?;

        // create a new key called "cities" whose initial value is
        // based on the "big-cities" list
        let mut cities_cursor = moment.put_cursor("cities")?;
        cities_cursor.write(big_cities.slot()?)?;

        // freeze here, so writes to cities won't mutate big-cities.
        // note: you can also freeze globally with `db.freeze()`,
        // but call it before `put_cursor` creates the cities cursor
        cities_cursor.freeze()?;

        let mut cities = WriteArrayList::new(&mut cities_cursor)?;
        cities.append("Charleston, SC")?;
        cities.append("Louisville, KY")?;
        Ok(())
    })?;

    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
    let cities = ReadArrayList::new(moment.get_cursor("cities")?.unwrap())?;
    assert_eq!(cities.count()?, 4);
    let big_cities = ReadArrayList::new(moment.get_cursor("big-cities")?.unwrap())?;
    assert_eq!(big_cities.count()?, 2);
    Ok(())
}
```

## Sorting and Paginating

The `Hash`-based structures are great for looking data up by key, but they store their contents in hash order. To show data in a sensible order one page at a time, you build and maintain your own index: a `SortedMap` whose keys sort the way you want. You keep it in sync by writing to it in the same transaction that writes the primary data. (To look entries up by a field rather than list them in order, an `Index` does this for you; see [Bulk Operations and Indexes](#bulk-operations-and-indexes).)

A `SortedMap` orders its keys lexicographically by their raw bytes. It is a count-augmented B+tree, so it can seek straight to a rank (`iter_from_index`, for pagination) or to the first key greater than or equal to a given value (`iter_from`, for type-ahead search), both in O(log n).

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;

    // (id, username, name), inserted in arbitrary order
    let users = [
        ("user1", "dave", "Dave Smith"),
        ("user2", "alice", "Alice Jones"),
        ("user3", "carol", "Carol White"),
        ("user4", "dan", "Dan Brown"),
        ("user5", "bob", "Bob Lee"),
    ];
    history.append_context(None, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        // the primary store: a HashMap from user id to the user's fields
        let mut id_to_user = moment.put_map("id->user")?;
        // the secondary index: a SortedMap ordered by username
        let mut username_to_id = WriteSortedMap::new(&mut moment.put_cursor("username->id")?)?;
        for (id, username, name) in users {
            let mut user = id_to_user.put_map(id)?;
            user.put("username", username)?;
            user.put("name", name)?;
            username_to_id.put(username, id)?;
        }
        Ok(())
    })?;

    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
    let id_to_user = moment.get_map("id->user")?.unwrap();
    let username_to_id = ReadSortedMap::new(moment.get_cursor("username->id")?.unwrap())?;

    // the equivalent of `ORDER BY username LIMIT 2 OFFSET 2`
    let mut page = Vec::new();
    for entry in username_to_id.iter_from_index(2)?.take(2) {
        let id = entry?.read_key_value_pair()?.value_cursor.read_bytes(Some(1024))?;
        let user = id_to_user.get_map(&id)?.unwrap();
        page.push(user.get_string("name", Some(1024))?.unwrap());
    }
    assert_eq!(page, ["Carol White", "Dan Brown"]);

    // type-ahead search: everyone whose username starts with "da"
    let mut matches = Vec::new();
    for entry in username_to_id.iter_from("da")? {
        let username = entry?.read_key_value_pair()?.key_cursor.read_string(Some(1024))?;
        if !username.starts_with("da") {
            break;
        }
        matches.push(username);
    }
    assert_eq!(matches, ["dan", "dave"]);
    Ok(())
}
```

To sort by a number, encode it big-endian so byte order matches numeric order. When a sort key isn't unique, append the id to keep every key distinct.

## Large Byte Arrays

When reading and writing large byte arrays, you probably don't want to have all of their contents in memory at once. To incrementally write to a byte array, get a writer from a cursor. It implements `std::io::Write`. If you need to set a format tag for the byte array, set the `format_tag` field on the writer before you call `finish`. To read a byte array incrementally, get a reader from a cursor. It implements `std::io::Read` and `std::io::Seek`.

```rust
use std::io::{BufRead, BufReader, Write};
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append_context(None, |cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        let mut long_text_cursor = moment.put_cursor("long-text")?;
        let mut writer = long_text_cursor.writer()?;
        for _ in 0..50 {
            writer.write_all(b"hello, world\n")?;
        }
        writer.finish()
    })?;

    let moment = ReadHashMap::new(history.get_cursor(-1)?.unwrap())?;
    let reader = moment.get_cursor("long-text")?.unwrap().reader()?;
    assert_eq!(BufReader::new(reader).lines().count(), 50);
    Ok(())
}
```

## Iterators

All data structures support iteration with `iter()`, which returns a standard `Iterator` of `Result<ReadCursor>`. Iterating a map or set yields cursors to key-value pairs; call `read_key_value_pair` on them to get a `key_cursor` and a `value_cursor`. In sets, the value always has a tag of `Tag::None`.

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    db.run_context(|cursor| {
        let mut people = WriteArrayList::new(cursor)?;
        let mut alice = WriteHashMap::new(&mut people.append_cursor()?)?;
        alice.put("name", "Alice")?;
        alice.put("age", 25u64)?;
        Ok(())
    })?;

    let people = ReadArrayList::new(db.root_cursor())?;
    for person in people.iter()? {
        let person = ReadHashMap::new(person?)?;
        for kv in person.iter()? {
            let kv = kv?.read_key_value_pair()?;
            let key = String::from_utf8(kv.key_cursor.read_bytes(Some(1024))?).unwrap();
            match kv.value_cursor.slot()?.tag {
                Tag::ShortBytes | Tag::Bytes => {
                    let value = kv.value_cursor.read_bytes(Some(1024))?;
                    println!("{key}: {}", String::from_utf8_lossy(&value));
                }
                Tag::Uint => println!("{key}: {}", kv.value_cursor.read_uint()?),
                Tag::Int => println!("{key}: {}", kv.value_cursor.read_int()?),
                Tag::Float => println!("{key}: {}", kv.value_cursor.read_float()?),
                _ => {}
            }
        }
    }
    Ok(())
}
```

`ArrayList` and `LinkedArrayList` also have an `iter_from` method, which starts the iterator from the given index. `SortedMap` and `SortedSet` have `iter_from` and `iter_from_index` to start the iterator from a key or index respectively.

## Accessors

The cursor methods above can do anything, but nesting and reading typed values take a few steps each. The collections have shorthands for the common cases:

* `WriteHashMap::put_map`, `put_set` and `put_list` return the collection at a key, storing the key and initializing the collection in one write if it's missing. An existing collection of that kind keeps its contents; any other value (including the other kind of hash collection, or a counted one) is an `Error::UnexpectedTag`, and nothing is written. `WriteArrayList` has the same methods taking an index, plus `append_map`, `append_set` and `append_list`. The returned collection belongs to the current transaction, so these must run inside one; on a top-level collection outside a transaction they return `Error::ExpectedTxStart` without writing anything.
* `ReadHashMap::get_map`, `get_set` and `get_list`, and the typed getters `get_bytes`, `get_string`, `get_int`, `get_uint` and `get_float`, return `Result<Option<_>>`. They return `None` if the key is missing or its value is empty (`Data::None`), and `Error::UnexpectedTag` if the value is a different type. Counted maps and sets aren't returned by `get_map` and `get_set`; use `ReadCountedHashMap::new` on `get_cursor`.
* `ReadCursor::read_string` reads a byte array as a `String`. Invalid UTF-8 is an `Error::InvalidUtf8` rather than being replaced; for lossy decoding, use `String::from_utf8_lossy` on `read_bytes`.
* `entries()` on hash and sorted maps yields a `ReadKvPairCursor` (a key cursor and a value cursor) for each pair, and `keys()` on hash and sorted sets yields key cursors. `iter()` still yields the raw cursors that need `read_key_value_pair`.

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::in_memory()?;
    db.run_context(|cursor| {
        let mut moment = WriteHashMap::new(cursor)?;
        moment.put("started-at", 1700000000i64)?;
        let mut merge = moment.put_map("merges")?.put_map("https://example.com/pr/1")?;
        merge.put("status", "merged")?;
        moment.put_set("tags")?.put("urgent")?;
        Ok(())
    })?;

    let moment = ReadHashMap::new(db.root_cursor())?;
    assert_eq!(moment.get_int("started-at")?, Some(1700000000));
    assert_eq!(moment.get_int("finished-at")?, None);

    if let Some(merges) = moment.get_map("merges")? {
        for kv in merges.entries()? {
            let kv = kv?;
            let url = kv.key_cursor.read_string(Some(1024))?;
            let status = ReadHashMap::new(kv.value_cursor)?.get_string("status", Some(1024))?;
            assert_eq!((url.as_str(), status.as_deref()), ("https://example.com/pr/1", Some("merged")));
        }
    }

    let tags = moment.get_set("tags")?.unwrap();
    for key in tags.keys()? {
        assert_eq!(key?.read_string(Some(1024))?, "urgent");
    }
    Ok(())
}
```

## Typed Collections

When the same collections are used all over an app, naming them and converting their keys and values by hand gets repetitive. A `Map<K, V>` or `Set<K>` declares a collection once, as a `const`, with its name in the parent map and its types. Each method takes the parent: reads take a `&ReadHashMap` (a moment, or any nested map; a `WriteHashMap` dereferences to one), and writes take a `&mut WriteHashMap`.

* A missing collection reads as empty: `get` returns `None`, `contains` returns `false`, and `iter` yields nothing. Writes create it with `put_map`/`put_set`, so they run inside a transaction like those. `remove`, and `Set::insert` of a key that's already there, write nothing.
* Like the typed getters, an empty value (`Data::None`) reads as a missing key, for `get`, `contains`, `remove` and `iter` alike.
* `iter` yields owned `(key, value)` pairs (or keys, for a set) as `Result`s.
* A value that doesn't decode is an `Error::Decode`, with the collection's name, the key and what was wrong, rather than being skipped. So is anything under the name that isn't the right kind of collection, for reads and writes alike. I/O errors stay `Error::Io`.
* The data is a plain hash map or set under the name, so untyped code and the other implementations read and write the same collections.

Keys are converted by a `KeyCodec`, implemented for `str`, `String`, `[u8]`, `Vec<u8>` and the integer types (big-endian at the type's full width). Values are converted by a `ValueCodec`, which reads from a `ReadCursor` and writes through a `WriteCursor`, so a value can be a nested structure. It's implemented for `String`, `Vec<u8>`, `i64`, `u64`, `f64`, `bool` (stored as the `Uint` `0` or `1`), and `Option<T>` (with `None` stored as an empty value). With the `serde` feature, `Json<T>` stores any serde type as JSON, tagged `js`; it also reads untagged JSON strings, so `Map<str, Json<Proposal>>` reads collections written with `serde_json::to_string`.

```rust
use xitdb::*;

const NAMES: Map<u64, String> = Map::new("names");
const SCORES: Map<str, i64> = Map::new("scores");
const STARTED: Set<str> = Set::new("started");

fn main() -> xitdb::Result<()> {
    let db = Database::in_memory()?;
    let history = History::new(&db)?;

    // a missing collection reads as empty
    assert_eq!(NAMES.get(&history.latest()?, &1)?, None);

    history.transact(|moment| {
        NAMES.put(moment, &1, "alice")?;
        NAMES.put(moment, &2, "bob")?;
        SCORES.put(moment, "alice", &10)?;
        STARTED.insert(moment, "alice")?;

        // definitions work on nested maps too
        let mut lobby = moment.put_map("rooms")?.put_map("lobby")?;
        STARTED.insert(&mut lobby, "bob")?;
        Ok::<_, xitdb::Error>(())
    })?;

    let moment = history.latest()?;
    assert_eq!(NAMES.get(&moment, &1)?.as_deref(), Some("alice"));
    assert_eq!(SCORES.get(&moment, "alice")?, Some(10));
    assert!(STARTED.contains(&moment, "alice")?);
    assert!(!STARTED.contains(&moment, "bob")?);

    let mut names = Vec::new();
    for entry in NAMES.iter(&moment)? {
        let (id, name) = entry?;
        names.push((id, name));
    }
    names.sort();
    assert_eq!(names, [(1, "alice".to_string()), (2, "bob".to_string())]);

    let lobby = moment.get_map("rooms")?.unwrap().get_map("lobby")?.unwrap();
    assert!(STARTED.contains(&lobby, "bob")?);

    // a value of the wrong type is an error, not a silent None
    history.transact(|moment| moment.put_map("scores")?.put("bob", "ten"))?;
    let err = SCORES.get(&history.latest()?, "bob").unwrap_err();
    assert!(matches!(err, Error::Decode(_)));
    assert_eq!(err.to_string(), r#"couldn't decode "scores" at key "bob": expected an integer, found ShortBytes"#);
    Ok(())
}
```

Values can't be typed collections themselves. To keep one collection per key, like the rooms above, open the nested map with `put_map` and `get_map` (or a `Map`'s `collection_mut` and `collection`) and use the definitions on it.

## Bulk Operations and Indexes

Typed maps have bulk operations, each a single call inside a transaction: `retain(parent, |key, value| keep)` removes every entry it doesn't keep, `remove_all(parent, keys)` removes many keys at once, and `update_where(parent, |key, value| matches, |value| change)` changes every value that matches. Each returns how many entries it removed or changed. `update_where` changes a copy of each value and only writes it back if it's no longer equal (`PartialEq`) to what was stored, so values need `Clone` and `PartialEq`. `keys_where` and `entries_where` read the entries that match. A `Set` has `retain` and `remove_all` too. They read everything first and write after, never create a missing collection, and write nothing when nothing matches, so a transaction that removes or changes nothing isn't committed.

An `Index<K, V, I>` is a secondary index on a `Map<K, V>`: a function, which can't capture anything, derives an index key of type `I` from each value (or `None`, to leave it out), and `get` returns the primary keys of every entry with that index key, `entries` the entries themselves, and `keys` the distinct index keys. Indexes are one-to-many. An `IndexedMap` is a map with its indexes; its `put`, `remove`, `remove_all`, `retain` and `update_where` (the map's own bulk operations, which report each entry they remove or change) keep every index up to date in the same transaction. The changes are collected first, then each index is opened once and written only where an entry's index key changed.

An index is stored as a plain hash map under its own name, in the same parent as the map, from each index key to a hash set of primary keys; a set is removed when its last entry is, and an empty one reads as missing. So the name can't be the map's or another index's: `Index::new` panics (a compile error in a `const`) on the map's name, and an `IndexedMap`'s writes panic on a shared one. Writes that bypass the `IndexedMap`, through the plain `Map` or untyped code, leave it stale, as does adding an index to a map that already has data. `rebuild` (on an `Index` or an `IndexedMap`) makes it match the map again, reading the map once for all of an `IndexedMap`'s indexes and writing only the differences, so it can run in a migration or on every start.

```rust
use xitdb::*;

// merge URL -> status
const STATUSES: Map<str, String> = Map::new("statuses");
// merges by status, except drafts
const BY_STATUS: Index<str, String, str> =
    Index::new(STATUSES, "statuses-by-status", |status| (status != "draft").then(|| status.to_owned()));
const INDEXED_STATUSES: IndexedMap<str, String> = IndexedMap::new(STATUSES, &[&BY_STATUS]);

fn main() -> xitdb::Result<()> {
    let db = Database::in_memory()?;
    let history = History::new(&db)?;
    history.transact(|moment| {
        INDEXED_STATUSES.put(moment, "pr/1", "open")?;
        INDEXED_STATUSES.put(moment, "pr/2", "open")?;
        INDEXED_STATUSES.put(moment, "pr/3", "draft")?;
        INDEXED_STATUSES.put(moment, "pr/4", "merged")
    })?;

    let moment = history.latest()?;
    let mut open = BY_STATUS.get(&moment, "open")?;
    open.sort();
    assert_eq!(open, ["pr/1", "pr/2"]);
    assert!(BY_STATUS.get(&moment, "draft")?.is_empty());

    // merge pr/2, and drop what's merged; the index follows both
    history.transact(|moment| {
        INDEXED_STATUSES.update_where(moment, |url, _| url == "pr/2", |status| *status = "merged".to_string())?;
        INDEXED_STATUSES.retain(moment, |_, status| status != "merged")
    })?;
    let moment = history.latest()?;
    assert_eq!(BY_STATUS.get(&moment, "open")?, ["pr/1"]);
    assert!(BY_STATUS.get(&moment, "merged")?.is_empty());

    // nothing matches, so nothing is written or committed
    let (removed, committed) = history.transact_with_status(|moment| STATUSES.remove_all(moment, ["pr/9"]))?;
    assert_eq!((removed, committed), (0, false));

    // a write through the plain map skips the index, and rebuild catches it up
    history.transact(|moment| STATUSES.put(moment, "pr/5", "open"))?;
    assert_eq!(BY_STATUS.get(&history.latest()?, "open")?, ["pr/1"]);
    assert!(history.transact(|moment| BY_STATUS.rebuild(moment))?);
    assert_eq!(BY_STATUS.get(&history.latest()?, "open")?.len(), 2);
    Ok(())
}
```

## Records

A struct that's stored as a nested map of its fields, like the merges in the [Accessors](#accessors) example, otherwise needs its field names repeated wherever it's read and written. With the `derive` feature, `#[derive(Record)]` makes the struct a `ValueCodec` that does it, so a `Map` can store it:

* Each field is stored under its name, or `#[xitdb(rename = "...")]`, with its type as its codec: `String`, `Vec<u8>`, `i64`, `u64`, `f64`, `bool`, an `Option` of one, or another record. `#[xitdb(codec = Json<T>)]` picks another codec (`Option<Json<T>>` for an `Option<T>` field).
* A missing field reads as `Default::default()`, so adding a field needs no migration. With `#[xitdb(required)]`, it's an error instead.
* An `Option` field that's `None` is missing from the map, rather than stored as an empty value; writing `None` removes it. The codec decides this (`ValueCodec::is_missing`), not how the type is spelled, so a type alias of an `Option` works the same.
* Keys in the map that aren't fields, such as ones written by newer code, are ignored when reading and kept when writing, by `put` too: the stored map is changed in place, not replaced.
* A field that doesn't decode is an `Error::Decode` that names it, along with the collection and the key.
* If `xitdb` isn't at `::xitdb`, such as when it's re-exported, give its path with `#[xitdb(crate = "path")]` on the struct.

`Map::update` reads a record, applies a function to a copy, and writes only the fields whose values changed: compared with `PartialEq`, except that floats are compared by their bits, so `-0.0` is a change from `0.0` and a NaN isn't a change from the same NaN. Only the changed fields of a nested record are written. If no field changed, it writes nothing at all, not even the collection, so the transaction isn't committed; there's no need to compare first. For a collection in a nested map, `Map::update_at` takes the path to it and only opens the maps along it if a field changed, since getting the nested map with `put_map` first would already copy the path. A missing key is left missing, and `update` returns `None`; `Map::upsert` starts from the default record instead. The derive supports structs with named fields and no generics, and needs every field to implement `PartialEq`.

```rust
#[cfg(feature = "derive")]
fn main() -> xitdb::Result<()> {
    use xitdb::*;

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
    let url = "https://example.com/pr/1";

    let db = Database::in_memory()?;
    let history = History::new(&db)?;
    let merge = Merge { title: "Add records".into(), started_at: 1700000000, ..Merge::default() };
    history.transact(|moment| MERGES.put(moment, url, &merge))?;

    // the same data as writing each field by hand, with no "thread" yet
    let moment = history.latest()?;
    let stored = moment.get_map("merges")?.unwrap().get_map(url)?.unwrap();
    assert_eq!(stored.get_int("started-at")?, Some(1700000000));
    assert_eq!(stored.get_uint("question")?, Some(0));
    assert!(stored.get_cursor("thread")?.is_none());
    assert_eq!(MERGES.get(&moment, url)?, Some(merge));

    // only "question" and "thread" are written
    history.transact(|moment| {
        MERGES.update(moment, url, |merge| {
            merge.question = true;
            merge.thread_id = Some("thread-1".into());
        })
    })?;
    let merge = MERGES.get(&history.latest()?, url)?.unwrap();
    assert!(merge.question);
    assert_eq!(merge.thread_id.as_deref(), Some("thread-1"));

    // an update that changes nothing isn't committed
    let (_, committed) =
        history.transact_with_status(|moment| MERGES.update(moment, url, |merge| merge.question = true))?;
    assert!(!committed);
    Ok(())
}

#[cfg(not(feature = "derive"))]
fn main() {}
```

## Hashing

The hashing data structures will create the hash for you when you call methods like `put` or `get_cursor`. If you want to do the hashing yourself, there are methods like `put_by_hash` and `get_cursor_by_hash` that take the hash.

When initializing a database, you tell xitdb how to hash with the `Hasher`. `Hasher::sha1()` (behind the default `sha1` feature) uses SHA-1. For any other algorithm, give `Hasher::new` a function from the data to its hash:

```rust
use sha2::{Digest, Sha256};
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let hasher = Hasher::new(|data| Sha256::digest(data).to_vec()).with_id(*b"sha2");
    let db = Database::new(CoreMemory::new(), hasher)?;

    // the size of the hash is stored in the header, along with the
    // optional four-byte hash id
    let mut core = db.into_core();
    core.seek_to(0)?;
    let header = Header::read(&mut core)?;
    assert_eq!(header.hash_size, 32);
    assert_eq!(id_to_bytes(header.hash_id), *b"sha2");
    Ok(())
}
```

If you try opening a database later with a hashing algorithm that has the wrong hash size, it will return `Error::InvalidHashSize`. The hash id is only written to the database header when it is first initialized; when you open it later, the hash id in the `Hasher` is ignored. If you are unsure which algorithm a database uses, read its header first, as above. I recommend using `sha2` as the hash id for SHA-256 and SHA-512, and distinguishing them by the hash size.

## Compaction

Normally, an immutable database grows forever, because old data is never deleted. To reclaim disk space and clear the history, xitdb supports compaction. This involves completely rebuilding the database to only contain the data accessible from the latest copy (i.e., "moment") of the database.

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    for i in 0..10u64 {
        history.append(i)?;
    }

    let compacted = db.compact(CoreMemory::new(), &mut MemoryOffsetMap::new())?;
    let history = ReadArrayList::new(compacted.root_cursor())?;
    assert_eq!(history.count()?, 1);
    assert_eq!(history.get_cursor(0)?.unwrap().read_uint()?, 9);
    Ok(())
}
```

The compacted database is written to a separate core. The target must be a new or empty database, so compaction returns `Error::TargetNotEmpty` if it already has data.

To compact a database file in place, use `Database::compact_file`. It writes the compacted copy to a new temporary file next to the original (`<path>.compacting-<random>`), closes the original, and renames the copy over it, so the file at the path is always either the original or the complete compacted database. The database you call it on becomes the compacted one, keeps its `Hasher`, and can keep writing. The last argument wraps a file in a core; it is how `compact_file` opens the new file, and reopens the original if the rename fails:

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let path = std::env::temp_dir().join(format!("xitdb-readme-compact-file-{}.db", std::process::id()));
    let mut db = Database::open(&path)?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    for i in 0..10u64 {
        history.append(i)?;
    }

    db.compact_file(&path, &mut MemoryOffsetMap::new(), CoreBufferedFile::new)?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    assert_eq!(history.count()?, 1);
    history.append(10u64)?;
    assert_eq!(history.count()?, 2);

    drop(db);
    std::fs::remove_file(&path)?;
    Ok(())
}
```

If the database is a `Database<DynCore>`, pass `|file| Box::new(CoreBufferedFile::new(file)) as DynCore`. Since it takes `&mut self`, it also works on a database behind a `Mutex`.

The original file is never lost. If compaction fails, the original stays open and unchanged, and the temporary file is removed. If the rename fails, the original is reopened. If the rename fails and the original can't be reopened either, the database stays on the temporary file and `compact_file` returns `Error::CompactFileReopenFailed` with its path: don't delete that file. Calling `compact_file` again with the original path retries the replacement. On Unix, the directory is synced after the rename, so the rename is durable.

Since the file is replaced rather than rewritten, keep in mind:

* Other processes that have the file open keep using the old file (see [Thread Safety](#thread-safety)). A writer in another process would keep committing to the old file, and those commits would be lost. So compact while holding the exclusive lock on the lock file (see [Initializing a Database](#initializing-a-database)), and have writers reopen the database after they take the lock.
* Symlinks are resolved, so the file they point to is replaced, but other hard links to the file keep the old one.
* The new file gets the original's permissions, but not its owner or group.

The offset map records where each copied object lives in the compacted database so shared references and cycles point to the same copied object. The in-memory `MemoryOffsetMap` grows with the number of live objects copied. To avoid holding that in memory, use a `FileOffsetMap`, which keeps the offsets in a scratch xitdb database. Run the compaction inside a single transaction on it, so the offsets aren't each committed separately:

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let db = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut db.root_cursor())?;
    history.append("hello")?;

    // usually a temporary file
    let scratch = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut compacted = None;
    scratch.run_context(|cursor| {
        let mut offsets = FileOffsetMap::new(cursor)?;
        compacted = Some(db.compact(CoreMemory::new(), &mut offsets)?);
        Ok(())
    })?;

    let compacted = compacted.unwrap();
    let history = ReadArrayList::new(compacted.root_cursor())?;
    assert_eq!(history.count()?, 1);
    Ok(())
}
```

## Replication

Since xitdb files are append-only, it is absurdly easy to replicate them: just copy the bytes that the destination doesn't have yet! Once a transaction is committed, its bytes never change, except for a small header that points at the latest commit. That makes it easy to keep a copy of a database (a "replica") up to date, whether it's another file on the same machine or on another machine across a network.

```rust
use xitdb::*;

fn main() -> xitdb::Result<()> {
    let source = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let replica = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let mut history = WriteArrayList::new(&mut source.root_cursor())?;
    history.append("first moment")?;

    // on the replica: describe what it already has
    let state = replica.replica_state()?;
    // on the source: decide which bytes to send, and write them
    let start = source.replication_start(state)?;
    let end = source.committed_size()?;
    let mut buffer = Vec::new();
    source.read_committed(start, end, &mut buffer)?;
    // on the replica: apply them
    replica.apply_replicated(start, &mut buffer.as_slice(), end - start)?;

    let replicated = ReadArrayList::new(replica.root_cursor())?;
    assert_eq!(replicated.get_cursor(-1)?.unwrap().read_bytes(None)?, b"first moment");
    Ok(())
}
```

Over a network, the replica sends its `ReplicaState` (two integers: its committed size and a checksum of its latest commit), and the source replies with `start`, the length, and then the bytes. Since `read_committed` takes an `io::Write` and `apply_replicated` takes an `io::Read`, the bytes can be streamed directly over the connection without buffering them in memory.

A replica can start out as any new database. Each database has a random file ID, so the first sync sees that the replica isn't a copy of the source and sends the entire source file, replacing the replica. The same happens if the replica can no longer be extended, such as when the source is replaced by a compacted copy or restored from an older backup: `replication_start` returns 0, and the replica is replaced with a full copy.

If a sync is interrupted, the replica stays at its last commit, and the next sync discards whatever was partially written. The exception is when `start` is 0: the replica is truncated before the copy begins, so an interrupted copy leaves it unusable until the next sync succeeds. If that matters to you, check whether `start` is 0, and if so, write the copy to a new file and only replace the old replica after `apply_replicated` succeeds.

Only change a replica with `apply_replicated`. If you write to it directly, it no longer matches the source, and the next sync will replace it.

### Replicating to TypeScript

Replicas don't have to use this crate. Replication to and from the TypeScript implementation (the [`xitdb`](https://www.npmjs.com/package/xitdb) npm package, 0.26.0) is tested by `interop/ts/run.sh`, which needs cargo, Node 22.18 or later, and pnpm or npm. It runs `examples/ts_replication.rs`, which keeps a database in memory like a server would, and `interop/ts/client.ts`, which holds an in-memory replica like a browser client would:

* A new replica gets a full copy of a history with every data type, then a delta for each transaction, and reads every value back.
* The replica sends its `ReplicaState`, and `replication_start` returns its committed size, so it only gets what it missed.
* After the source is compacted into a new database, `replication_start` returns 0, and the replica gets a full copy.
* Both compute the same trailer checksums, and a database written in TypeScript replicates to this crate.

The test sends a `ReplicaState` as JSON, with the checksum as a decimal string, because it is a u64 and a JSON number can only hold integers up to 2^53:

```json
{"committedSize":137438,"checksum":"11364480133251437419"}
```

In TypeScript, that is `{ committedSize: state.committedSize, checksum: state.checksum.toString() }` one way and `{ committedSize, checksum: BigInt(checksum) }` the other.

To keep replicas up to date after each transaction, the source can send everyone the bytes the transaction added, from the committed size before it to the one after it, along with that start position. A replica that missed one of them must not apply the next, and doesn't: in TypeScript, `openReplicated(start, length)` throws `InvalidRangeException` when `start` is neither 0 nor the replica's `committedSize()`, and `close()` throws `InvalidDatabaseException` when the bytes don't end with a trailer of the replica's file at `start + length`, such as bytes from before the source was compacted. Either way, the replica stays at its last commit, and it should sync again by sending its `ReplicaState`.

Note that in xitdb-ts 0.26.0, `readUint()` and `readInt()` return a JavaScript number, so they lose precision past 2^53, and `readUint()` throws `ExpectedUnsignedLongException` for values of 2^63 or more. For the exact value, read the slot: `BigInt.asUintN(64, cursor.slot().value)` for a uint, and `cursor.slot().value` for an int.

## Thread Safety

It is possible to read the database from multiple threads without locks, even while writes are happening. This is a big benefit of immutable databases. However, each thread needs to use its own `Database` instance (a `Database` is `Send` but not `Sync`), each with its own file handle. Also, keep in mind that writes still need to come from one thread at a time; across processes, take an exclusive lock on a separate lock file before writing (see [Initializing a Database](#initializing-a-database)).

A reader in another thread or process can keep its `Database` open: the root is read again on each operation, so it sees new commits as they happen. But when the writer replaces the file, as `compact_file` does, the reader's handle still points at the old file, and it won't see anything written afterwards. Such a reader should either open the database for each read (with `Database::open_read_only`), or check whether the file was replaced and reopen it. The compacted file has a new file ID, so compare `Database::open_read_only(&path)?.header().file_id` with the reader's `db.header().file_id`.

On Unix, a file can be renamed over while other processes have it open. On Windows, that only works if every handle to it was opened with `FILE_SHARE_DELETE`, and if `std::fs::rename` can use POSIX rename semantics (`FileRenameInfoEx`). Rust's `std::fs::File` opens files with `FILE_SHARE_DELETE`, so on NTFS on current Windows versions, readers using it don't block `compact_file`. But a handle opened without it (by another program, for example) makes the rename fail. So does any other open handle on FAT or exFAT, some network shares, and older Windows 10 builds, where `std::fs::rename` falls back to `MoveFileExW`. There, close readers in other processes before compacting.

## Compatibility

This crate reads and writes the same format as the other implementations. Its test suite is a port of the Go implementation's, and it includes a database written by the Go implementation (`tests/testdata/test.db`). `interop/run.sh` round-trips a database between this crate and the Go implementation: Rust writes every data type, Go verifies it and appends a moment, Rust verifies that and compacts the database, and Go verifies the compacted copy. `interop/ts/run.sh` replicates databases between this crate and the TypeScript implementation (see [Replicating to TypeScript](#replicating-to-typescript)).

The API follows the Go implementation's, adapted to Rust:

* Lookups that can miss return `Result<Option<_>>` instead of a nil cursor.
* Go's string, `Bytes` and hash variants of map methods (`Put`, `PutBytes`, `PutByHash`) become methods taking `impl AsRef<[u8]>` keys, plus `_bytes` variants for keys with a format tag and `_by_hash` variants.
* `All()` and `AllFrom()` become `iter()` and `iter_from()`, returning standard iterators.
* In the low-level path API, a context function is not a path part; use `WriteCursor::write_path_context`, which runs it at the end of the path.
