# Verification of `src/`

The crate's own code is checked by [Verus](https://github.com/verus-lang/verus).
Verified code lives in `verus!` blocks: `cargo verus verify` checks it against
its specifications, and a normal `cargo build` erases the specifications and
proofs, so the compiled crate is unchanged. CI runs both (the `verify-crate`
job in `.github/workflows/verus.yml`). There are no `assume`s or `admit`s; the
trusted code is listed below.

`verus/` holds separate models of the data structures with deeper functional
proofs (see `verus/README.md`). This file is about the code that runs.

## How the file is seen

`src/store.rs` describes the database file as a byte sequence that is read
and written at positions (`Store`). The algorithms are written against
`Store` and verified against its specification:

- a non-empty read returns the bytes of the file;
- a write within the file replaces exactly those bytes;
- a write past the end keeps every byte that was there;
- `set_length` truncates or zero-extends, and `sync` changes nothing.

Writing functions take a `limit`: the position where the current
transaction started (`tx_floor` in `database.rs`). Everything before it
belongs to committed transactions, and the verified guarantee is that none
of it changes, apart from the root header that a commit rewrites.

They also take `copy_at`, the crate's `max(tx_start, frozen_at)`, which
only decides what is copied rather than changed in place: a block reached
through a path is copied if it lies before `copy_at`. Freezing and
concatenation move `copy_at` forward so that shared data gets copied. The
proofs need nothing from `copy_at` except that it is at least `limit`, so
they hold whatever it is.

## Old snapshots never change

`src/snapshot.rs` proves what the write guarantee means for readers
(`theorem_snapshots_unchanged`). After any write that keeps
`tx_hdr_ok(f, g, limit)`, as every verified write does, any array list,
hash map, linked array list or sorted map (by rank) read whose blocks all
lie in committed data
(between the root header and `limit`) returns the same result as before,
and its blocks still lie in committed data. So by induction the result
holds after any sequence of writes. Committed data only points at
committed data, so every read of a past moment is such a read.

Sorted map reads by key compare keys stored as byte arrays, and have no
read specification yet; reads by rank (`sorted_get_by_index`, specified by
`sorted_read`) are covered.

## The boundary

Verus checks verified code against its specification, but code outside
`verus!` blocks could call a verified function without meeting its
`requires`, and then the function's guarantees wouldn't hold. So no
verified function that unverified code calls has a `requires`: each one
checks its preconditions at run time and returns an error if they fail.
`verus/check_boundary.py`, run in CI, fails if unverified code calls a
verified function that has one.

So whatever the unverified orchestration does, every write it makes to the
file goes through a verified function that changes nothing before `limit`
except the root header. Nothing else writes to the file, apart from the
full replication apply's deliberate `set_length(0)`.

This boundary found a bug (below): the orchestration had been calling
verified functions without meeting their preconditions.

## What is verified

Every function below runs in the crate, with the properties listed.

- **Encodings** (`slot.rs`, `format.rs`, `bytes.rs`): slots, tags, headers,
  trailers, key/value pairs, b-tree nodes, slot blocks and counts.
  - Each decoder inverts its encoder, and decoding rejects exactly the
    invalid bytes.
  - `decode_counts` rejects negative counts.
- **Checksums** (`crc64.rs`): `TABLE` and `checksum` compute CRC-64/XZ as
  defined bit by bit.
- **The array list** (`array_list_store.rs`): the slot walk, append and
  slice.
  - In read mode the walk returns exactly what the bytes lead to.
  - In write mode nothing before `limit` changes, and the slot returned is
    at or after `limit`.
  - `array_list_shift` is `log16`, so `MaxShiftExceeded` is unreachable.
- **The hash map** (`map_store.rs`): the slot walk and removal.
  - In read mode the walk returns exactly what the bytes lead to.
  - In write mode and removal nothing before `limit` changes.
  - The returned slot, key or value position is writable.
- **Linked array lists** (`btree_io.rs`, `btree_join.rs`, `btree.rs`):
  - node reads, the copy-on-write node write, and the descent (exactly what
    the bytes lead to);
  - insert, get-for-write and remove (nothing before `limit` changes);
  - join and split, which only append.
- **Sorted maps** (`sorted_store.rs`): get, get-by-index, rank, paths,
  put, remove and root growth. Reads change nothing, and writes change
  nothing before `limit`.
- **Path steps** (`path_store.rs`): what each step of a path writes when it
  creates, copies or updates a collection or writes data. None of them
  changes a committed byte other than the root header.
- **Commits** (`commit_store.rs`):
  - creating a database;
  - starting and finishing a transaction;
  - `commit_root`, which changes only the root header and the trailer it
    appends;
  - `committed_size`, which only accepts a header that points at a trailer
    with a valid checksum and the same root;
  - `truncate`.
- **Replication** (`commit_store.rs`): `replica_state`, `replication_start`,
  `read_committed`, and applying replicated bytes, which changes nothing
  before where it resumes.
- **Compaction** (`compact_store.rs`): reads only the source, and changes
  nothing the target held before, whatever the offset map returns.
- **Cursors and iterators** (`cursor_store.rs`, `iter_store.rs`):
  - reading byte arrays and the reader's bounds;
  - the byte writer, which only writes inside its own byte array and at the
    slot pointing to it;
  - short-bytes packing, which round-trips;
  - the iterators' traversal (stack indexes stay in range, and it only
    reads);
  - key/value pair positions.
- **`CoreMemory`** (`core.rs`): its operations are verified against its
  buffer. Seeking then reading or writing, as `Database::read_at` and
  `write_at` do, meets the `Store` specification. So for in-memory
  databases, the `Store` assumption is proved.
- **Small helpers**: `resolve_index`, `hash_nibble`, the collection tags,
  the offset map's keys (injective), and B-tree node helpers.

Every offset computed from data read from the file is overflow-checked.
Corrupt pointers, sizes and counts make these functions return an error
instead of panicking.

Every verified function is proved to finish. Walks down the file (B-tree
and sorted map descents, iteration, compaction) take at most
`walk_bound` steps: one more than the number of the smallest blocks they
visit that fit in the file. A path through a valid file never visits a
block twice, so valid files behave as before. A corrupt file whose pointers
form a cycle now fails with `InvalidBTreeNode` or `InvalidDatabase` instead
of looping forever (`src/termination_tests.rs`). The recursive walks
(B-tree and sorted map writes, splits, compaction) use one stack frame per
step, so on a large enough corrupt file they can still overflow the stack
before the bound is reached. That is a crash, not a hang.

## Trusted

- **`DbStore`** (`store.rs`) forwards `Store` to a `Database`'s core
  through its `RefCell`. It assumes the core behaves like a file. That
  assumption is proved for `CoreMemory`.
- **`CoreFile` and `CoreBufferedFile`** (`core.rs`) call the operating
  system.
- **`IoSink` and `IoSource`** (`store.rs`) forward replication to the
  caller's `io::Write` and `io::Read`. Nothing is assumed about the bytes.
- **The offset map adapter** (`compact.rs`) forwards to the caller's
  `OffsetMap`. Nothing is assumed about what it returns.
- **Error constructors** that use `format!`.
- **The limit the orchestration passes.** `tx_floor` is set, when a
  transaction starts, to the file's length right after the verified
  truncation to the committed size, and doesn't change until the
  transaction ends.
- **Verus, its standard library `vstd`, and the Z3 solver.**

## Not verified

This code doesn't write to the file itself: it calls the verified
functions above, which check their preconditions (see "The boundary"). It
decides what to read and write, so a bug in it can produce wrong results,
but it can't change committed data.

- **Orchestration in `database.rs`:**
  - the path dispatcher (`read_slot_pointer` and the `match` in
    `read_part`), which threads closures;
  - transaction state (`tx_start`, `tx_floor`, `transaction`,
    `run_context`, `freeze`);
  - `copy_collection_if_frozen`, `check_frozen_slot`, `check_hash`;
  - `Database::new`'s control flow;
  - `compact`'s entry point.
- **Cursor plumbing in `cursor.rs`:** resolving slots, `read_uint` /
  `read_int` / `read_float`, `write_path`, and frozen checks.
- **The public wrappers** in `collections.rs` and the value types in
  `data.rs`, `hasher.rs` and `path.rs`.
- **Crash consistency:** writes are treated as atomic.

## Found by verifying

Each was confirmed with a test and fixed:

- a `u8` hash offset that overflowed for hashes longer than 127 bytes;
- negative b-tree counts that overflowed the rank arithmetic;
- offsets and sizes read from a corrupt file that overflowed
  (`header.size + 1`, `slot.value + 8`, pointers near `i64::MAX`, rank sums
  in sorted maps);
- the first version of the trusted `Store` specification, which claimed
  `CoreMemory` zero-pads writes past its end. It doesn't: it writes at the
  end;
- a copy-on-write violation. Changing a collection reached without its
  init part (for example a list inside a hash map that a new moment
  copied) changed the collection in place, so the previous, committed
  moment changed too. The boundary checks rejected the write. Now
  `copy_collection_if_frozen` also copies collections from before the
  transaction (`remove_without_init_keeps_old_moment` in
  `tests/regressions.rs`).
