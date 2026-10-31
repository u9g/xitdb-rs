# Verus proofs

Machine-checked proofs, by [Verus](https://github.com/verus-lang/verus), that
xitdb behaves as an immutable map-of-history: every data structure computes
what it should for every input and every size, and data committed before a
transaction reads the same after it.

```sh
verus verus/src/lib.rs --crate-type=lib
```

CI runs this on every change to `verus/` (`.github/workflows/verus.yml`, which
pins the Verus release). There are no `assume`s, `admit`s or
`external_body` functions, so everything below is proved from Verus's own
axioms.

## What is proved

### Encodings (`encoding.rs`) and checksums (`crc64.rs`)

- `Tag`, `Slot`, `Header`, `ArrayListHeader` and `BTreeHeader` are
  executable functions mirroring `src/slot.rs` and `src/format.rs`.
  - Decoding an encoding gives back the value.
  - Every byte string that decodes is the encoding of what it decodes to.
  - Decoding rejects exactly the invalid inputs.
  - One edge: `Header::from_bytes` ignores the padding byte, so a header
    re-encodes to the same bytes exactly when that byte is 0.
- The table-driven CRC of `src/crc64.rs` computes CRC-64/XZ as defined bit
  by bit, including the standard check value. The table construction and
  `checksum` are executable, with the crate's loops.

### The hash map (`hamt.rs`)

`read_map_slot` and `remove_map_slot`, modelled branch by branch over an
append-only store with the crate's copy-on-write rule. Positions before
`frozen` (the crate's `max(tx_start, frozen_at)`) are committed and never
written; later ones are written in place. The model covers copying committed
blocks and pairs, splitting a slot on a hash collision, and collapsing a
block left with one pair. For any hash length and map size:

- **Insert** (`theorem_put`) never fails, so `KeyOffsetExceeded` is
  unreachable. The map stays well-formed and holds exactly
  `old.insert(hash, value)`.
- **Remove** (`theorem_remove`) fails exactly when the key is absent.
  Otherwise the map stays well-formed and holds exactly `old.remove(hash)`.
- **Snapshots** (`lemma_snapshot_unchanged`): neither operation writes a
  committed position, so every committed map reads exactly as before.
- Well-formedness includes that no block of the current transaction is
  reachable twice, so writing one in place can't change another part of the
  tree.

### The array list (`array_list.rs`, `array_list_heap.rs`)

- **Index arithmetic.**
  - `array_list_shift` is executable and computes `log16`, through its use
    of `leading_zeros`.
  - `MaxShiftExceeded` is unreachable for any `i64` key.
  - Every key gets its own slot.
  - The root overflows exactly when the size reaches a power of 16.
  - `resolve_index` is correct.
- **As a tree:** get, append (`read_array_list_slot_append`) and slice
  (`read_array_list_slice`) give the stored values, the values plus the new
  one, and a prefix of them.
- **Over the hash map's store, with copy-on-write**
  (`array_list_heap.rs`): append and slice keep the list well-formed and
  give the right values, without writing a committed position.
  `theorem_history` composes this with the hash map in one store:
  appending a moment to the history and then editing a hash map leaves every
  committed history list and every committed hash map exactly as it was.

### Sorted maps and sets (`sorted.rs`)

The count-augmented B+tree of `src/sorted.rs`: `sorted_get`, `sorted_rank`,
`sorted_get_by_index`, `sorted_put` (with leaf and branch splits),
`sorted_grow_root` and `sorted_remove`, with keys abstracted to an ordered
type.

- A well-formed tree's entries are strictly sorted and respect the
  separators.
- Get, rank and get-by-index return the lookup, the number of smaller keys,
  and the indexing of that sorted sequence.
- Put and remove keep the tree well-formed, within the format's 16-entry
  node limit, and act on the entries exactly as a map insert and remove.

### Linked array lists (`linked_list.rs`)

The count-augmented B-tree of `src/btree.rs`:

- `read_btree_slot`;
- `btree_insert` with `btree_make_root`;
- `btree_remove`, which drops emptied children, merges underfull ones, and
  is followed by collapsing a one-child root;
- `btree_join`, through `btree_join_left`/`btree_join_right`,
  `btree_merge_nodes` and the assemble functions;
- `btree_split`, which `LinkedArrayListSlice` uses twice.

Get returns the value at an index, insert and remove insert and remove at
it, join concatenates, and split cuts at an index. Every result is a
well-formed tree with all leaves at one depth.

### Where the B-trees live (`btree_store.rs`)

Stored sorted-map and linked-list nodes materialize into the trees above.
Every write the B-tree code makes is one of four kinds:

- `sorted_write_node`/`btree_write_node`, which write in place only if the
  node is reusable;
- `write_sorted_node`/`write_btree_node`, which append;
- appending a key or value.

None of these writes a committed position. So every committed sorted map
and linked array list materializes to the same tree afterwards, and gives
the same entries, lookups, ranks and indexes.

## What is not proved

- **The Rust code itself.** The models mirror the crate's functions
  statement by statement, but Verus checks the models, not `src/`, and
  nothing mechanically keeps them in sync. The byte-level functions are
  executable code equivalent to the crate's, written with the operations
  Verus supports:
  - the encodings, CRC, `hash_nibble`, `array_list_shift`, the slot index,
    and `resolve_index`;
  - for example, explicit shifts instead of `to_be_bytes`.

  The data structures are spec-level models with abstract positions and
  values.
- **In-place B-tree writes.** For the hash map and the array list, the
  models prove that the tree being written is correct even though its
  mutable blocks are written in place. For the B-trees, the functional
  models prove what the algorithms compute, and `btree_store.rs` proves
  that committed trees are untouched. That writing a mutable node in place
  can't change another part of the current tree isn't modelled at the
  storage level. The crate handles that by freezing before `btree_join`
  shares subtrees.
- **Features around the data structures:**
  - Cursors and byte reading and writing.
  - Compaction.
  - Replication. Its central claim, that a replica whose trailer checksum
    matches is a prefix of the source, rests on 64-bit checksums and random
    commit IDs, so it's probabilistic rather than provable.
- **Crash consistency.** The models treat writes as atomic. Torn writes and
  recovery would need a model of the file system.
- **Hash collisions.** Like the crate, the model identifies hash map keys
  by their hash.

## Found while writing these

The hash map walked a hash with a `u8` nibble offset, but a hash longer than
127 bytes has more than 255 nibbles. Two keys whose hashes differ only past
nibble 255 overflowed the offset: debug builds panicked, and release builds
wrapped it to 0 and recursed until the stack overflowed. The model uses
unbounded integers for the offset, so the crate needs a `usize` (or any type
that can't overflow) for the proofs to describe it.
