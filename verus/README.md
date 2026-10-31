# Verus proofs

Machine-checked proofs, by [Verus](https://github.com/verus-lang/verus), that
xitdb's on-disk encodings and its core data structure algorithms are correct
for every input and every size, not just the inputs tests try.

```sh
verus verus/src/lib.rs --crate-type=lib
```

CI runs this on every change to `verus/` (`.github/workflows/verus.yml`, which
pins the Verus release). There are no `assume`s, `admit`s or
`external_body` functions, so everything below is proved from Verus's own
axioms.

## What is proved

### Encodings (`encoding.rs`)

`Tag`, `Slot`, `Header`, `ArrayListHeader` and `BTreeHeader` encoding and
decoding are executable functions that mirror `src/slot.rs` and
`src/format.rs`. For each one:

- decoding an encoding gives back the value;
- every byte string that decodes successfully is the encoding of what it
  decodes to, so no two values share an encoding;
- decoding rejects exactly the invalid inputs: tags above 16, and negative
  sizes or pointers.

One edge: `Header::from_bytes` ignores byte 3 (padding), so a header
re-encodes to the same bytes exactly when that byte is 0.

### The hash map (`hamt.rs`)

The core of the proofs. `read_map_slot` (read and write modes) and
`remove_map_slot` are modelled over an append-only store with the crate's
copy-on-write rule: positions before `frozen` (the crate's
`max(tx_start, frozen_at)`) are committed and never written, and later
positions are written in place. The model follows the code branch by branch:
copying old index blocks and pairs, splitting a slot on a hash collision,
and the `slot_to_return` loop that collapses a block left with one pair.

It proves, for hashes of any length and maps of any size:

- **Insert** (`theorem_put`) never fails: in particular `KeyOffsetExceeded`
  is unreachable for well-formed maps. The result is well-formed and holds
  exactly `old.insert(hash, value)`.
- **Remove** (`theorem_remove`) fails exactly when the key is absent.
  Otherwise the result is well-formed and holds exactly `old.remove(hash)`.
- **Snapshots** (`lemma_snapshot_unchanged`): neither operation writes a
  committed position. So every map committed before the transaction reads
  exactly as it did, however many operations follow.
- **Frame** (`lemma_frame`): a block reads the same in any store that agrees
  on the positions it reaches. Well-formedness includes that no block of the
  current transaction is reachable twice, so writing one in place can't
  change a different part of the tree.

`lemma_empty_map` shows that the empty map `HashMapInit` writes is
well-formed, so the theorems apply from the first insert on. `hash_nibble` is
also executable and verified against the model's `nibble`.

### Array list indexing (`array_list.rs`)

- `array_list_shift` is executable, verified to compute `log16(key)` through
  its use of `leading_zeros`.
- `MaxShiftExceeded` is unreachable: every `i64` key has a shift below 16.
- `(key >> (shift * 4)) & MASK` is nibble `shift` of the key, and keys below
  16^(s+1) with the same nibbles are equal, so no two items share a slot.
- On append (`read_array_list_slot_append`), the shift grows by exactly one,
  exactly when the size reaches a power of 16. When it does, every existing
  key has slot 0 at the new shift, which is where the old root is moved.
- `resolve_index` returns an in-range index exactly for indexes in
  `-size..size`, and counts negative ones from the end.

## What is not proved

- **The Rust code itself.** The models mirror the crate's functions
  statement by statement, but Verus checks the models, not `src/`. Nothing
  mechanically keeps the two in sync, so a change to an algorithm in `src/`
  needs the matching change here. The byte-level functions (encodings,
  `hash_nibble`, `array_list_shift`, the slot index, `resolve_index`) are
  executable code equivalent to the crate's, written with the operations
  Verus supports (explicit shifts instead of `to_be_bytes`, and `u64`
  instead of `i64` shifts of non-negative keys). The hash map
  is a spec-level model with abstract positions (one per block instead of
  byte offsets) and opaque values.
- **The rest of the crate:** B-trees (`LinkedArrayList`, `SortedMap`,
  `SortedSet`), array list slicing, cursors and byte I/O, compaction,
  replication, and the CRC.
- **Crash consistency.** The model treats writes as atomic. Torn writes and
  recovery would need a model of the file system.
- **Hash collisions.** Like the crate, the model identifies keys by their
  hash: two keys with the same hash are the same entry.

## Found while writing these

The hash map walked a hash with a `u8` nibble offset, but a hash longer than
127 bytes has more than 255 nibbles. Two keys whose hashes differ only past
nibble 255 overflowed the offset: debug builds panicked, and release builds
wrapped it to 0 and recursed until the stack overflowed. The model uses
unbounded integers for the offset, so the crate needs a `usize` (or any type
that can't overflow) for the proofs to describe it.
