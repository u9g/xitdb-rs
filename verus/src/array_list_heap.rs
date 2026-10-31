//! The array list over the same append-only store as the hash map
//! (`hamt.rs`), with the crate's copy-on-write rule: `read_array_list_slot`
//! in write mode (creating missing blocks and copying committed ones),
//! `read_array_list_slot_append` (moving a full root under a new one) and
//! `read_array_list_slice` (copying a committed root).
//!
//! Level-0 slots hold values (`Ptr::Kv(v)` here is a slot whose value is
//! `v`, such as the position of a moment's hash map). The results:
//!
//! * appending to a list holding `vals` gives one holding `vals.push(v)`,
//!   and slicing gives the first `size` values ([`theorem_append`],
//!   [`theorem_slice`]);
//! * neither writes a committed position, so every list committed before
//!   reads the same ([`lemma_list_snapshot_unchanged`]). Together with the
//!   hash map's theorems, which use the same store, a transaction that
//!   appends a moment and edits its hash map leaves every earlier moment
//!   intact ([`theorem_history`]).

use vstd::prelude::*;
use crate::hamt::{Store, Ptr, agree, write_slot, append_block, empty_block, store_ok};
use crate::array_list::{digit, log16, pow16, lemma_log16_bounds, lemma_slots_determine_key, lemma_append_shift};
use vstd::arithmetic::div_mod::*;

verus! {

pub open spec fn index_pos(p: Ptr) -> int {
    match p {
        Ptr::Index(q) => q,
        _ => -1,
    }
}

/// Everything a block at shift `sh` reaches.
pub open spec fn al_fp(s: Store, pos: int, sh: nat, x: int) -> bool
    decreases sh,
{
    x == pos || (sh > 0 && s.blocks.contains_key(pos) && exists|i: int|
        0 <= i < 16 && match #[trigger] s.blocks[pos][i] {
            Ptr::Index(q) => al_fp(s, q, (sh - 1) as nat, x),
            _ => false,
        })
}

pub open spec fn al_fp_child(s: Store, p: Ptr, csh: nat, x: int) -> bool {
    match p {
        Ptr::Index(q) => al_fp(s, q, csh, x),
        _ => false,
    }
}

/// A well-formed array list block at shift `sh`.
pub open spec fn awf(s: Store, pos: int, sh: nat, frozen: int) -> bool
    decreases sh,
{
    &&& s.blocks.contains_key(pos)
    &&& s.blocks[pos].len() == 16
    &&& forall|i: int| 0 <= i < 16 ==> match #[trigger] s.blocks[pos][i] {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(q) => sh > 0 && awf(s, q, (sh - 1) as nat, frozen),
    }
    &&& pos < frozen ==> forall|i: int| 0 <= i < 16 ==> index_pos(#[trigger] s.blocks[pos][i]) < frozen
    &&& (pos >= frozen && sh > 0) ==> forall|i: int|
        0 <= i < 16 ==> !al_fp_child(s, #[trigger] s.blocks[pos][i], (sh - 1) as nat, pos)
    &&& (pos >= frozen && sh > 0) ==> forall|i: int, j: int, x: int|
        0 <= i < 16 && 0 <= j < 16 && i != j && #[trigger] al_fp_child(s, s.blocks[pos][i], (sh - 1) as nat, x)
            && #[trigger] al_fp_child(s, s.blocks[pos][j], (sh - 1) as nat, x) ==> x < frozen
}

/// The child in slot `i` of a block at shift `sh` is well-formed.
pub open spec fn slot_ok(s: Store, p: Ptr, sh: nat, frozen: int) -> bool {
    match p {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(q) => sh > 0 && awf(s, q, (sh - 1) as nat, frozen),
    }
}

/// `read_array_list_slot` in read mode, then reading the value.
pub open spec fn al_lookup(s: Store, pos: int, key: int, sh: nat) -> Option<int>
    decreases sh,
{
    if !s.blocks.contains_key(pos) {
        None
    } else {
        let p = s.blocks[pos][digit(key, sh)];
        if sh == 0 {
            match p {
                Ptr::Kv(v) => Some(v),
                _ => None,
            }
        } else {
            match p {
                Ptr::Index(q) => al_lookup(s, q, key, (sh - 1) as nat),
                _ => None,
            }
        }
    }
}

/// What the slot at shift `sh` gives for `key`.
pub open spec fn slot_lookup(s: Store, p: Ptr, key: int, sh: nat) -> Option<int> {
    if sh == 0 {
        match p {
            Ptr::Kv(v) => Some(v),
            _ => None,
        }
    } else {
        match p {
            Ptr::Index(q) => al_lookup(s, q, key, (sh - 1) as nat),
            _ => None,
        }
    }
}

/// `read_array_list_slot` in write mode, then writing `v` into the slot.
pub open spec fn al_set(s: Store, pos: int, key: int, sh: nat, v: int, frozen: int) -> Store
    decreases sh,
{
    let i = digit(key, sh);
    if sh == 0 {
        write_slot(s, pos, i, Ptr::Kv(v))
    } else {
        match s.blocks[pos][i] {
            Ptr::Empty => {
                let n = s.next;
                al_set(write_slot(append_block(s, empty_block()), pos, i, Ptr::Index(n)), n, key, (sh - 1) as nat, v, frozen)
            },
            Ptr::Index(q) => if q < frozen {
                let n = s.next;
                al_set(write_slot(append_block(s, s.blocks[q]), pos, i, Ptr::Index(n)), n, key, (sh - 1) as nat, v, frozen)
            } else {
                al_set(s, q, key, (sh - 1) as nat, v, frozen)
            },
            Ptr::Kv(_) => s,
        }
    }
}

/// `read_array_list_slot_append`, then writing `v`: the store and the new
/// root.
pub open spec fn al_append(s: Store, root: int, size: int, v: int, frozen: int) -> (Store, int) {
    let prev = log16(size - 1);
    let next = log16(size);
    if prev != next {
        let n = s.next;
        (al_set(append_block(s, empty_block().update(0, Ptr::Index(root))), n, size, next, v, frozen), n)
    } else {
        (al_set(s, root, size, next, v, frozen), root)
    }
}

pub open spec fn descend(s: Store, pos: int, d: nat) -> int
    decreases d,
{
    if d == 0 {
        pos
    } else {
        match s.blocks[pos][0] {
            Ptr::Index(q) => descend(s, q, (d - 1) as nat),
            _ => pos,
        }
    }
}

/// `read_array_list_slice`: follow slot 0 down, then copy the new root if
/// it is committed.
pub open spec fn al_slice(s: Store, root: int, old_size: int, size: int, frozen: int) -> (Store, int) {
    let r = descend(s, root, (log16(old_size - 1) - log16(size - 1)) as nat);
    if r < frozen {
        (append_block(s, s.blocks[r]), s.next)
    } else {
        (s, r)
    }
}

/// The list rooted at `root` holds exactly `vals`.
pub open spec fn list_holds(s: Store, root: int, vals: Seq<int>, frozen: int) -> bool {
    &&& awf(s, root, log16(vals.len() - 1), frozen)
    &&& forall|k: int| 0 <= k < vals.len() ==> #[trigger] al_lookup(s, root, k, log16(vals.len() - 1)) == Some(vals[k])
}

// basic facts

proof fn lemma_digit_range(k: int, j: nat)
    requires
        k >= 0,
    ensures
        0 <= digit(k, j) < 16,
{
    lemma_pow16_pos(j);
}

proof fn lemma_pow16_pos(n: nat)
    ensures
        pow16(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow16_pos((n - 1) as nat);
    }
}

proof fn lemma_slot_ok(s: Store, pos: int, sh: nat, frozen: int, i: int)
    requires
        awf(s, pos, sh, frozen),
        0 <= i < 16,
    ensures
        slot_ok(s, s.blocks[pos][i], sh, frozen),
{
    assert(match s.blocks[pos][i] {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(q) => sh > 0 && awf(s, q, (sh - 1) as nat, frozen),
    });
}

proof fn lemma_lookup_slot(s: Store, pos: int, key: int, sh: nat)
    requires
        s.blocks.contains_key(pos),
    ensures
        al_lookup(s, pos, key, sh) == slot_lookup(s, s.blocks[pos][digit(key, sh)], key, sh),
{
}

pub proof fn lemma_al_fp_stored(s: Store, pos: int, sh: nat, frozen: int, x: int)
    requires
        store_ok(s, frozen),
        awf(s, pos, sh, frozen),
        al_fp(s, pos, sh, x),
    ensures
        s.blocks.contains_key(x),
        0 <= x < s.next,
    decreases sh,
{
    if x != pos {
        let i = choose|i: int| 0 <= i < 16 && match #[trigger] s.blocks[pos][i] {
            Ptr::Index(q) => al_fp(s, q, (sh - 1) as nat, x),
            _ => false,
        };
        lemma_slot_ok(s, pos, sh, frozen, i);
        lemma_al_fp_stored(s, index_pos(s.blocks[pos][i]), (sh - 1) as nat, frozen, x);
    }
}

pub proof fn lemma_al_fp_frozen(s: Store, pos: int, sh: nat, frozen: int, x: int)
    requires
        awf(s, pos, sh, frozen),
        pos < frozen,
        al_fp(s, pos, sh, x),
    ensures
        x < frozen,
    decreases sh,
{
    if x != pos {
        let i = choose|i: int| 0 <= i < 16 && match #[trigger] s.blocks[pos][i] {
            Ptr::Index(q) => al_fp(s, q, (sh - 1) as nat, x),
            _ => false,
        };
        lemma_slot_ok(s, pos, sh, frozen, i);
        assert(index_pos(s.blocks[pos][i]) < frozen);
        lemma_al_fp_frozen(s, index_pos(s.blocks[pos][i]), (sh - 1) as nat, frozen, x);
    }
}

proof fn lemma_al_fp_child_stored(s: Store, p: Ptr, sh: nat, frozen: int, x: int)
    requires
        store_ok(s, frozen),
        slot_ok(s, p, sh, frozen),
        sh > 0,
        al_fp_child(s, p, (sh - 1) as nat, x),
    ensures
        0 <= x < s.next,
{
    lemma_al_fp_stored(s, index_pos(p), (sh - 1) as nat, frozen, x);
}

/// The frame lemma for array lists.
pub proof fn lemma_al_frame(s: Store, t: Store, pos: int, sh: nat, frozen: int)
    requires
        awf(s, pos, sh, frozen),
        forall|x: int| al_fp(s, pos, sh, x) ==> #[trigger] agree(s, t, x),
    ensures
        awf(t, pos, sh, frozen),
        forall|x: int| #[trigger] al_fp(t, pos, sh, x) == al_fp(s, pos, sh, x),
        forall|k: int| #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh),
    decreases sh,
{
    assert(agree(s, t, pos));
    let b = s.blocks[pos];
    assert(t.blocks[pos] == b);
    assert forall|i: int| 0 <= i < 16 implies {
        &&& slot_ok(t, #[trigger] b[i], sh, frozen)
        &&& sh > 0 ==> forall|x: int| #[trigger] al_fp_child(t, b[i], (sh - 1) as nat, x) == al_fp_child(s, b[i], (sh - 1) as nat, x)
        &&& forall|k: int| #[trigger] slot_lookup(t, b[i], k, sh) == slot_lookup(s, b[i], k, sh)
    } by {
        lemma_slot_ok(s, pos, sh, frozen, i);
        if let Ptr::Index(q) = b[i] {
            assert forall|x: int| al_fp(s, q, (sh - 1) as nat, x) implies #[trigger] agree(s, t, x) by {
                assert(al_fp(s, pos, sh, x));
            }
            lemma_al_frame(s, t, q, (sh - 1) as nat, frozen);
        }
    }
    assert forall|i: int| 0 <= i < 16 implies match #[trigger] t.blocks[pos][i] {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(q) => sh > 0 && awf(t, q, (sh - 1) as nat, frozen),
    } by {
        assert(slot_ok(t, b[i], sh, frozen));
    }
    if sh > 0 && pos >= frozen {
        assert forall|i: int| 0 <= i < 16 implies !al_fp_child(t, #[trigger] t.blocks[pos][i], (sh - 1) as nat, pos) by {
            assert(!al_fp_child(s, b[i], (sh - 1) as nat, pos));
        }
        assert forall|i: int, j: int, x: int|
            0 <= i < 16 && 0 <= j < 16 && i != j && #[trigger] al_fp_child(t, t.blocks[pos][i], (sh - 1) as nat, x)
                && #[trigger] al_fp_child(t, t.blocks[pos][j], (sh - 1) as nat, x) implies x < frozen by {
            assert(al_fp_child(s, b[i], (sh - 1) as nat, x) && al_fp_child(s, b[j], (sh - 1) as nat, x));
        }
    }
    assert forall|x: int| #[trigger] al_fp(t, pos, sh, x) == al_fp(s, pos, sh, x) by {
        if al_fp(s, pos, sh, x) && x != pos {
            let i = choose|i: int| 0 <= i < 16 && match #[trigger] s.blocks[pos][i] {
                Ptr::Index(q) => al_fp(s, q, (sh - 1) as nat, x),
                _ => false,
            };
            assert(al_fp_child(s, b[i], (sh - 1) as nat, x));
            assert(al_fp_child(t, t.blocks[pos][i], (sh - 1) as nat, x));
        }
        if al_fp(t, pos, sh, x) && x != pos {
            let i = choose|i: int| 0 <= i < 16 && match #[trigger] t.blocks[pos][i] {
                Ptr::Index(q) => al_fp(t, q, (sh - 1) as nat, x),
                _ => false,
            };
            assert(al_fp_child(t, b[i], (sh - 1) as nat, x));
            assert(al_fp_child(s, s.blocks[pos][i], (sh - 1) as nat, x));
        }
    }
    assert forall|k: int| #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh) by {
        let d = digit(k, sh);
        if 0 <= d < 16 {
            assert(slot_lookup(t, b[d], k, sh) == slot_lookup(s, b[d], k, sh));
        }
    }
}

/// Every list committed before a transaction reads the same in a store
/// that kept the committed positions.
pub proof fn lemma_list_snapshot_unchanged(s: Store, t: Store, root: int, sh: nat, frozen: int)
    requires
        store_ok(s, frozen),
        awf(s, root, sh, frozen),
        root < frozen,
        forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x),
    ensures
        awf(t, root, sh, frozen),
        forall|k: int| #[trigger] al_lookup(t, root, k, sh) == al_lookup(s, root, k, sh),
{
    assert forall|x: int| al_fp(s, root, sh, x) implies #[trigger] agree(s, t, x) by {
        lemma_al_fp_frozen(s, root, sh, frozen, x);
        lemma_al_fp_stored(s, root, sh, frozen, x);
    }
    lemma_al_frame(s, t, root, sh, frozen);
}

proof fn lemma_agree_trans(s: Store, t: Store, u: Store, x: int)
    requires
        agree(s, t, x),
        agree(t, u, x),
    ensures
        agree(s, u, x),
{
}

/// A copy of a committed block at a new position reads the same.
proof fn lemma_al_copy_frozen(s: Store, t: Store, q: int, n: int, sh: nat, frozen: int)
    requires
        store_ok(s, frozen),
        awf(s, q, sh, frozen),
        q < frozen,
        n >= frozen,
        t.blocks.contains_key(n),
        t.blocks[n] == s.blocks[q],
        forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x),
    ensures
        awf(t, n, sh, frozen),
        forall|x: int| #[trigger] al_fp(t, n, sh, x) ==> x == n || (x < frozen && al_fp(s, q, sh, x)),
        forall|k: int| #[trigger] al_lookup(t, n, k, sh) == al_lookup(s, q, k, sh),
{
    let b = s.blocks[q];
    assert forall|i: int| 0 <= i < 16 implies {
        &&& slot_ok(t, #[trigger] b[i], sh, frozen)
        &&& sh > 0 ==> forall|x: int| #[trigger] al_fp_child(t, b[i], (sh - 1) as nat, x) ==> x < frozen && al_fp(s, q, sh, x)
        &&& forall|k: int| #[trigger] slot_lookup(t, b[i], k, sh) == slot_lookup(s, b[i], k, sh)
    } by {
        lemma_slot_ok(s, q, sh, frozen, i);
        if let Ptr::Index(c) = b[i] {
            assert(c < frozen);
            lemma_list_snapshot_unchanged(s, t, c, (sh - 1) as nat, frozen);
            assert forall|x: int| #[trigger] al_fp_child(t, b[i], (sh - 1) as nat, x) implies x < frozen && al_fp(s, q, sh, x) by {
                assert forall|y: int| al_fp(s, c, (sh - 1) as nat, y) implies #[trigger] agree(s, t, y) by {
                    lemma_al_fp_frozen(s, c, (sh - 1) as nat, frozen, y);
                    lemma_al_fp_stored(s, c, (sh - 1) as nat, frozen, y);
                }
                lemma_al_frame(s, t, c, (sh - 1) as nat, frozen);
                lemma_al_fp_frozen(s, c, (sh - 1) as nat, frozen, x);
                assert(al_fp(s, c, (sh - 1) as nat, x));
                assert(al_fp(s, q, sh, x));
            }
        }
    }
    assert forall|i: int| 0 <= i < 16 implies match #[trigger] t.blocks[n][i] {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(c) => sh > 0 && awf(t, c, (sh - 1) as nat, frozen),
    } by {
        assert(slot_ok(t, b[i], sh, frozen));
    }
    assert(awf(t, n, sh, frozen));
    assert forall|x: int| #[trigger] al_fp(t, n, sh, x) implies x == n || (x < frozen && al_fp(s, q, sh, x)) by {
        if x != n {
            let i = choose|i: int| 0 <= i < 16 && match #[trigger] t.blocks[n][i] {
                Ptr::Index(c) => al_fp(t, c, (sh - 1) as nat, x),
                _ => false,
            };
            assert(al_fp_child(t, b[i], (sh - 1) as nat, x));
        }
    }
    assert forall|k: int| #[trigger] al_lookup(t, n, k, sh) == al_lookup(s, q, k, sh) by {
        let d = digit(k, sh);
        if 0 <= d < 16 {
            assert(slot_lookup(t, b[d], k, sh) == slot_lookup(s, b[d], k, sh));
        }
    }
}

/// A block of this transaction whose slot `i` now holds `np`, written in
/// place.
proof fn lemma_al_rebuild(s: Store, t: Store, pos: int, sh: nat, i: int, np: Ptr, frozen: int)
    requires
        store_ok(s, frozen),
        awf(s, pos, sh, frozen),
        pos >= frozen,
        sh > 0,
        0 <= i < 16,
        t.blocks.contains_key(pos),
        t.blocks[pos] == s.blocks[pos].update(i, np),
        forall|j: int, x: int| 0 <= j < 16 && j != i && #[trigger] al_fp_child(s, s.blocks[pos][j], (sh - 1) as nat, x) ==> agree(s, t, x),
        slot_ok(t, np, sh, frozen),
        !al_fp_child(t, np, (sh - 1) as nat, pos),
        forall|x: int| #[trigger] al_fp_child(t, np, (sh - 1) as nat, x) ==> al_fp_child(s, s.blocks[pos][i], (sh - 1) as nat, x) || s.next <= x,
    ensures
        awf(t, pos, sh, frozen),
        forall|x: int| #[trigger] al_fp(t, pos, sh, x) ==> al_fp(s, pos, sh, x) || s.next <= x,
        forall|k: int| digit(k, sh) != i ==> #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh),
        forall|k: int| digit(k, sh) == i ==> #[trigger] al_lookup(t, pos, k, sh) == slot_lookup(t, np, k, sh),
{
    let b = s.blocks[pos];
    let tb = t.blocks[pos];
    let csh = (sh - 1) as nat;
    assert forall|j: int| 0 <= j < 16 && j != i implies {
        &&& slot_ok(t, #[trigger] b[j], sh, frozen)
        &&& forall|x: int| #[trigger] al_fp_child(t, b[j], csh, x) == al_fp_child(s, b[j], csh, x)
        &&& forall|x: int| #[trigger] al_fp_child(s, b[j], csh, x) ==> 0 <= x < s.next
        &&& forall|k: int| #[trigger] slot_lookup(t, b[j], k, sh) == slot_lookup(s, b[j], k, sh)
    } by {
        lemma_slot_ok(s, pos, sh, frozen, j);
        if let Ptr::Index(q) = b[j] {
            assert forall|x: int| al_fp(s, q, csh, x) implies #[trigger] agree(s, t, x) by {
                assert(al_fp_child(s, b[j], csh, x));
            }
            lemma_al_frame(s, t, q, csh, frozen);
            assert forall|x: int| #[trigger] al_fp_child(s, b[j], csh, x) implies 0 <= x < s.next by {
                lemma_al_fp_stored(s, q, csh, frozen, x);
            }
        }
    }
    assert forall|j: int| 0 <= j < 16 implies match #[trigger] tb[j] {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(q) => sh > 0 && awf(t, q, csh, frozen),
    } by {
        if j != i {
            assert(tb[j] == b[j]);
            assert(slot_ok(t, b[j], sh, frozen));
        } else {
            assert(slot_ok(t, np, sh, frozen));
        }
    }
    assert forall|j: int| 0 <= j < 16 implies !al_fp_child(t, #[trigger] tb[j], csh, pos) by {
        if j != i {
            assert(tb[j] == b[j]);
            assert(!al_fp_child(s, b[j], csh, pos));
        }
    }
    assert forall|j: int, k: int, x: int|
        0 <= j < 16 && 0 <= k < 16 && j != k && #[trigger] al_fp_child(t, tb[j], csh, x)
            && #[trigger] al_fp_child(t, tb[k], csh, x) implies x < frozen by {
        if j != i && k != i {
            assert(tb[j] == b[j] && tb[k] == b[k]);
            assert(al_fp_child(s, b[j], csh, x) && al_fp_child(s, b[k], csh, x));
        } else if j == i {
            assert(tb[k] == b[k]);
            assert(al_fp_child(s, b[k], csh, x));
            assert(al_fp_child(s, b[i], csh, x));
        } else {
            assert(tb[j] == b[j]);
            assert(al_fp_child(s, b[j], csh, x));
            assert(al_fp_child(s, b[i], csh, x));
        }
    }
    assert(awf(t, pos, sh, frozen));
    assert forall|x: int| #[trigger] al_fp(t, pos, sh, x) implies al_fp(s, pos, sh, x) || s.next <= x by {
        if x != pos {
            let j = choose|j: int| 0 <= j < 16 && match #[trigger] t.blocks[pos][j] {
                Ptr::Index(q) => al_fp(t, q, csh, x),
                _ => false,
            };
            assert(al_fp_child(t, tb[j], csh, x));
            if j != i {
                assert(tb[j] == b[j]);
                assert(al_fp_child(s, s.blocks[pos][j], csh, x));
            } else if !(s.next <= x) {
                assert(al_fp_child(s, s.blocks[pos][i], csh, x));
            }
        }
    }
    assert forall|k: int| digit(k, sh) != i implies #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh) by {
        let d = digit(k, sh);
        if 0 <= d < 16 {
            assert(tb[d] == b[d]);
            assert(slot_lookup(t, b[d], k, sh) == slot_lookup(s, b[d], k, sh));
        }
    }
}

/// What a write to a mutable list block may change.
pub open spec fn al_frame_ok(s: Store, t: Store, pos: int, sh: nat, frozen: int) -> bool {
    &&& t.next >= s.next
    &&& forall|x: int| 0 <= x < s.next && (x < frozen || !al_fp(s, pos, sh, x)) ==> #[trigger] agree(s, t, x)
    &&& forall|x: int| #[trigger] al_fp(t, pos, sh, x) ==> al_fp(s, pos, sh, x) || s.next <= x
}

proof fn lemma_empty_awf(s: Store, n: int, sh: nat, frozen: int)
    requires
        s.blocks.contains_key(n),
        s.blocks[n] == empty_block(),
        n >= frozen,
    ensures
        awf(s, n, sh, frozen),
        forall|x: int| #[trigger] al_fp(s, n, sh, x) ==> x == n,
        forall|k: int| k >= 0 ==> #[trigger] al_lookup(s, n, k, sh) is None,
{
    assert forall|i: int| 0 <= i < 16 implies match #[trigger] s.blocks[n][i] {
        Ptr::Empty => true,
        Ptr::Kv(_) => sh == 0,
        Ptr::Index(q) => sh > 0 && awf(s, q, (sh - 1) as nat, frozen),
    } by {
        assert(s.blocks[n][i] == Ptr::Empty);
    }
    assert forall|i: int| 0 <= i < 16 implies !al_fp_child(s, #[trigger] s.blocks[n][i], (sh - 1) as nat, n) by {
        assert(s.blocks[n][i] == Ptr::Empty);
    }
    assert forall|x: int| #[trigger] al_fp(s, n, sh, x) implies x == n by {
        if x != n {
            let i = choose|i: int| 0 <= i < 16 && match #[trigger] s.blocks[n][i] {
                Ptr::Index(q) => al_fp(s, q, (sh - 1) as nat, x),
                _ => false,
            };
            assert(s.blocks[n][i] == Ptr::Empty);
        }
    }
    assert forall|k: int| k >= 0 implies #[trigger] al_lookup(s, n, k, sh) is None by {
        lemma_digit_range(k, sh);
        assert(s.blocks[n][digit(k, sh)] == Ptr::Empty);
    }
}

pub open spec fn differs_upto(k: int, key: int, sh: nat) -> bool {
    exists|j: nat| j <= sh && digit(k, j) != digit(key, j)
}

/// Writing a key into a mutable, well-formed block.
pub proof fn lemma_al_set(s: Store, pos: int, key: int, sh: nat, v: int, frozen: int)
    requires
        store_ok(s, frozen),
        awf(s, pos, sh, frozen),
        pos >= frozen,
        key >= 0,
    ensures
        ({
            let t = al_set(s, pos, key, sh, v, frozen);
            &&& store_ok(t, frozen)
            &&& awf(t, pos, sh, frozen)
            &&& al_frame_ok(s, t, pos, sh, frozen)
            &&& al_lookup(t, pos, key, sh) == Some(v)
            &&& forall|k: int| k >= 0 && differs_upto(k, key, sh) ==> #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh)
        }),
    decreases sh,
{
    let i = digit(key, sh);
    lemma_digit_range(key, sh);
    let b = s.blocks[pos];
    let t = al_set(s, pos, key, sh, v, frozen);
    assert(al_fp(s, pos, sh, pos));
    if sh == 0 {
        assert(t == write_slot(s, pos, i, Ptr::Kv(v)));
        assert forall|j: int| 0 <= j < 16 implies match #[trigger] t.blocks[pos][j] {
            Ptr::Empty => true,
            Ptr::Kv(_) => sh == 0,
            Ptr::Index(q) => sh > 0 && awf(t, q, (sh - 1) as nat, frozen),
        } by {
            if j != i {
                assert(t.blocks[pos][j] == b[j]);
                lemma_slot_ok(s, pos, sh, frozen, j);
            }
        }
        assert forall|x: int| #[trigger] al_fp(t, pos, sh, x) implies al_fp(s, pos, sh, x) || s.next <= x by {}
        assert forall|k: int| k >= 0 && differs_upto(k, key, sh) implies #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh) by {
            let j = choose|j: nat| j <= sh && digit(k, j) != digit(key, j);
            lemma_digit_range(k, 0);
        }
    } else {
        let csh = (sh - 1) as nat;
        lemma_slot_ok(s, pos, sh, frozen, i);
        assert forall|x: int| #[trigger] al_fp_child(s, b[i], csh, x) implies al_fp(s, pos, sh, x) by {}
        // the siblings of slot i don't reach pos or anything mutable slot i reaches
        assert forall|j: int, x: int|
            0 <= j < 16 && j != i && #[trigger] al_fp_child(s, b[j], csh, x) implies
                x != pos && 0 <= x < s.next && (x < frozen || !al_fp_child(s, b[i], csh, x)) by {
            lemma_slot_ok(s, pos, sh, frozen, j);
            lemma_al_fp_child_stored(s, b[j], sh, frozen, x);
        }
        match b[i] {
            Ptr::Kv(_) => {},
            Ptr::Empty => {
                let n = s.next;
                let s1 = append_block(s, empty_block());
                let s2 = write_slot(s1, pos, i, Ptr::Index(n));
                lemma_empty_awf(s2, n, csh, frozen);
                assert(store_ok(s2, frozen));
                lemma_al_set(s2, n, key, csh, v, frozen);
                assert(t == al_set(s2, n, key, csh, v, frozen));
                lemma_al_set_finish(s, s2, t, pos, key, sh, v, frozen, n);
                assert forall|k: int| k >= 0 && differs_upto(k, key, sh) implies #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh) by {
                    if digit(k, sh) == i {
                        let j = choose|j: nat| j <= sh && digit(k, j) != digit(key, j);
                        assert(differs_upto(k, key, csh));
                        assert(al_lookup(s2, n, k, csh) is None);
                        lemma_lookup_slot(s, pos, k, sh);
                    }
                }
            },
            Ptr::Index(q) => {
                if q < frozen {
                    let n = s.next;
                    let s1 = append_block(s, s.blocks[q]);
                    let s2 = write_slot(s1, pos, i, Ptr::Index(n));
                    assert forall|x: int| 0 <= x < frozen implies #[trigger] agree(s, s2, x) by {}
                    lemma_al_copy_frozen(s, s2, q, n, csh, frozen);
                    assert(store_ok(s2, frozen));
                    lemma_al_set(s2, n, key, csh, v, frozen);
                    assert(t == al_set(s2, n, key, csh, v, frozen));
                    lemma_al_set_finish(s, s2, t, pos, key, sh, v, frozen, n);
                    assert forall|k: int| k >= 0 && differs_upto(k, key, sh) implies #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh) by {
                        if digit(k, sh) == i {
                            let j = choose|j: nat| j <= sh && digit(k, j) != digit(key, j);
                            assert(differs_upto(k, key, csh));
                            assert(al_lookup(s2, n, k, csh) == al_lookup(s, q, k, csh));
                            lemma_lookup_slot(s, pos, k, sh);
                        }
                    }
                } else {
                    lemma_al_set(s, q, key, csh, v, frozen);
                    assert(t == al_set(s, q, key, csh, v, frozen));
                    assert(!al_fp(s, q, csh, pos)) by {
                        assert(!al_fp_child(s, b[i], csh, pos));
                    }
                    assert(agree(s, t, pos));
                    assert(b.update(i, Ptr::Index(q)) =~= b);
                    assert forall|j: int, x: int| 0 <= j < 16 && j != i && #[trigger] al_fp_child(s, b[j], csh, x) implies agree(s, t, x) by {
                        if !(x < frozen) {
                            assert(!al_fp_child(s, b[i], csh, x));
                        }
                    }
                    assert forall|x: int| #[trigger] al_fp_child(t, Ptr::Index(q), csh, x) implies al_fp_child(s, b[i], csh, x) || s.next <= x by {
                        assert(al_fp(t, q, csh, x));
                    }
                    assert(!al_fp_child(t, Ptr::Index(q), csh, pos)) by {
                        if al_fp(t, q, csh, pos) {
                            assert(al_fp(s, q, csh, pos) || s.next <= pos);
                        }
                    }
                    lemma_al_rebuild(s, t, pos, sh, i, Ptr::Index(q), frozen);
                    assert forall|x: int| 0 <= x < s.next && (x < frozen || !al_fp(s, pos, sh, x)) implies #[trigger] agree(s, t, x) by {
                        if !(x < frozen) {
                            assert(!al_fp_child(s, b[i], csh, x));
                        }
                    }
                    assert forall|k: int| k >= 0 && differs_upto(k, key, sh) implies #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh) by {
                        if digit(k, sh) == i {
                            let j = choose|j: nat| j <= sh && digit(k, j) != digit(key, j);
                            assert(differs_upto(k, key, csh));
                            lemma_lookup_slot(s, pos, k, sh);
                        }
                    }
                }
            },
        }
    }
}

/// The end of writing through a slot that now points at a new block `n`
/// (a fresh one, or a copy of a committed one) in `s2`.
proof fn lemma_al_set_finish(s: Store, s2: Store, t: Store, pos: int, key: int, sh: nat, v: int, frozen: int, n: int)
    requires
        store_ok(s, frozen),
        awf(s, pos, sh, frozen),
        pos >= frozen,
        sh > 0,
        key >= 0,
        n == s.next,
        s2.next == s.next + 1,
        s2.blocks.contains_key(pos),
        s2.blocks[pos] == s.blocks[pos].update(digit(key, sh), Ptr::Index(n)),
        forall|x: int| 0 <= x < s.next && x != pos ==> #[trigger] agree(s, s2, x),
        store_ok(s2, frozen),
        awf(s2, n, (sh - 1) as nat, frozen),
        forall|x: int| #[trigger] al_fp(s2, n, (sh - 1) as nat, x) ==> x == n || al_fp_child(s, s.blocks[pos][digit(key, sh)], (sh - 1) as nat, x),
        ({
            let csh = (sh - 1) as nat;
            &&& store_ok(t, frozen)
            &&& awf(t, n, csh, frozen)
            &&& al_frame_ok(s2, t, n, csh, frozen)
            &&& al_lookup(t, n, key, csh) == Some(v)
            &&& forall|k: int| k >= 0 && differs_upto(k, key, csh) ==> #[trigger] al_lookup(t, n, k, csh) == al_lookup(s2, n, k, csh)
        }),
    ensures
        awf(t, pos, sh, frozen),
        al_frame_ok(s, t, pos, sh, frozen),
        al_lookup(t, pos, key, sh) == Some(v),
        forall|k: int| digit(k, sh) != digit(key, sh) ==> #[trigger] al_lookup(t, pos, k, sh) == al_lookup(s, pos, k, sh),
        forall|k: int| digit(k, sh) == digit(key, sh) ==> #[trigger] al_lookup(t, pos, k, sh) == al_lookup(t, n, k, (sh - 1) as nat),
{
    let i = digit(key, sh);
    let csh = (sh - 1) as nat;
    let b = s.blocks[pos];
    lemma_digit_range(key, sh);
    lemma_slot_ok(s, pos, sh, frozen, i);
    assert(al_fp(s, pos, sh, pos));
    assert(!al_fp_child(s, b[i], csh, pos));
    assert(!al_fp(s2, n, csh, pos));
    assert(agree(s2, t, pos));
    assert(t.blocks[pos] == b.update(i, Ptr::Index(n)));
    assert forall|j: int, x: int| 0 <= j < 16 && j != i && #[trigger] al_fp_child(s, b[j], csh, x) implies agree(s, t, x) by {
        lemma_slot_ok(s, pos, sh, frozen, j);
        lemma_al_fp_child_stored(s, b[j], sh, frozen, x);
        assert(!al_fp_child(s, b[j], csh, pos));
        assert(agree(s, s2, x));
        if !(x < frozen) {
            assert(!al_fp_child(s, b[i], csh, x));
            assert(!al_fp(s2, n, csh, x));
        }
        assert(agree(s2, t, x));
        lemma_agree_trans(s, s2, t, x);
    }
    assert forall|x: int| #[trigger] al_fp_child(t, Ptr::Index(n), csh, x) implies al_fp_child(s, b[i], csh, x) || s.next <= x by {
        assert(al_fp(t, n, csh, x));
        assert(al_fp(s2, n, csh, x) || s2.next <= x);
    }
    assert(!al_fp_child(t, Ptr::Index(n), csh, pos)) by {
        if al_fp(t, n, csh, pos) {
            assert(al_fp(s2, n, csh, pos) || s2.next <= pos);
        }
    }
    lemma_al_rebuild(s, t, pos, sh, i, Ptr::Index(n), frozen);
    assert forall|x: int| 0 <= x < s.next && (x < frozen || !al_fp(s, pos, sh, x)) implies #[trigger] agree(s, t, x) by {
        assert(agree(s, s2, x));
        if !(x < frozen) {
            assert(!al_fp_child(s, b[i], csh, x));
            assert(!al_fp(s2, n, csh, x));
        }
        assert(agree(s2, t, x));
        lemma_agree_trans(s, s2, t, x);
    }
}

/// Appending to a list rooted at a block of this transaction.
pub proof fn theorem_append(s: Store, root: int, vals: Seq<int>, v: int, frozen: int)
    requires
        store_ok(s, frozen),
        list_holds(s, root, vals, frozen),
        root >= frozen,
    ensures
        ({
            let (t, r) = al_append(s, root, vals.len() as int, v, frozen);
            &&& store_ok(t, frozen)
            &&& r >= frozen
            &&& list_holds(t, r, vals.push(v), frozen)
            &&& forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x)
        }),
{
    let size = vals.len() as int;
    let prev = log16(size - 1);
    let next = log16(size);
    let vals2 = vals.push(v);
    assert(vals2.len() - 1 == size);
    if size >= 1 {
        lemma_append_shift(size);
    } else {
        assert(prev == 0 && next == 0);
    }
    let (t, r) = al_append(s, root, size, v, frozen);
    // the root to write into, holding vals at shift `next`
    let (s1, r1) = if prev != next {
        (append_block(s, empty_block().update(0, Ptr::Index(root))), s.next)
    } else {
        (s, root)
    };
    assert(store_ok(s1, frozen));
    assert(forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, s1, x));
    if prev != next {
        let n = s.next;
        let nb = empty_block().update(0, Ptr::Index(root));
        assert forall|x: int| al_fp(s, root, prev, x) implies #[trigger] agree(s, s1, x) by {
            lemma_al_fp_stored(s, root, prev, frozen, x);
        }
        lemma_al_frame(s, s1, root, prev, frozen);
        assert forall|j: int| 0 <= j < 16 implies match #[trigger] s1.blocks[n][j] {
            Ptr::Empty => true,
            Ptr::Kv(_) => next == 0,
            Ptr::Index(q) => next > 0 && awf(s1, q, (next - 1) as nat, frozen),
        } by {
            if j != 0 {
                assert(s1.blocks[n][j] == Ptr::Empty);
            }
        }
        assert forall|j: int| 0 <= j < 16 implies !al_fp_child(s1, #[trigger] s1.blocks[n][j], (next - 1) as nat, n) by {
            if j == 0 {
                if al_fp(s1, root, prev, n) {
                    lemma_al_fp_stored(s, root, prev, frozen, n);
                }
            } else {
                assert(s1.blocks[n][j] == Ptr::Empty);
            }
        }
        assert forall|j: int, j2: int, x: int|
            0 <= j < 16 && 0 <= j2 < 16 && j != j2 && #[trigger] al_fp_child(s1, s1.blocks[n][j], (next - 1) as nat, x)
                && #[trigger] al_fp_child(s1, s1.blocks[n][j2], (next - 1) as nat, x) implies x < frozen by {
            if j != 0 {
                assert(s1.blocks[n][j] == Ptr::Empty);
            } else {
                assert(s1.blocks[n][j2] == Ptr::Empty);
            }
        }
        assert(awf(s1, n, next, frozen));
    }
    assert forall|k: int| 0 <= k < size implies #[trigger] al_lookup(s1, r1, k, next) == Some(vals[k]) by {
        assert(al_lookup(s, root, k, prev) == Some(vals[k]));
        if prev != next {
            lemma_log16_bounds(k, prev);
            lemma_log16_bounds(size - 1, prev);
            lemma_pow16_pos(next);
            lemma_basic_div(k, pow16(next) as int);
            assert(digit(k, next) == 0);
            assert(al_lookup(s1, root, k, prev) == al_lookup(s, root, k, prev));
        }
    }
    assert(t == al_set(s1, r1, size, next, v, frozen));
    lemma_al_set(s1, r1, size, next, v, frozen);
    assert forall|k: int| 0 <= k < vals2.len() implies #[trigger] al_lookup(t, r, k, next) == Some(vals2[k]) by {
        if k < size {
            lemma_log16_bounds(size, next);
            lemma_log16_bounds(k, next);
            if size >= 1 {
                lemma_log16_bounds(size - 1, next);
            }
            if forall|j: nat| j <= next ==> #[trigger] digit(k, j) == digit(size, j) {
                lemma_slots_determine_key(k, size, next);
            }
            let j = choose|j: nat| !(j <= next ==> #[trigger] digit(k, j) == digit(size, j));
            assert(differs_upto(k, size, next));
        }
    }
    assert forall|x: int| 0 <= x < frozen implies #[trigger] agree(s, t, x) by {
        assert(agree(s, s1, x));
        assert(agree(s1, t, x));
    }
}

/// Following slot 0 down from a block whose slot-0 chain holds key 0.
proof fn lemma_descend(s: Store, pos: int, sh: nat, d: nat, frozen: int)
    requires
        awf(s, pos, sh, frozen),
        d <= sh,
        al_lookup(s, pos, 0, sh) is Some,
    ensures
        awf(s, descend(s, pos, d), (sh - d) as nat, frozen),
        forall|k: int| k >= 0 && (forall|j: nat| (sh - d) < j <= sh ==> #[trigger] digit(k, j) == 0) ==> #[trigger] al_lookup(s, descend(s, pos, d), k, (sh - d) as nat) == al_lookup(s, pos, k, sh),
        al_lookup(s, descend(s, pos, d), 0, (sh - d) as nat) is Some,
        pos < frozen ==> descend(s, pos, d) < frozen,
    decreases d,
{
    if d > 0 {
        lemma_pow16_pos(sh);
        lemma_basic_div(0, pow16(sh) as int);
        assert(digit(0, sh) == 0);
        let p = s.blocks[pos][0];
        lemma_slot_ok(s, pos, sh, frozen, 0);
        assert(p is Index);
        let q = index_pos(p);
        lemma_descend(s, q, (sh - 1) as nat, (d - 1) as nat, frozen);
        assert forall|k: int| k >= 0 && (forall|j: nat| (sh - d) < j <= sh ==> #[trigger] digit(k, j) == 0) implies #[trigger] al_lookup(s, descend(s, pos, d), k, (sh - d) as nat) == al_lookup(s, pos, k, sh) by {
            assert(digit(k, sh) == 0);
            assert(forall|j: nat| ((sh - 1) as nat - (d - 1) as nat) < j <= (sh - 1) as nat ==> #[trigger] digit(k, j) == 0);
        }
    }
}

/// Slicing a list keeps the first `size` values and touches no committed
/// position.
pub proof fn theorem_slice(s: Store, root: int, vals: Seq<int>, size: int, frozen: int)
    requires
        store_ok(s, frozen),
        list_holds(s, root, vals, frozen),
        0 <= size <= vals.len(),
    ensures
        ({
            let (t, r) = al_slice(s, root, vals.len() as int, size, frozen);
            &&& store_ok(t, frozen)
            &&& r >= frozen
            &&& list_holds(t, r, vals.subrange(0, size), frozen)
            &&& forall|x: int| 0 <= x < frozen ==> #[trigger] agree(s, t, x)
        }),
{
    let old = vals.len() as int;
    let p = log16(old - 1);
    let q = log16(size - 1);
    let sub = vals.subrange(0, size);
    if size >= 1 {
        lemma_log16_bounds(size - 1, q);
        lemma_log16_bounds(old - 1, p);
        if q > p {
            lemma_log16_bounds(size - 1, p);
        }
    }
    let d = (p - q) as nat;
    let r0 = descend(s, root, d);
    // r0 holds the first `size` values at shift q
    if p == q {
        assert(r0 == root);
        assert forall|k: int| 0 <= k < sub.len() implies #[trigger] al_lookup(s, r0, k, q) == Some(sub[k]) by {
            assert(al_lookup(s, root, k, p) == Some(vals[k]));
        }
    } else {
        assert(q < p);
        assert(old >= 2) by {
            if old <= 1 {
                assert(p == 0);
            }
        }
        assert(al_lookup(s, root, 0, p) == Some(vals[0]));
        lemma_descend(s, root, p, d, frozen);
        assert((p - d) as nat == q);
        assert forall|k: int| 0 <= k < sub.len() implies #[trigger] al_lookup(s, r0, k, q) == Some(sub[k]) by {
            lemma_log16_bounds(k, q);
            lemma_log16_bounds(size - 1, q);
            assert forall|j: nat| q < j <= p implies #[trigger] digit(k, j) == 0 by {
                crate::array_list::lemma_pow16_mono(q + 1, j);
                lemma_pow16_pos(j);
                lemma_basic_div(k, pow16(j) as int);
            }
            assert(al_lookup(s, root, k, p) == Some(vals[k]));
        }
    }
    if p != q {
        assert(awf(s, r0, q, frozen));
    }
    if r0 < frozen {
        let t = append_block(s, s.blocks[r0]);
        assert forall|x: int| 0 <= x < frozen implies #[trigger] agree(s, t, x) by {}
        lemma_al_copy_frozen(s, t, r0, s.next, q, frozen);
    }
}

/// History: in one transaction, appending a moment to a history list and
/// then any `put` into a hash map leaves every moment committed before the
/// transaction readable exactly as it was, along with every committed hash
/// map. (`theorem_append` and `hamt::theorem_put`/`theorem_remove` each keep
/// the committed positions; this composes them.)
pub proof fn theorem_history(
    s: Store,
    hist: int,
    moments: Seq<int>,
    v: int,
    map_root: int,
    h: Seq<u8>,
    val: int,
    frozen: int,
    len: int,
    old_hist: int,
    old_moments: Seq<int>,
    old_map: int,
)
    requires
        store_ok(s, frozen),
        list_holds(s, hist, moments, frozen),
        hist >= frozen,
        // a committed history and a committed map
        list_holds(s, old_hist, old_moments, frozen),
        old_hist < frozen,
        crate::hamt::wf(s, old_map, 0, Seq::empty(), frozen, len),
        old_map < frozen,
        // the hash map being edited, rooted in this transaction
        h.len() == len,
    ensures
        ({
            let (t1, _) = al_append(s, hist, moments.len() as int, v, frozen);
            &&& list_holds(t1, old_hist, old_moments, frozen)
            &&& crate::hamt::contents(t1, old_map, len) == crate::hamt::contents(s, old_map, len)
            &&& (crate::hamt::wf(t1, map_root, 0, Seq::empty(), frozen, len) && map_root >= frozen) ==> {
                let t2 = crate::hamt::put(t1, map_root, h, val, 0, frozen, len).unwrap();
                &&& list_holds(t2, old_hist, old_moments, frozen)
                &&& crate::hamt::contents(t2, old_map, len) == crate::hamt::contents(s, old_map, len)
            }
        }),
{
    theorem_append(s, hist, moments, v, frozen);
    let (t1, _) = al_append(s, hist, moments.len() as int, v, frozen);
    let sh = log16(old_moments.len() - 1);
    lemma_list_snapshot_unchanged(s, t1, old_hist, sh, frozen);
    crate::hamt::lemma_snapshot_unchanged(s, t1, old_map, frozen, len);
    if crate::hamt::wf(t1, map_root, 0, Seq::empty(), frozen, len) && map_root >= frozen {
        crate::hamt::theorem_put(t1, map_root, h, val, frozen, len);
        let t2 = crate::hamt::put(t1, map_root, h, val, 0, frozen, len).unwrap();
        assert forall|x: int| 0 <= x < frozen implies #[trigger] agree(s, t2, x) by {
            assert(agree(s, t1, x));
            assert(agree(t1, t2, x));
        }
        lemma_list_snapshot_unchanged(s, t2, old_hist, sh, frozen);
        crate::hamt::lemma_snapshot_unchanged(s, t2, old_map, frozen, len);
    }
}

} // verus!
