//! The index arithmetic of the array list in `src/database.rs` and
//! `src/format.rs` (`array_list_shift`, `read_array_list_slot`,
//! `read_array_list_slot_append` and `resolve_index`).
//!
//! An array list is a tree of index blocks of 16 slots whose leaves are the
//! items. A root with shift `s` holds keys below 16^(s+1), and key `k` is
//! found by taking nibble `s`, then `s - 1`, ..., then 0 of `k` as slot
//! numbers. These lemmas show that this addresses every item in its own
//! slot, that the shift never reaches `MAX_BRANCH_LENGTH` (so
//! `MaxShiftExceeded` is unreachable), and that appending moves the old
//! root to slot 0 of a new root exactly when it is full, which is where
//! every existing key expects it.

use vstd::prelude::*;
use vstd::std_specs::bits::*;
use vstd::arithmetic::power2::*;
use vstd::arithmetic::div_mod::*;
use vstd::bits::*;

verus! {

pub open spec fn pow16(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        16 * pow16((n - 1) as nat)
    }
}

/// The integer log16 of `k`, or 0 if `k < 16`.
pub open spec fn log16(k: int) -> nat
    decreases k,
{
    if k < 16 {
        0
    } else {
        1 + log16(k / 16)
    }
}

/// Nibble `j` of `k`: the slot key `k` takes at shift `j`.
pub open spec fn digit(k: int, j: nat) -> int {
    (k / pow16(j) as int) % 16
}

pub open spec fn log2(k: int) -> nat
    decreases k,
{
    if k < 2 {
        0
    } else {
        1 + log2(k / 2)
    }
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

proof fn lemma_pow16_pow2(n: nat)
    ensures
        pow16(n) == pow2(4 * n),
    decreases n,
{
    lemma2_to64();
    if n > 0 {
        lemma_pow16_pow2((n - 1) as nat);
        lemma_pow2_adds((4 * (n - 1)) as nat, 4);
        assert((4 * (n - 1)) as nat + 4 == 4 * n);
    }
}

/// `k < 16^(n+1)` exactly when `log16(k) <= n`.
pub proof fn lemma_log16_bounds(k: int, n: nat)
    requires
        k >= 0,
    ensures
        k < pow16(n + 1) <==> log16(k) <= n,
    decreases n,
{
    reveal_with_fuel(pow16, 2);
    if n == 0 {
        if k >= 16 {
            assert(log16(k) >= 1);
        }
    } else if k >= 16 {
        lemma_log16_bounds(k / 16, (n - 1) as nat);
        lemma_pow16_pos(n);
        lemma_fundamental_div_mod(k, 16);
        assert(pow16(n + 1) == 16 * pow16(n));
        assert(k / 16 < pow16(n) <==> k < 16 * pow16(n)) by {
            if k / 16 < pow16(n) {
                assert(k < 16 * pow16(n)) by (nonlinear_arith)
                    requires
                        k == 16 * (k / 16) + k % 16,
                        k % 16 < 16,
                        k / 16 < pow16(n),
                ;
            } else {
                assert(k >= 16 * pow16(n)) by (nonlinear_arith)
                    requires
                        k == 16 * (k / 16) + k % 16,
                        k % 16 >= 0,
                        k / 16 >= pow16(n),
                ;
            }
        }
    } else {
        lemma_pow16_pos(n);
        assert(pow16(n + 1) == 16 * pow16(n));
    }
}

/// `16^log16(k) <= k` for `k >= 1`.
proof fn lemma_log16_lower(k: int)
    requires
        k >= 1,
    ensures
        pow16(log16(k)) <= k,
    decreases k,
{
    if k >= 16 {
        lemma_log16_lower(k / 16);
        lemma_fundamental_div_mod(k, 16);
        assert(pow16(log16(k)) == 16 * pow16(log16(k / 16)));
    }
}

proof fn lemma_log16_pow16(n: nat)
    ensures
        log16(pow16(n) as int) == n,
    decreases n,
{
    if n > 0 {
        lemma_log16_pow16((n - 1) as nat);
        lemma_pow16_pos((n - 1) as nat);
        assert((16 * pow16((n - 1) as nat)) / 16 == pow16((n - 1) as nat));
    }
}

proof fn lemma_log2_div16(k: int)
    requires
        k >= 16,
    ensures
        log2(k) == 4 + log2(k / 16),
{
    lemma_div_denominator(k, 2, 2);
    lemma_div_denominator(k / 4, 2, 2);
    lemma_div_denominator(k, 4, 4);
    assert(k / 2 / 2 == k / 4);
    assert(k / 4 / 2 / 2 == k / 16);
    assert(k / 2 / 2 / 2 / 2 == k / 16);
    assert(log2(k) == 1 + log2(k / 2));
    assert(log2(k / 2) == 1 + log2(k / 2 / 2));
    assert(log2(k / 2 / 2) == 1 + log2(k / 2 / 2 / 2));
    assert(log2(k / 2 / 2 / 2) == 1 + log2(k / 2 / 2 / 2 / 2));
}

proof fn lemma_log2_log16(k: int)
    requires
        k >= 1,
    ensures
        log2(k) / 4 == log16(k),
    decreases k,
{
    if k < 16 {
        reveal_with_fuel(log2, 5);
        assert(log2(k) < 4);
    } else {
        lemma_log2_div16(k);
        lemma_log2_log16(k / 16);
    }
}

/// `leading_zeros` is 63 minus the integer log2.
proof fn lemma_leading_zeros(x: u64)
    requires
        x >= 1,
    ensures
        u64_leading_zeros(x) == 63 - log2(x as int),
    decreases x,
{
    reveal(u64_leading_zeros);
    if x >= 2 {
        lemma_leading_zeros(x / 2);
    } else {
        assert(u64_leading_zeros(0) == 64);
    }
}

/// `array_list_shift`: the shift of the root of an array list whose last
/// key is `key`, which is `log16(key)`.
pub fn array_list_shift(key: i64) -> (r: u8)
    ensures
        r as nat == log16(key as int),
        r < 16,
{
    if key < 16 {
        0
    } else {
        let lz = (key as u64).leading_zeros();
        proof {
            lemma_leading_zeros(key as u64);
            lemma_log2_log16(key as int);
            lemma_log16_bounds(key as int, 15);
            lemma_pow16_pow2(16);
            lemma2_to64_rest();
        }
        ((63 - lz) / 4) as u8
    }
}

/// `MaxShiftExceeded` can't happen: every `i64` key has a shift below
/// `MAX_BRANCH_LENGTH` (16).
pub proof fn lemma_shift_bounded(key: i64)
    ensures
        log16(key as int) < 16,
{
    if key >= 0 {
        lemma_log16_bounds(key as int, 15);
        lemma_pow16_pow2(16);
        lemma2_to64_rest();
    }
}

/// `(key >> (shift * BIT_COUNT)) & MASK`, the slot of `key` at `shift`.
pub fn array_list_slot(key: i64, shift: u8) -> (r: i64)
    requires
        key >= 0,
        shift < 16,
    ensures
        r == digit(key as int, shift as nat),
        0 <= r < 16,
{
    let k = key as u64;
    let n = shift as u64 * 4;
    let shifted = k >> n;
    let r = shifted & 15;
    proof {
        lemma_u64_shr_is_div(k, n);
        lemma_pow16_pow2(shift as nat);
        assert(shifted & 15 == shifted % 16) by (bit_vector);
    }
    r as i64
}

/// Keys below 16^(s+1) with the same slots at every shift up to `s` are
/// the same key, so no two items share a slot.
pub proof fn lemma_slots_determine_key(k1: int, k2: int, s: nat)
    requires
        0 <= k1 < pow16(s + 1),
        0 <= k2 < pow16(s + 1),
        forall|j: nat| j <= s ==> #[trigger] digit(k1, j) == digit(k2, j),
    ensures
        k1 == k2,
    decreases s,
{
    lemma_fundamental_div_mod(k1, 16);
    lemma_fundamental_div_mod(k2, 16);
    assert(pow16(0) == 1);
    assert(digit(k1, 0) == k1 % 16 && digit(k2, 0) == k2 % 16);
    if s == 0 {
        assert(pow16(1) == 16);
        assert(digit(k1, 0) == digit(k2, 0));
    } else {
        lemma_pow16_pos(s);
        assert(pow16(s + 1) == 16 * pow16(s));
        assert(k1 / 16 < pow16(s)) by {
            lemma_div_by_multiple_is_strongly_ordered(k1, pow16(s + 1) as int, pow16(s) as int, 16);
        }
        assert(k2 / 16 < pow16(s)) by {
            lemma_div_by_multiple_is_strongly_ordered(k2, pow16(s + 1) as int, pow16(s) as int, 16);
        }
        assert forall|j: nat| j <= (s - 1) as nat implies #[trigger] digit(k1 / 16, j) == digit(k2 / 16, j) by {
            lemma_pow16_pos(j);
            lemma_div_denominator(k1, 16, pow16(j) as int);
            lemma_div_denominator(k2, 16, pow16(j) as int);
            assert(pow16(j + 1) == 16 * pow16(j));
            assert(digit(k1, j + 1) == digit(k2, j + 1));
        }
        lemma_slots_determine_key(k1 / 16, k2 / 16, (s - 1) as nat);
        assert(digit(k1, 0) == digit(k2, 0));
    }
}

/// Appending key `size` (`read_array_list_slot_append`): the shift either
/// stays the same, and `size` fits under the old root, or grows by one
/// exactly when `size` is a power of 16, and then every existing key has
/// slot 0 at the new root's shift, which is where the old root goes.
pub proof fn lemma_append_shift(size: int)
    requires
        size >= 1,
    ensures
        log16(size) == log16(size - 1) ==> size < pow16(log16(size - 1) + 1),
        log16(size) != log16(size - 1) ==> {
            &&& log16(size) == log16(size - 1) + 1
            &&& size == pow16(log16(size))
            &&& forall|k: int| 0 <= k < size ==> #[trigger] digit(k, log16(size)) == 0
        },
{
    let s = log16(size - 1);
    lemma_log16_bounds(size - 1, s);
    lemma_log16_bounds(size, s);
    if size < pow16(s + 1) {
        // log16 is monotone
        if log16(size) < s {
            lemma_log16_bounds(size - 1, log16(size));
            lemma_log16_bounds(size, log16(size));
        }
    } else {
        assert(size == pow16(s + 1));
        lemma_log16_pow16(s + 1);
        assert forall|k: int| 0 <= k < size implies #[trigger] digit(k, log16(size)) == 0 by {
            lemma_pow16_pos(s + 1);
            lemma_basic_div(k, pow16(s + 1) as int);
        }
    }
}

/// `resolve_index`: a negative index counts from the end.
pub fn resolve_index(index: i64, size: i64) -> (r: Option<i64>)
    requires
        size >= 0,
    ensures
        r is None <==> !(-size <= index < size),
        r matches Some(i) ==> 0 <= i < size && i == if index < 0 {
            size + index
        } else {
            index as int
        },
{
    if index >= size || index < -size {
        return None;
    }
    Some(if index < 0 {
        size + index
    } else {
        index
    })
}

// the array list as a tree

/// A slot of an array list block: empty, a value (at shift 0), or a child
/// block (above shift 0).
pub enum ANode {
    Empty,
    Value(int),
    Index(Seq<ANode>),
}

/// The block at shift `s` is well-formed: 16 slots, holding values at
/// shift 0 and well-formed child blocks above it.
pub open spec fn awf(n: ANode, s: nat) -> bool
    decreases s,
{
    match n {
        ANode::Index(b) => {
            &&& b.len() == 16
            &&& forall|i: int| 0 <= i < 16 ==> match #[trigger] b[i] {
                ANode::Empty => true,
                ANode::Value(_) => s == 0,
                ANode::Index(_) => s > 0 && awf(b[i], (s - 1) as nat),
            }
        },
        _ => false,
    }
}

/// `read_array_list_slot` in `WriteMode::ReadOnly`, then reading the value.
pub open spec fn aget(n: ANode, key: int, s: nat) -> Option<int>
    decreases s,
{
    match n {
        ANode::Index(b) => if b.len() != 16 {
            None
        } else if s == 0 {
            match b[digit(key, 0)] {
                ANode::Value(v) => Some(v),
                _ => None,
            }
        } else {
            aget(b[digit(key, s)], key, (s - 1) as nat)
        },
        _ => None,
    }
}

pub open spec fn empty_block() -> Seq<ANode> {
    Seq::new(16, |i: int| ANode::Empty)
}

/// `read_array_list_slot` in `WriteMode::ReadWrite`, then writing `v`:
/// missing blocks on the way are created.
pub open spec fn aset(n: ANode, key: int, s: nat, v: int) -> ANode
    decreases s,
{
    match n {
        ANode::Index(b) => {
            let i = digit(key, s);
            if s == 0 {
                ANode::Index(b.update(i, ANode::Value(v)))
            } else {
                let child = match b[i] {
                    ANode::Index(_) => b[i],
                    _ => ANode::Index(empty_block()),
                };
                ANode::Index(b.update(i, aset(child, key, (s - 1) as nat, v)))
            }
        },
        _ => n,
    }
}

/// `ArrayListAppend` of `v` to a list of `size` values: a full root moves to
/// slot 0 of a new root first.
pub open spec fn append(root: ANode, size: int, v: int) -> ANode {
    let prev = log16(size - 1);
    let next = log16(size);
    let r = if prev != next {
        ANode::Index(empty_block().update(0, root))
    } else {
        root
    };
    aset(r, size, next, v)
}

/// Following slot 0 down `d` levels.
pub open spec fn descend(n: ANode, d: nat) -> ANode
    decreases d,
{
    if d == 0 {
        n
    } else {
        match n {
            ANode::Index(b) => descend(b[0], (d - 1) as nat),
            _ => n,
        }
    }
}

/// `read_array_list_slice`: the root of the first `size` values.
pub open spec fn slice(root: ANode, old_size: int, size: int) -> ANode {
    descend(root, (log16(old_size - 1) - log16(size - 1)) as nat)
}

/// The tree holds exactly `vals`, read at the root's shift.
pub open spec fn holds(root: ANode, vals: Seq<int>) -> bool {
    &&& awf(root, log16(vals.len() - 1))
    &&& forall|k: int| 0 <= k < vals.len() ==> #[trigger] aget(root, k, log16(vals.len() - 1)) == Some(vals[k])
}

proof fn lemma_digit_range(k: int, j: nat)
    requires
        k >= 0,
    ensures
        0 <= digit(k, j) < 16,
{
    lemma_pow16_pos(j);
}

/// A key below 16^(s+1) has digit 0 above shift `s`.
proof fn lemma_high_digits_zero(k: int, s: nat, j: nat)
    requires
        0 <= k < pow16(s + 1),
        j > s,
    ensures
        digit(k, j) == 0,
{
    lemma_pow16_mono(s + 1, j);
    lemma_pow16_pos(j);
    lemma_basic_div(k, pow16(j) as int);
}

pub proof fn lemma_pow16_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow16(a) <= pow16(b),
    decreases b,
{
    if b > a {
        lemma_pow16_mono(a, (b - 1) as nat);
        lemma_pow16_pos((b - 1) as nat);
    }
}

/// Writing `key` changes no key that differs from it in a digit up to `s`,
/// and makes `key` read `v`.
proof fn lemma_aset(n: ANode, key: int, s: nat, v: int)
    requires
        awf(n, s),
        key >= 0,
    ensures
        awf(aset(n, key, s, v), s),
        aget(aset(n, key, s, v), key, s) == Some(v),
        forall|k: int| k >= 0 && (exists|j: nat| j <= s && digit(k, j) != digit(key, j)) ==> #[trigger] aget(aset(n, key, s, v), k, s) == aget(n, k, s),
    decreases s,
{
    let b = n->Index_0;
    let i = digit(key, s);
    lemma_digit_range(key, s);
    if s == 0 {
        let b2 = b.update(i, ANode::Value(v));
        assert forall|j: int| 0 <= j < 16 implies match #[trigger] b2[j] {
            ANode::Empty => true,
            ANode::Value(_) => s == 0,
            ANode::Index(_) => s > 0 && awf(b2[j], (s - 1) as nat),
        } by {
            if j != i {
                assert(b2[j] == b[j]);
            }
        }
        assert forall|k: int| k >= 0 && (exists|j: nat| j <= s && digit(k, j) != digit(key, j)) implies #[trigger] aget(aset(n, key, s, v), k, s) == aget(n, k, s) by {
            lemma_digit_range(k, 0);
        }
    } else {
        let child = match b[i] {
            ANode::Index(_) => b[i],
            _ => ANode::Index(empty_block()),
        };
        assert(awf(child, (s - 1) as nat)) by {
            if !(b[i] is Index) {
                assert forall|j: int| 0 <= j < 16 implies match #[trigger] empty_block()[j] {
                    ANode::Empty => true,
                    ANode::Value(_) => (s - 1) as nat == 0,
                    ANode::Index(_) => (s - 1) as nat > 0 && awf(empty_block()[j], (s - 2) as nat),
                } by {}
            }
        }
        lemma_aset(child, key, (s - 1) as nat, v);
        let nc = aset(child, key, (s - 1) as nat, v);
        let b2 = b.update(i, nc);
        assert forall|j: int| 0 <= j < 16 implies match #[trigger] b2[j] {
            ANode::Empty => true,
            ANode::Value(_) => s == 0,
            ANode::Index(_) => s > 0 && awf(b2[j], (s - 1) as nat),
        } by {
            if j != i {
                assert(b2[j] == b[j]);
            } else {
                assert(nc is Index);
            }
        }
        assert forall|k: int| k >= 0 && (exists|j: nat| j <= s && digit(k, j) != digit(key, j)) implies #[trigger] aget(aset(n, key, s, v), k, s) == aget(n, k, s) by {
            lemma_digit_range(k, s);
            let ik = digit(k, s);
            if ik == i {
                let j = choose|j: nat| j <= s && digit(k, j) != digit(key, j);
                assert(j <= (s - 1) as nat);
                assert(exists|j: nat| j <= (s - 1) as nat && digit(k, j) != digit(key, j));
                assert(aget(nc, k, (s - 1) as nat) == aget(child, k, (s - 1) as nat));
                assert(aget(aset(n, key, s, v), k, s) == aget(nc, k, (s - 1) as nat));
                assert(aget(n, k, s) == aget(b[i], k, (s - 1) as nat));
                // an empty slot reads as nothing, before and after creating a block
                if !(b[i] is Index) {
                    lemma_aget_empty(k, (s - 1) as nat);
                }
            } else {
                assert(b2[ik] == b[ik]);
            }
        }
    }
}

/// A fresh, empty block holds nothing.
proof fn lemma_aget_empty(k: int, s: nat)
    requires
        k >= 0,
    ensures
        aget(ANode::Index(empty_block()), k, s) is None,
{
    lemma_digit_range(k, s);
    lemma_digit_range(k, 0);
    assert(empty_block()[digit(k, s)] == ANode::Empty);
    assert(empty_block()[digit(k, 0)] == ANode::Empty);
    if s > 0 {
        assert(aget(ANode::Empty, k, (s - 1) as nat) is None);
    }
}

/// Appending to a list holding `vals` gives one holding `vals.push(v)`.
pub proof fn theorem_append(root: ANode, vals: Seq<int>, v: int)
    requires
        holds(root, vals),
    ensures
        holds(append(root, vals.len() as int, v), vals.push(v)),
{
    let size = vals.len() as int;
    let prev = log16(size - 1);
    let next = log16(size);
    let vals2 = vals.push(v);
    assert(vals2.len() - 1 == size);
    let r = if prev != next { ANode::Index(empty_block().update(0, root)) } else { root };
    // r holds vals at shift next
    if size >= 1 {
        lemma_append_shift(size);
    } else {
        assert(prev == 0 && next == 0);
    }
    assert(awf(r, next)) by {
        if prev != next {
            let b = empty_block().update(0, root);
            assert forall|j: int| 0 <= j < 16 implies match #[trigger] b[j] {
                ANode::Empty => true,
                ANode::Value(_) => next == 0,
                ANode::Index(_) => next > 0 && awf(b[j], (next - 1) as nat),
            } by {
                if j != 0 {
                    assert(b[j] == ANode::Empty);
                }
            }
        }
    }
    assert forall|k: int| 0 <= k < size implies #[trigger] aget(r, k, next) == Some(vals[k]) by {
        assert(aget(root, k, prev) == Some(vals[k]));
        if prev != next {
            lemma_log16_bounds(k, prev);
            if size - 1 >= 0 {
                lemma_log16_bounds(size - 1, prev);
            }
            lemma_high_digits_zero(k, prev, next);
            let b = empty_block().update(0, root);
            assert(b[0] == root);
        }
    }
    lemma_aset(r, size, next, v);
    assert forall|k: int| 0 <= k < vals2.len() implies #[trigger] aget(append(root, size, v), k, next) == Some(vals2[k]) by {
        if k < size {
            // k and size differ in a digit up to `next`
            lemma_log16_bounds(size, next);
            lemma_log16_bounds(k, next);
            if size >= 1 {
                lemma_log16_bounds(size - 1, next);
            }
            if forall|j: nat| j <= next ==> #[trigger] digit(k, j) == digit(size, j) {
                lemma_slots_determine_key(k, size, next);
            }
            let j = choose|j: nat| !(j <= next ==> #[trigger] digit(k, j) == digit(size, j));
            assert(j <= next && digit(k, j) != digit(size, j));
        }
    }
}

/// Following slot 0 down from a block whose slot-0 chain holds key 0.
proof fn lemma_descend(n: ANode, s: nat, d: nat)
    requires
        awf(n, s),
        d <= s,
        aget(n, 0, s) is Some,
    ensures
        awf(descend(n, d), (s - d) as nat),
        forall|k: int| k >= 0 && (forall|j: nat| (s - d) < j <= s ==> #[trigger] digit(k, j) == 0) ==> #[trigger] aget(descend(n, d), k, (s - d) as nat) == aget(n, k, s),
        aget(descend(n, d), 0, (s - d) as nat) is Some,
    decreases d,
{
    if d > 0 {
        let b = n->Index_0;
        lemma_pow16_pos(s);
        lemma_basic_div(0, pow16(s) as int);
        assert(digit(0, s) == 0);
        assert(aget(n, 0, s) == aget(b[0], 0, (s - 1) as nat));
        assert(b[0] is Index);
        assert(awf(b[0], (s - 1) as nat));
        lemma_descend(b[0], (s - 1) as nat, (d - 1) as nat);
        assert forall|k: int| k >= 0 && (forall|j: nat| (s - d) < j <= s ==> #[trigger] digit(k, j) == 0) implies #[trigger] aget(descend(n, d), k, (s - d) as nat) == aget(n, k, s) by {
            assert(digit(k, s) == 0);
            assert(forall|j: nat| ((s - 1) as nat - (d - 1) as nat) < j <= (s - 1) as nat ==> #[trigger] digit(k, j) == 0);
        }
    }
}

/// Slicing a list holding `vals` to `size` values gives one holding the
/// first `size` of them.
pub proof fn theorem_slice(root: ANode, vals: Seq<int>, size: int)
    requires
        holds(root, vals),
        0 <= size <= vals.len(),
    ensures
        holds(slice(root, vals.len() as int, size), vals.subrange(0, size)),
{
    let old = vals.len() as int;
    let p = log16(old - 1);
    let q = log16(size - 1);
    let sub = vals.subrange(0, size);
    // the new shift is at most the old one
    if size >= 1 {
        lemma_log16_bounds(size - 1, q);
        lemma_log16_bounds(old - 1, p);
        if q > p {
            lemma_log16_bounds(size - 1, p);
        }
    }
    if p == q {
        assert(slice(root, old, size) == root);
        assert forall|k: int| 0 <= k < sub.len() implies #[trigger] aget(root, k, q) == Some(sub[k]) by {
            assert(aget(root, k, p) == Some(vals[k]));
        }
    } else {
        assert(q < p);
        assert(old >= 2) by {
            if old <= 1 {
                assert(p == 0);
            }
        }
        assert(aget(root, 0, p) == Some(vals[0]));
        lemma_descend(root, p, (p - q) as nat);
        assert((p - (p - q) as nat) as nat == q);
        assert forall|k: int| 0 <= k < sub.len() implies #[trigger] aget(slice(root, old, size), k, q) == Some(sub[k]) by {
            lemma_log16_bounds(k, q);
            lemma_log16_bounds(size - 1, q);
            assert forall|j: nat| q < j <= p implies #[trigger] digit(k, j) == 0 by {
                lemma_high_digits_zero(k, q, j);
            }
            assert(aget(root, k, p) == Some(vals[k]));
        }
    }
}

/// An empty list (`ArrayListInit`) is an empty block.
pub proof fn lemma_empty_array_list()
    ensures
        holds(ANode::Index(empty_block()), Seq::empty()),
{
    let b = empty_block();
    assert forall|j: int| 0 <= j < 16 implies match #[trigger] b[j] {
        ANode::Empty => true,
        ANode::Value(_) => log16(-1) == 0,
        ANode::Index(_) => log16(-1) > 0 && awf(b[j], (log16(-1) - 1) as nat),
    } by {}
}

/// Reading a key the list holds gives its value.
pub proof fn lemma_array_list_get(root: ANode, vals: Seq<int>, k: int)
    requires
        holds(root, vals),
        0 <= k < vals.len(),
    ensures
        aget(root, k, log16(vals.len() - 1)) == Some(vals[k]),
{
}

} // verus!
