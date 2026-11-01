//! Arithmetic about the array list's 16-way index: `log16`, nibbles of a
//! key, and `leading_zeros` (checked by Verus).

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::bits::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power2::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::*;

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

pub proof fn lemma_pow16_pos(n: nat)
    ensures
        pow16(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow16_pos((n - 1) as nat);
    }
}

pub proof fn lemma_pow16_pow2(n: nat)
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
pub proof fn lemma_log16_lower(k: int)
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

pub proof fn lemma_log16_pow16(n: nat)
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

pub proof fn lemma_log2_div16(k: int)
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

pub proof fn lemma_log2_log16(k: int)
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
pub proof fn lemma_leading_zeros(x: u64)
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

} // verus!
