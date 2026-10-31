//! `src/crc64.rs`: the table-driven CRC computes CRC-64/XZ as defined bit
//! by bit (the reflected ECMA-182 polynomial, all-ones init and xorout).
//!
//! The table construction and `checksum` are executable functions with the
//! same loops as the crate's, verified against the bitwise definition, and
//! the standard check value is evaluated from the definition.

use vstd::prelude::*;

verus! {

pub const POLY: u64 = 0xC96C_5795_D787_0F42;

/// One bit of the reflected CRC.
pub open spec fn step(c: u64) -> u64 {
    if c & 1u64 == 1u64 {
        (c >> 1u64) ^ 0xC96C5795D7870F42u64
    } else {
        c >> 1u64
    }
}

pub open spec fn steps(c: u64, n: nat) -> u64
    decreases n,
{
    if n == 0 {
        c
    } else {
        steps(step(c), (n - 1) as nat)
    }
}

/// The CRC register after `data`, one bit at a time.
pub open spec fn crc_bits(crc: u64, data: Seq<u8>) -> u64
    decreases data.len(),
{
    if data.len() == 0 {
        crc
    } else {
        crc_bits(steps(crc ^ (data[0] as u64), 8), data.drop_first())
    }
}

/// CRC-64/XZ of `data`.
pub open spec fn crc64_spec(data: Seq<u8>) -> u64 {
    !crc_bits(!0u64, data)
}

/// `TABLE[i]`.
pub open spec fn table(i: u64) -> u64 {
    steps(i, 8)
}

/// The register after `data`, a byte at a time through the table, as
/// `checksum` computes it.
pub open spec fn crc_table(crc: u64, data: Seq<u8>) -> u64
    decreases data.len(),
{
    if data.len() == 0 {
        crc
    } else {
        crc_table(table((crc ^ (data[0] as u64)) & 0xffu64) ^ (crc >> 8u64), data.drop_first())
    }
}

proof fn lemma_step_xor(x: u64, y: u64)
    by (bit_vector)
    ensures
        (if (x ^ y) & 1u64 == 1u64 { ((x ^ y) >> 1u64) ^ 0xC96C5795D7870F42u64 } else { (x ^ y) >> 1u64 }) == (if x
            & 1u64 == 1u64 { (x >> 1u64) ^ 0xC96C5795D7870F42u64 } else { x >> 1u64 }) ^ (if y & 1u64 == 1u64 {
            (y >> 1u64) ^ 0xC96C5795D7870F42u64
        } else {
            y >> 1u64
        }),
{
}

/// The CRC is linear: `steps(x ^ y) == steps(x) ^ steps(y)`.
proof fn lemma_steps_xor(x: u64, y: u64, n: nat)
    ensures
        steps(x ^ y, n) == steps(x, n) ^ steps(y, n),
    decreases n,
{
    if n > 0 {
        lemma_step_xor(x, y);
        lemma_steps_xor(step(x), step(y), (n - 1) as nat);
    }
}

proof fn lemma_step_even(z: u64)
    by (bit_vector)
    requires
        z & 1u64 == 0u64,
    ensures
        (if z & 1u64 == 1u64 { (z >> 1u64) ^ 0xC96C5795D7870F42u64 } else { z >> 1u64 }) == z >> 1u64,
{
}

/// With its low `n` bits clear, `n` steps just shift.
proof fn lemma_steps_shift(z: u64, n: nat)
    requires
        n <= 8,
        z & 0xffu64 == 0u64 || n == 0,
    ensures
        steps(z, n) == z >> (n as u64),
{
    let zero = 0nat as u64;
    assert(z >> zero == z) by (bit_vector)
        requires
            zero == 0u64,
    ;
    if n > 0 {
        assert(z & 1u64 == 0u64) by (bit_vector)
            requires
                z & 0xffu64 == 0u64,
        ;
        assert forall|k: u64| k < 8 implies #[trigger] step(z >> k) == (z >> k) >> 1u64 by {
            assert((z >> k) & 1u64 == 0u64) by (bit_vector)
                requires
                    z & 0xffu64 == 0u64,
                    k < 8,
            ;
            lemma_step_even(z >> k);
        }
        lemma_steps_shift_from(z, 0, n);
        let zero = 0nat as u64;
        assert(zero == 0u64);
        assert(z >> zero == z) by (bit_vector)
            requires
                zero == 0u64,
        ;
        assert((n - 0) as nat == n);
    }
}

proof fn lemma_steps_shift_from(z: u64, k: nat, n: nat)
    requires
        k <= n <= 8,
        forall|k: u64| k < 8 ==> #[trigger] step(z >> k) == (z >> k) >> 1u64,
    ensures
        steps(z >> (k as u64), (n - k) as nat) == z >> (n as u64),
    decreases n - k,
{
    if k < n {
        let kk = k as u64;
        let k1 = (k + 1) as u64;
        assert((z >> kk) >> 1u64 == z >> k1) by (bit_vector)
            requires
                kk < 8,
                k1 == kk + 1,
        ;
        lemma_steps_shift_from(z, k + 1, n);
    }
}

/// One byte through the table is eight bits of the definition.
pub proof fn lemma_table_byte(crc: u64, b: u8)
    ensures
        table((crc ^ (b as u64)) & 0xffu64) ^ (crc >> 8u64) == steps(crc ^ (b as u64), 8),
{
    let x = crc ^ (b as u64);
    let lo = x & 0xffu64;
    let hi = x & !0xffu64;
    assert(x == lo ^ hi) by (bit_vector)
        requires
            lo == x & 0xffu64,
            hi == x & !0xffu64,
    ;
    assert(hi & 0xffu64 == 0u64) by (bit_vector)
        requires
            hi == x & !0xffu64,
    ;
    assert(hi >> 8u64 == crc >> 8u64) by (bit_vector)
        requires
            hi == (crc ^ (b as u64)) & !0xffu64,
    ;
    lemma_steps_xor(lo, hi, 8);
    lemma_steps_shift(hi, 8);
}

/// The table-driven CRC is the bitwise CRC.
pub proof fn theorem_crc_table(crc: u64, data: Seq<u8>)
    ensures
        crc_table(crc, data) == crc_bits(crc, data),
    decreases data.len(),
{
    if data.len() > 0 {
        lemma_table_byte(crc, data[0]);
        theorem_crc_table(steps(crc ^ (data[0] as u64), 8), data.drop_first());
    }
}

/// The standard check value of CRC-64/XZ.
pub proof fn lemma_check_value()
    ensures
        crc64_spec(seq![0x31u8, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) == 0x995D_C9BB_DF19_39FAu64,
{
    assert(crc64_spec(seq![0x31u8, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) == 0x995D_C9BB_DF19_39FAu64) by (compute);
}

// the crate's loops

/// The inner loop of the `TABLE` initializer.
pub fn table_entry(i: u64) -> (r: u64)
    ensures
        r == table(i),
{
    let mut crc = i;
    let mut bit: u64 = 0;
    while bit < 8
        invariant
            bit <= 8,
            steps(crc, (8 - bit) as nat) == table(i),
        decreases 8 - bit,
    {
        crc = if crc & 1 == 1 {
            (crc >> 1) ^ POLY
        } else {
            crc >> 1
        };
        bit += 1;
    }
    crc
}

/// The `TABLE` initializer.
pub fn make_table() -> (t: Vec<u64>)
    ensures
        t@.len() == 256,
        forall|i: int| 0 <= i < 256 ==> #[trigger] t@[i] == table(i as u64),
{
    let mut t: Vec<u64> = Vec::new();
    let mut i: u64 = 0;
    while i < 256
        invariant
            i <= 256,
            t@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] t@[j] == table(j as u64),
        decreases 256 - i,
    {
        t.push(table_entry(i));
        i += 1;
    }
    t
}

/// `checksum`, given the table.
pub fn checksum(t: &Vec<u64>, data: &[u8]) -> (r: u64)
    requires
        t@.len() == 256,
        forall|i: int| 0 <= i < 256 ==> #[trigger] t@[i] == table(i as u64),
    ensures
        r == crc64_spec(data@),
{
    let mut crc: u64 = !0u64;
    let mut n: usize = 0;
    assert(data@.subrange(0, data@.len() as int) =~= data@);
    while n < data.len()
        invariant
            n <= data@.len(),
            t@.len() == 256,
            forall|i: int| 0 <= i < 256 ==> #[trigger] t@[i] == table(i as u64),
            crc_table(crc, data@.subrange(n as int, data@.len() as int)) == crc_table(!0u64, data@),
        decreases data.len() - n,
    {
        let byte = data[n];
        let idx = ((crc ^ byte as u64) & 0xff) as usize;
        proof {
            assert(((crc ^ byte as u64) & 0xffu64) < 256) by (bit_vector);
            let rest = data@.subrange(n as int, data@.len() as int);
            assert(rest[0] == byte);
            assert(rest.drop_first() =~= data@.subrange(n as int + 1, data@.len() as int));
        }
        crc = t[idx] ^ (crc >> 8);
        n += 1;
    }
    proof {
        assert(data@.subrange(n as int, data@.len() as int) =~= Seq::<u8>::empty());
        theorem_crc_table(!0u64, data@);
    }
    !crc
}

} // verus!
