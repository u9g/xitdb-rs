//! Big-endian integer encoding, with its specification and round-trip
//! proofs (checked by Verus).

use vstd::prelude::*;

verus! {

// big-endian integers

pub open spec fn be_u64_spec(b: Seq<u8>) -> u64 {
    ((b[0] as u64) << 56u64) | ((b[1] as u64) << 48u64) | ((b[2] as u64) << 40u64) | ((b[3] as u64)
        << 32u64) | ((b[4] as u64) << 24u64) | ((b[5] as u64) << 16u64) | ((b[6] as u64) << 8u64)
        | (b[7] as u64)
}

pub open spec fn u64_be_spec(x: u64) -> Seq<u8> {
    seq![
        (x >> 56u64) as u8,
        (x >> 48u64) as u8,
        (x >> 40u64) as u8,
        (x >> 32u64) as u8,
        (x >> 24u64) as u8,
        (x >> 16u64) as u8,
        (x >> 8u64) as u8,
        x as u8,
    ]
}

pub proof fn lemma_u64_bytes(x: u64)
    by (bit_vector)
    ensures
        ((((x >> 56u64) as u8) as u64) << 56u64) | ((((x >> 48u64) as u8) as u64) << 48u64) | ((((x
            >> 40u64) as u8) as u64) << 40u64) | ((((x >> 32u64) as u8) as u64) << 32u64) | ((((x
            >> 24u64) as u8) as u64) << 24u64) | ((((x >> 16u64) as u8) as u64) << 16u64) | ((((x
            >> 8u64) as u8) as u64) << 8u64) | ((x as u8) as u64) == x,
{
}

pub proof fn lemma_bytes_u64(b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8)
    by (bit_vector)
    ensures
        ({
            let x = ((b0 as u64) << 56u64) | ((b1 as u64) << 48u64) | ((b2 as u64) << 40u64) | ((
            b3 as u64) << 32u64) | ((b4 as u64) << 24u64) | ((b5 as u64) << 16u64) | ((b6 as u64)
                << 8u64) | (b7 as u64);
            &&& (x >> 56u64) as u8 == b0
            &&& (x >> 48u64) as u8 == b1
            &&& (x >> 40u64) as u8 == b2
            &&& (x >> 32u64) as u8 == b3
            &&& (x >> 24u64) as u8 == b4
            &&& (x >> 16u64) as u8 == b5
            &&& (x >> 8u64) as u8 == b6
            &&& x as u8 == b7
        }),
{
}

/// `u64::from_be_bytes(..)` of `u64::to_be_bytes(x)` is `x`.
pub proof fn lemma_be_u64_roundtrip(x: u64)
    ensures
        u64_be_spec(x).len() == 8,
        be_u64_spec(u64_be_spec(x)) == x,
{
    lemma_u64_bytes(x);
}

/// `u64::to_be_bytes(..)` of `u64::from_be_bytes(b)` is `b`.
pub proof fn lemma_u64_be_roundtrip(b: Seq<u8>)
    requires
        b.len() == 8,
    ensures
        u64_be_spec(be_u64_spec(b)) == b,
{
    lemma_bytes_u64(b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]);
    assert(u64_be_spec(be_u64_spec(b)) =~= b);
}

/// Two's complement reinterpretation, as `x as u64` / `x as i64` do.
pub open spec fn i2u(x: i64) -> u64 {
    #[verifier::truncate]
    (x as u64)
}

pub open spec fn u2i(x: u64) -> i64 {
    #[verifier::truncate]
    (x as i64)
}

pub proof fn lemma_i2u_bv(x: i64)
    by (bit_vector)
    ensures
        (#[verifier::truncate] ((#[verifier::truncate] (x as u64)) as i64)) == x,
{
}

pub proof fn lemma_u2i_bv(x: u64)
    by (bit_vector)
    ensures
        (#[verifier::truncate] ((#[verifier::truncate] (x as i64)) as u64)) == x,
{
}

pub proof fn lemma_i64_u64_roundtrip(x: i64, y: u64)
    ensures
        u2i(i2u(x)) == x,
        i2u(u2i(y)) == y,
{
    lemma_i2u_bv(x);
    lemma_u2i_bv(y);
}

pub fn u64_to_be_bytes(x: u64) -> (r: [u8; 8])
    ensures
        r@ == u64_be_spec(x),
{
    let r = [
        (x >> 56) as u8,
        (x >> 48) as u8,
        (x >> 40) as u8,
        (x >> 32) as u8,
        (x >> 24) as u8,
        (x >> 16) as u8,
        (x >> 8) as u8,
        x as u8,
    ];
    assert(r@ =~= u64_be_spec(x));
    r
}

pub fn u64_from_be_bytes(b: &[u8]) -> (r: u64)
    requires
        b@.len() == 8,
    ensures
        r == be_u64_spec(b@),
{
    ((b[0] as u64) << 56) | ((b[1] as u64) << 48) | ((b[2] as u64) << 40) | ((b[3] as u64) << 32)
        | ((b[4] as u64) << 24) | ((b[5] as u64) << 16) | ((b[6] as u64) << 8) | (b[7] as u64)
}

pub open spec fn be_u16_spec(b: Seq<u8>) -> u16 {
    ((b[0] as u16) << 8u16) | (b[1] as u16)
}

pub open spec fn u16_be_spec(x: u16) -> Seq<u8> {
    seq![(x >> 8u16) as u8, x as u8]
}

pub proof fn lemma_u16_bytes(x: u16)
    by (bit_vector)
    ensures
        ((((x >> 8u16) as u8) as u16) << 8u16) | ((x as u8) as u16) == x,
{
}

pub proof fn lemma_bytes_u16(b0: u8, b1: u8)
    by (bit_vector)
    ensures
        ((((b0 as u16) << 8u16) | (b1 as u16)) >> 8u16) as u8 == b0,
        (((b0 as u16) << 8u16) | (b1 as u16)) as u8 == b1,
{
}

pub open spec fn be_u32_spec(b: Seq<u8>) -> u32 {
    ((b[0] as u32) << 24u32) | ((b[1] as u32) << 16u32) | ((b[2] as u32) << 8u32) | (b[3] as u32)
}

pub open spec fn u32_be_spec(x: u32) -> Seq<u8> {
    seq![(x >> 24u32) as u8, (x >> 16u32) as u8, (x >> 8u32) as u8, x as u8]
}

pub proof fn lemma_u32_bytes(x: u32)
    by (bit_vector)
    ensures
        ((((x >> 24u32) as u8) as u32) << 24u32) | ((((x >> 16u32) as u8) as u32) << 16u32) | ((((x
            >> 8u32) as u8) as u32) << 8u32) | ((x as u8) as u32) == x,
{
}

pub proof fn lemma_bytes_u32(b0: u8, b1: u8, b2: u8, b3: u8)
    by (bit_vector)
    ensures
        ({
            let x = ((b0 as u32) << 24u32) | ((b1 as u32) << 16u32) | ((b2 as u32) << 8u32) | (
            b3 as u32);
            &&& (x >> 24u32) as u8 == b0
            &&& (x >> 16u32) as u8 == b1
            &&& (x >> 8u32) as u8 == b2
            &&& x as u8 == b3
        }),
{
}

} // verus!
