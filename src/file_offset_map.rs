use crate::collections::WriteHashMap;
use crate::compact::OffsetMap;
use crate::core::Core;
use crate::cursor::WriteCursor;
use crate::data::Data;
use crate::error::{Error, Result};
use vstd::prelude::*;

/// Stores compaction offsets in a hash map in a separate scratch database
/// (typically a temporary file), without retaining the mappings in memory.
///
/// Create it with the cursor that [`Database::run_context`](crate::Database::run_context)
/// gives you on the scratch database, and run the compaction inside that
/// same transaction, so the offsets aren't each committed separately. The
/// scratch database's hash size must be at least 8 bytes.
pub struct FileOffsetMap<'a, C: Core> {
    map: WriteHashMap<'a, C>,
}

impl<'a, C: Core> FileOffsetMap<'a, C> {
    pub fn new(cursor: &mut WriteCursor<'a, C>) -> Result<Self> {
        if cursor.db.hash_size() < 8 {
            return Err(Error::InvalidHashSize);
        }
        Ok(FileOffsetMap { map: WriteHashMap::new(cursor)? })
    }

    fn key(&self, offset: i64) -> Vec<u8> {
        // encode the offset directly rather than hashing it, preserving exact
        // keys. verified below
        offset_key(self.map.cursor().db.hash_size(), offset)
    }
}

verus! {

/// The key of an offset: zeros, then the offset in its last 8 bytes.
pub open spec fn offset_key_spec(hash_size: int, offset: i64) -> Seq<u8> {
    Seq::new((hash_size - 8) as nat, |i: int| 0u8) + crate::bytes::u64_be_spec(crate::bytes::i2u(offset))
}

/// `FileOffsetMap::key`.
fn offset_key(hash_size: usize, offset: i64) -> (r: Vec<u8>)
    requires
        hash_size >= 8,
    ensures
        r@ == offset_key_spec(hash_size as int, offset),
{
    let mut key = Vec::new();
    let mut i: usize = 0;
    while i < hash_size - 8
        invariant
            i <= hash_size - 8,
            key@ == Seq::new(i as nat, |k: int| 0u8),
        decreases hash_size - 8 - i,
    {
        key.push(0);
        i += 1;
        assert(key@ =~= Seq::new(i as nat, |k: int| 0u8));
    }
    let b = crate::bytes::u64_to_be_bytes(offset as u64);
    let mut j: usize = 0;
    while j < 8
        invariant
            j <= 8,
            key@ == Seq::new((hash_size - 8) as nat, |k: int| 0u8) + b@.subrange(0, j as int),
        decreases 8 - j,
    {
        key.push(b[j]);
        j += 1;
        assert(key@ =~= Seq::new((hash_size - 8) as nat, |k: int| 0u8) + b@.subrange(0, j as int));
    }
    assert(b@.subrange(0, 8) =~= b@);
    key
}

/// Different offsets get different keys, so the map never confuses them.
proof fn lemma_offset_key_injective(hash_size: int, a: i64, b: i64)
    requires
        hash_size >= 8,
        offset_key_spec(hash_size, a) == offset_key_spec(hash_size, b),
    ensures
        a == b,
{
    let ka = offset_key_spec(hash_size, a);
    let kb = offset_key_spec(hash_size, b);
    assert(ka.subrange(hash_size - 8, hash_size) =~= crate::bytes::u64_be_spec(crate::bytes::i2u(a)));
    assert(kb.subrange(hash_size - 8, hash_size) =~= crate::bytes::u64_be_spec(crate::bytes::i2u(b)));
    crate::bytes::lemma_be_u64_roundtrip(crate::bytes::i2u(a));
    crate::bytes::lemma_be_u64_roundtrip(crate::bytes::i2u(b));
    crate::bytes::lemma_i64_u64_roundtrip(a, 0);
    crate::bytes::lemma_i64_u64_roundtrip(b, 0);
}

} // verus!

impl<C: Core> OffsetMap for FileOffsetMap<'_, C> {
    fn reset(&mut self) -> Result<()> {
        let mut cursor = self.map.write_cursor().clone();
        cursor.write(Data::None)?;
        self.map = WriteHashMap::new(&mut cursor)?;
        Ok(())
    }

    fn get(&mut self, source_offset: i64) -> Result<Option<i64>> {
        match self.map.get_cursor_by_hash(&self.key(source_offset))? {
            Some(cursor) => Ok(Some(cursor.read_uint()? as i64)),
            None => Ok(None),
        }
    }

    fn put(&mut self, source_offset: i64, target_offset: i64) -> Result<()> {
        let key = self.key(source_offset);
        self.map.put_by_hash(&key, target_offset as u64)
    }
}
