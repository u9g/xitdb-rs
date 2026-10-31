use crate::collections::WriteHashMap;
use crate::compact::OffsetMap;
use crate::core::Core;
use crate::cursor::WriteCursor;
use crate::data::Data;
use crate::error::{Error, Result};

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
        // encode the offset directly rather than hashing it, preserving exact keys
        let mut key = vec![0u8; self.map.cursor().db.hash_size()];
        let len = key.len();
        key[len - 8..].copy_from_slice(&offset.to_be_bytes());
        key
    }
}

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
