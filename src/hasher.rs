use std::fmt;
use std::sync::Arc;

type HashFn = dyn Fn(&[u8]) -> Vec<u8> + Send + Sync;

/// Tells a [`Database`](crate::Database) how to hash the keys of hash maps
/// and hash sets.
///
/// The size of the hash is stored in the database header, and opening a
/// database with a hasher of a different size fails with
/// [`Error::InvalidHashSize`](crate::Error::InvalidHashSize).
#[derive(Clone)]
pub struct Hasher {
    hash: Arc<HashFn>,
    /// The name of the hashing algorithm, stored in the header of new
    /// databases. It is ignored when opening an existing database.
    pub id: u32,
    /// The file ID of a new database. If 0, a random one is used.
    pub file_id: u64,
}

impl Hasher {
    /// Creates a hasher from a hash function. The function must always
    /// return hashes of the same length.
    pub fn new(hash: impl Fn(&[u8]) -> Vec<u8> + Send + Sync + 'static) -> Hasher {
        Hasher { hash: Arc::new(hash), id: 0, file_id: 0 }
    }

    /// A SHA-1 hasher with the hash id `sha1`.
    #[cfg(feature = "sha1")]
    pub fn sha1() -> Hasher {
        use sha1::Digest;
        Hasher::new(|data| sha1::Sha1::digest(data).to_vec()).with_id(*b"sha1")
    }

    pub fn with_id(mut self, id: [u8; 4]) -> Hasher {
        self.id = bytes_to_id(id);
        self
    }

    pub fn with_file_id(mut self, file_id: u64) -> Hasher {
        self.file_id = file_id;
        self
    }

    pub fn digest(&self, data: &[u8]) -> Vec<u8> {
        (self.hash)(data)
    }

    /// The length of the hashes this hasher produces.
    pub fn hash_size(&self) -> usize {
        self.digest(&[]).len()
    }
}

impl fmt::Debug for Hasher {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Hasher")
            .field("id", &id_to_bytes(self.id))
            .field("file_id", &self.file_id)
            .finish_non_exhaustive()
    }
}

pub fn bytes_to_id(name: [u8; 4]) -> u32 {
    u32::from_be_bytes(name)
}

pub fn id_to_bytes(id: u32) -> [u8; 4] {
    id.to_be_bytes()
}
