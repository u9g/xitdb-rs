//! Typed, named collections, declared once and used against a parent hash
//! map, and the codecs that convert their keys and values.
//!
//! A [`Map`] or [`Set`] is only a name and a pair of types, so it can be a
//! `const`. Each method takes the parent map it lives in (a moment, or any
//! nested map) and opens the collection under its name: reads with
//! [`ReadHashMap::get_map`]-style lookups, where a missing collection reads
//! as empty, and writes with [`WriteHashMap::put_map`], which creates it.
//!
//! ```
//! use xitdb::{Database, History, Map, Set};
//!
//! const NAMES: Map<u64, String> = Map::new("names");
//! const ADMINS: Set<u64> = Set::new("admins");
//!
//! # fn main() -> xitdb::Result<()> {
//! let db = Database::in_memory()?;
//! let history = History::new(&db)?;
//! history.transact(|moment| {
//!     NAMES.put(moment, &1, "alice")?;
//!     ADMINS.insert(moment, &1)?;
//!     Ok::<_, xitdb::Error>(())
//! })?;
//!
//! let moment = history.latest()?;
//! assert_eq!(NAMES.get(&moment, &1)?.as_deref(), Some("alice"));
//! assert!(ADMINS.contains(&moment, &1)?);
//! # Ok(())
//! # }
//! ```

use std::borrow::{Borrow, Cow};
use std::fmt;
use std::marker::PhantomData;

use crate::collections::{KeyIterator, KvPairIterator, ReadHashMap, ReadHashSet, WriteHashMap, WriteHashSet};
use crate::core::Core;
use crate::cursor::{ReadCursor, WriteCursor};
use crate::data::Data;
use crate::error::{DecodeError, Error, Result};
use crate::slot::Tag;

/// Converts a key of a typed collection to and from the bytes it's hashed
/// and stored as.
///
/// It's implemented for the borrowed form of the key (`str`, `[u8]`), so
/// methods take `&K` and iteration yields [`KeyCodec::Owned`]:
///
/// * `str` and `String` are their UTF-8 bytes, so they read and write the
///   same keys as [`WriteHashMap::put`] with a string.
/// * `[u8]` and `Vec<u8>` are the bytes themselves.
/// * The integer types are their big-endian bytes at the type's full width
///   (two's complement for the signed ones), like Java's `ByteBuffer` and
///   Go's `binary.BigEndian`. The width is part of the key, so a `u32` key
///   and a `u64` key with the same value are different keys, and decoding
///   bytes of another length is an error. Use a `str` key for numbers that
///   are stored as decimal strings.
pub trait KeyCodec: fmt::Debug {
    type Owned: fmt::Debug;

    /// The bytes that are hashed and stored as the key.
    fn encode_key(&self) -> Cow<'_, [u8]>;

    /// Decodes stored key bytes, returning an [`Error::Decode`] (made with
    /// [`Error::decode`]) if they aren't a valid key.
    fn decode_key(bytes: Vec<u8>) -> Result<Self::Owned>;
}

/// Reads a value of a typed collection from a [`ReadCursor`] and writes it
/// through a [`WriteCursor`].
///
/// The codec is often the value type itself (`String`, `u64`), but it can
/// be a marker for an encoding, like `Json`, so reads return
/// [`ValueCodec::Owned`] and writes take a [`ValueCodec::Borrowed`].
///
/// Since a codec gets a cursor rather than [`Data`], a value can be any
/// structure: `write` can make a nested map with [`WriteHashMap::new`], and
/// `read` can open it with [`ReadHashMap::new`].
///
/// The built-in codecs check what they read: a value of the wrong type is an
/// [`Error::Decode`], not a default. Typed collections treat an empty value
/// ([`Data::None`]) as a missing key, like [`ReadHashMap::get_map`], so
/// `read` only sees one inside a nested structure:
///
/// * `String` and `Vec<u8>` are byte arrays. They're written without a
///   format tag, and read with any.
/// * `i64` and `u64` are written as [`Data::Int`] and [`Data::Uint`]. Each
///   also reads the other, if the value fits.
/// * `f64` is [`Data::Float`].
/// * `bool` is [`Data::Uint`] `0` or `1`; any other value is an error.
/// * `Option<T>` writes `None` as an empty value ([`Data::None`]), and reads
///   an empty value as `None`. In a [`Map`], that reads as a missing key,
///   so use [`Map::remove`] there; `Option` is for nested structures,
///   where a missing field and an empty one should both mean `None`.
/// * `Json<T>`, behind the `serde` feature, is JSON in a byte array.
pub trait ValueCodec {
    /// What reads return.
    type Owned;
    /// What writes take.
    type Borrowed: ?Sized;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Self::Owned>;

    fn write<C: Core>(value: &Self::Borrowed, cursor: &mut WriteCursor<'_, C>) -> Result<()>;
}

// Keys

impl KeyCodec for str {
    type Owned = String;

    fn encode_key(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.as_bytes())
    }

    fn decode_key(bytes: Vec<u8>) -> Result<String> {
        string_from_utf8(bytes)
    }
}

impl KeyCodec for String {
    type Owned = String;

    fn encode_key(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self.as_bytes())
    }

    fn decode_key(bytes: Vec<u8>) -> Result<String> {
        string_from_utf8(bytes)
    }
}

impl KeyCodec for [u8] {
    type Owned = Vec<u8>;

    fn encode_key(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self)
    }

    fn decode_key(bytes: Vec<u8>) -> Result<Vec<u8>> {
        Ok(bytes)
    }
}

impl KeyCodec for Vec<u8> {
    type Owned = Vec<u8>;

    fn encode_key(&self) -> Cow<'_, [u8]> {
        Cow::Borrowed(self)
    }

    fn decode_key(bytes: Vec<u8>) -> Result<Vec<u8>> {
        Ok(bytes)
    }
}

macro_rules! int_key_codec {
    ($($int:ty),*) => {
        $(
            impl KeyCodec for $int {
                type Owned = $int;

                fn encode_key(&self) -> Cow<'_, [u8]> {
                    Cow::Owned(self.to_be_bytes().to_vec())
                }

                fn decode_key(bytes: Vec<u8>) -> Result<$int> {
                    let bytes = bytes.try_into().map_err(|bytes: Vec<u8>| {
                        Error::decode(format!(
                            "expected a {}-byte {} key, found {} bytes",
                            size_of::<$int>(),
                            stringify!($int),
                            bytes.len()
                        ))
                    })?;
                    Ok(<$int>::from_be_bytes(bytes))
                }
            }
        )*
    };
}

int_key_codec!(u8, u16, u32, u64, i8, i16, i32, i64);

fn string_from_utf8(bytes: Vec<u8>) -> Result<String> {
    String::from_utf8(bytes).map_err(|err| Error::decode(format!("invalid utf-8: {}", err.utf8_error())))
}

// Values

/// The tag of the value at `cursor`, as typed collections read it.
fn value_tag<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Tag> {
    Ok(cursor.slot()?.tag)
}

fn unexpected(expected: &str, found: Tag) -> Error {
    Error::decode(format!("expected {expected}, found {found:?}"))
}

fn read_bytes<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Vec<u8>> {
    match value_tag(cursor)? {
        Tag::Bytes | Tag::ShortBytes => cursor.read_bytes(None),
        tag => Err(unexpected("bytes", tag)),
    }
}

impl ValueCodec for String {
    type Owned = String;
    type Borrowed = str;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<String> {
        string_from_utf8(read_bytes(cursor)?)
    }

    fn write<C: Core>(value: &str, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        cursor.write(value)
    }
}

impl ValueCodec for Vec<u8> {
    type Owned = Vec<u8>;
    type Borrowed = [u8];

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Vec<u8>> {
        read_bytes(cursor)
    }

    fn write<C: Core>(value: &[u8], cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        cursor.write(value)
    }
}

impl ValueCodec for i64 {
    type Owned = i64;
    type Borrowed = i64;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<i64> {
        match value_tag(cursor)? {
            Tag::Int => cursor.read_int(),
            Tag::Uint => {
                let value = cursor.read_uint()?;
                i64::try_from(value).map_err(|_| Error::decode(format!("{value} doesn't fit in an i64")))
            }
            tag => Err(unexpected("an integer", tag)),
        }
    }

    fn write<C: Core>(value: &i64, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        cursor.write(*value)
    }
}

impl ValueCodec for u64 {
    type Owned = u64;
    type Borrowed = u64;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<u64> {
        match value_tag(cursor)? {
            Tag::Uint => cursor.read_uint(),
            Tag::Int => {
                let value = cursor.read_int()?;
                u64::try_from(value).map_err(|_| Error::decode(format!("{value} doesn't fit in a u64")))
            }
            tag => Err(unexpected("an integer", tag)),
        }
    }

    fn write<C: Core>(value: &u64, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        cursor.write(*value)
    }
}

impl ValueCodec for f64 {
    type Owned = f64;
    type Borrowed = f64;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<f64> {
        match value_tag(cursor)? {
            Tag::Float => cursor.read_float(),
            tag => Err(unexpected("a float", tag)),
        }
    }

    fn write<C: Core>(value: &f64, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        cursor.write(*value)
    }
}

impl ValueCodec for bool {
    type Owned = bool;
    type Borrowed = bool;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<bool> {
        match value_tag(cursor)? {
            Tag::Uint => match cursor.read_uint()? {
                0 => Ok(false),
                1 => Ok(true),
                value => Err(Error::decode(format!("expected 0 or 1 for a bool, found {value}"))),
            },
            tag => Err(unexpected("a bool (0 or 1)", tag)),
        }
    }

    fn write<C: Core>(value: &bool, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        cursor.write(u64::from(*value))
    }
}

impl<T: ValueCodec> ValueCodec for Option<T>
where
    T::Owned: Borrow<T::Borrowed>,
{
    type Owned = Option<T::Owned>;
    type Borrowed = Option<T::Owned>;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Option<T::Owned>> {
        match value_tag(cursor)? {
            Tag::None => Ok(None),
            _ => T::read(cursor).map(Some),
        }
    }

    fn write<C: Core>(value: &Option<T::Owned>, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        match value {
            Some(value) => T::write(value.borrow(), cursor),
            None => cursor.write(Data::None),
        }
    }
}

/// A [`ValueCodec`] that stores `T` as JSON, in a byte array with the
/// format tag `js`. Reads also accept a byte array without a format tag,
/// so JSON written as a plain string before reads the same; any other tag
/// is an [`Error::Decode`], as is JSON that doesn't deserialize as `T`.
///
/// A value that can't be serialized (for example, a map with non-string
/// keys) is an [`Error::Io`], as from [`serde_json::to_writer`].
///
/// ```
/// use serde::{Deserialize, Serialize};
/// use xitdb::{Database, History, Json, Map};
///
/// #[derive(Serialize, Deserialize, Debug, PartialEq)]
/// struct Proposal {
///     id: String,
///     votes: u64,
/// }
///
/// const PROPOSALS: Map<str, Json<Proposal>> = Map::new("proposals");
///
/// # fn main() -> xitdb::Result<()> {
/// let db = Database::in_memory()?;
/// let history = History::new(&db)?;
/// let proposal = Proposal { id: "p1".into(), votes: 3 };
/// history.transact(|moment| PROPOSALS.put(moment, &proposal.id, &proposal))?;
/// assert_eq!(PROPOSALS.get(&history.latest()?, "p1")?, Some(proposal));
/// # Ok(())
/// # }
/// ```
#[cfg(feature = "serde")]
pub struct Json<T>(PhantomData<fn() -> T>);

/// The format tag of [`Json`] values.
#[cfg(feature = "serde")]
pub const JSON_FORMAT_TAG: [u8; 2] = *b"js";

#[cfg(feature = "serde")]
impl<T: serde::Serialize + serde::de::DeserializeOwned> ValueCodec for Json<T> {
    type Owned = T;
    type Borrowed = T;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<T> {
        let tag = value_tag(cursor)?;
        if !matches!(tag, Tag::Bytes | Tag::ShortBytes) {
            return Err(unexpected("json bytes", tag));
        }
        let bytes = cursor.read_bytes_object(None)?;
        match bytes.format_tag {
            None | Some(JSON_FORMAT_TAG) => {}
            Some(other) => {
                let other = String::from_utf8_lossy(&other);
                return Err(Error::decode(format!("expected format tag \"js\" or none, found {other:?}")));
            }
        }
        serde_json::from_slice(&bytes.value).map_err(|err| Error::decode(format!("invalid json: {err}")))
    }

    fn write<C: Core>(value: &T, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        let json = serde_json::to_vec(value).map_err(std::io::Error::from)?;
        cursor.write(Data::tagged_bytes(json, JSON_FORMAT_TAG))
    }
}

// Collections

/// Adds the collection's name and the key to a decode error from a codec.
/// [`Error::UnexpectedTag`] and [`Error::InvalidUtf8`], which a codec gets
/// from the cursor methods, become decode errors too, so they get the same
/// context. Context the codec already added is kept.
fn with_context(err: Error, collection: &str, key: impl FnOnce() -> Option<String>) -> Error {
    let mut decode = match err {
        Error::Decode(decode) => decode,
        Error::UnexpectedTag | Error::InvalidUtf8(_) => {
            Box::new(DecodeError { collection: None, key: None, message: err.to_string() })
        }
        other => return other,
    };
    decode.collection.get_or_insert_with(|| collection.to_owned());
    if decode.key.is_none() {
        decode.key = key();
    }
    Error::Decode(decode)
}

/// A typed hash map stored under `name` in a parent hash map. `K` is the
/// key's [`KeyCodec`] and `V` the value's [`ValueCodec`].
///
/// It holds no data, so declare it once as a `const` and use it with any
/// parent map: a moment, or a map nested in one. Reads take the parent as
/// a [`ReadHashMap`] (a [`WriteHashMap`] dereferences to one), and a
/// missing collection reads as empty. Writes take a [`WriteHashMap`] and
/// create the collection if it's missing; like [`WriteHashMap::put_map`],
/// they must run inside a transaction, such as [`History::transact`].
///
/// The collection is a plain hash map, so it's the same data as
/// `parent.put_map(name)?.put(key, value)`, and untyped code (or another
/// xitdb implementation) can read and write it too.
///
/// Values can't be typed collections themselves. To nest one per key, open
/// the nested map with [`WriteHashMap::put_map`] or
/// [`ReadHashMap::get_map`] (or [`Map::collection_mut`] and
/// [`Map::collection`]) and use another definition on it as the parent.
///
/// [`History::transact`]: crate::History::transact
pub struct Map<K: ?Sized, V> {
    name: &'static str,
    types: PhantomData<fn(&K) -> V>,
}

impl<K: ?Sized, V> Clone for Map<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: ?Sized, V> Copy for Map<K, V> {}

impl<K: ?Sized, V> fmt::Debug for Map<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Map").field("name", &self.name).finish()
    }
}

impl<K: ?Sized, V> Map<K, V> {
    pub const fn new(name: &'static str) -> Self {
        Map { name, types: PhantomData }
    }

    /// The key the collection is stored under in its parent.
    pub const fn name(&self) -> &'static str {
        self.name
    }

    /// The untyped collection, or `None` if it's missing.
    pub fn collection<'a, C: Core>(&self, parent: &ReadHashMap<'a, C>) -> Result<Option<ReadHashMap<'a, C>>> {
        parent.get_map(self.name)
    }

    /// The untyped collection, creating it if it's missing (see
    /// [`WriteHashMap::put_map`]).
    pub fn collection_mut<'a, C: Core>(&self, parent: &mut WriteHashMap<'a, C>) -> Result<WriteHashMap<'a, C>> {
        parent.put_map(self.name)
    }
}

impl<K: KeyCodec + ?Sized, V: ValueCodec> Map<K, V> {
    /// The value of `key`, or `None` if it's missing or empty (see
    /// [`ReadHashMap::get_map`]), or the collection is. A value its codec
    /// can't decode is an [`Error::Decode`] with the collection's name and
    /// the key.
    pub fn get<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &K) -> Result<Option<V::Owned>> {
        let Some(map) = self.collection(parent)? else { return Ok(None) };
        match map.get_cursor(key.encode_key())? {
            Some(cursor) if cursor.slot_ptr.slot.tag != Tag::None => {
                let value =
                    V::read(&cursor).map_err(|err| with_context(err, self.name, || Some(format!("{key:?}"))))?;
                Ok(Some(value))
            }
            _ => Ok(None),
        }
    }

    /// Whether `key` has a value. Like [`Map::get`], an empty value counts
    /// as missing, but this doesn't decode it.
    pub fn contains<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &K) -> Result<bool> {
        let Some(map) = self.collection(parent)? else { return Ok(false) };
        Ok(map.get_slot(key.encode_key())?.is_some_and(|slot| slot.tag != Tag::None))
    }

    /// Sets `key` to `value`, creating the collection if it's missing.
    pub fn put<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K, value: &V::Borrowed) -> Result<()> {
        let mut cursor = self.collection_mut(parent)?.put_cursor(key.encode_key())?;
        V::write(value, &mut cursor)
    }

    /// Removes `key`, returning whether it was in the collection. If it
    /// wasn't, nothing is written, so the collection isn't created.
    pub fn remove<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K) -> Result<bool> {
        let key = key.encode_key();
        match self.collection(parent)? {
            Some(map) if map.get_slot(&key)?.is_some() => self.collection_mut(parent)?.remove(&key),
            _ => Ok(false),
        }
    }

    /// Iterates over the keys and values, decoded, in hash order. Empty
    /// values are skipped, as [`Map::get`] treats them as missing.
    pub fn iter<'a, C: Core>(&self, parent: &ReadHashMap<'a, C>) -> Result<MapIter<'a, C, K, V>> {
        let pairs = self.collection(parent)?.map(|map| map.entries()).transpose()?;
        Ok(MapIter { name: self.name, pairs, types: PhantomData })
    }
}

/// Iterates over the decoded keys and values of a [`Map`]. Made by
/// [`Map::iter`].
pub struct MapIter<'a, C: Core, K: ?Sized, V> {
    name: &'static str,
    pairs: Option<KvPairIterator<'a, C>>,
    types: PhantomData<fn(&K) -> V>,
}

impl<C: Core, K: KeyCodec + ?Sized, V: ValueCodec> Iterator for MapIter<'_, C, K, V> {
    type Item = Result<(K::Owned, V::Owned)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let kv = match self.pairs.as_mut()?.next()? {
                Ok(kv) => kv,
                Err(err) => return Some(Err(err)),
            };
            if kv.value_cursor.slot_ptr.slot.tag == Tag::None {
                continue;
            }
            return Some(read_entry::<C, K, V>(self.name, &kv.key_cursor, &kv.value_cursor));
        }
    }
}

fn read_key<C: Core, K: KeyCodec + ?Sized>(name: &str, cursor: &ReadCursor<'_, C>) -> Result<K::Owned> {
    let bytes = cursor.read_bytes(None)?;
    let describe = |bytes: &[u8]| Some(format!("{:?}", String::from_utf8_lossy(bytes)));
    K::decode_key(bytes.clone()).map_err(|err| with_context(err, name, || describe(&bytes)))
}

fn read_entry<C: Core, K: KeyCodec + ?Sized, V: ValueCodec>(
    name: &str,
    key_cursor: &ReadCursor<'_, C>,
    value_cursor: &ReadCursor<'_, C>,
) -> Result<(K::Owned, V::Owned)> {
    let key = read_key::<C, K>(name, key_cursor)?;
    let value = V::read(value_cursor).map_err(|err| with_context(err, name, || Some(format!("{key:?}"))))?;
    Ok((key, value))
}

/// A typed hash set stored under `name` in a parent hash map. `K` is the
/// key's [`KeyCodec`]. Like [`Map`], it holds no data, and is used with
/// any parent map.
///
/// The collection is a plain hash set, the same data as
/// `parent.put_set(name)?.put(key)`.
pub struct Set<K: ?Sized> {
    name: &'static str,
    types: PhantomData<fn(&K)>,
}

impl<K: ?Sized> Clone for Set<K> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K: ?Sized> Copy for Set<K> {}

impl<K: ?Sized> fmt::Debug for Set<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Set").field("name", &self.name).finish()
    }
}

impl<K: ?Sized> Set<K> {
    pub const fn new(name: &'static str) -> Self {
        Set { name, types: PhantomData }
    }

    /// The key the collection is stored under in its parent.
    pub const fn name(&self) -> &'static str {
        self.name
    }

    /// The untyped collection, or `None` if it's missing.
    pub fn collection<'a, C: Core>(&self, parent: &ReadHashMap<'a, C>) -> Result<Option<ReadHashSet<'a, C>>> {
        parent.get_set(self.name)
    }

    /// The untyped collection, creating it if it's missing (see
    /// [`WriteHashMap::put_set`]).
    pub fn collection_mut<'a, C: Core>(&self, parent: &mut WriteHashMap<'a, C>) -> Result<WriteHashSet<'a, C>> {
        parent.put_set(self.name)
    }
}

impl<K: KeyCodec + ?Sized> Set<K> {
    pub fn contains<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &K) -> Result<bool> {
        self.contains_encoded(parent, &key.encode_key())
    }

    fn contains_encoded<C: Core>(&self, parent: &ReadHashMap<'_, C>, key: &[u8]) -> Result<bool> {
        match self.collection(parent)? {
            Some(set) => set.contains(key),
            None => Ok(false),
        }
    }

    /// Adds `key`, returning whether it was new. If it wasn't, nothing is
    /// written.
    pub fn insert<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K) -> Result<bool> {
        let key = key.encode_key();
        if self.contains_encoded(parent, &key)? {
            return Ok(false);
        }
        self.collection_mut(parent)?.put(&key)?;
        Ok(true)
    }

    /// Removes `key`, returning whether it was in the set. If it wasn't,
    /// nothing is written, so the collection isn't created.
    pub fn remove<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K) -> Result<bool> {
        let key = key.encode_key();
        if !self.contains_encoded(parent, &key)? {
            return Ok(false);
        }
        self.collection_mut(parent)?.remove(&key)
    }

    /// Iterates over the decoded keys, in hash order.
    pub fn iter<'a, C: Core>(&self, parent: &ReadHashMap<'a, C>) -> Result<SetIter<'a, C, K>> {
        let keys = self.collection(parent)?.map(|set| set.keys()).transpose()?;
        Ok(SetIter { name: self.name, keys, types: PhantomData })
    }
}

/// Iterates over the decoded keys of a [`Set`]. Made by [`Set::iter`].
pub struct SetIter<'a, C: Core, K: ?Sized> {
    name: &'static str,
    keys: Option<KeyIterator<'a, C>>,
    types: PhantomData<fn(&K)>,
}

impl<C: Core, K: KeyCodec + ?Sized> Iterator for SetIter<'_, C, K> {
    type Item = Result<K::Owned>;

    fn next(&mut self) -> Option<Self::Item> {
        let cursor = self.keys.as_mut()?.next()?;
        Some(cursor.and_then(|cursor| read_key::<C, K>(self.name, &cursor)))
    }
}
