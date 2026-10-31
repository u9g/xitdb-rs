//! Records: structs stored as a nested hash map of their fields, usually
//! with `#[derive(Record)]`, and the [`Map`] methods that update them.

use std::borrow::Borrow;

use crate::collections::{ReadHashMap, WriteHashMap};
use crate::core::Core;
use crate::cursor::{ReadCursor, WriteCursor};
use crate::data::Data;
use crate::error::{DecodeError, Error, Result};
use crate::slot::Tag;
use crate::typed::{KeyCodec, Map, ValueCodec};

/// A struct stored as a hash map of its fields, each under its own key
/// with its own [`ValueCodec`]. That's the data that hand-written code
/// makes with `put_map(key)?.put("title", ...)`, so the two can read each
/// other's records, and so can the other xitdb implementations.
///
/// Implement it with `#[derive(Record)]`, behind the `derive` feature,
/// which also implements [`ValueCodec`] for the struct (with `Owned` and
/// `Borrowed` both `Self`), so it can be the value of a [`Map`], or a field
/// of another record. The derive supports structs with named fields and no
/// generics. For each field:
///
/// * It's stored under the field's name, or the name given with
///   `#[xitdb(rename = "...")]`.
/// * Its codec is its type, which must be a [`ValueCodec`] whose `Owned` is
///   that type (`String`, `Vec<u8>`, `i64`, `u64`, `f64`, `bool`, or
///   another record), unless `#[xitdb(codec = Type)]` picks another, such
///   as `Json<T>`.
/// * A missing field, or one whose value is empty ([`Data::None`]), reads
///   as `Default::default()`, so adding a field to a struct needs no
///   migration. With `#[xitdb(required)]`, it's an error instead.
/// * An `Option<T>` field is stored as a `T` (with the `codec`, if given)
///   when it's `Some`, and is missing when it's `None`: writing `None`
///   removes it, rather than storing an empty value.
/// * Its type must implement `PartialEq`, for [`Record::changed_fields`].
///
/// Keys in the stored map that aren't fields, such as ones written by
/// newer code, are ignored when reading, and kept when writing: the
/// record's map is changed in place, field by field, rather than replaced.
///
/// A field that doesn't decode is an [`Error::Decode`] with the field's
/// name in [`DecodeError::field`] (a path like `"merge.title"`, for a field
/// of a nested record), along with the collection and key that a [`Map`]
/// adds. A stored value that isn't a hash map is an error too.
pub trait Record: Sized {
    /// The names the fields are stored under, in declaration order.
    const FIELDS: &'static [&'static str];

    /// Reads the record from the map of its fields.
    fn read_fields<C: Core>(map: &ReadHashMap<'_, C>) -> Result<Self>;

    /// Writes every field to `map`, removing the `Option` fields that are
    /// `None`. Other keys in `map` are kept.
    fn write_fields<C: Core>(&self, map: &mut WriteHashMap<'_, C>) -> Result<()>;

    /// The names of the fields whose values differ from `old`'s, compared
    /// with `PartialEq`.
    fn changed_fields(&self, old: &Self) -> Vec<&'static str>;

    /// Like [`Record::write_fields`], but only writes the fields that
    /// [`Record::changed_fields`] returns. If there are none, nothing is
    /// written, but `map` was already opened for writing; use
    /// [`Map::update`] to not even open it.
    fn write_changed_fields<C: Core>(&self, old: &Self, map: &mut WriteHashMap<'_, C>) -> Result<()>;
}

impl<K: KeyCodec + ?Sized, V: Record + ValueCodec<Owned = V, Borrowed = V> + Clone> Map<K, V> {
    /// Reads the record at `key`, applies `f` to a copy, and writes only the
    /// fields that `f` changed, returning the new record. A field that
    /// changed is written whole: a nested record that changed is rewritten
    /// field by field, keeping its unknown keys.
    ///
    /// If `f` changes nothing, nothing is written, not even the collection,
    /// so [`History::transact`] doesn't commit a new moment. If `key` is
    /// missing, `f` isn't called, nothing is written, and this returns
    /// `None`; use [`Map::upsert`] to start from a default record.
    ///
    /// [`History::transact`]: crate::History::transact
    pub fn update<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        key: &K,
        f: impl FnOnce(&mut V),
    ) -> Result<Option<V>> {
        let Some(old) = self.get(parent, key)? else { return Ok(None) };
        self.write_update(parent, key, old, f).map(Some)
    }

    /// Like [`Map::update`], but if `key` is missing, `f` is applied to
    /// `V::default()`, and the result is written whole, as with
    /// [`Map::put`].
    pub fn upsert<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K, f: impl FnOnce(&mut V)) -> Result<V>
    where
        V: Default,
    {
        match self.get(parent, key)? {
            Some(old) => self.write_update(parent, key, old, f),
            None => {
                let mut new = V::default();
                f(&mut new);
                self.put(parent, key, &new)?;
                Ok(new)
            }
        }
    }

    /// Applies `f` to a copy of `old`, the record at `key`, and writes the
    /// fields that changed, if any.
    fn write_update<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        key: &K,
        old: V,
        f: impl FnOnce(&mut V),
    ) -> Result<V> {
        let mut new = old.clone();
        f(&mut new);
        if !new.changed_fields(&old).is_empty() {
            let mut cursor = self.collection_mut(parent)?.put_cursor(key.encode_key())?;
            new.write_changed_fields(&old, &mut WriteHashMap::new(&mut cursor)?)?;
        }
        Ok(new)
    }
}

// What #[derive(Record)] generates calls these, through xitdb::__private.

/// [`ValueCodec::read`] for a record.
pub fn read_record<C: Core, R: Record>(cursor: &ReadCursor<'_, C>) -> Result<R> {
    match cursor.slot()?.tag {
        Tag::HashMap => R::read_fields(&ReadHashMap::new(cursor)?),
        tag => Err(Error::decode(format!("expected a hash map, found {tag:?}"))),
    }
}

/// [`ValueCodec::write`] for a record. An existing hash map is changed in
/// place, so keys that aren't fields are kept; any other value is
/// replaced.
pub fn write_record<C: Core, R: Record>(value: &R, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
    if !matches!(cursor.read.slot()?.tag, Tag::None | Tag::HashMap) {
        cursor.write(Data::None)?;
    }
    value.write_fields(&mut WriteHashMap::new(cursor)?)
}

/// Reads the field `name` with the codec `V`, or `None` if it's missing or
/// empty. An error has the field's name added, as `with_field` does.
pub fn read_field<C: Core, V: ValueCodec<Owned = T>, T>(map: &ReadHashMap<'_, C>, name: &str) -> Result<Option<T>> {
    let Some(cursor) = map.get_value_cursor(name)? else { return Ok(None) };
    V::read(&cursor).map(Some).map_err(|err| with_field(err, name))
}

/// Writes the field `name` with the codec `V`.
pub fn write_field<C: Core, V: ValueCodec, T: Borrow<V::Borrowed>>(
    map: &mut WriteHashMap<'_, C>,
    name: &str,
    value: &T,
) -> Result<()> {
    V::write(value.borrow(), &mut map.put_cursor(name)?)
}

/// Removes the field `name`, if it's there.
pub fn remove_field<C: Core>(map: &mut WriteHashMap<'_, C>, name: &str) -> Result<()> {
    if map.get_slot(name)?.is_some() {
        map.remove(name)?;
    }
    Ok(())
}

/// The error for a missing `#[xitdb(required)]` field.
pub fn missing_field(name: &str) -> Error {
    with_field(Error::decode("the field is missing"), name)
}

/// Adds the field `name` to an error from reading it, in front of any
/// field a nested record already added. Like a [`Map`], every error but
/// [`Error::Io`] becomes an [`Error::Decode`].
fn with_field(err: Error, name: &str) -> Error {
    let mut decode = match err {
        Error::Decode(decode) => decode,
        Error::Io(_) => return err,
        other => Box::new(DecodeError { collection: None, key: None, field: None, message: other.to_string() }),
    };
    decode.field = Some(match decode.field.take() {
        Some(inner) => format!("{name}.{inner}"),
        None => name.to_owned(),
    });
    Error::Decode(decode)
}

/// `#[derive(Record)]` rejects what it doesn't support. Tuple structs,
/// unit structs, enums and generic structs:
///
/// ```compile_fail
/// #[derive(xitdb::Record)]
/// struct Point(i64, i64);
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record)]
/// struct Empty;
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record)]
/// enum Status {
///     Open,
///     Merged,
/// }
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Wrapper<T> {
///     value: T,
/// }
/// ```
///
/// A required `Option`, an unknown attribute, and two fields stored under
/// the same name:
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     #[xitdb(required)]
///     thread: Option<String>,
/// }
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     #[xitdb(skip)]
///     title: String,
/// }
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     title: String,
///     #[xitdb(rename = "title")]
///     name: String,
/// }
/// ```
///
/// A field type that isn't its own codec, a codec that reads another type,
/// and a field without `PartialEq`:
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     count: u32,
/// }
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     #[xitdb(codec = u64)]
///     count: i64,
/// }
/// ```
///
/// ```compile_fail
/// #[derive(Clone)]
/// struct Opaque;
///
/// #[derive(xitdb::Record, Clone)]
/// struct Merge {
///     #[xitdb(codec = String)]
///     title: Opaque,
/// }
/// ```
///
/// For comparison, this compiles:
///
/// ```
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     #[xitdb(rename = "started-at", required)]
///     started_at: i64,
///     #[xitdb(codec = String)]
///     thread: Option<String>,
/// }
/// ```
#[cfg(all(doctest, feature = "derive"))]
struct UnsupportedDerives;
