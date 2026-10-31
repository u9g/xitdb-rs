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
/// * It's stored under the field's name (without `r#`), or the name given
///   with `#[xitdb(rename = "...")]`.
/// * Its codec is its type, which must be a [`ValueCodec`] whose `Owned` is
///   that type (`String`, `Vec<u8>`, `i64`, `u64`, `f64`, `bool`, an
///   `Option` of one of those, or another record), unless
///   `#[xitdb(codec = Type)]` picks another, such as `Json<T>` (or
///   `Option<Json<T>>` for an `Option<T>` field).
/// * A missing field, or one whose value is empty ([`Data::None`]), reads
///   as `Default::default()`, so adding a field to a struct needs no
///   migration. With `#[xitdb(required)]`, it's an error instead.
/// * A value that its codec's [`ValueCodec::is_missing`] says is missing,
///   which is `None` for an `Option` field, is stored by leaving the field
///   out: writing it removes the field, rather than storing an empty value.
///   The codec decides, not how the type is spelled, so this holds for a
///   type alias of an `Option` too.
/// * Its type must implement `PartialEq`, which [`Record::changed_fields`]
///   uses unless the codec's [`ValueCodec::changed`] decides.
///
/// If the `xitdb` crate isn't at `::xitdb`, such as when it's re-exported,
/// give its path with `#[xitdb(crate = "path")]` on the struct.
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

    /// Writes every field to `map`, removing the ones whose values are
    /// missing (see [`ValueCodec::is_missing`]). Other keys in `map` are
    /// kept.
    fn write_fields<C: Core>(&self, map: &mut WriteHashMap<'_, C>) -> Result<()>;

    /// The names of the fields whose values differ from `old`'s, as their
    /// codecs' [`ValueCodec::changed`] decides: with `PartialEq` by
    /// default, and by their bits for an `f64`.
    fn changed_fields(&self, old: &Self) -> Vec<&'static str>;

    /// Writes the fields that differ from `old`'s, as
    /// [`Record::changed_fields`] decides, comparing each field once. A
    /// changed field is written with its codec's
    /// [`ValueCodec::write_changed`], so only the changed fields of a
    /// nested record are written. `map` is only opened once a field has
    /// changed, so if none did, nothing at all is written. Returns whether
    /// any field was written.
    fn write_changed_fields<'a, C, F>(&self, old: &Self, map: &mut LazyMap<'a, C, F>) -> Result<bool>
    where
        C: Core,
        F: FnOnce() -> Result<WriteHashMap<'a, C>>;
}

/// A [`WriteHashMap`] that's opened the first time it's used, for
/// [`Record::write_changed_fields`].
pub struct LazyMap<'a, C: Core, F> {
    open: Option<F>,
    map: Option<WriteHashMap<'a, C>>,
}

impl<'a, C: Core, F: FnOnce() -> Result<WriteHashMap<'a, C>>> LazyMap<'a, C, F> {
    /// A map that `open` opens when it's first used.
    pub fn new(open: F) -> Self {
        LazyMap { open: Some(open), map: None }
    }

    /// The map, opening it if it isn't open yet. If opening it failed
    /// before, this returns [`Error::CursorNotWriteable`].
    pub fn get(&mut self) -> Result<&mut WriteHashMap<'a, C>> {
        if self.map.is_none() {
            let open = self.open.take().ok_or(Error::CursorNotWriteable)?;
            self.map = Some(open()?);
        }
        Ok(self.map.as_mut().expect("the map was just opened"))
    }

    /// Whether the map was opened.
    pub fn is_open(&self) -> bool {
        self.map.is_some()
    }
}

impl<K: KeyCodec + ?Sized, V: Record + ValueCodec<Owned = V, Borrowed = V> + Clone> Map<K, V> {
    /// Reads the record at `key`, applies `f` to a copy, and writes only the
    /// fields that `f` changed (see [`Record::write_changed_fields`]),
    /// returning the new record.
    ///
    /// The collection and the record are only opened for writing once a
    /// field is known to have changed, so if `f` changes nothing, nothing
    /// at all is written, and [`History::transact`] doesn't commit a new
    /// moment. If `key` is missing, `f` isn't called, nothing is written,
    /// and this returns `None`; use [`Map::upsert`] to start from a default
    /// record.
    ///
    /// `parent` is usually a moment. For a parent nested in it, use
    /// [`Map::update_at`]: getting the parent with
    /// [`WriteHashMap::put_map`] writes a copy of the path to it, so the
    /// moment would be committed even if nothing changed.
    ///
    /// [`History::transact`]: crate::History::transact
    pub fn update<C: Core>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        key: &K,
        f: impl FnOnce(&mut V),
    ) -> Result<Option<V>> {
        self.update_at(parent, &[] as &[&[u8]], key, f)
    }

    /// Like [`Map::update`], for the collection in a hash map nested in
    /// `parent`: `path` is the keys of the maps it's in, starting from
    /// `parent`. They're read along the path, and only opened with
    /// [`WriteHashMap::put_map`] once a field has changed, so an unchanged
    /// record writes nothing at any depth. A missing map along the path is
    /// like a missing key: nothing is written, and this returns `None`.
    pub fn update_at<C: Core, P: AsRef<[u8]>>(
        &self,
        parent: &mut WriteHashMap<'_, C>,
        path: &[P],
        key: &K,
        f: impl FnOnce(&mut V),
    ) -> Result<Option<V>> {
        let mut nested = None;
        for part in path {
            let map: &ReadHashMap<'_, C> = nested.as_ref().unwrap_or(parent);
            match map.get_map(part)? {
                Some(map) => nested = Some(map),
                None => return Ok(None),
            }
        }
        let Some(old) = self.get(nested.as_ref().unwrap_or(parent), key)? else { return Ok(None) };
        self.write_update(parent, path, key, old, f).map(Some)
    }

    /// Like [`Map::update`], but if `key` is missing, `f` is applied to
    /// `V::default()`, and the result is written whole, as with
    /// [`Map::put`].
    pub fn upsert<C: Core>(&self, parent: &mut WriteHashMap<'_, C>, key: &K, f: impl FnOnce(&mut V)) -> Result<V>
    where
        V: Default,
    {
        match self.get(parent, key)? {
            Some(old) => self.write_update(parent, &[] as &[&[u8]], key, old, f),
            None => {
                let mut new = V::default();
                f(&mut new);
                self.put(parent, key, &new)?;
                Ok(new)
            }
        }
    }

    /// Applies `f` to a copy of `old`, the record at `key` in the collection
    /// at `path` in `parent`, and writes the fields that changed, if any.
    fn write_update<'a, C: Core, P: AsRef<[u8]>>(
        &self,
        parent: &mut WriteHashMap<'a, C>,
        path: &[P],
        key: &K,
        old: V,
        f: impl FnOnce(&mut V),
    ) -> Result<V> {
        let mut new = old.clone();
        f(&mut new);
        let mut map = LazyMap::new(|| {
            let mut nested: Option<WriteHashMap<'a, C>> = None;
            for part in path {
                let map = match &mut nested {
                    Some(map) => map.put_map(part)?,
                    None => parent.put_map(part)?,
                };
                nested = Some(map);
            }
            let mut cursor = self.collection_mut(nested.as_mut().unwrap_or(parent))?.put_cursor(key.encode_key())?;
            WriteHashMap::new(&mut cursor)
        });
        new.write_changed_fields(&old, &mut map)?;
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

/// [`ValueCodec::write_changed`] for a record: only the fields that
/// changed are written. If the stored value isn't a hash map (the field was
/// missing, so `old` is a default), the whole record is written, so that
/// fields equal to their defaults, such as required ones, are stored too.
pub fn write_record_changed<C: Core, R: Record>(old: &R, new: &R, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
    if cursor.read.slot()?.tag != Tag::HashMap {
        return write_record(new, cursor);
    }
    new.write_changed_fields(old, &mut LazyMap::new(|| WriteHashMap::new(cursor)))?;
    Ok(())
}

/// Reads the field `name` with the codec `V`, or `None` if it's missing or
/// empty. An error has the field's name added, as `with_field` does.
pub fn read_field<C: Core, V: ValueCodec<Owned = T>, T>(map: &ReadHashMap<'_, C>, name: &str) -> Result<Option<T>> {
    let Some(cursor) = map.get_value_cursor(name)? else { return Ok(None) };
    V::read(&cursor).map(Some).map_err(|err| with_field(err, name))
}

/// Writes the field `name` with the codec `V`, or removes it if the value
/// is missing.
pub fn write_field<C: Core, V: ValueCodec, T: Borrow<V::Borrowed>>(
    map: &mut WriteHashMap<'_, C>,
    name: &str,
    value: &T,
) -> Result<()> {
    let value = value.borrow();
    if V::is_missing(value) {
        // the map was opened for writing in this transaction, so it's
        // already a copy, and removing a key that isn't there writes nothing
        map.remove(name)?;
        return Ok(());
    }
    V::write(value, &mut map.put_cursor(name)?)
}

/// Whether a field changed, by its codec's [`ValueCodec::changed`], or by
/// `PartialEq` if the codec leaves it to that.
pub fn field_changed<V: ValueCodec>(old: &V::Owned, new: &V::Owned) -> bool
where
    V::Owned: PartialEq,
{
    V::changed(old, new).unwrap_or_else(|| old != new)
}

/// Writes the field `name`, which changed from `old` to `new`, with the
/// codec `V`, or removes it if the new value is missing.
pub fn write_changed_field<C: Core, V: ValueCodec, T: Borrow<V::Borrowed>>(
    map: &mut WriteHashMap<'_, C>,
    name: &str,
    old: &V::Owned,
    new: &T,
) -> Result<()> {
    let new = new.borrow();
    if V::is_missing(new) {
        map.remove(name)?;
        return Ok(());
    }
    V::write_changed(old, new, &mut map.put_cursor(name)?)
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
/// A required `Option`, an unknown attribute, attributes given twice, and
/// two fields stored under the same name:
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
///     #[xitdb(rename = "name", rename = "title")]
///     title: String,
/// }
/// ```
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     #[xitdb(codec = String)]
///     #[xitdb(codec = String)]
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
/// A crate path that doesn't lead to xitdb:
///
/// ```compile_fail
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// #[xitdb(crate = "not_xitdb")]
/// struct Merge {
///     title: String,
/// }
/// ```
///
/// A field type that isn't its own codec, a codec that reads another type
/// (such as the codec of an `Option`'s contents), and a field without
/// `PartialEq`:
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
/// #[derive(xitdb::Record, Clone, PartialEq)]
/// struct Merge {
///     #[xitdb(codec = String)]
///     thread: Option<String>,
/// }
/// ```
///
/// ```compile_fail
/// use xitdb::{Core, ReadCursor, Result, ValueCodec, WriteCursor};
///
/// #[derive(Clone, Default)]
/// struct Opaque(u64);
///
/// impl ValueCodec for Opaque {
///     type Owned = Opaque;
///     type Borrowed = Opaque;
///
///     fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Opaque> {
///         u64::read(cursor).map(Opaque)
///     }
///
///     fn write<C: Core>(value: &Opaque, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
///         u64::write(&value.0, cursor)
///     }
/// }
///
/// #[derive(xitdb::Record, Clone)]
/// struct Merge {
///     opaque: Opaque,
/// }
/// ```
///
/// For comparison, this compiles: the same codec, but with `PartialEq`, and
/// the attributes used correctly:
///
/// ```
/// use xitdb::{Core, ReadCursor, Result, ValueCodec, WriteCursor};
///
/// #[derive(Clone, Default, PartialEq)]
/// struct Opaque(u64);
///
/// impl ValueCodec for Opaque {
///     type Owned = Opaque;
///     type Borrowed = Opaque;
///
///     fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Opaque> {
///         u64::read(cursor).map(Opaque)
///     }
///
///     fn write<C: Core>(value: &Opaque, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
///         u64::write(&value.0, cursor)
///     }
/// }
///
/// #[derive(xitdb::Record, Clone)]
/// #[xitdb(crate = "xitdb")]
/// struct Merge {
///     opaque: Opaque,
///     #[xitdb(rename = "started-at", required)]
///     started_at: i64,
///     #[xitdb(codec = Option<String>)]
///     thread: Option<String>,
/// }
/// ```
#[cfg(all(doctest, feature = "derive"))]
struct UnsupportedDerives;
