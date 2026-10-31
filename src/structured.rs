//! Structured values: any serde type stored as nested hash maps, array
//! lists and scalars, rather than as one blob, and written by changing only
//! what differs from what's stored.
//!
//! The stored shape is plain, so it can be read without this module, by
//! untyped code or by the other xitdb implementations:
//!
//! * A struct, or a map, is a hash map from each field's name (or each
//!   key) to its value. A map key that's a string or bytes is stored as
//!   those bytes; an integer, a bool, a char or a unit variant is stored as
//!   its text (`"42"`, `"true"`), as JSON does. Any other key type is an
//!   error.
//! * A sequence, a tuple, or a tuple struct is an array list.
//! * A string, a char, or bytes (with `serialize_bytes`, as `serde_bytes`
//!   does; a plain `Vec<u8>` is a sequence) is a byte array.
//! * A signed integer is a [`Data::Int`], an unsigned one a [`Data::Uint`],
//!   a float a [`Data::Float`], and a bool the `Uint` `0` or `1`, as the
//!   [`ValueCodec`]s of `i64`, `u64`, `f64` and `bool` store them. An
//!   `i128` or `u128` is stored the same way if it fits in 64 bits, and is
//!   an error otherwise.
//! * `None`, `()` and a unit struct are left out of a map: a field that's
//!   `None` is a missing key. Where a slot has to exist, as an item of a
//!   list or the value of a variant, they're an empty value
//!   ([`Data::None`]).
//! * A newtype struct is its contents.
//! * An enum is externally tagged, like serde_json's default: a unit
//!   variant is its name, as a byte array, and any other variant is a hash
//!   map with one key, the variant's name, whose value is the variant's
//!   contents (its value, a list of its fields, or a map of its fields).
//!
//! Writing compares with what's stored as it goes, and only writes what
//! differs; see [`write_structured`].

use std::collections::HashSet;
use std::fmt;
use std::io;
use std::marker::PhantomData;

use serde::de::{self, DeserializeOwned, DeserializeSeed, IntoDeserializer, Visitor};
use serde::ser::{self, Serialize};

use crate::collections::{KvPairIterator, ReadArrayList, ReadHashMap, WriteArrayList, WriteHashMap, has_value};
use crate::core::Core;
use crate::cursor::{CursorIterator, ReadCursor, WriteCursor};
use crate::data::Data;
use crate::database::is_root;
use crate::error::{Error, Result};
use crate::slot::Tag;
use crate::typed::ValueCodec;

/// A [`ValueCodec`] that stores a serde type as nested hash maps, array
/// lists and scalars (see [`write_structured`] for the shape), so that
/// writing a new value over a stored one writes only what changed.
///
/// [`ValueCodec::write`] is [`write_structured`]: it writes the parts of
/// the value that differ from what's at the cursor, and nothing else. A
/// [`Map`](crate::Map) opens its collection and the key before calling it,
/// so [`Map::put`](crate::Map::put) of an unchanged value still copies the
/// path to it; use [`put_structured`] for a value that's often unchanged.
///
/// A value that doesn't deserialize as `T` is an [`Error::Decode`] whose
/// [`DecodeError::field`](crate::DecodeError::field) is the path to the
/// part that didn't, like `"clusters.3.checks.0.state"`.
///
/// ```
/// use serde::{Deserialize, Serialize};
/// use xitdb::{Database, History, Map, Structured};
///
/// #[derive(Serialize, Deserialize, Debug, PartialEq)]
/// struct Check {
///     name: String,
///     passed: bool,
/// }
///
/// const CHECKS: Map<str, Structured<Vec<Check>>> = Map::new("checks");
///
/// # fn main() -> xitdb::Result<()> {
/// let db = Database::in_memory()?;
/// let history = History::new(&db)?;
/// let checks = vec![Check { name: "build".into(), passed: true }];
/// history.transact(|moment| CHECKS.put(moment, "pr/1", &checks))?;
/// assert_eq!(CHECKS.get(&history.latest()?, "pr/1")?, Some(checks));
/// # Ok(())
/// # }
/// ```
pub struct Structured<T>(PhantomData<fn() -> T>);

impl<T: Serialize + DeserializeOwned> ValueCodec for Structured<T> {
    type Owned = T;
    type Borrowed = T;

    fn read<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<T> {
        read_structured(cursor)
    }

    fn write<C: Core>(value: &T, cursor: &mut WriteCursor<'_, C>) -> Result<()> {
        write_structured(cursor, value).map(drop)
    }
}

/// Reads a value that [`write_structured`] wrote, or any data of the same
/// shape. Keys of a hash map whose values are empty ([`Data::None`]) are
/// skipped, like missing ones.
pub fn read_structured<C: Core, T: DeserializeOwned>(cursor: &ReadCursor<'_, C>) -> Result<T> {
    T::deserialize(ValueDe { cursor: cursor.resolved_cursor()? }).map_err(|err| err.0)
}

/// Writes `value` at `cursor` as nested data (see [`Structured`]), writing
/// only what differs from what's stored there, and returns whether it
/// wrote anything.
///
/// It reads what's stored as it serializes, and compares:
///
/// * A scalar is only written if it differs, as [`ReadCursor::equals`]
///   compares (so floats compare by their bits).
/// * A struct or map over a stored hash map changes it in place: each
///   field is compared the same way, recursively, fields that are `None`
///   or no longer there are removed, and new ones are added.
/// * A sequence over a stored array list is compared item by item, by
///   index. Items past the stored length are appended, and if the new
///   sequence is shorter, the list is sliced to its length.
/// * Anything stored of another kind is replaced.
///
/// Containers are only opened for writing once something in them differs,
/// so an unchanged part writes nothing, and an unchanged value writes
/// nothing at all. A small change writes the changed values and a copy of
/// the blocks along the path to them, not the rest of the value.
///
/// Lists are compared by index, so inserting, removing or reordering items
/// anywhere but at the end changes every item after that point, and they're
/// all written again. Store a collection whose items have IDs as a map
/// keyed by ID, along with a list of the IDs if the order matters.
///
/// It must run inside a transaction, such as [`History::transact`]. A
/// value that can't be serialized (a map key of an unsupported type, or a
/// 128-bit integer that doesn't fit in 64 bits) is an [`Error::Io`], as
/// for [`Json`](crate::Json); what was written before it stays written,
/// and is discarded with the transaction if the error is returned from it.
///
/// [`History::transact`]: crate::History::transact
pub fn write_structured<C: Core, T: Serialize + ?Sized>(cursor: &mut WriteCursor<'_, C>, value: &T) -> Result<bool> {
    let existing = Some(cursor.read.resolved_cursor()?);
    let mut root = CursorRoot { cursor, opened: false };
    let place = Place { target: Target::Child(&mut root, Key::Root), existing, opened: None };
    value.serialize(ValueSer { place, optional: false }).map_err(|err| err.0)?;
    let opened = root.opened;
    // the writes went through a copy of the cursor, so catch it up
    if opened
        && let Some(position) = cursor.read.slot_ptr.position
        && !is_root(&cursor.read.slot_ptr)
    {
        let slot = cursor.read.db.read_slot_at(position)?;
        cursor.read.slot_ptr = cursor.read.slot_ptr.with_slot(slot);
    }
    Ok(opened)
}

/// Writes `value` under `key` in `map`, as [`write_structured`] does, and
/// returns whether it wrote anything. The key is only opened if something
/// changed, so if nothing did, nothing at all is written, and
/// [`History::transact`] doesn't commit a new moment. A value that
/// serializes as `None` removes `key`.
///
/// [`History::transact`]: crate::History::transact
pub fn put_structured<C: Core, T: Serialize + ?Sized>(
    map: &mut WriteHashMap<'_, C>,
    key: impl AsRef<[u8]>,
    value: &T,
) -> Result<bool> {
    let key = key.as_ref();
    let existing = map.get_cursor(key)?;
    let had_key = existing.is_some();
    let mut root = MapRoot { map, opened: false };
    let place = Place { target: Target::Child(&mut root, Key::Map(key.to_vec())), existing, opened: None };
    let present = value.serialize(ValueSer { place, optional: true }).map_err(|err| err.0)?;
    let mut wrote = root.opened;
    if !present && had_key {
        wrote |= map.remove(key)?;
    }
    Ok(wrote)
}

/// Reads the value under `key` in `map`, as [`read_structured`] does, or
/// `None` if `key` is missing or its value is empty.
pub fn get_structured<C: Core, T: DeserializeOwned>(
    map: &ReadHashMap<'_, C>,
    key: impl AsRef<[u8]>,
) -> Result<Option<T>> {
    map.get_value_cursor(key)?.map(|cursor| read_structured(&cursor)).transpose()
}

// Errors

/// xitdb's error, as serde's serializers and deserializers need an error
/// type of their own.
struct Wrapped(Error);

impl From<Error> for Wrapped {
    fn from(err: Error) -> Self {
        Wrapped(err)
    }
}

impl fmt::Debug for Wrapped {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for Wrapped {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl std::error::Error for Wrapped {}

impl ser::Error for Wrapped {
    fn custom<M: fmt::Display>(msg: M) -> Self {
        Wrapped(Error::Io(io::Error::new(io::ErrorKind::InvalidInput, msg.to_string())))
    }
}

impl de::Error for Wrapped {
    fn custom<M: fmt::Display>(msg: M) -> Self {
        Wrapped(Error::decode(msg.to_string()))
    }
}

impl Wrapped {
    /// Adds `name` to the front of the path of a decode error.
    fn in_field(self, name: impl fmt::Display) -> Wrapped {
        let mut decode = match self.0 {
            Error::Decode(decode) => decode,
            other => return Wrapped(other),
        };
        decode.field = Some(match decode.field.take() {
            Some(inner) => format!("{name}.{inner}"),
            None => name.to_string(),
        });
        Wrapped(Error::Decode(decode))
    }
}

type SerResult<T> = std::result::Result<T, Wrapped>;

// Writing

/// Where a value is, in the container it's in.
enum Key {
    /// The value that a root writes.
    Root,
    Map(Vec<u8>),
    Index(i64),
    Append,
}

/// A container that values are written into, opened for writing only when
/// one of them needs to be.
trait Parent<'a, C: Core> {
    /// Opens the container if it isn't yet, and returns a cursor to `key`.
    fn child(&mut self, key: &Key) -> Result<WriteCursor<'a, C>>;
}

/// The cursor given to [`write_structured`].
struct CursorRoot<'r, 'a, C: Core> {
    cursor: &'r mut WriteCursor<'a, C>,
    opened: bool,
}

impl<'a, C: Core> Parent<'a, C> for CursorRoot<'_, 'a, C> {
    fn child(&mut self, _: &Key) -> Result<WriteCursor<'a, C>> {
        self.opened = true;
        Ok(self.cursor.clone())
    }
}

/// The map given to [`put_structured`].
struct MapRoot<'r, 'a, C: Core> {
    map: &'r mut WriteHashMap<'a, C>,
    opened: bool,
}

impl<'a, C: Core> Parent<'a, C> for MapRoot<'_, 'a, C> {
    fn child(&mut self, key: &Key) -> Result<WriteCursor<'a, C>> {
        let Key::Map(key) = key else { unreachable!("a map root only has map keys") };
        self.opened = true;
        self.map.put_cursor(key)
    }
}

/// The place a value is written to: a key in its parent, with what's
/// stored there now, and a cursor to it once it's opened.
struct Place<'p, 'a, C: Core> {
    target: Target<'p, 'a, C>,
    existing: Option<ReadCursor<'a, C>>,
    opened: Option<WriteCursor<'a, C>>,
}

enum Target<'p, 'a, C: Core> {
    Child(&'p mut dyn Parent<'a, C>, Key),
    /// The contents of a tuple or struct variant, in the map that holds its
    /// name, which is finished along with them.
    Variant { outer: Box<MapSer<'p, 'a, C>>, key: Vec<u8>, hash: Option<Vec<u8>> },
}

impl<'a, C: Core> Place<'_, 'a, C> {
    /// A cursor to the place, opening it (and its parents) if it isn't yet.
    fn cursor(&mut self) -> Result<&mut WriteCursor<'a, C>> {
        if self.opened.is_none() {
            let cursor = match &mut self.target {
                Target::Child(parent, key) => parent.child(key)?,
                Target::Variant { outer, key, .. } => outer.child(&Key::Map(key.clone()))?,
            };
            self.opened = Some(cursor);
        }
        Ok(self.opened.as_mut().expect("the place was just opened"))
    }

    /// The tag of what's stored, or `None` if nothing is.
    fn existing_tag(&self) -> Result<Option<Tag>> {
        self.existing.as_ref().map(|cursor| Ok(cursor.slot()?.tag)).transpose()
    }

    /// Writes `data` unless it's already there.
    fn write(&mut self, data: Data<'_>) -> Result<()> {
        if let Some(existing) = &self.existing
            && existing.equals_data(&data)?
        {
            return Ok(());
        }
        self.cursor()?.write(data)
    }

    /// For a container: opens the place, replacing what's stored if it
    /// isn't `tag` or empty.
    fn open_container(&mut self, tag: Tag) -> Result<&mut WriteCursor<'a, C>> {
        let replace = !matches!(self.existing_tag()?, None | Some(Tag::None)) && self.existing_tag()? != Some(tag);
        let cursor = self.cursor()?;
        if replace {
            cursor.write(Data::None)?;
        }
        Ok(cursor)
    }

    /// Finishes the variant whose contents this place holds, if it does.
    fn finish(self) -> SerResult<()> {
        if let Target::Variant { mut outer, hash, .. } = self.target {
            outer.seen.extend(hash);
            outer.finish()?;
        }
        Ok(())
    }
}

/// Serializes a value into a [`Place`]. `Ok` is whether the value is
/// present: `None` and `()` aren't, where they're `optional`, so the parent
/// map leaves their key out.
struct ValueSer<'p, 'a, C: Core> {
    place: Place<'p, 'a, C>,
    optional: bool,
}

impl<'a, C: Core> ValueSer<'_, 'a, C> {
    fn scalar(mut self, data: Data<'_>) -> SerResult<bool> {
        self.place.write(data)?;
        Ok(true)
    }

    fn none(self) -> SerResult<bool> {
        if self.optional {
            return Ok(false);
        }
        self.scalar(Data::None)
    }
}

fn too_big(value: impl fmt::Display) -> Wrapped {
    ser::Error::custom(format_args!("{value} doesn't fit in 64 bits"))
}

impl<'p, 'a, C: Core> ser::Serializer for ValueSer<'p, 'a, C> {
    type Ok = bool;
    type Error = Wrapped;
    type SerializeSeq = SeqSer<'p, 'a, C>;
    type SerializeTuple = SeqSer<'p, 'a, C>;
    type SerializeTupleStruct = SeqSer<'p, 'a, C>;
    type SerializeTupleVariant = SeqSer<'p, 'a, C>;
    type SerializeMap = MapSer<'p, 'a, C>;
    type SerializeStruct = MapSer<'p, 'a, C>;
    type SerializeStructVariant = MapSer<'p, 'a, C>;

    fn serialize_bool(self, v: bool) -> SerResult<bool> {
        self.scalar(Data::Uint(u64::from(v)))
    }

    fn serialize_i8(self, v: i8) -> SerResult<bool> {
        self.scalar(Data::Int(v.into()))
    }

    fn serialize_i16(self, v: i16) -> SerResult<bool> {
        self.scalar(Data::Int(v.into()))
    }

    fn serialize_i32(self, v: i32) -> SerResult<bool> {
        self.scalar(Data::Int(v.into()))
    }

    fn serialize_i64(self, v: i64) -> SerResult<bool> {
        self.scalar(Data::Int(v))
    }

    fn serialize_i128(self, v: i128) -> SerResult<bool> {
        self.scalar(Data::Int(i64::try_from(v).map_err(|_| too_big(v))?))
    }

    fn serialize_u8(self, v: u8) -> SerResult<bool> {
        self.scalar(Data::Uint(v.into()))
    }

    fn serialize_u16(self, v: u16) -> SerResult<bool> {
        self.scalar(Data::Uint(v.into()))
    }

    fn serialize_u32(self, v: u32) -> SerResult<bool> {
        self.scalar(Data::Uint(v.into()))
    }

    fn serialize_u64(self, v: u64) -> SerResult<bool> {
        self.scalar(Data::Uint(v))
    }

    fn serialize_u128(self, v: u128) -> SerResult<bool> {
        self.scalar(Data::Uint(u64::try_from(v).map_err(|_| too_big(v))?))
    }

    fn serialize_f32(self, v: f32) -> SerResult<bool> {
        self.scalar(Data::Float(v.into()))
    }

    fn serialize_f64(self, v: f64) -> SerResult<bool> {
        self.scalar(Data::Float(v))
    }

    fn serialize_char(self, v: char) -> SerResult<bool> {
        self.scalar(Data::bytes(v.encode_utf8(&mut [0; 4]).as_bytes().to_vec()))
    }

    fn serialize_str(self, v: &str) -> SerResult<bool> {
        self.scalar(Data::string(v))
    }

    fn serialize_bytes(self, v: &[u8]) -> SerResult<bool> {
        self.scalar(Data::bytes(v))
    }

    fn serialize_none(self) -> SerResult<bool> {
        self.none()
    }

    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> SerResult<bool> {
        value.serialize(self)
    }

    fn serialize_unit(self) -> SerResult<bool> {
        self.none()
    }

    fn serialize_unit_struct(self, _name: &'static str) -> SerResult<bool> {
        self.none()
    }

    fn serialize_unit_variant(self, _name: &'static str, _index: u32, variant: &'static str) -> SerResult<bool> {
        self.scalar(Data::string(variant))
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(self, _name: &'static str, value: &T) -> SerResult<bool> {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        value: &T,
    ) -> SerResult<bool> {
        let mut outer = MapSer::new(self.place)?;
        outer.field(variant.as_bytes(), value, false)?;
        outer.finish()
    }

    fn serialize_seq(self, _len: Option<usize>) -> SerResult<SeqSer<'p, 'a, C>> {
        SeqSer::new(self.place)
    }

    fn serialize_tuple(self, _len: usize) -> SerResult<SeqSer<'p, 'a, C>> {
        SeqSer::new(self.place)
    }

    fn serialize_tuple_struct(self, _name: &'static str, _len: usize) -> SerResult<SeqSer<'p, 'a, C>> {
        SeqSer::new(self.place)
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> SerResult<SeqSer<'p, 'a, C>> {
        SeqSer::new(variant_place(self.place, variant)?)
    }

    fn serialize_map(self, _len: Option<usize>) -> SerResult<MapSer<'p, 'a, C>> {
        MapSer::new(self.place)
    }

    fn serialize_struct(self, _name: &'static str, _len: usize) -> SerResult<MapSer<'p, 'a, C>> {
        MapSer::new(self.place)
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        variant: &'static str,
        _len: usize,
    ) -> SerResult<MapSer<'p, 'a, C>> {
        MapSer::new(variant_place(self.place, variant)?)
    }
}

/// The place for the contents of a tuple or struct variant: the value of
/// the variant's name, in a map at `place`.
fn variant_place<'p, 'a, C: Core>(place: Place<'p, 'a, C>, variant: &str) -> SerResult<Place<'p, 'a, C>> {
    let outer = MapSer::new(place)?;
    let key = variant.as_bytes().to_vec();
    let (hash, existing) = outer.lookup(&key)?;
    Ok(Place { target: Target::Variant { outer: Box::new(outer), key, hash }, existing, opened: None })
}

/// The hash of a key in a stored map, if there is one, and what's stored
/// at it, if anything.
type Lookup<'a, C> = (Option<Vec<u8>>, Option<ReadCursor<'a, C>>);

/// Serializes a struct, a map, or the map around a variant, into a hash map.
struct MapSer<'p, 'a, C: Core> {
    place: Place<'p, 'a, C>,
    /// The stored map, if there is one.
    existing: Option<ReadHashMap<'a, C>>,
    map: Option<WriteHashMap<'a, C>>,
    /// The hashes of the stored map's keys that are still present.
    seen: HashSet<Vec<u8>>,
    /// The key of a map entry whose value is next.
    key: Option<Vec<u8>>,
}

impl<'p, 'a, C: Core> MapSer<'p, 'a, C> {
    fn new(place: Place<'p, 'a, C>) -> SerResult<Self> {
        let existing = match &place.existing {
            Some(cursor) if cursor.slot()?.tag == Tag::HashMap => Some(ReadHashMap::new(cursor.clone())?),
            _ => None,
        };
        let mut ser = MapSer { place, existing, map: None, seen: HashSet::new(), key: None };
        // a new map is written even if it stays empty
        if ser.existing.is_none() {
            ser.open()?;
        }
        Ok(ser)
    }

    fn open(&mut self) -> Result<&mut WriteHashMap<'a, C>> {
        if self.map.is_none() {
            let cursor = self.place.open_container(Tag::HashMap)?;
            self.map = Some(WriteHashMap::new(cursor)?);
        }
        Ok(self.map.as_mut().expect("the map was just opened"))
    }

    /// The hash of `key`, and what's stored at it, in the stored map.
    fn lookup(&self, key: &[u8]) -> Result<Lookup<'a, C>> {
        let Some(existing) = &self.existing else { return Ok((None, None)) };
        let hash = existing.hash(key);
        let cursor = existing.get_cursor_by_hash(&hash)?;
        Ok((Some(hash), cursor))
    }

    fn field<T: Serialize + ?Sized>(&mut self, key: &[u8], value: &T, optional: bool) -> SerResult<()> {
        let (hash, existing) = self.lookup(key)?;
        let place = Place { target: Target::Child(self, Key::Map(key.to_vec())), existing, opened: None };
        if value.serialize(ValueSer { place, optional })? {
            self.seen.extend(hash);
        }
        Ok(())
    }

    /// Removes the stored keys that weren't written again.
    fn finish(mut self) -> SerResult<bool> {
        if let Some(existing) = &self.existing {
            let mut stale = Vec::new();
            for kv in existing.entries()? {
                let kv = kv?;
                if !self.seen.contains(&kv.hash) {
                    stale.push(kv.hash);
                }
            }
            for hash in stale {
                self.open()?.remove_by_hash(&hash)?;
            }
        }
        self.place.finish()?;
        Ok(true)
    }
}

impl<'a, C: Core> Parent<'a, C> for MapSer<'_, 'a, C> {
    fn child(&mut self, key: &Key) -> Result<WriteCursor<'a, C>> {
        let Key::Map(key) = key else { unreachable!("a map only has map keys") };
        self.open()?.put_cursor(key)
    }
}

impl<C: Core> ser::SerializeStruct for MapSer<'_, '_, C> {
    type Ok = bool;
    type Error = Wrapped;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, key: &'static str, value: &T) -> SerResult<()> {
        self.field(key.as_bytes(), value, true)
    }

    fn end(self) -> SerResult<bool> {
        self.finish()
    }
}

impl<C: Core> ser::SerializeStructVariant for MapSer<'_, '_, C> {
    type Ok = bool;
    type Error = Wrapped;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, key: &'static str, value: &T) -> SerResult<()> {
        self.field(key.as_bytes(), value, true)
    }

    fn end(self) -> SerResult<bool> {
        self.finish()
    }
}

impl<C: Core> ser::SerializeMap for MapSer<'_, '_, C> {
    type Ok = bool;
    type Error = Wrapped;

    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> SerResult<()> {
        self.key = Some(key.serialize(KeySer)?);
        Ok(())
    }

    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> SerResult<()> {
        let key = self.key.take().ok_or_else(|| <Wrapped as ser::Error>::custom("a map value came before its key"))?;
        self.field(&key, value, true)
    }

    fn end(self) -> SerResult<bool> {
        self.finish()
    }
}

/// Serializes a sequence, a tuple, or the contents of a tuple variant, into
/// an array list.
struct SeqSer<'p, 'a, C: Core> {
    place: Place<'p, 'a, C>,
    /// The stored list, if there is one, and its length.
    existing: Option<ReadArrayList<'a, C>>,
    existing_len: i64,
    list: Option<WriteArrayList<'a, C>>,
    /// The index of the next item.
    index: i64,
}

impl<'p, 'a, C: Core> SeqSer<'p, 'a, C> {
    fn new(place: Place<'p, 'a, C>) -> SerResult<Self> {
        let existing = match &place.existing {
            Some(cursor) if cursor.slot()?.tag == Tag::ArrayList => Some(ReadArrayList::new(cursor.clone())?),
            _ => None,
        };
        let existing_len = existing.as_ref().map(|list| list.count()).transpose()?.unwrap_or(0);
        let mut ser = SeqSer { place, existing, existing_len, list: None, index: 0 };
        // a new list is written even if it stays empty
        if ser.existing.is_none() {
            ser.open()?;
        }
        Ok(ser)
    }

    fn open(&mut self) -> Result<&mut WriteArrayList<'a, C>> {
        if self.list.is_none() {
            let cursor = self.place.open_container(Tag::ArrayList)?;
            self.list = Some(WriteArrayList::new(cursor)?);
        }
        Ok(self.list.as_mut().expect("the list was just opened"))
    }

    fn item<T: Serialize + ?Sized>(&mut self, value: &T) -> SerResult<()> {
        let (key, existing) = match &self.existing {
            Some(list) if self.index < self.existing_len => (Key::Index(self.index), list.get_cursor(self.index)?),
            _ => (Key::Append, None),
        };
        let place = Place { target: Target::Child(self, key), existing, opened: None };
        value.serialize(ValueSer { place, optional: false })?;
        self.index += 1;
        Ok(())
    }

    /// Removes the stored items past the new length.
    fn finish(mut self) -> SerResult<bool> {
        if self.index < self.existing_len {
            let len = self.index;
            self.open()?.slice(len)?;
        }
        self.place.finish()?;
        Ok(true)
    }
}

impl<'a, C: Core> Parent<'a, C> for SeqSer<'_, 'a, C> {
    fn child(&mut self, key: &Key) -> Result<WriteCursor<'a, C>> {
        match *key {
            Key::Index(index) => self.open()?.put_cursor(index),
            Key::Append => self.open()?.append_cursor(),
            _ => unreachable!("a list only has indexes"),
        }
    }
}

macro_rules! seq_impls {
    ($($trait:ident :: $method:ident),*) => {
        $(
            impl<C: Core> ser::$trait for SeqSer<'_, '_, C> {
                type Ok = bool;
                type Error = Wrapped;

                fn $method<T: Serialize + ?Sized>(&mut self, value: &T) -> SerResult<()> {
                    self.item(value)
                }

                fn end(self) -> SerResult<bool> {
                    self.finish()
                }
            }
        )*
    };
}

seq_impls!(
    SerializeSeq::serialize_element,
    SerializeTuple::serialize_element,
    SerializeTupleStruct::serialize_field,
    SerializeTupleVariant::serialize_field
);

/// Serializes a map key to the bytes it's stored as.
struct KeySer;

fn bad_key() -> Wrapped {
    ser::Error::custom("a map key must be a string, bytes, an integer, a bool, a char or a unit variant")
}

macro_rules! key_as_text {
    ($($method:ident: $ty:ty),*) => {
        $(
            fn $method(self, v: $ty) -> SerResult<Vec<u8>> {
                Ok(v.to_string().into_bytes())
            }
        )*
    };
}

impl ser::Serializer for KeySer {
    type Ok = Vec<u8>;
    type Error = Wrapped;
    type SerializeSeq = ser::Impossible<Vec<u8>, Wrapped>;
    type SerializeTuple = ser::Impossible<Vec<u8>, Wrapped>;
    type SerializeTupleStruct = ser::Impossible<Vec<u8>, Wrapped>;
    type SerializeTupleVariant = ser::Impossible<Vec<u8>, Wrapped>;
    type SerializeMap = ser::Impossible<Vec<u8>, Wrapped>;
    type SerializeStruct = ser::Impossible<Vec<u8>, Wrapped>;
    type SerializeStructVariant = ser::Impossible<Vec<u8>, Wrapped>;

    key_as_text!(
        serialize_bool: bool, serialize_i8: i8, serialize_i16: i16, serialize_i32: i32, serialize_i64: i64,
        serialize_i128: i128, serialize_u8: u8, serialize_u16: u16, serialize_u32: u32, serialize_u64: u64,
        serialize_u128: u128, serialize_char: char, serialize_str: &str
    );

    fn serialize_f32(self, _v: f32) -> SerResult<Vec<u8>> {
        Err(bad_key())
    }

    fn serialize_f64(self, _v: f64) -> SerResult<Vec<u8>> {
        Err(bad_key())
    }

    fn serialize_bytes(self, v: &[u8]) -> SerResult<Vec<u8>> {
        Ok(v.to_vec())
    }

    fn serialize_none(self) -> SerResult<Vec<u8>> {
        Err(bad_key())
    }

    fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> SerResult<Vec<u8>> {
        value.serialize(self)
    }

    fn serialize_unit(self) -> SerResult<Vec<u8>> {
        Err(bad_key())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> SerResult<Vec<u8>> {
        Err(bad_key())
    }

    fn serialize_unit_variant(self, _name: &'static str, _index: u32, variant: &'static str) -> SerResult<Vec<u8>> {
        Ok(variant.as_bytes().to_vec())
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(self, _name: &'static str, value: &T) -> SerResult<Vec<u8>> {
        value.serialize(self)
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> SerResult<Vec<u8>> {
        Err(bad_key())
    }

    fn serialize_seq(self, _len: Option<usize>) -> SerResult<Self::SerializeSeq> {
        Err(bad_key())
    }

    fn serialize_tuple(self, _len: usize) -> SerResult<Self::SerializeTuple> {
        Err(bad_key())
    }

    fn serialize_tuple_struct(self, _name: &'static str, _len: usize) -> SerResult<Self::SerializeTupleStruct> {
        Err(bad_key())
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> SerResult<Self::SerializeTupleVariant> {
        Err(bad_key())
    }

    fn serialize_map(self, _len: Option<usize>) -> SerResult<Self::SerializeMap> {
        Err(bad_key())
    }

    fn serialize_struct(self, _name: &'static str, _len: usize) -> SerResult<Self::SerializeStruct> {
        Err(bad_key())
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> SerResult<Self::SerializeStructVariant> {
        Err(bad_key())
    }
}

// Reading

/// Deserializes the value at a cursor.
struct ValueDe<'a, C: Core> {
    cursor: ReadCursor<'a, C>,
}

impl<'a, C: Core> ValueDe<'a, C> {
    fn tag(&self) -> Result<Tag> {
        Ok(self.cursor.slot()?.tag)
    }

    fn unexpected(&self, expected: &str) -> SerResult<Wrapped> {
        Ok(de::Error::custom(format_args!("expected {expected}, found {:?}", self.tag()?)))
    }
}

impl<'de, C: Core> de::Deserializer<'de> for ValueDe<'_, C> {
    type Error = Wrapped;

    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        let slot = self.cursor.slot()?;
        match slot.tag {
            Tag::None => visitor.visit_unit(),
            Tag::Uint => visitor.visit_u64(slot.value as u64),
            Tag::Int => visitor.visit_i64(slot.value),
            Tag::Float => visitor.visit_f64(f64::from_bits(slot.value as u64)),
            Tag::Bytes | Tag::ShortBytes => match String::from_utf8(self.cursor.read_bytes(None)?) {
                Ok(string) => visitor.visit_string(string),
                Err(err) => visitor.visit_byte_buf(err.into_bytes()),
            },
            Tag::HashMap => visitor.visit_map(MapDe::new(&self.cursor)?),
            Tag::ArrayList => visitor.visit_seq(SeqDe::new(&self.cursor)?),
            _ => Err(self.unexpected("a hash map, an array list or a scalar")?),
        }
    }

    fn deserialize_bool<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        let slot = self.cursor.slot()?;
        match (slot.tag, slot.value) {
            (Tag::Uint, 0) => visitor.visit_bool(false),
            (Tag::Uint, 1) => visitor.visit_bool(true),
            _ => Err(self.unexpected("a bool (the Uint 0 or 1)")?),
        }
    }

    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        match self.tag()? {
            Tag::None => visitor.visit_none(),
            _ => visitor.visit_some(self),
        }
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(self, _name: &'static str, visitor: V) -> SerResult<V::Value> {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        match self.tag()? {
            Tag::Bytes | Tag::ShortBytes => visitor.visit_byte_buf(self.cursor.read_bytes(None)?),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        self.deserialize_bytes(visitor)
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> SerResult<V::Value> {
        match self.tag()? {
            Tag::Bytes | Tag::ShortBytes => {
                let variant: String = self.cursor.read_string(None)?;
                visitor.visit_enum(variant.into_deserializer())
            }
            Tag::HashMap => {
                let mut entries = ReadHashMap::new(self.cursor.clone())?.entries()?;
                let (Some(entry), None) = (entries.next(), entries.next()) else {
                    return Err(de::Error::custom("expected a map with one key, the variant's name"));
                };
                let kv = entry?;
                let variant = String::from_utf8(read_key(&kv.key_cursor)?)
                    .map_err(|_| <Wrapped as de::Error>::custom("a variant's name isn't valid utf-8"))?;
                visitor.visit_enum(EnumDe { variant, content: kv.value_cursor })
            }
            _ => Err(self.unexpected("a variant's name, or a map with one key")?),
        }
    }

    fn deserialize_ignored_any<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        visitor.visit_unit()
    }

    serde::forward_to_deserialize_any! {
        i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string unit unit_struct seq tuple tuple_struct map
        struct identifier
    }
}

/// The bytes of a stored map key.
fn read_key<C: Core>(cursor: &ReadCursor<'_, C>) -> Result<Vec<u8>> {
    match cursor.slot()?.tag {
        Tag::Bytes | Tag::ShortBytes => cursor.read_bytes(None),
        tag => Err(Error::decode(format!("expected a byte array key, found {tag:?}"))),
    }
}

/// The entries of a hash map, skipping empty values.
struct MapDe<'a, C: Core> {
    entries: KvPairIterator<'a, C>,
    value: Option<ReadCursor<'a, C>>,
    key: Vec<u8>,
}

impl<'a, C: Core> MapDe<'a, C> {
    fn new(cursor: &ReadCursor<'a, C>) -> Result<Self> {
        Ok(MapDe { entries: ReadHashMap::new(cursor.clone())?.entries()?, value: None, key: Vec::new() })
    }
}

impl<'de, C: Core> de::MapAccess<'de> for MapDe<'_, C> {
    type Error = Wrapped;

    fn next_key_seed<K: DeserializeSeed<'de>>(&mut self, seed: K) -> SerResult<Option<K::Value>> {
        for kv in self.entries.by_ref() {
            let kv = kv?;
            if !has_value(&kv.value_cursor) {
                continue;
            }
            self.key = read_key(&kv.key_cursor)?;
            self.value = Some(kv.value_cursor);
            return seed.deserialize(KeyDe { key: self.key.clone() }).map(Some);
        }
        Ok(None)
    }

    fn next_value_seed<V: DeserializeSeed<'de>>(&mut self, seed: V) -> SerResult<V::Value> {
        let cursor = self.value.take().ok_or_else(|| <Wrapped as de::Error>::custom("a map value without a key"))?;
        seed.deserialize(ValueDe { cursor }).map_err(|err| err.in_field(String::from_utf8_lossy(&self.key)))
    }
}

/// The items of an array list.
struct SeqDe<'a, C: Core> {
    items: CursorIterator<'a, C>,
    index: i64,
    len: i64,
}

impl<'a, C: Core> SeqDe<'a, C> {
    fn new(cursor: &ReadCursor<'a, C>) -> Result<Self> {
        let list = ReadArrayList::new(cursor.clone())?;
        Ok(SeqDe { items: list.iter()?, index: 0, len: list.count()? })
    }
}

impl<'de, C: Core> de::SeqAccess<'de> for SeqDe<'_, C> {
    type Error = Wrapped;

    fn next_element_seed<T: DeserializeSeed<'de>>(&mut self, seed: T) -> SerResult<Option<T::Value>> {
        let Some(cursor) = self.items.next() else { return Ok(None) };
        let index = self.index;
        self.index += 1;
        seed.deserialize(ValueDe { cursor: cursor? }).map(Some).map_err(|err| err.in_field(index))
    }

    fn size_hint(&self) -> Option<usize> {
        usize::try_from(self.len - self.index).ok()
    }
}

/// A variant stored as a map with one key.
struct EnumDe<'a, C: Core> {
    variant: String,
    content: ReadCursor<'a, C>,
}

impl<'de, 'a, C: Core> de::EnumAccess<'de> for EnumDe<'a, C> {
    type Error = Wrapped;
    type Variant = VariantDe<'a, C>;

    fn variant_seed<V: DeserializeSeed<'de>>(self, seed: V) -> SerResult<(V::Value, VariantDe<'a, C>)> {
        let name: de::value::StrDeserializer<'_, Wrapped> = self.variant.as_str().into_deserializer();
        let value = seed.deserialize(name)?;
        Ok((value, VariantDe { variant: self.variant, content: ValueDe { cursor: self.content } }))
    }
}

struct VariantDe<'a, C: Core> {
    variant: String,
    content: ValueDe<'a, C>,
}

impl<'de, C: Core> de::VariantAccess<'de> for VariantDe<'_, C> {
    type Error = Wrapped;

    fn unit_variant(self) -> SerResult<()> {
        Ok(())
    }

    fn newtype_variant_seed<T: DeserializeSeed<'de>>(self, seed: T) -> SerResult<T::Value> {
        let variant = self.variant;
        seed.deserialize(self.content).map_err(|err| err.in_field(variant))
    }

    fn tuple_variant<V: Visitor<'de>>(self, _len: usize, visitor: V) -> SerResult<V::Value> {
        let variant = self.variant;
        de::Deserializer::deserialize_seq(self.content, visitor).map_err(|err| err.in_field(variant))
    }

    fn struct_variant<V: Visitor<'de>>(self, _fields: &'static [&'static str], visitor: V) -> SerResult<V::Value> {
        let variant = self.variant;
        de::Deserializer::deserialize_map(self.content, visitor).map_err(|err| err.in_field(variant))
    }
}

/// Deserializes a map key from its bytes: a string, bytes, or a number, a
/// bool or a char from its text.
struct KeyDe {
    key: Vec<u8>,
}

impl KeyDe {
    fn text(&self) -> SerResult<&str> {
        std::str::from_utf8(&self.key).map_err(|_| de::Error::custom("a map key isn't valid utf-8"))
    }

    fn parse<T: std::str::FromStr>(&self, kind: &str) -> SerResult<T> {
        let text = self.text()?;
        text.parse().map_err(|_| de::Error::custom(format_args!("expected {kind} map key, found {text:?}")))
    }
}

macro_rules! key_from_text {
    ($($method:ident => $visit:ident: $ty:ty),*) => {
        $(
            fn $method<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
                visitor.$visit(self.parse::<$ty>(stringify!($ty))?)
            }
        )*
    };
}

impl<'de> de::Deserializer<'de> for KeyDe {
    type Error = Wrapped;

    fn deserialize_any<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        match String::from_utf8(self.key) {
            Ok(string) => visitor.visit_string(string),
            Err(err) => visitor.visit_byte_buf(err.into_bytes()),
        }
    }

    key_from_text!(
        deserialize_bool => visit_bool: bool, deserialize_i8 => visit_i8: i8, deserialize_i16 => visit_i16: i16,
        deserialize_i32 => visit_i32: i32, deserialize_i64 => visit_i64: i64, deserialize_i128 => visit_i128: i128,
        deserialize_u8 => visit_u8: u8, deserialize_u16 => visit_u16: u16, deserialize_u32 => visit_u32: u32,
        deserialize_u64 => visit_u64: u64, deserialize_u128 => visit_u128: u128, deserialize_char => visit_char: char
    );

    fn deserialize_bytes<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        visitor.visit_byte_buf(self.key)
    }

    fn deserialize_byte_buf<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        visitor.visit_byte_buf(self.key)
    }

    fn deserialize_option<V: Visitor<'de>>(self, visitor: V) -> SerResult<V::Value> {
        visitor.visit_some(self)
    }

    fn deserialize_newtype_struct<V: Visitor<'de>>(self, _name: &'static str, visitor: V) -> SerResult<V::Value> {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_enum<V: Visitor<'de>>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> SerResult<V::Value> {
        visitor.visit_enum(self.text()?.into_deserializer())
    }

    serde::forward_to_deserialize_any! {
        f32 f64 str string unit unit_struct seq tuple tuple_struct map struct identifier ignored_any
    }
}
