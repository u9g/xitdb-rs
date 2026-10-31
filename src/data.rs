use std::borrow::Cow;

use crate::slot::Slot;

/// A byte array, optionally with a 2-byte format tag that tells readers
/// how to interpret it (for example `b"bi"` for a big integer).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct Bytes<'a> {
    pub value: Cow<'a, [u8]>,
    pub format_tag: Option<[u8; 2]>,
}

impl<'a> Bytes<'a> {
    pub fn new(value: impl Into<Cow<'a, [u8]>>) -> Bytes<'a> {
        Bytes { value: value.into(), format_tag: None }
    }

    pub fn tagged(value: impl Into<Cow<'a, [u8]>>, format_tag: [u8; 2]) -> Bytes<'a> {
        Bytes { value: value.into(), format_tag: Some(format_tag) }
    }

    /// Whether the bytes fit inline in a slot. Short bytes can't contain
    /// zeroes, because a zero marks the end of the value.
    pub fn is_short(&self) -> bool {
        let total_size = if self.format_tag.is_some() { 6 } else { 8 };
        self.value.len() <= total_size && !self.value.contains(&0)
    }

    pub fn into_owned(self) -> Bytes<'static> {
        Bytes { value: Cow::Owned(self.value.into_owned()), format_tag: self.format_tag }
    }
}

/// Anything that can be written to a slot.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum Data<'a> {
    /// Clears the slot. It is still marked as written, so it isn't
    /// treated as empty.
    #[default]
    None,
    /// Writes a slot as-is, which is how a data structure is cloned.
    Slot(Slot),
    Uint(u64),
    Int(i64),
    Float(f64),
    Bytes(Bytes<'a>),
}

impl<'a> Data<'a> {
    pub fn bytes(value: impl Into<Cow<'a, [u8]>>) -> Data<'a> {
        Data::Bytes(Bytes::new(value))
    }

    pub fn tagged_bytes(value: impl Into<Cow<'a, [u8]>>, format_tag: [u8; 2]) -> Data<'a> {
        Data::Bytes(Bytes::tagged(value, format_tag))
    }

    pub fn string(value: &'a str) -> Data<'a> {
        Data::Bytes(Bytes::new(value.as_bytes()))
    }

    pub fn tagged_string(value: &'a str, format_tag: [u8; 2]) -> Data<'a> {
        Data::Bytes(Bytes::tagged(value.as_bytes(), format_tag))
    }
}

impl From<Slot> for Data<'_> {
    fn from(slot: Slot) -> Self {
        Data::Slot(slot)
    }
}

impl From<Option<Slot>> for Data<'_> {
    fn from(slot: Option<Slot>) -> Self {
        slot.map_or(Data::None, Data::Slot)
    }
}

impl From<u64> for Data<'_> {
    fn from(value: u64) -> Self {
        Data::Uint(value)
    }
}

impl From<i64> for Data<'_> {
    fn from(value: i64) -> Self {
        Data::Int(value)
    }
}

impl From<f64> for Data<'_> {
    fn from(value: f64) -> Self {
        Data::Float(value)
    }
}

impl<'a> From<Bytes<'a>> for Data<'a> {
    fn from(bytes: Bytes<'a>) -> Self {
        Data::Bytes(bytes)
    }
}

impl<'a> From<&'a str> for Data<'a> {
    fn from(value: &'a str) -> Self {
        Data::string(value)
    }
}

impl From<String> for Data<'_> {
    fn from(value: String) -> Self {
        Data::bytes(value.into_bytes())
    }
}

impl<'a> From<&'a [u8]> for Data<'a> {
    fn from(value: &'a [u8]) -> Self {
        Data::bytes(value)
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for Data<'a> {
    fn from(value: &'a [u8; N]) -> Self {
        Data::bytes(&value[..])
    }
}

impl From<Vec<u8>> for Data<'_> {
    fn from(value: Vec<u8>) -> Self {
        Data::bytes(value)
    }
}
