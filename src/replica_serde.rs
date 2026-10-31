//! `Serialize` and `Deserialize` for [`ReplicaState`], so a replica can send
//! its state to the source as JSON. The form is
//! `{"committedSize":123,"checksum":"456"}`: the checksum is a u64, which a
//! JSON number can't always hold exactly (JavaScript numbers are exact up to
//! 2^53), so it is a decimal string. This is the form the TypeScript
//! implementation's `ReplicaState` is easily converted to and from.

use std::fmt;

use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::format::ReplicaState;

const FIELDS: &[&str] = &["committedSize", "checksum"];

impl Serialize for ReplicaState {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut state = serializer.serialize_struct("ReplicaState", 2)?;
        state.serialize_field("committedSize", &self.committed_size)?;
        state.serialize_field("checksum", &self.checksum.to_string())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for ReplicaState {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_struct("ReplicaState", FIELDS, ReplicaStateVisitor)
    }
}

struct ReplicaStateVisitor;

impl<'de> Visitor<'de> for ReplicaStateVisitor {
    type Value = ReplicaState;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(r#"a replica state like {"committedSize":123,"checksum":"456"}"#)
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<ReplicaState, A::Error> {
        let mut committed_size = None;
        let mut checksum = None;
        while let Some(key) = map.next_key::<String>()? {
            match key.as_str() {
                "committedSize" => {
                    if committed_size.is_some() {
                        return Err(de::Error::duplicate_field("committedSize"));
                    }
                    committed_size = Some(map.next_value::<i64>()?);
                }
                "checksum" => {
                    if checksum.is_some() {
                        return Err(de::Error::duplicate_field("checksum"));
                    }
                    let text = map.next_value::<String>()?;
                    let parsed = text.parse::<u64>().map_err(|_| {
                        de::Error::invalid_value(de::Unexpected::Str(&text), &"a u64 as a decimal string")
                    })?;
                    checksum = Some(parsed);
                }
                other => return Err(de::Error::unknown_field(other, FIELDS)),
            }
        }
        Ok(ReplicaState {
            committed_size: committed_size.ok_or_else(|| de::Error::missing_field("committedSize"))?,
            checksum: checksum.ok_or_else(|| de::Error::missing_field("checksum"))?,
        })
    }
}
