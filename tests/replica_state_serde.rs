//! The JSON form of `ReplicaState`, which replicas send to their source
//! (see "Replicating to TypeScript" in the README).
#![cfg(feature = "serde")]

use xitdb::*;

#[test]
fn replica_state_json_form() {
    let state = ReplicaState { committed_size: 137438, checksum: u64::MAX };
    let json = serde_json::to_string(&state).unwrap();
    assert_eq!(json, r#"{"committedSize":137438,"checksum":"18446744073709551615"}"#);
    assert_eq!(serde_json::from_str::<ReplicaState>(&json).unwrap(), state);

    // field order and whitespace don't matter
    let parsed: ReplicaState = serde_json::from_str(r#" { "checksum" : "0", "committedSize" : 53 } "#).unwrap();
    assert_eq!(parsed, ReplicaState { committed_size: 53, checksum: 0 });
}

#[test]
fn replica_state_json_round_trip() -> Result<()> {
    let source = Database::new(CoreMemory::new(), Hasher::sha1())?;
    let replica = Database::new(CoreMemory::new(), Hasher::sha1())?;
    WriteArrayList::new(&mut source.root_cursor())?.append("first moment")?;

    for _ in 0..2 {
        // the replica sends its state as JSON, and the source reads it
        let json = serde_json::to_string(&replica.replica_state()?).unwrap();
        let state: ReplicaState = serde_json::from_str(&json).unwrap();
        assert_eq!(state, replica.replica_state()?);
        let start = source.replication_start(state)?;
        let end = source.committed_size()?;
        let mut bytes = Vec::new();
        source.read_committed(start, end, &mut bytes)?;
        replica.apply_replicated(start, &mut bytes.as_slice(), end - start)?;
        assert_eq!(replica.replica_state()?, source.replica_state()?);
        WriteArrayList::new(&mut source.root_cursor())?.append("next moment")?;
    }
    Ok(())
}

#[test]
fn replica_state_json_rejects_other_forms() {
    for json in [
        // the checksum must be a string, because it doesn't always fit in a JSON number
        r#"{"committedSize":53,"checksum":12}"#,
        r#"{"committedSize":53,"checksum":"-1"}"#,
        r#"{"committedSize":53,"checksum":"18446744073709551616"}"#,
        r#"{"committedSize":53,"checksum":"0x12"}"#,
        r#"{"committedSize":"53","checksum":"12"}"#,
        r#"{"committedSize":53}"#,
        r#"{"checksum":"12"}"#,
        r#"{"committedSize":53,"checksum":"12","extra":1}"#,
        r#"{"committedSize":53,"checksum":"12","checksum":"13"}"#,
    ] {
        assert!(serde_json::from_str::<ReplicaState>(json).is_err(), "{json} is rejected");
    }
}
