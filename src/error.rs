use std::fmt;
use std::io;

/// Every error that xitdb can return.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// An error from the underlying [`Core`](crate::Core).
    Io(io::Error),
    NestedTopLevelWrite,
    FrozenSlot,
    FrozenBytes,
    ExpiredTransaction,
    InvalidDatabase,
    InvalidRange,
    TargetNotEmpty,
    TruncatedDatabase,
    InvalidVersion,
    InvalidHashSize,
    KeyNotFound,
    WriteNotAllowed,
    UnexpectedTag,
    CursorNotWriteable,
    ExpectedTxStart,
    KeyOffsetExceeded,
    StreamTooLong,
    EndOfStream,
    InvalidOffset,
    ExpectedUnsignedLong,
    UnexpectedWriterPosition,
    MaxShiftExceeded,
    InvalidBTreeNode,
    InvalidBTreeNodeKind,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Error::Io(err) => return write!(f, "io error: {err}"),
            Error::NestedTopLevelWrite => "nested top-level writes are not allowed",
            Error::FrozenSlot => {
                "writer points into frozen data; reacquire it from the transaction root"
            }
            Error::FrozenBytes => "byte writer points into frozen data",
            Error::ExpiredTransaction => "writer belongs to an expired transaction",
            Error::InvalidDatabase => "invalid database",
            Error::InvalidRange => "invalid range",
            Error::TargetNotEmpty => "target not empty",
            Error::TruncatedDatabase => "truncated database",
            Error::InvalidVersion => "invalid version",
            Error::InvalidHashSize => "invalid hash size",
            Error::KeyNotFound => "key not found",
            Error::WriteNotAllowed => "write not allowed",
            Error::UnexpectedTag => "unexpected tag",
            Error::CursorNotWriteable => "cursor not writeable",
            Error::ExpectedTxStart => "expected tx start",
            Error::KeyOffsetExceeded => "key offset exceeded",
            Error::StreamTooLong => "stream too long",
            Error::EndOfStream => "end of stream",
            Error::InvalidOffset => "invalid offset",
            Error::ExpectedUnsignedLong => "expected unsigned long",
            Error::UnexpectedWriterPosition => "unexpected writer position",
            Error::MaxShiftExceeded => "max shift exceeded",
            Error::InvalidBTreeNode => "invalid btree node",
            Error::InvalidBTreeNodeKind => "invalid btree node kind",
        };
        f.write_str(msg)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io(err) => Some(err),
            _ => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::Io(err)
    }
}

impl From<Error> for io::Error {
    fn from(err: Error) -> Self {
        match err {
            Error::Io(err) => err,
            #[cfg(not(kani))]
            other => io::Error::other(other),
            // an io::Error that can hold an Error makes the type recursive,
            // which kani would unwind on every drop of an Error
            #[cfg(kani)]
            other => io::Error::other(other.to_string()),
        }
    }
}

pub type Result<T, E = Error> = std::result::Result<T, E>;
