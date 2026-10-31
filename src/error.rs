use std::fmt;
use std::io;

/// Every error that xitdb can return.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// An error from the underlying [`Core`](crate::Core).
    #[cfg(not(kani))]
    Io(io::Error),
    // an io::Error can hold an Error, which makes the type recursive, and
    // kani would unwind its drop glue on every drop of an Error. proofs only
    // need the kind.
    #[cfg(kani)]
    Io(io::ErrorKind),
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
            #[cfg(not(kani))]
            Error::Io(err) => Some(err),
            _ => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        #[cfg(not(kani))]
        return Error::Io(err);
        #[cfg(kani)]
        return Error::Io(err.kind());
    }
}

impl From<Error> for io::Error {
    fn from(err: Error) -> Self {
        match err {
            #[cfg(not(kani))]
            Error::Io(err) => err,
            #[cfg(kani)]
            Error::Io(kind) => kind.into(),
            other => io::Error::other(other),
        }
    }
}

pub type Result<T, E = Error> = std::result::Result<T, E>;
