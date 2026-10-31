use std::fmt;
use std::io;
use std::path::PathBuf;

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
    /// [`Database::compact_file`](crate::Database::compact_file) couldn't
    /// rename the compacted copy over the original, and then couldn't
    /// reopen the original. The database is now the compacted copy at
    /// `temp_path`, so don't delete that file. The original is unchanged.
    CompactFileReopenFailed {
        /// Where the compacted copy, which the database now uses, lives.
        temp_path: PathBuf,
        /// Why the rename failed.
        rename_error: io::Error,
        /// Why reopening the original failed.
        reopen_error: Box<Error>,
    },
    /// A byte array read as a string isn't valid UTF-8.
    InvalidUtf8(std::str::Utf8Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Error::Io(err) => return write!(f, "io error: {err}"),
            Error::CompactFileReopenFailed { temp_path, rename_error, reopen_error } => {
                return write!(
                    f,
                    "renaming the compacted file failed ({rename_error}), and reopening the original failed                      ({reopen_error}); the database is now at {}",
                    temp_path.display()
                );
            }
            Error::InvalidUtf8(err) => return write!(f, "invalid utf-8: {err}"),
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
            Error::CompactFileReopenFailed { rename_error, .. } => Some(rename_error),
            Error::InvalidUtf8(err) => Some(err),
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
            other => io::Error::other(other),
        }
    }
}

pub type Result<T, E = Error> = std::result::Result<T, E>;
