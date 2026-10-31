//! The file as the verified algorithms see it: a sequence of bytes that is
//! read and written at positions.
//!
//! The data structure algorithms are written against [`Store`] and
//! checked by Verus against its specification. [`DbStore`] implements it
//! for a [`Database`] by forwarding to its [`Core`]. That forwarding is the
//! one trusted part: it assumes a `Core` behaves like a file.

use crate::core::Core;
use crate::database::Database;
use crate::error::Result;
use vstd::prelude::*;

verus! {

/// `f` with `data` written at `pos`, padding with zeros up to `pos` and
/// extending the file if the write runs past the end, as files do.
pub open spec fn overwrite(f: Seq<u8>, pos: int, data: Seq<u8>) -> Seq<u8> {
    let end = pos + data.len();
    let before = if pos <= f.len() { f.subrange(0, pos) } else { f + Seq::new((pos - f.len()) as nat, |i: int| 0u8) };
    before + data + if end < f.len() {
        f.subrange(end, f.len() as int)
    } else {
        Seq::empty()
    }
}

/// What a successful write of `data` at `pos` leaves: within the file,
/// exactly [`overwrite`]; past its end, at least every byte that was there
/// (a file pads with zeros up to `pos`, while [`CoreMemory`](crate::CoreMemory)
/// writes at its end instead).
pub open spec fn write_result(f: Seq<u8>, g: Seq<u8>, pos: int, data: Seq<u8>) -> bool {
    &&& pos <= f.len() ==> g == overwrite(f, pos, data)
    &&& pos > f.len() ==> g.len() >= f.len() && g.subrange(0, f.len() as int) == f
}

pub trait Store {
    /// The bytes of the file.
    spec fn file(&self) -> Seq<u8>;

    /// Fills `buf` with the bytes at `pos`, or fails.
    fn read_at(&mut self, pos: i64, buf: &mut [u8]) -> (r: Result<()>)
        ensures
            final(self).file() == old(self).file(),
            final(buf)@.len() == old(buf)@.len(),
            r is Ok ==> 0 <= pos,
            // an empty read succeeds even past the end of a CoreMemory
            (r is Ok && old(buf)@.len() > 0) ==> pos + old(buf)@.len() <= old(self).file().len()
                && final(buf)@ == old(self).file().subrange(pos as int, pos + old(buf)@.len()),
    ;

    /// Writes `data` at `pos`. If it fails, the file is left in an unknown
    /// state.
    fn write_at(&mut self, pos: i64, data: &[u8]) -> (r: Result<()>)
        ensures
            r is Ok ==> 0 <= pos && write_result(old(self).file(), final(self).file(), pos as int, data@),
    ;

    /// The length of the file.
    fn len(&mut self) -> (r: Result<i64>)
        ensures
            final(self).file() == old(self).file(),
            r matches Ok(n) ==> n == old(self).file().len(),
    ;

    /// Truncates or zero-extends the file to `len` bytes.
    fn set_length(&mut self, len: u64) -> (r: Result<()>)
        ensures
            r is Ok ==> final(self).file() == resize(old(self).file(), len as int),
    ;

    /// Makes the file durable. Its bytes don't change.
    fn sync(&mut self) -> (r: Result<()>)
        ensures
            final(self).file() == old(self).file(),
    ;
}

/// `f` truncated or zero-extended to `len` bytes.
pub open spec fn resize(f: Seq<u8>, len: int) -> Seq<u8> {
    if len <= f.len() {
        f.subrange(0, len)
    } else {
        f + Seq::new((len - f.len()) as nat, |i: int| 0u8)
    }
}

/// Writes `data` at the end of the file and returns where.
pub fn append<S: Store>(s: &mut S, data: &[u8]) -> (r: Result<i64>)
    ensures
        r matches Ok(pos) ==> pos == old(s).file().len() && final(s).file() == old(s).file() + data@,
{
    let pos = s.len()?;
    s.write_at(pos, data)?;
    proof {
        assert(overwrite(old(s).file(), pos as int, data@) =~= old(s).file() + data@);
    }
    Ok(pos)
}

#[verifier::external_trait_specification]
#[allow(dead_code)]
pub trait ExCore {
    type ExternalTraitSpecificationFor: Core;
}

/// A [`Database`]'s core as a [`Store`].
#[verifier::external_body]
#[verifier::reject_recursive_types(C)]
pub struct DbStore<'a, C: Core> {
    db: &'a Database<C>,
}

/// The bytes of a database's core: what the trusted forwarding below
/// promises to behave like.
pub uninterp spec fn db_file<'a, C: Core>(s: &DbStore<'a, C>) -> Seq<u8>;

impl<'a, C: Core> Store for DbStore<'a, C> {
    open spec fn file(&self) -> Seq<u8> {
        db_file(self)
    }

    #[verifier::external_body]
    fn read_at(&mut self, pos: i64, buf: &mut [u8]) -> (r: Result<()>) {
        self.db.read_at(pos, buf)
    }

    #[verifier::external_body]
    fn write_at(&mut self, pos: i64, data: &[u8]) -> (r: Result<()>) {
        self.db.write_at(pos, data)
    }

    #[verifier::external_body]
    fn len(&mut self) -> (r: Result<i64>) {
        self.db.len()
    }

    #[verifier::external_body]
    fn set_length(&mut self, len: u64) -> (r: Result<()>) {
        Ok(self.db.core().set_length(len)?)
    }

    #[verifier::external_body]
    fn sync(&mut self) -> (r: Result<()>) {
        Ok(self.db.core().sync()?)
    }
}

/// Where replicated bytes go. Nothing is assumed about it.
pub trait Sink {
    fn write_all(&mut self, data: &[u8]) -> (r: Result<()>);
}

/// Where replicated bytes come from. Nothing is assumed about the bytes.
pub trait Source {
    fn read_exact(&mut self, buf: &mut [u8]) -> (r: Result<()>)
        ensures
            final(buf)@.len() == old(buf)@.len(),
    ;
}

#[verifier::external_trait_specification]
#[allow(dead_code)]
pub trait ExWrite {
    type ExternalTraitSpecificationFor: std::io::Write;
}

#[verifier::external_trait_specification]
#[allow(dead_code)]
pub trait ExRead {
    type ExternalTraitSpecificationFor: std::io::Read;
}

/// An [`std::io::Write`] as a [`Sink`].
#[verifier::external_body]
#[verifier::reject_recursive_types(W)]
pub struct IoSink<'a, W: std::io::Write> {
    w: &'a mut W,
}

impl<'a, W: std::io::Write> Sink for IoSink<'a, W> {
    #[verifier::external_body]
    fn write_all(&mut self, data: &[u8]) -> (r: Result<()>) {
        Ok(self.w.write_all(data)?)
    }
}

/// An [`std::io::Read`] as a [`Source`].
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub struct IoSource<'a, R: std::io::Read> {
    r: &'a mut R,
}

impl<'a, R: std::io::Read> Source for IoSource<'a, R> {
    #[verifier::external_body]
    fn read_exact(&mut self, buf: &mut [u8]) -> (r: Result<()>) {
        Ok(self.r.read_exact(buf)?)
    }
}

} // verus!

impl<'a, C: Core> DbStore<'a, C> {
    pub(crate) fn new(db: &'a Database<C>) -> Self {
        DbStore { db }
    }
}

impl<'a, W: std::io::Write> IoSink<'a, W> {
    pub(crate) fn new(w: &'a mut W) -> Self {
        IoSink { w }
    }
}

impl<'a, R: std::io::Read> IoSource<'a, R> {
    pub(crate) fn new(r: &'a mut R) -> Self {
        IoSource { r }
    }
}
