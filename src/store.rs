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

pub trait Store {
    /// The bytes of the file.
    spec fn file(&self) -> Seq<u8>;

    /// Fills `buf` with the bytes at `pos`, or fails.
    fn read_at(&mut self, pos: i64, buf: &mut [u8]) -> (r: Result<()>)
        ensures
            final(self).file() == old(self).file(),
            final(buf)@.len() == old(buf)@.len(),
            r is Ok ==> 0 <= pos && pos + old(buf)@.len() <= old(self).file().len()
                && final(buf)@ == old(self).file().subrange(pos as int, pos + old(buf)@.len()),
    ;

    /// Writes `data` at `pos`. If it fails, the file is left in an unknown
    /// state.
    fn write_at(&mut self, pos: i64, data: &[u8]) -> (r: Result<()>)
        ensures
            r is Ok ==> 0 <= pos && final(self).file() == overwrite(old(self).file(), pos as int, data@),
    ;

    /// The length of the file.
    fn len(&mut self) -> (r: Result<i64>)
        ensures
            final(self).file() == old(self).file(),
            r matches Ok(n) ==> n == old(self).file().len(),
    ;
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
}

} // verus!

impl<'a, C: Core> DbStore<'a, C> {
    pub(crate) fn new(db: &'a Database<C>) -> Self {
        DbStore { db }
    }
}
