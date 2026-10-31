//! Committing and replication over a [`Store`] (`commit_root`,
//! `committed_size`, `truncate`, and the replication functions), checked by
//! Verus.
//!
//! A commit appends a trailer and rewrites the root header, and changes no
//! other byte ([`same_outside_header`]). That is why every committed byte
//! but the root header is immutable, and why a replica can stay in sync by
//! copying the bytes it doesn't have. `committed_size` only accepts a file
//! whose root header points at a trailer with a valid checksum and the same
//! root ([`trailer_ok`]).

#[allow(unused_imports)]
use crate::array_list_store::*;
use crate::bytes::*;
#[allow(unused_imports)]
use crate::crc64::*;
use crate::error::{Error, Result};
use crate::format::*;
use crate::slot::*;
use crate::store::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// `g` agrees with `f` on its first `upto` bytes, except the root header.
pub open spec fn same_outside_header(f: Seq<u8>, g: Seq<u8>, upto: int) -> bool {
    &&& upto <= f.len()
    &&& upto <= g.len()
    &&& forall|i: int| 0 <= i < upto && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) ==> #[trigger] g[i] == f[i]
}

/// A trailer for `root` with a valid checksum ends at `end`.
pub open spec fn trailer_ok(f: Seq<u8>, end: int, file_id: u64, t: RootTrailer) -> bool {
    &&& ROOT_TRAILER_LENGTH <= end <= f.len()
    &&& root_trailer_encode_spec(t) == f.subrange(end - ROOT_TRAILER_LENGTH, end)
    &&& t.checksum == crc64_spec(trailer_checksum_input(file_id, (end - ROOT_TRAILER_LENGTH) as i64, t.root, t.commit_id))
}

/// `read_root_header`.
pub fn read_root_header<S: Store>(s: &mut S) -> (r: Result<RootHeader>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> ROOT_HEADER_END <= old(s).file().len() && root_header_encode_spec(r.unwrap())
            == old(s).file().subrange(ROOT_HEADER_START as int, ROOT_HEADER_END as int),
{
    let mut buf = [0u8; ROOT_HEADER_LENGTH];
    s.read_at(ROOT_HEADER_START, &mut buf)?;
    let h = RootHeader::from_bytes(&buf)?;
    proof {
        assert(buf@.subrange(0, 17) =~= buf@);
    }
    Ok(h)
}

/// `read_root_trailer`: the trailer ending at `end`, if its checksum is
/// valid.
pub fn read_root_trailer<S: Store>(s: &mut S, end: i64, file_id: u64) -> (r: Result<RootTrailer>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> trailer_ok(old(s).file(), end as int, file_id, r.unwrap()),
{
    if end < ROOT_TRAILER_LENGTH as i64 {
        return Err(Error::InvalidDatabase);
    }
    let trailer_pos = end - ROOT_TRAILER_LENGTH as i64;
    let mut buf = [0u8; ROOT_TRAILER_LENGTH];
    s.read_at(trailer_pos, &mut buf)?;
    // check the checksum before decoding the root, because a corrupt
    // trailer can hold an unknown tag
    let checksum = read_u64(slice_subrange(buf.as_slice(), SLOT_LENGTH + 8, SLOT_LENGTH + 16));
    let commit_id = read_u64(slice_subrange(buf.as_slice(), SLOT_LENGTH, SLOT_LENGTH + 8));
    let f = u64_to_be_bytes(file_id);
    let p = u64_to_be_bytes(trailer_pos as u64);
    let c = u64_to_be_bytes(commit_id);
    let data = [
        f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7],
        p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7],
        buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7], buf[8],
        c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7],
    ];
    let expected = checksum_fn(&data);
    if checksum != expected {
        return Err(Error::InvalidDatabase);
    }
    let t = RootTrailer::from_bytes(&buf)?;
    proof {
        assert(buf@.subrange(0, 25) =~= buf@);
        lemma_slot_roundtrip(t.root);
        let e = root_trailer_encode_spec(t);
        assert(e.subrange(0, 9) =~= slot_encode_spec(t.root));
        assert(buf@.subrange(0, 9) =~= slot_encode_spec(t.root));
        assert(buf@.subrange(9, 17).subrange(0, 8) =~= buf@.subrange(9, 17));
        assert(buf@.subrange(17, 25).subrange(0, 8) =~= buf@.subrange(17, 25));
        lemma_u64_be_roundtrip(buf@.subrange(9, 17));
        lemma_u64_be_roundtrip(buf@.subrange(17, 25));
        assert(e.subrange(9, 17) =~= u64_be_spec(t.commit_id));
        assert(e.subrange(17, 25) =~= u64_be_spec(t.checksum));
        lemma_be_u64_roundtrip(t.commit_id);
        lemma_be_u64_roundtrip(t.checksum);
        assert(t.commit_id == commit_id);
        assert(t.checksum == checksum);
        assert(data@ =~= trailer_checksum_input(file_id, trailer_pos, t.root, t.commit_id));
    }
    Ok(t)
}

fn checksum_fn(data: &[u8]) -> (r: u64)
    ensures
        r == crc64_spec(data@),
{
    crate::crc64::checksum(data)
}

/// `committed_size`: the size of the committed bytes, which end with a
/// valid trailer for the root the header holds.
pub fn committed_size<S: Store>(s: &mut S, file_id: u64) -> (r: Result<i64>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> ROOT_HEADER_END + ROOT_TRAILER_LENGTH <= r.unwrap() <= old(s).file().len(),
        r is Ok ==> exists|h: RootHeader, t: RootTrailer|
            #![trigger root_header_encode_spec(h), trailer_ok(old(s).file(), r.unwrap() as int, file_id, t)]
            {
            &&& root_header_encode_spec(h) == old(s).file().subrange(ROOT_HEADER_START as int, ROOT_HEADER_END as int)
            &&& h.file_size == r.unwrap()
            &&& trailer_ok(old(s).file(), r.unwrap() as int, file_id, t)
            &&& t.root == h.root
        },
{
    let header = read_root_header(s)?;
    let minimum_size = ROOT_HEADER_END + ROOT_TRAILER_LENGTH as i64;
    if header.file_size < minimum_size {
        return Err(Error::InvalidDatabase);
    }
    if s.len()? < header.file_size {
        return Err(Error::TruncatedDatabase);
    }
    // the committed bytes must end with a trailer matching the header
    let trailer = read_root_trailer(s, header.file_size, file_id)?;
    if !slot_eq(trailer.root, header.root) {
        return Err(Error::InvalidDatabase);
    }
    Ok(header.file_size)
}

fn slot_eq(a: Slot, b: Slot) -> (r: bool)
    ensures
        r == (a == b),
{
    let r = a.value == b.value && a.full == b.full && a.tag.to_u8() == b.tag.to_u8();
    proof {
        lemma_tag_byte_injective(a.tag, b.tag);
    }
    r
}

/// `write_root_header`: points the root header at `root` and the current
/// end of the file.
pub fn write_root_header<S: Store>(s: &mut S, root: Slot) -> (r: Result<()>)
    requires
        old(s).file().len() >= ROOT_HEADER_END,
    ensures
        r is Ok ==> final(s).file() == overwrite(old(s).file(), ROOT_HEADER_START as int,
            root_header_encode_spec(RootHeader { file_size: old(s).file().len() as i64, root })),
        r is Ok ==> same_outside_header(old(s).file(), final(s).file(), old(s).file().len() as int),
        r is Ok ==> final(s).file().len() == old(s).file().len(),
{
    let file_size = s.len()?;
    let h = RootHeader { file_size, root };
    let bytes = h.to_bytes();
    s.write_at(ROOT_HEADER_START, &bytes)?;
    proof {
        lemma_slot_roundtrip(root);
        let f = old(s).file();
        let g = s.file();
        assert(bytes@.len() == 17);
        assert forall|i: int| 0 <= i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] g[i] == f[i] by {
            if i < 20 {
                assert(g[i] == f.subrange(0, 20)[i]);
            } else {
                assert(g[i] == f.subrange(37, f.len() as int)[i - 37]);
            }
        }
    }
    Ok(())
}

/// `commit_root`: appends a trailer for `root` and points the root header
/// at it. Only the root header and the appended bytes change.
pub fn commit_root<S: Store>(s: &mut S, root: Slot, commit_id: u64, file_id: u64) -> (r: Result<()>)
    requires
        old(s).file().len() >= ROOT_HEADER_END,
    ensures
        r is Ok ==> same_outside_header(old(s).file(), final(s).file(), old(s).file().len() as int),
        r is Ok ==> final(s).file().len() == old(s).file().len() + ROOT_TRAILER_LENGTH,
{
    let trailer_pos = s.len()?;
    let trailer = RootTrailer::new(file_id, trailer_pos, root, commit_id);
    let bytes = trailer.to_bytes();
    s.write_at(trailer_pos, &bytes)?;
    let ghost f1 = s.file();
    proof {
        let f = old(s).file();
        assert forall|i: int| 0 <= i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] f1[i] == f[i] by {
            assert(f1[i] == f.subrange(0, trailer_pos as int)[i]);
        }
    }

    // flush and fsync before updating the header, because updating
    // the header is what completes the transaction. without the
    // fsync, the OS could persist the header before the data it
    // points to, so a crash could commit a transaction whose data
    // never reached disk.
    s.sync()?;

    write_root_header(s, root)?;
    proof {
        let f = old(s).file();
        let g = s.file();
        assert forall|i: int| 0 <= i < f.len() && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] g[i] == f[i] by {
            assert(g[i] == f1[i]);
        }
    }
    Ok(())
}

/// `truncate`, when nothing is frozen past the committed bytes: anything
/// after them, such as the remains of a failed transaction, is cut off.
pub fn truncate_to_committed<S: Store>(s: &mut S, committed: i64) -> (r: Result<()>)
    requires
        0 <= committed <= old(s).file().len(),
    ensures
        r is Ok ==> final(s).file() == old(s).file().subrange(0, committed as int),
{
    if s.len()? > committed {
        s.set_length(committed as u64)?;
    } else {
        assert(old(s).file().subrange(0, committed as int) =~= old(s).file());
    }
    Ok(())
}

/// `truncate`, when bytes are frozen past the committed ones: they are
/// kept without publishing the failed transaction, by cutting off what
/// follows them and committing the current root again after them.
pub fn truncate_to_frozen<S: Store>(s: &mut S, frozen_at: i64, commit_id: u64, file_id: u64) -> (r: Result<()>)
    requires
        ROOT_HEADER_END <= frozen_at <= old(s).file().len(),
    ensures
        r is Ok ==> same_outside_header(old(s).file(), final(s).file(), frozen_at as int),
{
    let ghost f0 = s.file();
    if s.len()? > frozen_at {
        s.set_length(frozen_at as u64)?;
    }
    let ghost f1 = s.file();
    proof {
        if f1 != f0 {
            assert(f1 == f0.subrange(0, frozen_at as int));
        }
    }
    let root = read_root_header(s)?.root;
    commit_root(s, root, commit_id, file_id)?;
    s.sync()?;
    proof {
        let g = s.file();
        assert forall|i: int| 0 <= i < frozen_at && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) implies #[trigger] g[i] == f0[i] by {
            assert(g[i] == f1[i]);
            if f1 != f0 {
                assert(f1[i] == f0.subrange(0, frozen_at as int)[i]);
            }
        }
    }
    Ok(())
}

} // verus!
