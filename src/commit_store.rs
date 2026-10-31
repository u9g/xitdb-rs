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

/// The history: a commit for `root` whose trailer ends at `end`. Every
/// commit appends one, after the root header.
pub open spec fn in_history(f: Seq<u8>, file_id: u64, end: int, root: Slot) -> bool {
    &&& ROOT_HEADER_END + ROOT_TRAILER_LENGTH <= end
    &&& exists|t: RootTrailer| #[trigger] trailer_ok(f, end, file_id, t) && t.root == root
}

/// Every commit in `f`'s history up to `upto` is in `g`'s.
pub open spec fn history_kept(f: Seq<u8>, g: Seq<u8>, file_id: u64, upto: int) -> bool {
    forall|end: int, root: Slot| end <= upto && #[trigger] in_history(f, file_id, end, root) ==> in_history(g, file_id, end, root)
}

/// A file that agrees with `f` outside the root header keeps its history.
pub proof fn lemma_history_kept(f: Seq<u8>, g: Seq<u8>, file_id: u64, upto: int)
    requires
        upto <= f.len(),
        upto <= g.len(),
        forall|i: int| 0 <= i < upto && !(ROOT_HEADER_START <= i < ROOT_HEADER_END) ==> #[trigger] g[i] == f[i],
    ensures
        history_kept(f, g, file_id, upto),
{
    assert forall|end: int, root: Slot| end <= upto && #[trigger] in_history(f, file_id, end, root) implies in_history(g, file_id, end, root) by {
        let t = choose|t: RootTrailer| #[trigger] trailer_ok(f, end, file_id, t) && t.root == root;
        let a = end - ROOT_TRAILER_LENGTH;
        assert forall|i: int| 0 <= i < ROOT_TRAILER_LENGTH implies #[trigger] g.subrange(a, end)[i] == f.subrange(a, end)[i] by {
            assert(g[a + i] == f[a + i]);
        }
        assert(g.subrange(a, end) =~= f.subrange(a, end));
        assert(trailer_ok(g, end, file_id, t));
    }
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
        r is Ok ==> in_history(final(s).file(), file_id, final(s).file().len() as int, root),
        r is Ok ==> history_kept(old(s).file(), final(s).file(), file_id, old(s).file().len() as int),
{
    let trailer_pos = s.len()?;
    let trailer = RootTrailer::new(file_id, trailer_pos, root, commit_id);
    let bytes = trailer.to_bytes();
    s.write_at(trailer_pos, &bytes)?;
    let ghost f1 = s.file();
    proof {
        assert(f1 =~= old(s).file() + bytes@);
    }
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
        // the new commit
        let end = g.len() as int;
        let a = trailer_pos as int;
        assert forall|i: int| 0 <= i < ROOT_TRAILER_LENGTH implies #[trigger] g.subrange(a, end)[i] == bytes@[i] by {
            assert(g[a + i] == f1[a + i]);
        }
        assert(g.subrange(a, end) =~= bytes@);
        assert(trailer_ok(g, end, file_id, trailer));
        lemma_history_kept(f, g, file_id, f.len() as int);
    }
    Ok(())
}

/// `truncate`, when nothing is frozen past the committed bytes: anything
/// after them, such as the remains of a failed transaction, is cut off.
pub fn truncate_to_committed<S: Store>(s: &mut S, committed: i64) -> (r: Result<()>)
    ensures
        r is Ok ==> final(s).file() == old(s).file().subrange(0, committed as int),
{
    check_limit(s, committed, committed)?;
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
    ensures
        r is Ok ==> same_outside_header(old(s).file(), final(s).file(), frozen_at as int),
{
    check_limit(s, frozen_at, frozen_at)?;
    if frozen_at < ROOT_HEADER_END {
        return Err(Error::InvalidOffset);
    }
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

// replication

/// `replica_state`.
pub fn replica_state<S: Store>(s: &mut S, file_id: u64) -> (r: Result<ReplicaState>)
    ensures
        final(s).file() == old(s).file(),
{
    let committed_size = committed_size(s, file_id)?;
    let trailer = read_root_trailer(s, committed_size, file_id)?;
    Ok(ReplicaState { committed_size, checksum: trailer.checksum })
}

/// `replication_start`: the replica's committed size if its trailer
/// matches ours there, or 0 if it must be replaced.
pub fn replication_start<S: Store>(s: &mut S, file_id: u64, state: ReplicaState) -> (r: Result<i64>)
    ensures
        final(s).file() == old(s).file(),
        r is Ok ==> r.unwrap() == 0 || (r.unwrap() == state.committed_size && exists|t: RootTrailer|
            #[trigger] trailer_ok(old(s).file(), state.committed_size as int, file_id, t) && t.checksum == state.checksum),
{
    let committed_size = committed_size(s, file_id)?;
    if state.committed_size > committed_size {
        return Ok(0);
    }
    match read_root_trailer(s, state.committed_size, file_id) {
        Ok(trailer) => if trailer.checksum == state.checksum {
            Ok(state.committed_size)
        } else {
            Ok(0)
        },
        Err(Error::InvalidDatabase) => Ok(0),
        Err(Error::UnexpectedTag) => Ok(0),
        Err(err) => Err(err),
    }
}

/// `stream_bytes`: `length` bytes from `start`, written to `w`.
pub fn stream_bytes<S: Store, W: Sink>(s: &mut S, w: &mut W, start: i64, length: i64) -> (r: Result<()>)
    ensures
        final(s).file() == old(s).file(),
{
    let cap: usize = if length <= 0 { 0 } else if length > 4096 { 4096 } else { length as usize };
    let mut pos = start;
    let mut remaining = length;
    while remaining > 0
        invariant
            s.file() == old(s).file(),
            remaining > 0 ==> cap > 0,
            cap <= 4096,
        decreases remaining,
    {
        let chunk: usize = if remaining < cap as i64 { remaining as usize } else { cap };
        let mut piece = zero_bytes(chunk);
        s.read_at(pos, piece.as_mut_slice())?;
        w.write_all(piece.as_slice())?;
        pos = match pos.checked_add(chunk as i64) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        remaining = remaining - chunk as i64;
    }
    Ok(())
}

fn zero_bytes(n: usize) -> (r: Vec<u8>)
    ensures
        r@.len() == n,
{
    let mut r = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            r@.len() == i,
        decreases n - i,
    {
        r.push(0);
        i += 1;
    }
    r
}

/// `read_committed`: the committed bytes from `start` to `end`. From 0,
/// the root header is replaced by one for `end`, so the bytes are a
/// complete database.
pub fn read_committed<S: Store, W: Sink>(s: &mut S, w: &mut W, start: i64, end: i64, file_id: u64) -> (r: Result<()>)
    ensures
        final(s).file() == old(s).file(),
{
    let committed_size = committed_size(s, file_id)?;
    if start < 0 || start > end || end > committed_size {
        return Err(Error::InvalidRange);
    }
    if start > 0 && start < ROOT_HEADER_END {
        return Err(Error::InvalidRange);
    }
    if start == 0 {
        let trailer = read_root_trailer(s, end, file_id)?;
        stream_bytes(s, w, 0, ROOT_HEADER_START)?;
        let header = RootHeader { file_size: end, root: trailer.root }.to_bytes();
        w.write_all(&header)?;
        return stream_bytes(s, w, ROOT_HEADER_END, end - ROOT_HEADER_END);
    }
    stream_bytes(s, w, start, end - start)
}

/// The copying part of `apply_replicated`: `length` bytes from `r`,
/// written from `start` on. Nothing before `start` changes.
pub fn write_replicated<S: Store, R: Source>(s: &mut S, r: &mut R, start: i64, length: i64) -> (res: Result<()>)
    ensures
        res is Ok ==> kept_below(old(s).file(), final(s).file(), start as int),
{
    check_limit(s, start, start)?;
    let cap: usize = if length <= 0 { 0 } else if length > 4096 { 4096 } else { length as usize };
    let mut pos = start;
    let mut remaining = length;
    let ghost f0 = s.file();
    proof {
        assert(f0.subrange(0, start as int) =~= f0.subrange(0, start as int));
    }
    while remaining > 0
        invariant
            0 <= start <= pos,
            start <= f0.len(),
            f0 == old(s).file(),
            kept_below(f0, s.file(), start as int),
            remaining > 0 ==> cap > 0,
            cap <= 4096,
        decreases remaining,
    {
        let chunk: usize = if remaining < cap as i64 { remaining as usize } else { cap };
        let mut buf = zero_bytes(chunk);
        r.read_exact(buf.as_mut_slice())?;
        let ghost f1 = s.file();
        s.write_at(pos, buf.as_slice())?;
        proof {
            lemma_overwrite_keeps(f1, pos as int, buf@, start as int);
            lemma_kept_trans(f0, f1, s.file(), start as int);
        }
        pos = match pos.checked_add(chunk as i64) {
            Some(p) => p,
            None => return Err(Error::InvalidOffset),
        };
        remaining = remaining - chunk as i64;
    }
    Ok(())
}

/// The end of an incremental `apply_replicated`: the bytes must end with
/// a trailer, and the root header is pointed at it.
pub fn finish_replicated<S: Store>(s: &mut S, start: i64, length: i64, file_id: u64) -> (r: Result<()>)
    ensures
        r is Ok ==> same_outside_header(old(s).file(), final(s).file(), old(s).file().len() as int),
{
    if s.len()? < ROOT_HEADER_END {
        return Err(Error::InvalidDatabase);
    }
    let end = match start.checked_add(length) {
        Some(e) => e,
        None => return Err(Error::InvalidRange),
    };
    let trailer = read_root_trailer(s, end, file_id)?;
    s.sync()?;
    write_root_header(s, trailer.root)?;
    s.sync()?;
    Ok(())
}

// creating a database and transactions

/// `Database::new` on an empty file: the header, an empty root header, and
/// the first commit (whose ID is 0, so a new database's bytes only depend
/// on its file ID).
pub fn init_file<S: Store>(s: &mut S, header: Header) -> (r: Result<()>)
    ensures
        r is Ok ==> final(s).file().len() == HEADER_LENGTH + ROOT_HEADER_LENGTH + ROOT_TRAILER_LENGTH,
        r is Ok ==> final(s).file().subrange(0, HEADER_LENGTH as int) == header_encode_spec(header),
{
    if s.len()? != 0 {
        return Err(Error::InvalidDatabase);
    }
    let h = header.to_bytes();
    append(s, &h)?;
    let ghost f1 = s.file();
    let rh = RootHeader { file_size: 0, root: Slot::new(0, Tag::None) }.to_bytes();
    append(s, &rh)?;
    let ghost f2 = s.file();
    commit_root(s, Slot::new(0, Tag::None), 0, header.file_id)?;
    s.sync()?;
    proof {
        let g = s.file();
        assert(f1 =~= h@);
        assert forall|i: int| 0 <= i < HEADER_LENGTH implies g[i] == h@[i] by {
            assert(g[i] == f2[i]);
            assert(f2[i] == f1[i]);
        }
        assert(g.subrange(0, HEADER_LENGTH as int) =~= header_encode_spec(header));
    }
    Ok(())
}

/// Starting a transaction: the root slot copied to the end of the file,
/// where the transaction works on it.
pub fn begin_transaction<S: Store>(s: &mut S, root: Slot) -> (r: Result<i64>)
    ensures
        r is Ok ==> r.unwrap() == old(s).file().len(),
        r is Ok ==> final(s).file().len() >= old(s).file().len() && final(s).file().subrange(0, old(s).file().len() as int)
            == old(s).file(),
{
    let scratch_pos = s.len()?;
    write_slot_at(s, scratch_pos, root)?;
    proof {
        lemma_slot_roundtrip(root);
        assert(s.file().subrange(0, old(s).file().len() as int) =~= old(s).file());
    }
    Ok(scratch_pos)
}

/// Finishing a transaction: the copy of the root slot holds the new root,
/// so it is committed. Only the root header and the trailer change.
pub fn finish_transaction<S: Store>(s: &mut S, scratch_pos: i64, commit_id: u64, file_id: u64) -> (r: Result<Slot>)
    ensures
        r is Ok ==> same_outside_header(old(s).file(), final(s).file(), old(s).file().len() as int),
        r is Ok ==> in_history(final(s).file(), file_id, final(s).file().len() as int, r.unwrap()),
        r is Ok ==> history_kept(old(s).file(), final(s).file(), file_id, old(s).file().len() as int),
{
    if s.len()? < ROOT_HEADER_END {
        return Err(Error::InvalidDatabase);
    }
    let next_root = read_slot_at(s, scratch_pos)?;
    commit_root(s, next_root, commit_id, file_id)?;
    Ok(next_root)
}

} // verus!
