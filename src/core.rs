use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

use vstd::prelude::*;

/// Determines how a [`Database`](crate::Database) does i/o.
///
/// There are three implementations: [`CoreBufferedFile`] (recommended for
/// files), [`CoreFile`] and [`CoreMemory`].
pub trait Core {
    /// Fills `buf` from the current position, or fails.
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()>;
    /// Writes all of `buf` at the current position.
    fn write(&mut self, buf: &[u8]) -> io::Result<()>;
    fn length(&mut self) -> io::Result<u64>;
    fn seek_to(&mut self, pos: u64) -> io::Result<()>;
    fn position(&mut self) -> io::Result<u64>;
    fn set_length(&mut self, len: u64) -> io::Result<()>;
    fn flush(&mut self) -> io::Result<()>;
    /// Flushes and makes the data durable.
    fn sync(&mut self) -> io::Result<()>;
    /// Called when the core is done being used, to write out anything it
    /// buffers and report errors that dropping it would ignore. The default
    /// calls [`Core::flush`]. It doesn't make the data durable (committed
    /// transactions already are; call [`Core::sync`] for other writes), so
    /// it also succeeds on a read-only core. The core may still be used
    /// afterwards.
    ///
    /// This works through a [`DynCore`] or any other wrapper, since it
    /// doesn't consume the core.
    fn finish(&mut self) -> io::Result<()> {
        self.flush()
    }
}

/// A boxed [`Core`], for code that picks its core at runtime, such as a
/// file in production and memory in tests. It implements `Core`, so it can
/// be used as `Database<DynCore>`; see [`Database::into_dyn`](crate::Database::into_dyn).
pub type DynCore = Box<dyn Core + Send>;

impl<C: Core + ?Sized> Core for &mut C {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        (**self).read(buf)
    }
    fn write(&mut self, buf: &[u8]) -> io::Result<()> {
        (**self).write(buf)
    }
    fn length(&mut self) -> io::Result<u64> {
        (**self).length()
    }
    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        (**self).seek_to(pos)
    }
    fn position(&mut self) -> io::Result<u64> {
        (**self).position()
    }
    fn set_length(&mut self, len: u64) -> io::Result<()> {
        (**self).set_length(len)
    }
    fn flush(&mut self) -> io::Result<()> {
        (**self).flush()
    }
    fn sync(&mut self) -> io::Result<()> {
        (**self).sync()
    }
    fn finish(&mut self) -> io::Result<()> {
        (**self).finish()
    }
}

impl<C: Core + ?Sized> Core for Box<C> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        (**self).read(buf)
    }
    fn write(&mut self, buf: &[u8]) -> io::Result<()> {
        (**self).write(buf)
    }
    fn length(&mut self) -> io::Result<u64> {
        (**self).length()
    }
    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        (**self).seek_to(pos)
    }
    fn position(&mut self) -> io::Result<u64> {
        (**self).position()
    }
    fn set_length(&mut self, len: u64) -> io::Result<()> {
        (**self).set_length(len)
    }
    fn flush(&mut self) -> io::Result<()> {
        (**self).flush()
    }
    fn sync(&mut self) -> io::Result<()> {
        (**self).sync()
    }
    fn finish(&mut self) -> io::Result<()> {
        (**self).finish()
    }
}

// CoreMemory

verus! {

/// A database that lives entirely in memory.
///
/// Checked by Verus: its operations implement a file (see
/// [`mem_read_at`] and [`mem_write_at`], which meet the specification the
/// database's algorithms are verified against).
#[derive(Debug, Clone, Default)]
pub struct CoreMemory {
    buf: Vec<u8>,
    pos: usize,
}

impl CoreMemory {
    /// The position never passes the end.
    pub closed spec fn ok(&self) -> bool {
        self.pos <= self.buf@.len()
    }

    /// The bytes it holds.
    pub closed spec fn bytes(&self) -> Seq<u8> {
        self.buf@
    }

    pub closed spec fn position_spec(&self) -> int {
        self.pos as int
    }

    pub fn new() -> (r: CoreMemory)
        ensures
            r.ok(),
            r.bytes().len() == 0,
    {
        CoreMemory { buf: Vec::new(), pos: 0 }
    }

    /// Wraps existing database bytes, such as ones received over a network.
    pub fn from_bytes(buf: Vec<u8>) -> (r: CoreMemory)
        ensures
            r.ok(),
            r.bytes() == buf@,
    {
        CoreMemory { buf, pos: 0 }
    }

    pub fn as_bytes(&self) -> (r: &[u8])
        ensures
            r@ == self.bytes(),
    {
        self.buf.as_slice()
    }

    pub fn into_bytes(self) -> (r: Vec<u8>)
        ensures
            r@ == self.bytes(),
    {
        self.buf
    }

    /// `Core::read`: fills `out` from the position, or fails.
    pub fn read_impl(&mut self, out: &mut [u8]) -> (r: io::Result<()>)
        ensures
            final(self).ok(),
            final(self).bytes() == old(self).bytes(),
            final(out)@.len() == old(out)@.len(),
            r is Ok ==> old(self).position_spec() + old(out)@.len() <= old(self).bytes().len()
                && final(out)@ == old(self).bytes().subrange(old(self).position_spec(), old(self).position_spec() + old(out)@.len())
                && final(self).position_spec() == old(self).position_spec() + old(out)@.len(),
    {
        // the position never passes the end, but restore that if it did
        if self.pos > self.buf.len() {
            let e = eof_error(self.pos, out.len(), self.buf.len());
            self.pos = self.buf.len();
            return Err(e);
        }
        let end = match self.pos.checked_add(out.len()) {
            Some(e) => e,
            None => return Err(eof_error(self.pos, out.len(), self.buf.len())),
        };
        if end > self.buf.len() {
            return Err(eof_error(self.pos, out.len(), self.buf.len()));
        }
        let mut i: usize = 0;
        while i < out.len()
            invariant
                self.pos + out@.len() <= self.buf@.len(),
                end == self.pos + out@.len(),
                i <= out@.len(),
                out@.len() == old(out)@.len(),
                self.buf@ == old(self).buf@,
                self.pos == old(self).pos,
                forall|k: int| 0 <= k < i ==> #[trigger] out@[k] == self.buf@[self.pos + k],
            decreases out.len() - i,
        {
            out[i] = self.buf[self.pos + i];
            i += 1;
        }
        self.pos = end;
        proof {
            assert(out@ =~= old(self).buf@.subrange(old(self).pos as int, old(self).pos + old(out)@.len()));
        }
        Ok(())
    }

    /// `Core::write`: writes `data` at the position, extending the bytes if
    /// it runs past the end.
    pub fn write_impl(&mut self, data: &[u8]) -> (r: io::Result<()>)
        ensures
            r is Ok ==> final(self).ok(),
            r is Ok ==> final(self).bytes() == crate::store::overwrite(old(self).bytes(), old(self).position_spec(), data@),
            r is Ok ==> final(self).position_spec() == old(self).position_spec() + data@.len(),
    {
        // the position never passes the end, but restore that if it did
        if self.pos > self.buf.len() {
            let e = too_large_error();
            self.pos = self.buf.len();
            return Err(e);
        }
        let pos = self.pos;
        let new_pos = match pos.checked_add(data.len()) {
            Some(p) => p,
            None => return Err(too_large_error()),
        };
        let ghost f = self.buf@;
        let mut i: usize = 0;
        while i < data.len()
            invariant
                pos == old(self).pos,
                pos <= f.len(),
                f == old(self).buf@,
                pos + data@.len() == new_pos,
                i <= data@.len(),
                self.buf@.len() == if pos + i <= f.len() { f.len() as int } else { pos + i },
                forall|k: int| 0 <= k < pos ==> #[trigger] self.buf@[k] == f[k],
                forall|k: int| pos <= k < pos + i ==> #[trigger] self.buf@[k] == data@[k - pos],
                forall|k: int| pos + i <= k < self.buf@.len() ==> #[trigger] self.buf@[k] == f[k],
            decreases data.len() - i,
        {
            if pos + i < self.buf.len() {
                self.buf.set(pos + i, data[i]);
            } else {
                self.buf.push(data[i]);
            }
            i += 1;
        }
        self.pos = new_pos;
        proof {
            assert(self.buf@ =~= crate::store::overwrite(f, pos as int, data@));
        }
        Ok(())
    }

    /// `Core::seek_to`: the position, clamped to the end.
    pub fn seek_impl(&mut self, pos: u64)
        ensures
            final(self).ok(),
            final(self).bytes() == old(self).bytes(),
            final(self).position_spec() == if pos <= old(self).bytes().len() { pos as int } else { old(self).bytes().len() as int },
    {
        let len = self.buf.len();
        self.pos = if pos <= len as u64 { pos as usize } else { len };
    }

    /// `Core::set_length`: truncates the bytes (it can't extend them).
    pub fn set_length_impl(&mut self, len: u64) -> (r: io::Result<()>)
        ensures
            final(self).ok(),
            r is Ok ==> len <= old(self).bytes().len() && final(self).bytes() == old(self).bytes().subrange(0, len as int),
            r is Err ==> final(self).bytes() == old(self).bytes(),
    {
        // the position never passes the end, but restore that if it did
        if self.pos > self.buf.len() {
            let e = invalid_length_error();
            self.pos = self.buf.len();
            return Err(e);
        }
        if len > self.buf.len() as u64 {
            return Err(invalid_length_error());
        }
        let len = len as usize;
        if len == 0 || self.pos > len {
            self.pos = len;
        }
        self.buf.truncate(len);
        Ok(())
    }

    pub fn length_impl(&self) -> (r: u64)
        ensures
            r == self.bytes().len(),
    {
        self.buf.len() as u64
    }
}

#[verifier::external_body]
fn too_large_error() -> io::Error {
    io::Error::other("memory too large")
}

#[verifier::external_body]
fn invalid_length_error() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, "invalid memory length")
}

#[verifier::external_body]
fn eof_error(pos: usize, len: usize, size: usize) -> io::Error {
    io::Error::new(
        io::ErrorKind::UnexpectedEof,
        format!("read beyond end of memory: pos={pos}, len={len}, size={size}"),
    )
}

/// What `Database::read_at` does with a `CoreMemory`: seek, then read. It
/// meets the [`Store`](crate::store::Store) specification of `read_at`.
#[allow(dead_code)] // the proof that CoreMemory meets the Store spec
pub fn mem_read_at(m: &mut CoreMemory, pos: i64, out: &mut [u8]) -> (r: Result<(), crate::Error>)
    requires
        old(m).ok(),
    ensures
        final(m).ok(),
        final(m).bytes() == old(m).bytes(),
        final(out)@.len() == old(out)@.len(),
        r is Ok ==> 0 <= pos,
        (r is Ok && old(out)@.len() > 0) ==> pos + old(out)@.len() <= old(m).bytes().len()
            && final(out)@ == old(m).bytes().subrange(pos as int, pos + old(out)@.len()),
{
    if pos < 0 {
        return Err(crate::Error::InvalidOffset);
    }
    m.seek_impl(pos as u64);
    match m.read_impl(out) {
        Ok(()) => Ok(()),
        Err(e) => Err(crate::Error::Io(e)),
    }
}

/// What `Database::write_at` does with a `CoreMemory`: seek, then write. It
/// meets the [`Store`](crate::store::Store) specification of `write_at`.
#[allow(dead_code)] // the proof that CoreMemory meets the Store spec
pub fn mem_write_at(m: &mut CoreMemory, pos: i64, data: &[u8]) -> (r: Result<(), crate::Error>)
    requires
        old(m).ok(),
    ensures
        r is Ok ==> final(m).ok(),
        r is Ok ==> 0 <= pos && crate::store::write_result(old(m).bytes(), final(m).bytes(), pos as int, data@),
{
    if pos < 0 {
        return Err(crate::Error::InvalidOffset);
    }
    let ghost f = m.bytes();
    m.seek_impl(pos as u64);
    match m.write_impl(data) {
        Ok(()) => {
            proof {
                let g = m.bytes();
                if pos > f.len() {
                    // the write lands at the end
                    assert(g.subrange(0, f.len() as int) =~= f);
                }
            }
            Ok(())
        },
        Err(e) => Err(crate::Error::Io(e)),
    }
}

} // verus!

impl Core for CoreMemory {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        self.read_impl(buf)
    }

    fn write(&mut self, data: &[u8]) -> io::Result<()> {
        self.write_impl(data)
    }

    fn length(&mut self) -> io::Result<u64> {
        Ok(self.length_impl())
    }

    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        self.seek_impl(pos);
        Ok(())
    }

    fn position(&mut self) -> io::Result<u64> {
        Ok(self.pos as u64)
    }

    fn set_length(&mut self, len: u64) -> io::Result<()> {
        self.set_length_impl(len)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn sync(&mut self) -> io::Result<()> {
        Ok(())
    }
}

// CoreFile

/// A file-backed database with no buffering. [`CoreBufferedFile`] is
/// almost always a better choice.
#[derive(Debug)]
pub struct CoreFile {
    pub file: File,
}

impl CoreFile {
    pub fn new(file: File) -> CoreFile {
        CoreFile { file }
    }

    pub fn into_inner(self) -> File {
        self.file
    }
}

impl Core for CoreFile {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        self.file.read_exact(buf)
    }

    fn write(&mut self, buf: &[u8]) -> io::Result<()> {
        self.file.write_all(buf)
    }

    fn length(&mut self) -> io::Result<u64> {
        Ok(self.file.metadata()?.len())
    }

    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        self.file.seek(SeekFrom::Start(pos)).map(|_| ())
    }

    fn position(&mut self) -> io::Result<u64> {
        self.file.stream_position()
    }

    fn set_length(&mut self, len: u64) -> io::Result<()> {
        self.file.set_len(len)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }

    fn sync(&mut self) -> io::Result<()> {
        self.file.sync_all()
    }
}

// CoreBufferedFile

pub const DEFAULT_BUFFER_SIZE: usize = 8 * 1024 * 1024;

/// A file-backed database that buffers writes in memory, which
/// dramatically improves performance. This is the recommended core for
/// file-based databases.
///
/// Buffered data is flushed when the core is dropped, but errors are
/// ignored there, so call [`CoreBufferedFile::close`] (or [`Core::finish`]
/// when the core is behind a [`DynCore`] or a generic `C: Core`) to
/// observe them.
#[derive(Debug)]
pub struct CoreBufferedFile {
    file: Option<File>,
    memory: CoreMemory,
    buffer_size: usize,
    file_pos: u64,
    memory_pos: u64,
    // the file's length, cached so that length() doesn't need to ask the OS
    // every time data is allocated. another process may write to the file
    // whenever this one isn't, so it is only set once we begin writing, and
    // it is cleared when the writes are flushed.
    file_len: Option<u64>,
}

impl CoreBufferedFile {
    pub fn new(file: File) -> CoreBufferedFile {
        CoreBufferedFile::with_buffer_size(file, DEFAULT_BUFFER_SIZE)
    }

    pub fn with_buffer_size(file: File, buffer_size: usize) -> CoreBufferedFile {
        CoreBufferedFile {
            file: Some(file),
            memory: CoreMemory::new(),
            buffer_size,
            file_pos: 0,
            memory_pos: 0,
            file_len: None,
        }
    }

    /// Opens the file at `path` for reading and writing, creating it if it
    /// doesn't exist. Existing contents are kept.
    ///
    /// The file isn't locked. Only one process may write to a database at
    /// a time, so when writing from multiple processes, hold an exclusive
    /// lock on a separate lock file (such as `<path>.lock`) while opening
    /// and writing. Don't lock the database file itself: on some platforms,
    /// such as Windows, that lock is mandatory and would block readers.
    pub fn open(path: impl AsRef<Path>) -> io::Result<CoreBufferedFile> {
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path)?;
        Ok(CoreBufferedFile::new(file))
    }

    /// Opens the existing file at `path` for reading only. Reads never block
    /// writes, so this is safe while another process is writing to the file.
    /// Writing to a database opened this way fails with an i/o error, and
    /// so does passing an empty file to [`Database::new`](crate::Database::new),
    /// which would initialize it; [`Database::open_read_only`](crate::Database::open_read_only)
    /// checks for that.
    pub fn open_read_only(path: impl AsRef<Path>) -> io::Result<CoreBufferedFile> {
        Ok(CoreBufferedFile::new(File::open(path)?))
    }

    /// Flushes buffered data and returns the file.
    pub fn close(mut self) -> io::Result<File> {
        self.flush()?;
        Ok(self.file.take().expect("file is only taken on close"))
    }

    fn file(&mut self) -> &mut File {
        self.file.as_mut().expect("file is only taken on close")
    }

    fn memory_size(&self) -> u64 {
        self.memory.buf.len() as u64
    }

    fn stat_length(&mut self) -> io::Result<u64> {
        Ok(self.file().metadata()?.len())
    }

    fn write_to_file(&mut self, pos: u64, data: &[u8]) -> io::Result<()> {
        // if the write fails partway, the file's length is unknown
        let file_len = self.file_len.take();
        let file = self.file();
        file.seek(SeekFrom::Start(pos))?;
        file.write_all(data)?;
        if let Some(file_len) = file_len {
            self.file_len = Some(file_len.max(pos + data.len() as u64));
        }
        Ok(())
    }

    fn flush_buffer(&mut self) -> io::Result<()> {
        self.file_len = None;
        if self.memory_size() > 0 {
            let buf = std::mem::take(&mut self.memory.buf);
            let result = self.write_to_file(self.memory_pos, &buf);
            self.memory.buf = buf;
            result?;
            self.memory.buf.clear();
            self.memory.pos = 0;
        }
        Ok(())
    }
}

impl Core for CoreBufferedFile {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        let mut pos = 0usize;
        let len = buf.len();

        // read from disk -- before the in-memory buffer
        if self.file_pos < self.memory_pos {
            let size_before_mem = len.min((self.memory_pos - self.file_pos) as usize);
            let file_pos = self.file_pos;
            let file = self.file();
            file.seek(SeekFrom::Start(file_pos))?;
            file.read_exact(&mut buf[..size_before_mem])?;
            pos += size_before_mem;
            self.file_pos += size_before_mem as u64;
        }

        if pos == len {
            return Ok(());
        }

        // read from the in-memory buffer
        let memory_size = self.memory_size();
        if self.file_pos >= self.memory_pos && self.file_pos < self.memory_pos + memory_size {
            let mem_pos = (self.file_pos - self.memory_pos) as usize;
            let size_in_mem = (memory_size as usize - mem_pos).min(len - pos);
            buf[pos..pos + size_in_mem]
                .copy_from_slice(&self.memory.buf[mem_pos..mem_pos + size_in_mem]);
            pos += size_in_mem;
            self.file_pos += size_in_mem as u64;
        }

        if pos == len {
            return Ok(());
        }

        // read from disk -- after the in-memory buffer
        if self.file_pos >= self.memory_pos + memory_size {
            let file_pos = self.file_pos;
            let file = self.file();
            file.seek(SeekFrom::Start(file_pos))?;
            file.read_exact(&mut buf[pos..])?;
            self.file_pos += (len - pos) as u64;
        }

        Ok(())
    }

    fn write(&mut self, data: &[u8]) -> io::Result<()> {
        let n = data.len() as u64;
        if n == 0 {
            return Ok(());
        }
        let buffer_size = self.buffer_size as u64;

        // the in-memory buffer is a single contiguous window of the file
        // starting at memory_pos. start a new window at this position if
        // the buffer is empty, the write is past the end of the window,
        // or the write would grow the window beyond the max size.
        if self.memory_size() == 0
            || self.file_pos > self.memory_pos + self.memory_size()
            || (self.file_pos >= self.memory_pos
                && self.file_pos - self.memory_pos + n > buffer_size)
        {
            self.flush_buffer()?;
            self.memory_pos = self.file_pos;
        }

        if self.file_len.is_none() {
            self.file_len = Some(self.stat_length()?);
        }

        if self.file_pos >= self.memory_pos && self.file_pos - self.memory_pos + n <= buffer_size {
            // write to the in-memory buffer
            self.memory.seek_to(self.file_pos - self.memory_pos)?;
            self.memory.write(data)?;
        } else {
            // a direct disk write that overlaps the buffered region would be
            // clobbered by a later flush of stale buffer bytes, so flush first
            if self.file_pos < self.memory_pos + self.memory_size()
                && self.file_pos + n > self.memory_pos
            {
                self.flush_buffer()?;
            }
            self.write_to_file(self.file_pos, data)?;
        }

        self.file_pos += n;
        Ok(())
    }

    fn length(&mut self) -> io::Result<u64> {
        let file_len = match self.file_len {
            Some(len) => len,
            None => self.stat_length()?,
        };
        let buffer_size = self.memory_size();
        // a failed allocation or a rollback can leave an empty
        // buffer positioned beyond the file's end.
        if buffer_size == 0 {
            return Ok(file_len);
        }
        Ok((self.memory_pos + buffer_size).max(file_len))
    }

    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        self.file_pos = pos;
        Ok(())
    }

    fn position(&mut self) -> io::Result<u64> {
        Ok(self.file_pos)
    }

    fn set_length(&mut self, len: u64) -> io::Result<()> {
        // discard buffered bytes past the new end rather than flushing them.
        // a rollback must not depend on writing the data it is throwing away,
        // because that write may be what failed (e.g. the disk is full).
        if len <= self.memory_pos {
            self.memory.set_length(0)?;
        } else if len < self.memory_pos + self.memory_size() {
            self.memory.set_length(len - self.memory_pos)?;
        }
        self.file_len = None;
        self.file().set_len(len)?;
        if len < self.file_pos {
            self.file_pos = len;
        }
        Ok(())
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flush_buffer()
    }

    fn sync(&mut self) -> io::Result<()> {
        self.flush_buffer()?;
        self.file().sync_all()
    }
}

impl Drop for CoreBufferedFile {
    fn drop(&mut self) {
        if self.file.is_some() {
            let _ = self.flush_buffer();
        }
    }
}
