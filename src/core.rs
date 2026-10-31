use std::fs::{File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;

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
    /// Called when the core is done being used, to flush anything it
    /// buffers and report errors that dropping it would ignore. The
    /// default calls [`Core::sync`]. The core may still be used afterwards.
    ///
    /// Unlike [`CoreBufferedFile::close`], this works through a
    /// [`DynCore`] or any other wrapper, since it doesn't consume the core.
    fn close(&mut self) -> io::Result<()> {
        self.sync()
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
    fn close(&mut self) -> io::Result<()> {
        (**self).close()
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
    fn close(&mut self) -> io::Result<()> {
        (**self).close()
    }
}

// CoreMemory

/// A database that lives entirely in memory.
#[derive(Debug, Clone, Default)]
pub struct CoreMemory {
    buf: Vec<u8>,
    pos: usize,
}

impl CoreMemory {
    pub fn new() -> CoreMemory {
        CoreMemory::default()
    }

    /// Wraps existing database bytes, such as ones received over a network.
    pub fn from_bytes(buf: Vec<u8>) -> CoreMemory {
        CoreMemory { buf, pos: 0 }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.buf
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }
}

impl Core for CoreMemory {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<()> {
        let end = self.pos + buf.len();
        if end > self.buf.len() {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                format!(
                    "read beyond end of memory: pos={}, len={}, size={}",
                    self.pos,
                    buf.len(),
                    self.buf.len()
                ),
            ));
        }
        buf.copy_from_slice(&self.buf[self.pos..end]);
        self.pos = end;
        Ok(())
    }

    fn write(&mut self, data: &[u8]) -> io::Result<()> {
        let pos = self.pos;
        if pos < self.buf.len() {
            let before_end = data.len().min(self.buf.len() - pos);
            self.buf[pos..pos + before_end].copy_from_slice(&data[..before_end]);
            self.buf.extend_from_slice(&data[before_end..]);
        } else {
            // pad with zeros if position is beyond current length
            self.buf.resize(pos, 0);
            self.buf.extend_from_slice(data);
        }
        self.pos = pos + data.len();
        Ok(())
    }

    fn length(&mut self) -> io::Result<u64> {
        Ok(self.buf.len() as u64)
    }

    fn seek_to(&mut self, pos: u64) -> io::Result<()> {
        self.pos = (pos as usize).min(self.buf.len());
        Ok(())
    }

    fn position(&mut self) -> io::Result<u64> {
        Ok(self.pos as u64)
    }

    fn set_length(&mut self, len: u64) -> io::Result<()> {
        let len = len as usize;
        if len > self.buf.len() {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "invalid memory length"));
        }
        if len == 0 || self.pos > len {
            self.pos = len;
        }
        self.buf.truncate(len);
        Ok(())
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
/// ignored there, so call [`CoreBufferedFile::close`] (or [`Core::close`]
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
    /// a time, so when writing from multiple processes, take an exclusive
    /// lock on the file first (see [`CoreBufferedFile::get_ref`]).
    pub fn open(path: impl AsRef<Path>) -> io::Result<CoreBufferedFile> {
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path)?;
        Ok(CoreBufferedFile::new(file))
    }

    /// Opens the existing file at `path` for reading only. Reads never block
    /// writes, so this is safe while another process is writing to the file.
    /// Writing to a database opened this way fails with an i/o error.
    pub fn open_read_only(path: impl AsRef<Path>) -> io::Result<CoreBufferedFile> {
        Ok(CoreBufferedFile::new(File::open(path)?))
    }

    /// Borrows the file, for example to lock it. Don't read or write
    /// through it, because buffered writes may not have reached it yet.
    pub fn get_ref(&self) -> &File {
        self.file.as_ref().expect("file is only taken on close")
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
