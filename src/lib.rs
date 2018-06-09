//! Fast key-value storage for immutable content-addressed data
//!
//! ```
//! use std::io::Write;
//!
//! let mut buf = Vec::new();
//! {
//!     let mut writer = carchive::Writer::new(3, &mut buf);
//!     writer.write_all(b"value").unwrap();
//!     writer.finish_value(b"key");
//!     writer.finish(&[]).unwrap();
//! }
//!
//! let reader = carchive::Reader::new(&buf).unwrap();
//! assert_eq!(reader.key_len(), 3);
//! assert_eq!(reader.get(b"key").unwrap(), b"value");
//! assert!(reader.get(b"bad").is_none());
//! ```


#![warn(missing_docs)]

extern crate byteorder;
#[macro_use]
extern crate failure;

use std::io::{self, Read, Seek, SeekFrom};
use std::fs::File;
use std::cmp::Ordering;
use std::collections::BTreeMap;

use byteorder::{LittleEndian, WriteBytesExt, ReadBytesExt, ByteOrder};
use failure::Fail;

/// Archive encoder.
///
/// ```no_run
/// use std::fs::File;
/// use std::io::Write;
///
/// let mut writer = carchive::Writer::new(4, File::create("example.car").unwrap());
/// writer.write_all(b"value1").unwrap();
/// writer.finish_value(b"key1");
/// // ...
/// writer.finish(&[]).unwrap();
/// ```
#[derive(Debug)]
pub struct Writer<T> {
    inner: T,
    key_len: u32,
    value_end: u64,
    cursor: u64,
    values: BTreeMap<Box<[u8]>, (u64, u64)>,
}

impl<T> io::Write for Writer<T>
    where T: io::Write
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.cursor += n as u64;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> { self.inner.flush() }
}

impl<T> Writer<T> {
    /// Access the inner value
    pub fn get_ref(&self) -> &T { &self.inner }
    /// Access the inner value mutably
    pub fn get_mut(&mut self) -> &mut T { &mut self.inner }
}

impl<T> Writer<T>
    where T: io::Write
{
    /// Create a new writer using keys of `key_len` bytes and writing data to `inner`.
    pub fn new(key_len: u32, inner: T) -> Self {
        Writer {
            inner, key_len,
            value_end: 0,
            cursor: 0,
            values: BTreeMap::new(),
        }
    }

    /// Set the `key` to use for previously written data, and begin a new value.
    ///
    /// For fast random access, keys must be approximately uniformly distributed. Hashes make good keys for this reason.
    ///
    /// This is done after writing a value so that the the key can be computed from the value (for example, by a hash
    /// function) without multiple passes.
    pub fn finish_value(&mut self, key: &[u8]) {
        assert_eq!(key.len(), self.key_len as usize, "key sizes must be constant");
        self.values.insert(key.to_vec().into(), (self.value_end, self.cursor - self.value_end));
        self.value_end = self.cursor;
    }

    /// Check whether `key` has already been written.
    pub fn contains(&self, key: &[u8]) -> bool {
        self.values.contains_key(key)
    }

    /// Length of keys used by this archive.
    pub fn key_len(&self) -> u32 { self.key_len }

    /// Write out the archive index and headers.
    ///
    /// `extensions` can be used to store custom unstructured header data. Note that for extension data to be
    /// accessible, it should be either fixed length or end with a fixed-size length tag.
    pub fn finish(mut self, extensions: &[u8]) -> io::Result<()> {
        self.inner.write_all(extensions)?;
        for (key, &(start, len)) in &self.values {
            self.inner.write_all(key)?;
            self.inner.write_u64::<LittleEndian>(start as u64)?;
            self.inner.write_u64::<LittleEndian>(len as u64)?;
        }
        self.inner.write_u64::<LittleEndian>(self.values.len() as u64)?;
        self.inner.write_u32::<LittleEndian>(self.key_len)?;
        Ok(())
    }
}

impl Writer<File> {
    /// Open an existing file for appending.
    ///
    /// This loads the index of an existing archive fully into memory, truncates it from the file, and allows new data
    /// to be appended to the end. Modifying or removing existing data is not supported. If you re-write the same key
    /// with a new value, the storage for the old value will remain allocated.
    pub fn open(mut file: File) -> io::Result<Self> {
        let len = file.metadata()?.len();
        if len < 8 { return Err(io::Error::new(io::ErrorKind::InvalidData, Error::Header.compat())); }
        file.seek(SeekFrom::Start(len-12))?;
        let index_len = file.read_u64::<LittleEndian>()?;
        let key_len = file.read_u32::<LittleEndian>()?;
        let index_start = len - 4 - 8 - index_len * (key_len as u64 + 16);
        file.seek(SeekFrom::Start(index_start))?;
        let mut values = BTreeMap::new();
        for _ in 0..index_len {
            let mut key = vec![0; key_len as usize];
            file.read_exact(&mut key[..])?;
            let start = file.read_u64::<LittleEndian>()?;
            let len = file.read_u64::<LittleEndian>()?;
            values.insert(key.into(), (start, len));
        }
        file.seek(SeekFrom::Start(index_start))?;
        file.set_len(index_start)?;
        Ok(Self {
            inner: file,
            key_len,
            value_end: index_start,
            cursor: index_start,
            values,
        })
    }
}

#[derive(Debug, Fail, Eq, PartialEq)]
/// Error generated when processing a malformed archive.
pub enum Error {
    /// Malformed archive header.
    #[fail(display = "malformed header")]
    Header,
    /// Malformed archive index entry.
    #[fail(display = "index entry {} is malformed", _0)]
    Index(u64),
}

/// Decoder for in-memory archives.
///
/// ```no_run
/// # const DATA: &[u8] = &[];
///
/// let reader = carchive::Reader::new(&DATA).unwrap();
/// assert_eq!(reader.get(b"key").unwrap(), b"value");
/// ```
#[derive(Debug, Clone)]
pub struct Reader<T> {
    data: T,
}

impl<T> Reader<T> {
    /// Access the inner value
    pub fn get_ref(&self) -> &T { &self.data }
    /// Access the inner value mutably
    pub fn get_mut(&mut self) -> &mut T { &mut self.data }
}

impl<T> Reader<T>
    where T: AsRef<[u8]>
{
    /// Create a `Reader` for an in-memory archive.
    pub fn new(data: T) -> Result<Self, Error> {
        let len = data.as_ref().len();
        if len < 8 { return Err(Error::Header); }
        let result = Self { data };
        if (len as u64) < result.header_size() { return Err(Error::Header); }
        for i in 0..result.index_len() {
            let (_, start, entry_len) = result.index_entry(i);
            if let Some(x) = start.checked_add(entry_len) {
                if x > len as u64 { return Err(Error::Index(i)); }
            } else {
                return Err(Error::Index(i));
            }
        }
        Ok(result)
    }

    /// Find the value for a specific key.
    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        assert_eq!(key.len(), self.key_len() as usize, "unexpected key size");
        let n = self.index_len();
        let mut i = match n {
            0 => { return None; }
            1 => { 0 }
            _ => {
                let mut padded = [0; 8];
                let len = key.len().min(8);
                padded[8-len..].copy_from_slice(&key[key.len()-len..]);
                LittleEndian::read_u64(&padded) / (u64::max_value() / (n - 1))
            }
        };
        if self.index_entry(i).0 <= key {
            loop {
                let (entry, start, len) = self.index_entry(i);
                match entry.cmp(key) {
                    Ordering::Less => {
                        i += 1;
                        if i == n { return None; }
                    }
                    Ordering::Equal => { return Some(&self.data.as_ref()[start as usize..(start+len) as usize]); }
                    Ordering::Greater => { return None; }
                }
            }
        } else {
            loop {
                let (entry, start, len) = self.index_entry(i);
                match entry.cmp(key) {
                    Ordering::Greater => {
                        if i == 0 { return None; }
                        i -= 1;
                    }
                    Ordering::Equal => { return Some(&self.data.as_ref()[start as usize..(start+len) as usize]); }
                    Ordering::Less => { return None; }
                }
            }
        }
    }

    /// Access the last `offset` bytes of extension headers.
    ///
    /// Returns `None` if this would read before the start of the archive.
    pub fn extensions(&self, offset: usize) -> Option<&[u8]> {
        let end = (self.data.as_ref().len() as u64).checked_sub(self.header_size())?;
        let start = end.checked_sub(offset as u64)?;
        Some(&self.data.as_ref()[start as usize..end as usize])
    }

    fn header_size(&self) -> u64 { self.index_len() * (self.key_len() as u64 + 16) + 8 + 4 }

    fn index_entry(&self, i: u64) -> (&[u8], u64, u64) {
        let key_len = self.key_len() as usize;
        let data = self.data.as_ref();
        let row_size = key_len + 16;
        let index_end = data.len() - 8 - 4;
        let index_start = index_end - self.index_len() as usize * row_size;
        let index = &data[index_start..index_end];
        let entry = &index[i as usize * row_size..(i as usize + 1)*row_size];
        (&entry[0..key_len], LittleEndian::read_u64(&entry[key_len..key_len+8]), LittleEndian::read_u64(&entry[key_len+8..key_len+16]))
    }

    fn index_len(&self) -> u64 {
        let data = self.data.as_ref();
        LittleEndian::read_u64(&data[data.len() - 12..])
    }

    /// Length of keys used by this archive.
    pub fn key_len(&self) -> u32 {
        let data = self.data.as_ref();
        LittleEndian::read_u32(&data[data.len() - 4..])
    }

    /// Walk the archive's contents.
    pub fn iter(&self) -> Iter<T> { self.into_iter() }
}

/// Iterator over a `Reader`'s contents.
pub struct Iter<'a, T: 'a> {
    reader: &'a Reader<T>,
    cursor: u64,
}

impl<'a, T> Iterator for Iter<'a, T>
    where T: AsRef<[u8]>
{
    type Item = (&'a [u8], &'a [u8]);
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor == self.reader.index_len() { return None; }
        let (entry, start, len) = self.reader.index_entry(self.cursor);
        self.cursor += 1;
        Some((entry, &self.reader.data.as_ref()[start as usize..(start+len) as usize]))
    }
}

impl<'a, T> IntoIterator for &'a Reader<T>
    where T: AsRef<[u8]>
{
    type Item = (&'a [u8], &'a [u8]);
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Iter<'a, T> { Iter { reader: self, cursor: 0 } }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Write;

    const VALUES: &[(&[u8], &[u8])] =
        &[(b"abc", b"123"),
          (b"def", b"456"),
          (b"ghi", b"789")];

    #[test]
    fn roundtrip() {
        let mut buf = Vec::new();
        {
            let mut writer = Writer::new(3, &mut buf);
            for &(key, value) in VALUES.iter().rev() {
                writer.write_all(value).unwrap();
                writer.finish_value(key);
            }
            writer.finish(b"ext").unwrap();
        }

        let reader = Reader::new(&buf).unwrap();

        assert_eq!(reader.key_len(), 3);
        assert_eq!(reader.extensions(3).unwrap(), b"ext");
        assert_eq!(reader.get(b"abc").unwrap(), b"123");
        assert_eq!(reader.get(b"def").unwrap(), b"456");
        assert_eq!(reader.get(b"ghi").unwrap(), b"789");

        assert!(reader.get(b"aaa").is_none());
        assert!(reader.get(b"jkl").is_none());

        assert_eq!(reader.iter().collect::<Vec<_>>(), VALUES);
    }

    #[test]
    fn malformed_header() {
        assert_eq!(Reader::new(b"test").unwrap_err(), Error::Header);
    }
}
