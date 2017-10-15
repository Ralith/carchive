extern crate byteorder;

use std::{io, mem};
use std::collections::BTreeMap;
use std::borrow::Borrow;
use std::marker::PhantomData;

use byteorder::{LittleEndian, WriteBytesExt, ByteOrder};

/// the Ord impl *must* be consistent with a lexical ordering of the borrowed [u8]
// FIXME: Ditch Ord once generic array lengths are possible
pub trait Key: Borrow<[u8]> + Ord {
    const SIZE: usize;
}

pub struct Writer<K, T> {
    inner: T,
    cursor: usize,
    chunks: BTreeMap<K, (usize, usize)>,
}

pub struct ChunkWriter<'a, K: 'a, T: 'a>
    where K: Key
{
    inner: &'a mut Writer<K, T>,
    start: usize,
    key: mem::ManuallyDrop<K>,
}

impl<'a, K, T> io::Write for ChunkWriter<'a, K, T>
    where T: io::Write, K: Key
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = self.inner.inner.write(buf)?;
        self.inner.cursor += n;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> { self.inner.inner.flush() }
}

impl<'a, K, T> Drop for ChunkWriter<'a, K, T>
    where K: Key
{
    fn drop(&mut self) {
        let key = unsafe { mem::replace::<K>(&mut self.key, mem::uninitialized()) };
        self.inner.chunks.insert(key, (self.start, self.inner.cursor));
    }
}

impl<K, T> Writer<K, T>
    where T: io::Write, K: Key
{
    pub fn new(inner: T) -> Self {
        Writer {
            inner,
            cursor: 0,
            chunks: BTreeMap::new(),
        }
    }

    pub fn push<'a>(&'a mut self, key: K) -> ChunkWriter<'a, K, T> {
        ChunkWriter { key: mem::ManuallyDrop::new(key), start: self.cursor, inner: self }
    }

    pub fn finish(mut self) -> io::Result<()> {
        // FIXME: Nonblocking?
        for (key, &(start, len)) in &self.chunks {
            debug_assert!(key.borrow().len() == K::SIZE);
            self.inner.write_all(key.borrow())?;
            self.inner.write_u64::<LittleEndian>(start as u64)?;
            self.inner.write_u64::<LittleEndian>(len as u64)?;
        }
        self.inner.write_u64::<LittleEndian>(self.chunks.len() as u64)?;
        self.inner.write_u32::<LittleEndian>(K::SIZE as u32)?;
        Ok(())
    }
}

pub struct Reader<K, T> {
    data: T,
    _phantom: PhantomData<K>
}

impl<K, T> Reader<K, T>
    where T: AsRef<[u8]>, K: Key
{
    /// Returns None if key sizes don't match
    pub fn new(data: T) -> Option<Self> {
        let result = Reader { data, _phantom: PhantomData };
        if result.key_size() as usize != K::SIZE { None } else { Some(result) }
    }

    pub fn get(&self, key: &K) -> Option<&[u8]> {
        let key = key.borrow();
        let mut i = LittleEndian::read_u64(key) / (u64::max_value() / (self.index_len() - 1));
        if self.index_entry(i).0 <= key {
            while self.index_entry(i).0 <= key {
                let (entry, start, len) = self.index_entry(i);
                if key == entry {
                    return Some(&self.data.as_ref()[start as usize..(start+len) as usize]);
                }
                i += 1;
            }
        } else {
            while self.index_entry(i).0 > key {
                let (entry, start, len) = self.index_entry(i);
                if key == entry {
                    return Some(&self.data.as_ref()[start as usize..(start+len) as usize]);
                }
                i -= 1;
            }
        }
        None
    }

    pub fn index(&self) -> IndexIter<K, T> { IndexIter { reader: self, cursor: 0 } }

    // FIXME: &[u8; K::SIZE]
    fn index_entry(&self, i: u64) -> (&[u8], u64, u64) {
        let data = self.data.as_ref();
        let row_size = K::SIZE + 16;
        let index_end = data.len() - 12;
        let index_start = index_end - self.index_len() as usize * row_size;
        let index = &data[index_start..index_end];
        let entry = &index[i as usize * row_size..(i as usize + 1)*row_size];
        (&entry[0..K::SIZE], LittleEndian::read_u64(&entry[K::SIZE..K::SIZE+8]), LittleEndian::read_u64(&entry[K::SIZE+8..K::SIZE+16]))
    }

    fn index_len(&self) -> u64 {
        let data = self.data.as_ref();
        LittleEndian::read_u64(&data[data.len() - 12..data.len() - 4])
    }

    fn key_size(&self) -> u32 {
        let data = self.data.as_ref();
        LittleEndian::read_u32(&data[data.len() - 4..])
    }
}

pub struct IndexIter<'a, K: 'a, T: 'a> {
    reader: &'a Reader<K, T>,
    cursor: u64,
}

impl<'a, K, T> Iterator for IndexIter<'a, K, T>
    where T: AsRef<[u8]>, K: Key
{
    // FIXME: &'a [u8; K::SIZE]
    type Item = (&'a [u8], u64, u64);
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor == self.reader.index_len() { return None; }
        let result = self.reader.index_entry(self.cursor);
        self.cursor += 1;
        Some(result)
    }
}
