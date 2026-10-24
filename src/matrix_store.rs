use anyhow::{ensure, Context, Result};
use std::{
    collections::VecDeque,
    fs::File,
    io::{self, Cursor, Read, Seek, SeekFrom, Write},
    path::Path,
};

const MAGIC: &[u8; 8] = b"PMATRIX1";
const HEADER_BYTES: u64 = 40;
const CHUNK_BYTES: usize = 1024 * 1024;
const MAX_ENCODED_CHUNK: usize = CHUNK_BYTES + 65536;
const MAX_CACHED_CHUNKS: usize = 4;

#[derive(Clone, Copy)]
struct Chunk {
    offset: u64,
    encoded: u32,
    decoded: u32,
}

pub struct ChunkedMatrix {
    file: File,
    length: u64,
    position: u64,
    chunks: Vec<Chunk>,
    cache: VecDeque<(usize, Vec<u8>)>,
}

pub fn write_chunked(input: &mut impl Read, output: &mut File, cap: u64) -> Result<(u64, u64)> {
    output.write_all(&[0; HEADER_BYTES as usize])?;
    let mut chunks = Vec::new();
    let mut length = 0u64;
    loop {
        let mut bytes = Vec::with_capacity(CHUNK_BYTES);
        (&mut *input)
            .take(CHUNK_BYTES as u64)
            .read_to_end(&mut bytes)?;
        if bytes.is_empty() {
            break;
        }
        length = length
            .checked_add(bytes.len() as u64)
            .context("matrix length overflow")?;
        ensure!(length <= cap, "matrix decompression exceeds its byte limit");
        let encoded = zstd::bulk::compress(&bytes, 3)?;
        ensure!(
            encoded.len() <= MAX_ENCODED_CHUNK,
            "encoded matrix chunk limit"
        );
        chunks.push(Chunk {
            offset: output.stream_position()?,
            encoded: encoded.len() as u32,
            decoded: bytes.len() as u32,
        });
        output.write_all(&encoded)?;
    }
    ensure!(!chunks.is_empty(), "empty matrix input");
    let index_offset = output.stream_position()?;
    for chunk in &chunks {
        output.write_all(&chunk.offset.to_le_bytes())?;
        output.write_all(&chunk.encoded.to_le_bytes())?;
        output.write_all(&chunk.decoded.to_le_bytes())?;
    }
    let stored = output.stream_position()?;
    output.seek(SeekFrom::Start(0))?;
    output.write_all(MAGIC)?;
    output.write_all(&1u32.to_le_bytes())?;
    output.write_all(&(CHUNK_BYTES as u32).to_le_bytes())?;
    output.write_all(&length.to_le_bytes())?;
    output.write_all(&index_offset.to_le_bytes())?;
    output.write_all(&(chunks.len() as u32).to_le_bytes())?;
    output.write_all(&0u32.to_le_bytes())?;
    output.sync_all()?;
    Ok((length, stored))
}

impl ChunkedMatrix {
    pub fn open(mut file: File, cap: u64) -> Result<Self> {
        let stored = file.metadata()?.len();
        ensure!(stored >= HEADER_BYTES, "matrix container header length");
        let mut header = [0; HEADER_BYTES as usize];
        file.read_exact(&mut header)?;
        ensure!(&header[..8] == MAGIC, "matrix container magic");
        ensure!(
            u32::from_le_bytes(header[8..12].try_into()?) == 1,
            "matrix container version"
        );
        ensure!(
            u32::from_le_bytes(header[12..16].try_into()?) as usize == CHUNK_BYTES,
            "matrix chunk geometry"
        );
        ensure!(header[36..40] == [0; 4], "matrix container reserved bytes");
        let length = u64::from_le_bytes(header[16..24].try_into()?);
        let index_offset = u64::from_le_bytes(header[24..32].try_into()?);
        let count = u32::from_le_bytes(header[32..36].try_into()?) as u64;
        ensure!(length > 0 && length <= cap, "matrix decoded byte limit");
        ensure!(
            count == length.div_ceil(CHUNK_BYTES as u64),
            "matrix chunk count"
        );
        ensure!(
            index_offset >= HEADER_BYTES && index_offset.checked_add(count * 16) == Some(stored),
            "matrix container index bounds"
        );
        ensure!(
            stored <= HEADER_BYTES + count * (MAX_ENCODED_CHUNK as u64 + 16),
            "matrix stored byte limit"
        );
        file.seek(SeekFrom::Start(index_offset))?;
        let mut chunks = Vec::with_capacity(count as usize);
        let mut expected_offset = HEADER_BYTES;
        for index in 0..count {
            let mut entry = [0; 16];
            file.read_exact(&mut entry)?;
            let chunk = Chunk {
                offset: u64::from_le_bytes(entry[..8].try_into()?),
                encoded: u32::from_le_bytes(entry[8..12].try_into()?),
                decoded: u32::from_le_bytes(entry[12..].try_into()?),
            };
            let expected_length = (length - index * CHUNK_BYTES as u64).min(CHUNK_BYTES as u64);
            ensure!(
                chunk.offset == expected_offset
                    && (1..=MAX_ENCODED_CHUNK as u32).contains(&chunk.encoded),
                "matrix chunk range"
            );
            ensure!(
                chunk.decoded as u64 == expected_length,
                "matrix chunk decoded length"
            );
            expected_offset = expected_offset
                .checked_add(chunk.encoded as u64)
                .context("matrix offset overflow")?;
            ensure!(
                expected_offset <= index_offset,
                "matrix chunk exceeds payload"
            );
            chunks.push(chunk);
        }
        ensure!(expected_offset == index_offset, "matrix payload length");
        Ok(Self {
            file,
            length,
            position: 0,
            chunks,
            cache: VecDeque::new(),
        })
    }

    fn load(&mut self, index: usize) -> io::Result<&[u8]> {
        if let Some(at) = self.cache.iter().position(|entry| entry.0 == index) {
            let entry = self.cache.remove(at).expect("located matrix chunk");
            self.cache.push_back(entry);
        } else {
            let chunk = self.chunks[index];
            self.file.seek(SeekFrom::Start(chunk.offset))?;
            let mut encoded = vec![0; chunk.encoded as usize];
            self.file.read_exact(&mut encoded)?;
            let mut decoder = zstd::stream::read::Decoder::new(Cursor::new(encoded))?;
            decoder.window_log_max(20)?;
            let mut decoded = Vec::with_capacity(chunk.decoded as usize);
            decoder
                .take(chunk.decoded as u64 + 1)
                .read_to_end(&mut decoded)?;
            if decoded.len() != chunk.decoded as usize {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "matrix chunk output length",
                ));
            }
            if self.cache.len() == MAX_CACHED_CHUNKS {
                self.cache.pop_front();
            }
            self.cache.push_back((index, decoded));
        }
        Ok(&self.cache.back().expect("loaded matrix chunk").1)
    }
}

impl Read for ChunkedMatrix {
    fn read(&mut self, destination: &mut [u8]) -> io::Result<usize> {
        let mut written = 0;
        while written < destination.len() && self.position < self.length {
            let index = (self.position / CHUNK_BYTES as u64) as usize;
            let offset = (self.position % CHUNK_BYTES as u64) as usize;
            let bytes = self.load(index)?;
            let count = (bytes.len() - offset).min(destination.len() - written);
            destination[written..written + count].copy_from_slice(&bytes[offset..offset + count]);
            self.position += count as u64;
            written += count;
        }
        Ok(written)
    }
}

impl Seek for ChunkedMatrix {
    fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
        let next = match position {
            SeekFrom::Start(at) => at as i128,
            SeekFrom::Current(delta) => self.position as i128 + delta as i128,
            SeekFrom::End(delta) => self.length as i128 + delta as i128,
        };
        if next < 0 || next > self.length as i128 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "matrix seek bounds",
            ));
        }
        self.position = next as u64;
        Ok(self.position)
    }
}

pub enum MatrixReader {
    Plain(File),
    Chunked(ChunkedMatrix),
}

impl MatrixReader {
    pub fn open(path: &Path, cap: u64) -> Result<Self> {
        let compact = path.with_extension("pmatrix");
        if compact.exists() {
            return Ok(Self::Chunked(ChunkedMatrix::open(
                File::open(compact)?,
                cap,
            )?));
        }
        let file = File::open(path)?;
        ensure!(file.metadata()?.len() <= cap, "matrix file byte limit");
        Ok(Self::Plain(file))
    }
}

impl Read for MatrixReader {
    fn read(&mut self, destination: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Plain(file) => file.read(destination),
            Self::Chunked(file) => file.read(destination),
        }
    }
}

impl Seek for MatrixReader {
    fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
        match self {
            Self::Plain(file) => file.seek(position),
            Self::Chunked(file) => file.seek(position),
        }
    }
}
