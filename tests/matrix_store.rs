use paramo1d::matrix_store::{write_chunked, ChunkedMatrix};
use std::{
    fs::{self, File},
    io::{Cursor, Read, Seek, SeekFrom},
};

#[test]
fn chunked_store_preserves_canonical_bytes_across_random_seeks() {
    let bytes: Vec<_> = (0..2 * 1024 * 1024 + 73)
        .map(|i| (i ^ (i >> 8)) as u8)
        .collect();
    let path = tempfile::NamedTempFile::new().unwrap();
    let (logical, stored) = write_chunked(
        &mut Cursor::new(&bytes),
        &mut File::create(path.path()).unwrap(),
        4 << 20,
    )
    .unwrap();
    assert_eq!(logical, bytes.len() as u64);
    assert_eq!(stored, fs::metadata(path.path()).unwrap().len());
    let mut reader = ChunkedMatrix::open(File::open(path.path()).unwrap(), 4 << 20).unwrap();
    for offset in [0, 1_048_570, bytes.len() - 73, 128, 1_900_000, 0] {
        reader.seek(SeekFrom::Start(offset as u64)).unwrap();
        let mut output = vec![0; (bytes.len() - offset).min(151)];
        reader.read_exact(&mut output).unwrap();
        assert_eq!(output, bytes[offset..offset + output.len()]);
    }
    assert_eq!(reader.seek(SeekFrom::End(0)).unwrap(), logical);
    assert_eq!(reader.read(&mut [0; 1]).unwrap(), 0);
    assert!(reader.seek(SeekFrom::Start(u64::MAX)).is_err());
    assert!(reader.seek(SeekFrom::Start(0)).is_ok());
    assert!(reader.seek(SeekFrom::Current(-1)).is_err());
}

#[test]
fn matrix_container_enforces_lengths_ranges_and_decode_bounds() {
    let file = tempfile::NamedTempFile::new().unwrap();
    write_chunked(
        &mut Cursor::new(vec![7; 1024]),
        &mut File::create(file.path()).unwrap(),
        1024,
    )
    .unwrap();
    let original = fs::read(file.path()).unwrap();
    assert!(ChunkedMatrix::open(File::open(file.path()).unwrap(), 1023).is_err());
    for (at, replacement) in [(0, 0), (8, 2), (36, 1), (32, 255)] {
        let mut changed = original.clone();
        changed[at] = replacement;
        fs::write(file.path(), changed).unwrap();
        assert!(ChunkedMatrix::open(File::open(file.path()).unwrap(), 1024).is_err());
    }
    let mut changed = original.clone();
    changed[40] ^= 0xff;
    fs::write(file.path(), changed).unwrap();
    let mut reader = ChunkedMatrix::open(File::open(file.path()).unwrap(), 1024).unwrap();
    assert!(reader.read_to_end(&mut Vec::new()).is_err());
    let output = tempfile::NamedTempFile::new().unwrap();
    assert!(write_chunked(
        &mut Cursor::new(vec![1; 1025]),
        &mut File::create(output.path()).unwrap(),
        1024
    )
    .is_err());
}
