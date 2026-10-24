// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright (C) 2026 Paranoid Zero.

//! Optional prover-only storage for a one-time retirement proof. The file is
//! unnamed, private, process-local and removed on close. It is neither a
//! reusable cache nor a source of verifier authority.

use super::{Error, F128};
use std::{io::Write, path::Path};

pub(super) struct DiskCodeword {
    mapping: memmap2::Mmap,
    // Keep ownership of the anonymous file until after the map is dropped.
    _file: std::fs::File,
}

impl DiskCodeword {
    pub(super) fn spill(values: Vec<F128>, directory: &Path) -> Result<Self, Error> {
        let mut file = tempfile::tempfile_in(directory).map_err(workspace_error)?;
        let byte_length = values
            .len()
            .checked_mul(std::mem::size_of::<F128>())
            .ok_or(Error::Shape)?;
        if byte_length == 0 {
            return Err(Error::Shape);
        }
        // SAFETY: F128 is repr(C, align(16)) with exactly two initialized u64
        // fields and no padding. This file stays on this process/machine; it
        // is deliberately not a wire encoding or a portable cached artifact.
        let bytes =
            unsafe { std::slice::from_raw_parts(values.as_ptr().cast::<u8>(), byte_length) };
        file.write_all(bytes).map_err(workspace_error)?;
        file.flush().map_err(workspace_error)?;
        drop(values);
        // SAFETY: the file has no name, its handle is private, and no writer
        // can mutate/truncate it while the read-only mapping is alive.
        let mapping = unsafe { memmap2::MmapOptions::new().len(byte_length).map(&file) }
            .map_err(workspace_error)?;
        if mapping.as_ptr().align_offset(std::mem::align_of::<F128>()) != 0 {
            return Err(Error::Shape);
        }
        Ok(Self {
            mapping,
            _file: file,
        })
    }

    pub(super) fn values(&self) -> &[F128] {
        // SAFETY: spill checked alignment/length and wrote initialized F128s.
        // All bit patterns are valid F128 values; backing bytes are immutable.
        unsafe {
            std::slice::from_raw_parts(
                self.mapping.as_ptr().cast::<F128>(),
                self.mapping.len() / std::mem::size_of::<F128>(),
            )
        }
    }
}

fn workspace_error(error: std::io::Error) -> Error {
    Error::Workspace(error.to_string())
}
