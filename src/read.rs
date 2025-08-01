#[derive(Copy, Clone)]
pub struct ReadCtxt<'a> {
    pub input: &'a [u8],
    pub offset: usize,
}

impl<'a> std::fmt::Debug for ReadCtxt<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ReadCtxt {{ input: [_; {}], offset: {} }}",
            self.input.len(),
            self.offset
        )
    }
}

impl<'a> ReadCtxt<'a> {
    pub fn new(input: &'a [u8]) -> ReadCtxt<'a> {
        let offset = 0;
        ReadCtxt { input, offset }
    }

    pub fn remaining(&self) -> &'a [u8] {
        &self.input[self.offset..]
    }
    /// Creates a new `ReadCtxt` with the same `input` as the current `ReadCtxt`, but with an `offset` of `n`.
    ///
    /// The new `ReadCtxt` is only created if `n` is a valid offset into the `input` slice.
    pub fn seek_to(&self, n: usize) -> Option<ReadCtxt<'a>> {
        if n <= self.input.len() {
            Some(ReadCtxt { offset: n, ..*self })
        } else {
            None
        }
    }

    /// Splits the current `ReadCtxt` at the given position relative to the current offset,
    /// returning a tuple of two `ReadCtxt` instances if the split is valid.
    ///
    /// The first `ReadCtxt` contains the range from the current offset to `offset + n`,
    /// and the second `ReadCtxt` starts at `offset + n` and extends to the end of the input.
    ///
    /// Returns `None` if the specified position is out of bounds, i.e., if `offset + n`
    /// exceeds the length of the input.
    pub fn split_at(&self, n: usize) -> Option<(ReadCtxt<'a>, ReadCtxt<'a>)> {
        if self.offset + n <= self.input.len() {
            let fst = ReadCtxt {
                input: &self.input[..self.offset + n],
                ..*self
            };
            let snd = ReadCtxt {
                offset: self.offset + n,
                ..*self
            };
            Some((fst, snd))
        } else {
            None
        }
    }

    pub(crate) fn skip_remainder(&self) -> ReadCtxt<'a> {
        let offset = self.input.len();
        ReadCtxt {
            input: self.input,
            offset,
        }
    }
}

impl<'a> ReadCtxt<'a> {
    pub fn read_byte(&self) -> Option<(u8, ReadCtxt<'a>)> {
        if self.offset + 1 <= self.input.len() {
            let b = self.input[self.offset];
            Some((
                b,
                ReadCtxt {
                    offset: self.offset + 1,
                    ..*self
                },
            ))
        } else {
            None
        }
    }

    pub fn read_u16be(&self) -> Option<(u16, ReadCtxt<'a>)> {
        const SZ: usize = std::mem::size_of::<u16>();
        if self.offset + SZ <= self.input.len() {
            let raw = &self.input[self.offset..self.offset + SZ];
            Some((
                u16::from_be_bytes(raw.try_into().unwrap()),
                ReadCtxt {
                    offset: self.offset + SZ,
                    ..*self
                },
            ))
        } else {
            None
        }
    }

    pub fn read_u32be(&self) -> Option<(u32, ReadCtxt<'a>)> {
        const SZ: usize = std::mem::size_of::<u32>();
        if self.offset + SZ <= self.input.len() {
            let raw = &self.input[self.offset..self.offset + SZ];
            Some((
                u32::from_be_bytes(raw.try_into().unwrap()),
                ReadCtxt {
                    offset: self.offset + SZ,
                    ..*self
                },
            ))
        } else {
            None
        }
    }

    pub fn read_u64be(&self) -> Option<(u64, ReadCtxt<'a>)> {
        const SZ: usize = std::mem::size_of::<u64>();
        if self.offset + SZ <= self.input.len() {
            let raw = &self.input[self.offset..self.offset + SZ];
            Some((
                u64::from_be_bytes(raw.try_into().unwrap()),
                ReadCtxt {
                    offset: self.offset + SZ,
                    ..*self
                },
            ))
        } else {
            None
        }
    }
}
