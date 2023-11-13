struct Sparse<T> {
    value: T,         // the actual value being stored
    ix: usize,        // the logical index of the value if all holes were expanded
    trail_len: usize, // how many indices following the current one represent a hole in the store
}

impl<T> Sparse<T> {
    /// Returns the relative ordering of a given concrete index to the logical range of indices encompassed
    /// by a [`Sparse<_>`].
    ///
    /// If the index is fully out of the bounds of the current `Sparse<_>`, returns the natural ordering
    /// of `value` to relative `self.ix`.
    ///
    /// Otherwise, returns `Equal`, indicating either a precise match on `self.ix` or that `index` falls within
    /// the trailing holes encompassed by `self.`
    pub fn range_cmp(&self, value: usize) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        match self.ix.cmp(&value) {
            Greater => Greater,
            Equal => Equal,
            Less => match (self.ix + self.trail_len).cmp(&value) {
                Less => Less,
                _ => Equal,
            },
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = Option<&T>> {
        std::iter::once(Some(&self.value)).chain(std::iter::repeat(None).take(self.trail_len))
    }
}

/// Specialized structure for storing values of Option<T> when Some is rare
pub struct SparseVec<T> {
    sparses: Vec<Sparse<T>>, // backing storage containing alternating Hits and Holes
    v_len: usize,            // effective length of the Vec<Option<T>> if expanded
    leads: usize,            // number of leading None-elements
}

impl<T> SparseVec<T> {
    pub const fn new() -> Self {
        Self {
            sparses: Vec::new(),
            v_len: 0,
            leads: 0,
        }
    }

    pub fn push(&mut self, value: Option<T>) {
        match value {
            Some(value) => {
                let ix = self.v_len;
                let trail_len = 0;
                self.sparses.push(Sparse {
                    value,
                    ix,
                    trail_len,
                });
                self.v_len += 1;
            }
            None => match self.sparses.last_mut() {
                None => {
                    debug_assert_eq!(
                        self.v_len, self.leads,
                        "No elements, but length {} != leads {}",
                        self.v_len, self.leads
                    );
                    self.v_len += 1;
                    self.leads += 1;
                }
                Some(ref mut last) => {
                    last.trail_len += 1;
                    self.v_len += 1;
                }
            },
        }
    }

    pub fn len(&self) -> usize {
        self.v_len
    }

    pub fn checked_len(&self) -> usize {
        self.sparses.iter().fold(self.leads, |acc, sp| {
            debug_assert_eq!(acc, sp.ix);
            acc + 1 + sp.trail_len
        })
    }

    pub fn is_empty(&self) -> bool {
        let empty = self.leads == 0 && self.sparses.is_empty();
        if empty {
            debug_assert_eq!(self.v_len, 0, "empty, but v_len = {} != 0", self.v_len)
        }
        empty
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.sparses.is_empty() {
            if self.leads > 0 {
                self.leads -= 1;
                self.v_len -= 1;
                return None;
            } else {
                panic!("cannot pop from empty SparseVec");
            }
        }
        let last = self.sparses.last_mut().expect("empty store ruled out");
        let trailing = last.trail_len;
        if trailing == 0 {
            self.v_len -= 1;
            Some(self.sparses.pop().expect("already peeked").value)
        } else {
            last.trail_len -= 1;
            self.v_len -= 1;
            None
        }
    }

    /// Returns the store-index of the Sparse that logically contains the given index.
    ///
    /// If the index is in range but before the first sparse, returns `Err(true)``.
    /// IF the index is out of range, returns `Err(false)`.
    fn spanning_index(&self, index: usize) -> Result<usize, bool> {
        if index < self.leads {
            Err(true)
        } else if index >= self.v_len {
            Err(false)
        } else {
            match self.sparses.binary_search_by(|sp| sp.range_cmp(index)) {
                Ok(sp_ix) => Ok(sp_ix),
                Err(_) => unreachable!("sparses always form a total cover over the index-space"),
            }
        }
    }

    pub fn sparse_index(&self, index: usize) -> Option<&T> {
        match self.spanning_index(index) {
            Ok(sp_ix) => {
                let sp = &self.sparses[sp_ix];
                (sp.ix == index).then(|| &sp.value)
            }
            Err(true) => None,
            Err(false) => panic!("out of range index into SparseVec"),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = Option<&T>> {
        std::iter::repeat(None)
            .take(self.leads)
            .chain(self.sparses.iter().flat_map(|sp| sp.iter()))
    }

    pub fn extend(&mut self, other: Self) {}

    pub fn truncate(&mut self, len: usize) {
        if self.v_len <= len {
            return;
        }
        if self.leads >= len {
            self.sparses.clear();
            self.leads = len;
            self.v_len = len;
        } else {
            let Ok(last_sp_ix) = self.spanning_index(len - 1) else {
                panic!("all edge cases are ruled out")
            };
            // Non-edge-case: we have to remove any sparses following the last one we will include
            if last_sp_ix < self.sparses.len() - 1 {
                self.sparses.drain(last_sp_ix + 1..);
            }
            let last_sp = &mut self.sparses[last_sp_ix];
            let ix = last_sp.ix;
            last_sp.trail_len = len - (ix + 1);
            self.v_len = len;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn opt_vec_strat<T>(max_len: usize) -> impl Strategy<Value = Vec<Option<T>>>
    where
        Option<T>: Arbitrary,
    {
        prop::collection::vec(any::<Option<T>>(), 0..=max_len)
    }

    fn vec_and_truncate<T>(max_len: usize) -> impl Strategy<Value = (Vec<Option<T>>, usize)>
    where
        Option<T>: Arbitrary,
        T: Clone,
    {
        opt_vec_strat(max_len).prop_flat_map(|v| {
            let l = v.len();
            (Just(v), 0..2 * l + 1)
        })
    }

    proptest! {
        #[test]
        fn iter_roundtrip(src: Vec<Option<bool>>) {
            let mut sv = SparseVec::new();
            for elt in src.iter() {
                sv.push(elt.clone());
            }
            prop_assert_eq!(src.len(), sv.len());
            let tgt = sv.iter().map(|x| x.cloned()).collect::<Vec<Option<bool>>>();
            prop_assert_eq!(&src, &tgt);
        }

        #[test]
        fn truncate_identical((mut src, len) in vec_and_truncate::<bool>(20)) {
            let mut sv = SparseVec::new();
            for elt in src.iter() {
                sv.push(elt.clone());
            };
            sv.truncate(len);
            prop_assert!(sv.len() == len || len > src.len());
            let tgt = sv.iter().map(|x| x.cloned()).collect::<Vec<Option<bool>>>();
            src.truncate(len);
            prop_assert_eq!(&src, &tgt);
        }
    }
}
