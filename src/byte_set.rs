use std::ops::{Range, RangeInclusive};
use std::{fmt, ops};

use serde::ser::{Serialize, SerializeSeq, SerializeStruct, Serializer};

pub mod pretty_print;

/// Compact, allocation-free set of `u8`s.
///
/// # Terminology
///
/// The public API speaks only of *bytes* (elements of the set, `0..=255`).
/// Internally, the set is a 256-bit bitmap stored as four *words* (`u64`s);
/// word `w` covers bytes `64*w .. 64*w + 64`, and byte `b` is *bit* `b % 64`
/// (counting from the LSB) of word `b / 64`. A *mask* is a `u64` with some
/// bits set. The only place this layout is exposed is [`ByteSet::from_bits`] /
/// [`ByteSet::to_bits`].
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct ByteSet {
    /// Each bit of the array represents a number in the range `0..=255`
    ///
    /// A given `0 <= n < 256` is represented by `bits[q] & (1 << m)` where `q := n / 64` and `m := n % 64`.
    bits: [u64; 4],
}

/// Helper function to compute the index of the least-significant set bit in a `u64`, returning `None` if the input is zero.
const fn min_set_bit(x: u64) -> Option<u8> {
    match x.trailing_zeros() {
        64 => None,
        i => Some(i as u8),
    }
}

/// Helper function to compute the index of the most-significant set bit in a `u64`, returning `None` if the input is zero.
const fn max_set_bit(x: u64) -> Option<u8> {
    match x.leading_zeros() {
        64 => None,
        i => Some((63 - i) as u8),
    }
}

/// Word index and single-bit mask that represent `byte` in a ByteSet
const fn locate(byte: u8) -> (usize, u64) {
    ((byte / 64) as usize, 1u64 << (byte % 64))
}

impl ByteSet {
    pub(crate) const NULL_RAW: [u64; 4] = [0; 4];
    pub(crate) const FULL_RAW: [u64; 4] = [u64::MAX; 4];

    /// Equivalent to [`ByteSet::empty`].
    pub const fn new() -> ByteSet {
        ByteSet::empty()
    }

    pub const fn from_bytes(bytes: &[u8]) -> ByteSet {
        let mut bs = ByteSet::empty();
        let mut i = 0;
        while i < bytes.len() {
            bs.insert(bytes[i]);
            i += 1;
        }
        bs
    }

    /// Constructs a ByteSet directly from its 256-bit representation: byte `B`
    /// is included iff bit `B % 64` (counting from the LSB) of `bits[B / 64]`
    /// is set. So `bits[0]` covers bytes `0..64`, and `bits[3]` covers `192..=255`.
    ///
    /// This is public and `const` so that ByteSet constants can be written
    /// (and emitted by codegen) without any runtime construction; the layout is
    /// therefore a stable contract between the generator and generated code.
    pub const fn from_bits(bits: [u64; 4]) -> ByteSet {
        ByteSet { bits }
    }

    /// Returns the 256-bit representation of this set, in the layout accepted by
    /// [`ByteSet::from_bits`] (of which this is the inverse).
    pub const fn to_bits(&self) -> [u64; 4] {
        self.bits
    }

    /// Constructs the union of `self` and `other`.
    pub const fn union(&self, other: &Self) -> Self {
        Self::from_bits([
            self.bits[0] | other.bits[0],
            self.bits[1] | other.bits[1],
            self.bits[2] | other.bits[2],
            self.bits[3] | other.bits[3],
        ])
    }

    pub const fn empty() -> ByteSet {
        ByteSet::from_bits(ByteSet::NULL_RAW)
    }

    /// Constructs the set containing only `byte`.
    pub const fn singleton(byte: u8) -> ByteSet {
        let mut words = [0; 4];
        let (word, mask) = locate(byte);
        words[word] = mask;
        ByteSet::from_bits(words)
    }

    pub const fn full() -> ByteSet {
        ByteSet::from_bits(ByteSet::FULL_RAW)
    }

    /// Iterates over the members of the set in ascending order.
    ///
    /// Note that this tests each of the 256 candidate bytes, regardless of how
    /// many are actually in the set.
    pub fn iter(&self) -> impl '_ + Iterator<Item = u8> {
        (0..=255).filter(|b| self.contains(*b))
    }

    /// Returns the smallest byte in the set, or `None` iff the set is empty.
    pub const fn min_elem(&self) -> Option<u8> {
        if let Some(i) = min_set_bit(self.bits[0]) {
            return Some(i);
        }
        if let Some(i) = min_set_bit(self.bits[1]) {
            return Some(0x40 + i);
        }
        if let Some(i) = min_set_bit(self.bits[2]) {
            return Some(0x80 + i);
        }
        if let Some(i) = min_set_bit(self.bits[3]) {
            return Some(0xc0 + i);
        }
        None
    }

    /// Returns the largest byte in the set, or `None` iff the set is empty.
    pub const fn max_elem(&self) -> Option<u8> {
        if let Some(i) = max_set_bit(self.bits[3]) {
            return Some(0xc0 + i);
        }
        if let Some(i) = max_set_bit(self.bits[2]) {
            return Some(0x80 + i);
        }
        if let Some(i) = max_set_bit(self.bits[1]) {
            return Some(0x40 + i);
        }
        if let Some(i) = max_set_bit(self.bits[0]) {
            return Some(i);
        }
        None
    }

    /// Returns the number of bytes in the set.
    ///
    /// The result is a `u32` because a full set has 256 members, which does not fit in a `u8`.
    pub const fn len(&self) -> u32 {
        self.bits[0].count_ones()
            + self.bits[1].count_ones()
            + self.bits[2].count_ones()
            + self.bits[3].count_ones()
    }

    pub const fn is_empty(&self) -> bool {
        (self.bits[0] | self.bits[1] | self.bits[2] | self.bits[3]) == 0
    }

    pub const fn is_full(&self) -> bool {
        (self.bits[0] & self.bits[1] & self.bits[2] & self.bits[3]) == u64::MAX
    }

    pub const fn eq_set(&self, other: &ByteSet) -> bool {
        self.bits[0] == other.bits[0]
            && self.bits[1] == other.bits[1]
            && self.bits[2] == other.bits[2]
            && self.bits[3] == other.bits[3]
    }

    pub const fn insert(&mut self, byte: u8) {
        let (word, mask) = locate(byte);
        self.bits[word] |= mask;
    }

    pub const fn remove(&mut self, byte: u8) {
        let (word, mask) = locate(byte);
        self.bits[word] &= !mask;
    }

    pub const fn contains(&self, byte: u8) -> bool {
        let (word, mask) = locate(byte);
        self.bits[word] & mask != 0
    }

    pub const fn complement(&self) -> ByteSet {
        ByteSet::from_bits([!self.bits[0], !self.bits[1], !self.bits[2], !self.bits[3]])
    }

    /// Constructs the set of bytes in `self` but not in `other`.
    pub const fn difference(&self, other: &ByteSet) -> ByteSet {
        ByteSet::from_bits([
            self.bits[0] & !other.bits[0],
            self.bits[1] & !other.bits[1],
            self.bits[2] & !other.bits[2],
            self.bits[3] & !other.bits[3],
        ])
    }

    pub const fn intersection(&self, other: &ByteSet) -> ByteSet {
        ByteSet::from_bits([
            self.bits[0] & other.bits[0],
            self.bits[1] & other.bits[1],
            self.bits[2] & other.bits[2],
            self.bits[3] & other.bits[3],
        ])
    }

    pub const fn is_disjoint(&self, other: &ByteSet) -> bool {
        ByteSet::intersection(self, other).is_empty()
    }
}

impl<const LEN: usize> From<[u8; LEN]> for ByteSet {
    fn from(bytes: [u8; LEN]) -> ByteSet {
        let mut bs = ByteSet::new();
        for b in bytes {
            bs.insert(b);
        }
        bs
    }
}

impl<'a> From<&'a [u8]> for ByteSet {
    fn from(bytes: &'a [u8]) -> ByteSet {
        let mut bs = ByteSet::new();
        for b in bytes {
            bs.insert(*b);
        }
        bs
    }
}

impl From<Range<u8>> for ByteSet {
    fn from(value: Range<u8>) -> Self {
        if value.end <= value.start {
            ByteSet::empty()
        } else {
            ByteSet::from(value.start..=value.end - 1)
        }
    }
}

impl From<RangeInclusive<u8>> for ByteSet {
    fn from(value: RangeInclusive<u8>) -> Self {
        let lo = value.start();
        let hi = value.end();
        // optimize for singletons and empty-sets
        match lo.cmp(hi) {
            std::cmp::Ordering::Less => (),
            std::cmp::Ordering::Equal => return ByteSet::from([*lo]),
            std::cmp::Ordering::Greater => return ByteSet::empty(),
        }
        let start_ix = *lo / 64;
        let end_ix = *hi / 64;
        if start_ix == end_ix {
            // because the values are contiguous, if they are within the same word
            // the mask is just the bits from `lo % 64` up to `hi % 64` (inclusive)
            let mask = (u64::MAX << (*lo % 64)) & (u64::MAX >> (63 - *hi % 64));
            let mut bits = [0; 4];
            bits[start_ix as usize] = mask;
            ByteSet { bits }
        } else {
            // Fall-back to FromIter implementation, which is less efficient in general
            value.collect::<ByteSet>()
        }
    }
}

impl FromIterator<u8> for ByteSet {
    fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> Self {
        let mut bs = ByteSet::empty();
        for byte in iter {
            bs.insert(byte);
        }
        bs
    }
}

/// Sets with fewer than 128 members are shown as `{b0, b1, ...}`; sets with
/// 128 or more are shown as `!{...}`, listing the complement instead.
impl fmt::Debug for ByteSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.len() < 128 {
            f.debug_set().entries(self.iter()).finish()
        } else {
            f.write_str("!")?;
            f.debug_set().entries((!self).iter()).finish()
        }
    }
}

impl ops::Not for &ByteSet {
    type Output = ByteSet;

    fn not(self) -> ByteSet {
        self.complement()
    }
}

impl ops::Not for ByteSet {
    type Output = ByteSet;

    fn not(self) -> ByteSet {
        !&self
    }
}

/// Serializes as a struct `{ tag, data }`, where `data` is an ascending sequence of bytes.
/// Sets with fewer than 128 members use `tag: "includes"` and list their members;
/// sets with 128 or more use `tag: "excludes"` and list the bytes *not* in the set.
impl Serialize for ByteSet {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        struct All(ByteSet);

        impl Serialize for All {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let len = usize::try_from(self.0.len()).unwrap();
                let mut seq = serializer.serialize_seq(Some(len))?;
                for b in self.0.iter() {
                    seq.serialize_element(&b)?;
                }
                seq.end()
            }
        }

        let mut byte_set = serializer.serialize_struct("ByteSet", 2)?;
        if self.len() < 128 {
            byte_set.serialize_field("tag", "includes")?;
            byte_set.serialize_field("data", &All(*self))?;
        } else {
            byte_set.serialize_field("tag", "excludes")?;
            byte_set.serialize_field("data", &All(!*self))?;
        }
        byte_set.end()
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::sample;

    use super::*;

    fn any_byte_set() -> impl Strategy<Value = ByteSet> {
        Strategy::prop_union(
            sample::select(vec![ByteSet::empty(), ByteSet::full()]).boxed(),
            any::<[u64; 4]>().prop_map(ByteSet::from_bits).boxed(),
        )
    }

    mod is_empty {
        use super::*;

        #[test]
        fn test_empty() {
            assert!(ByteSet::empty().is_empty());
        }

        #[test]
        fn test_full() {
            assert!(!ByteSet::full().is_empty());
        }

        proptest! {
            #[test]
            fn test_any(b in any::<u8>()) {
                assert!(!ByteSet::from([b]).is_empty())
            }
        }
    }

    mod contains {
        use super::*;

        proptest! {
            #[test]
            fn test_any(b in any::<u8>()) {
                assert!(ByteSet::from([b]).contains(b));
            }

            #[test]
            fn test_insert(b in any::<u8>(), mut bs in any_byte_set()) {
                bs.insert(b);
                assert!(bs.contains(b));
            }

            #[test]
            fn test_remove(b in any::<u8>(), mut bs in any_byte_set()) {
                bs.remove(b);
                assert!(!bs.contains(b));
            }
        }
    }

    mod is_disjoint {
        use super::*;

        proptest! {
            #[test]
            fn test_complement(bs in any_byte_set()) {
                assert!(ByteSet::is_disjoint(&bs, &bs.complement()));
            }

            #[test]
            fn test_difference_left(bs0 in any_byte_set(), bs1 in any_byte_set()) {
                assert!(ByteSet::is_disjoint(&ByteSet::difference(&bs0, &bs1), &bs1));
            }

            #[test]
            fn test_difference_right(bs0 in any_byte_set(), bs1 in any_byte_set()) {
                assert!(ByteSet::is_disjoint(&bs0, &ByteSet::difference(&bs1, &bs0)));
            }
        }
    }

    mod min_max_elem {
        use super::*;

        #[test]
        fn test_empty() {
            assert_eq!(ByteSet::empty().min_elem(), None);
            assert_eq!(ByteSet::empty().max_elem(), None);
        }

        proptest! {
            #[test]
            fn test_any(bs in any_byte_set()) {
                prop_assert_eq!(bs.min_elem(), bs.iter().min());
                prop_assert_eq!(bs.max_elem(), bs.iter().max());
            }

            #[test]
            fn test_singleton(b in any::<u8>()) {
                prop_assert_eq!(ByteSet::singleton(b).min_elem(), Some(b));
                prop_assert_eq!(ByteSet::singleton(b).max_elem(), Some(b));
            }
        }
    }

    #[test]
    fn test_debug_below_128() {
        assert_eq!(format!("{:?}", ByteSet::from([32, 1])), "{1, 32}");
    }

    #[test]
    fn test_debug_above_128() {
        assert_eq!(format!("{:?}", !ByteSet::from([32, 1])), "!{1, 32}");
    }

    mod same_result {
        use super::*;

        prop_compose! {
        fn range_in_quadrant(q: u8)
                            (start in (q*64)..=(q*64)+63)
                            (start in Just(start), end in start..=(q*64)+63) -> (u8, u8) {
                                (start, end)
                            }
                        }
        prop_compose! {
            fn range_any()(start in 0u8..=255)(start in Just(start), end in start..=255) -> (u8, u8) {
                (start, end)
            }
        }

        fn range_bounds() -> impl Strategy<Value = (u8, u8)> {
            prop_oneof![(0u8..=3).prop_flat_map(range_in_quadrant), range_any(),]
        }

        proptest! {
            #[test]
            fn single_quadrant((start, end) in range_bounds()) {
                let bs_range_inc = ByteSet::from(start..=end);
                // NOTE - hack to avoid overflowing integer bounds when end == 255
                let bs_range_exc = if end < 255 {
                    ByteSet::from(start..end+1)
                } else {
                    bs_range_inc
                };
                let bs_iter = (start..=end).collect::<ByteSet>();
                let bs_manual = {
                    let mut tmp = ByteSet::empty();
                    for i in start..=end {
                        tmp.insert(i);
                    }
                    tmp
                };
                prop_assert_eq!(bs_range_inc, bs_range_exc);
                prop_assert_eq!(bs_range_inc, bs_iter);
                prop_assert_eq!(bs_range_inc, bs_manual);
            }
        }
    }
}
