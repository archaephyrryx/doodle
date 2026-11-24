//! Integration tests to ensure our `doodle::prelude` definitions are sound
//! and behave as expected.

use doodle::prelude;
use proptest::prelude::*;

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_succ_u8_max() {
    let _ = prelude::succ(u8::MAX);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_succ_u16_max() {
    let _ = prelude::succ(u16::MAX);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_succ_u32_max() {
    let _ = prelude::succ(u32::MAX);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_succ_u64_max() {
    let _ = prelude::succ(u64::MAX);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_pred_u8_zero() {
    let _ = prelude::pred(0u8);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_pred_u16_zero() {
    let _ = prelude::pred(0u16);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_pred_u32_zero() {
    let _ = prelude::pred(0u32);
}

#[test]
#[cfg_attr(debug_assertions, should_panic)]
fn test_pred_u64_zero() {
    let _ = prelude::pred(0u64);
}

proptest! {
    #[test]
    fn test_succ_u8_nonmax(x in 0..u8::MAX) {
        prop_assert_eq!(prelude::succ(x), x + 1);
    }

    #[test]
    fn test_succ_u16_nonmax(x in 0..u16::MAX) {
        prop_assert_eq!(prelude::succ(x), x + 1);
    }

    #[test]
    fn test_succ_u32_nonmax(x in 0..u32::MAX) {
        prop_assert_eq!(prelude::succ(x), x + 1);
    }

    #[test]
    fn test_succ_u64_nonmax(x in 0..u64::MAX) {
        prop_assert_eq!(prelude::succ(x), x + 1);
    }

    #[test]
    fn test_pred_u8_nonzero(x in 1..=u8::MAX) {
        prop_assert_eq!(prelude::pred(x), x - 1);
    }

    #[test]
    fn test_pred_u16_nonzero(x in 1..=u16::MAX) {
        prop_assert_eq!(prelude::pred(x), x - 1);
    }

    #[test]
    fn test_pred_u32_nonzero(x in 1..=u32::MAX) {
        prop_assert_eq!(prelude::pred(x), x - 1);
    }

    #[test]
    fn test_pred_u64_nonzero(x in 1..=u64::MAX) {
        prop_assert_eq!(prelude::pred(x), x - 1);
    }
}

/// `find_by_key_*` and `find_by_bytes_key_*` return the element each mode specifies when keys are
/// duplicated: the first for `sorted` (leftmost) and `unsorted`/`first`, the last for `last`.
#[test]
fn test_find_by_key_duplicates() {
    let entries = [(1u8, 'a'), (2, 'b'), (2, 'c'), (2, 'd'), (3, 'e')];
    let key = |e: &(u8, char)| e.0;
    assert_eq!(
        prelude::find_by_key_sorted(key, 2, &entries),
        Some(&(2, 'b'))
    );
    assert_eq!(
        prelude::find_by_key_first(key, 2, &entries),
        Some(&(2, 'b'))
    );
    assert_eq!(prelude::find_by_key_last(key, 2, &entries), Some(&(2, 'd')));
    for q in [0, 4] {
        assert_eq!(prelude::find_by_key_sorted(key, q, &entries), None);
        assert_eq!(prelude::find_by_key_last(key, q, &entries), None);
    }
    assert_eq!(prelude::find_by_key_sorted(key, 2, &[]), None);
}

#[test]
fn test_find_by_bytes_key() {
    let entries: [(&[u8], u8); 6] = [
        (b"", 0),
        (b"a", 1),
        (b"ab", 2),
        (b"ab", 3),
        (b"b", 4),
        (b"ba", 5),
    ];
    fn key<'b>(e: &'b (&[u8], u8)) -> &'b [u8] {
        e.0
    }
    assert_eq!(
        prelude::find_by_bytes_key_sorted(key, b"ab", &entries),
        Some(&entries[2])
    );
    assert_eq!(
        prelude::find_by_bytes_key_first(key, b"ab", &entries),
        Some(&entries[2])
    );
    assert_eq!(
        prelude::find_by_bytes_key_last(key, b"ab", &entries),
        Some(&entries[3])
    );
    assert_eq!(
        prelude::find_by_bytes_key_sorted(key, b"", &entries),
        Some(&entries[0])
    );
    assert_eq!(
        prelude::find_by_bytes_key_sorted(key, b"ba", &entries),
        Some(&entries[5])
    );
    for q in [&b"aa"[..], b"abc", b"c"] {
        assert_eq!(prelude::find_by_bytes_key_sorted(key, q, &entries), None);
        assert_eq!(prelude::find_by_bytes_key_first(key, q, &entries), None);
        assert_eq!(prelude::find_by_bytes_key_last(key, q, &entries), None);
    }
}

proptest! {
    /// On a sorted sequence, the binary search agrees with a linear search for the first match.
    #[test]
    fn test_find_by_key_sorted_is_leftmost(mut keys in proptest::collection::vec(0u8..8, 0..24), q in 0u8..9) {
        keys.sort();
        let entries: Vec<(u8, usize)> = keys.iter().copied().zip(0..).collect();
        let key = |e: &(u8, usize)| e.0;
        prop_assert_eq!(
            prelude::find_by_key_sorted(key, q, &entries),
            prelude::find_by_key_first(key, q, &entries)
        );
        let bytes: Vec<(Vec<u8>, usize)> = keys.iter().map(|&k| vec![b'a'; k as usize]).zip(0..).collect();
        fn bkey(e: &(Vec<u8>, usize)) -> &[u8] {
            e.0.as_slice()
        }
        let bq = vec![b'a'; q as usize];
        prop_assert_eq!(
            prelude::find_by_bytes_key_sorted(bkey, &bq, &bytes),
            prelude::find_by_bytes_key_first(bkey, &bq, &bytes)
        );
    }
}
