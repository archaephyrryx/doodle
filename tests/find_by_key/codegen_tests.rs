#![cfg(test)]

use crate::*;
use doodle::prelude::*;

#[test]
fn test_find_by_key() {
    // three (key, n) entries, sorted by key, with "ab" duplicated: owned keys, then borrowed keys
    // (captured without advancing, then read again as `_k`), then the borrowed queries
    let data = [
        b'a', b'b', 1, b'a', b'b', 7, b'c', b'd', 7, //
        b'a', b'b', 1, b'a', b'b', 2, b'c', b'd', 3, //
        b'a', b'b', b'a', b'c',
    ];
    let mut p = Parser::new(&data);
    let main = Decoder_test_main(&mut p).unwrap();
    let n = |e: &Option<test_owned>| e.as_ref().map(|e| e.n);
    let bn = |e: &Option<test_borrowed>| e.as_ref().map(|e| e.n);
    // byte-string keys: the leftmost, first or last of the duplicates
    assert_eq!(n(&main.owned_sorted), Some(1));
    assert_eq!(n(&main.owned_first), Some(1));
    assert_eq!(n(&main.owned_last), Some(7));
    assert_eq!(n(&main.owned_sorted_missing), None);
    assert_eq!(n(&main.owned_last_missing), None);
    assert_eq!(bn(&main.borrowed_sorted), Some(1));
    assert_eq!(bn(&main.borrowed_first), Some(1));
    assert_eq!(bn(&main.borrowed_last), Some(2));
    assert_eq!(bn(&main.borrowed_sorted_missing), None);
    assert_eq!(bn(&main.borrowed_last_missing), None);
    // integer keys (`n`, which is sorted too)
    let k = |e: &Option<test_owned>| e.as_ref().map(|e| e.k.clone());
    assert_eq!(k(&main.n_sorted), Some(b"ab".to_vec()));
    assert_eq!(k(&main.n_first), Some(b"ab".to_vec()));
    assert_eq!(k(&main.n_last), Some(b"cd".to_vec()));
}
