#![cfg(test)]

use crate::*;
use doodle::prelude::*;

/// The number of `'a'`s each level read, outermost first.
fn pads(top: &test_down) -> Vec<usize> {
    let mut pads = Vec::new();
    let mut cur = top;
    loop {
        pads.push(cur.pad.len());
        match cur.rest.as_ref() {
            test_down_rest_S_next_rest::Z(_) => return pads,
            test_down_rest_S_next_rest::S(s) => cur = &s.next,
        }
    }
}

#[test]
fn test_recursive_args() {
    // down(0) reads no 'a's, down(1) one, down(2) two.
    let data = b"SaSaaZ";
    let mut p = Parser::new(data);
    let top = Decoder_test_down(&mut p).unwrap();
    assert_eq!(pads(&top), vec![0, 1, 2]);
}

#[test]
fn test_recursive_args_rejects_wrong_count() {
    // down(2) requires two 'a's but finds one.
    let data = b"SaSaZ";
    let mut p = Parser::new(data);
    assert!(Decoder_test_down(&mut p).is_err());
}
