#![allow(unused_imports)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code)]
#![allow(unsafe_op_in_unsafe_fn)]
#![cfg_attr(rustfmt, rustfmt::skip)]

mod codegen_tests;
pub mod api_helper;

use doodle::prelude::*;
use doodle::try_sub;

impl CommonObject for test_owned {
type Args<'x> = ();

type Output<'x> = test_owned;

fn parse<'input>(p: &mut Parser<'input>, _: ()) -> Result<Self::Output<'input>, ParseError> {
Decoder_test_owned(p)
}
}

/// expected size: 32
/// trait-ready: unique decoder function (d#2)
#[derive(Debug, Clone)]
pub struct test_owned {
k: Vec<u8>,
n: u8
}

impl<'a> CommonObject for test_borrowed<'a> {
type Args<'x> = ();

type Output<'x> = test_borrowed<'x>;

fn parse<'input>(p: &mut Parser<'input>, _: ()) -> Result<Self::Output<'input>, ParseError> {
Decoder_test_borrowed(p)
}
}

/// expected size: 40
/// trait-ready: unique decoder function (d#3)
#[derive(Debug, Clone)]
pub struct test_borrowed<'input> {
k: &'input [u8],
_k: Vec<u8>,
n: u8
}

/// expected size: 568
/// trait-unready: multiple (2) decoders exist (d#{0, 1})
#[derive(Debug, Clone)]
pub struct test_main<'input> {
owned: Vec<test_owned>,
borrowed: Vec<test_borrowed<'input>>,
q_hit: &'input [u8],
_q_hit: Vec<u8>,
q_miss: &'input [u8],
_q_miss: Vec<u8>,
owned_sorted: Option<test_owned>,
owned_first: Option<test_owned>,
owned_last: Option<test_owned>,
owned_sorted_missing: Option<test_owned>,
owned_last_missing: Option<test_owned>,
borrowed_sorted: Option<test_borrowed<'input>>,
borrowed_first: Option<test_borrowed<'input>>,
borrowed_last: Option<test_borrowed<'input>>,
borrowed_sorted_missing: Option<test_borrowed<'input>>,
borrowed_last_missing: Option<test_borrowed<'input>>,
n_sorted: Option<test_owned>,
n_first: Option<test_owned>,
n_last: Option<test_owned>
}

/// d#0
fn Decoder_test_main<'input>(input: &mut Parser<'input>) -> Result<test_main<'input>, ParseError> {
Decoder1(input)
}

/// d#1
fn Decoder1<'input>(input: &mut Parser<'input>) -> Result<test_main<'input>, ParseError> {
let owned = {
let mut accum = Vec::new();
for _ in 0..3u8 {
let next_elem = (Decoder_test_owned(input))?;
accum.push(next_elem)
};
accum
};
let borrowed = {
let mut accum = Vec::new();
for _ in 0..3u8 {
let next_elem = (Decoder_test_borrowed(input))?;
accum.push(next_elem)
};
accum
};
let q_hit = {
let here_view = input.view();
here_view.read_len(2u8 as usize)
};
let _q_hit = {
let mut accum = Vec::new();
for _ in 0..2u8 {
let next_elem = input.read_byte()?;
accum.push(next_elem)
};
accum
};
let q_miss = {
let here_view = input.view();
here_view.read_len(2u8 as usize)
};
let _q_miss = {
let mut accum = Vec::new();
for _ in 0..2u8 {
let next_elem = input.read_byte()?;
accum.push(next_elem)
};
accum
};
let owned_sorted = (find_by_bytes_key_sorted(|elem: &test_owned| slice_all(&elem.k), slice_all(&[97u8, 98u8].to_vec()), slice_all(&owned))).cloned();
let owned_first = (find_by_bytes_key_first(|elem: &test_owned| slice_all(&elem.k), slice_all(&[97u8, 98u8].to_vec()), slice_all(&owned))).cloned();
let owned_last = (find_by_bytes_key_last(|elem: &test_owned| slice_all(&elem.k), slice_all(&[97u8, 98u8].to_vec()), slice_all(&owned))).cloned();
let owned_sorted_missing = (find_by_bytes_key_sorted(|elem: &test_owned| slice_all(&elem.k), slice_all(&[97u8, 99u8].to_vec()), slice_all(&owned))).cloned();
let owned_last_missing = (find_by_bytes_key_last(|elem: &test_owned| slice_all(&elem.k), slice_all(&[97u8, 99u8].to_vec()), slice_all(&owned))).cloned();
let borrowed_sorted = (find_by_bytes_key_sorted(|elem: &test_borrowed<'input>| slice_all(&elem.k), slice_all(&q_hit), slice_all(&borrowed))).cloned();
let borrowed_first = (find_by_bytes_key_first(|elem: &test_borrowed<'input>| slice_all(&elem.k), slice_all(&q_hit), slice_all(&borrowed))).cloned();
let borrowed_last = (find_by_bytes_key_last(|elem: &test_borrowed<'input>| slice_all(&elem.k), slice_all(&q_hit), slice_all(&borrowed))).cloned();
let borrowed_sorted_missing = (find_by_bytes_key_sorted(|elem: &test_borrowed<'input>| slice_all(&elem.k), slice_all(&q_miss), slice_all(&borrowed))).cloned();
let borrowed_last_missing = (find_by_bytes_key_last(|elem: &test_borrowed<'input>| slice_all(&elem.k), slice_all(&q_miss), slice_all(&borrowed))).cloned();
let n_sorted = (find_by_key_sorted(|elem: &test_owned| elem.n, 7u8, slice_all(&owned))).cloned();
let n_first = (find_by_key_first(|elem: &test_owned| elem.n, 7u8, slice_all(&owned))).cloned();
let n_last = (find_by_key_last(|elem: &test_owned| elem.n, 7u8, slice_all(&owned))).cloned();
PResult::Ok(test_main { owned, borrowed, q_hit, _q_hit, q_miss, _q_miss, owned_sorted, owned_first, owned_last, owned_sorted_missing, owned_last_missing, borrowed_sorted, borrowed_first, borrowed_last, borrowed_sorted_missing, borrowed_last_missing, n_sorted, n_first, n_last })
}

/// d#2
fn Decoder_test_owned(input: &mut Parser<'_>) -> Result<test_owned, ParseError> {
let k = {
let mut accum = Vec::new();
for _ in 0..2u8 {
let next_elem = input.read_byte()?;
accum.push(next_elem)
};
accum
};
let n = input.read_byte()?;
PResult::Ok(test_owned { k, n })
}

/// d#3
fn Decoder_test_borrowed<'input>(input: &mut Parser<'input>) -> Result<test_borrowed<'input>, ParseError> {
let k = {
let here_view = input.view();
here_view.read_len(2u8 as usize)
};
let _k = {
let mut accum = Vec::new();
for _ in 0..2u8 {
let next_elem = input.read_byte()?;
accum.push(next_elem)
};
accum
};
let n = input.read_byte()?;
PResult::Ok(test_borrowed { k, _k, n })
}
