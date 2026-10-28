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

/// expected size: 48
/// trait-orphaned: no decoder functions provided
#[derive(Debug, Clone)]
pub enum test_down_rest_S_next_rest { S(test_down_rest_S), Z(u8) }

/// expected size: 32
/// trait-unready: multiple (3) decoders exist (d#{0, 1, 2})
#[derive(Debug, Clone)]
pub struct test_down {
pad: Vec<u8>,
rest: Box<test_down_rest_S_next_rest>
}

/// expected size: 40
/// trait-orphaned: no decoder functions provided
#[derive(Debug, Clone)]
pub struct test_down_rest_S {
tag: u8,
next: test_down
}

/// d#0
fn Decoder_test_down(input: &mut Parser<'_>) -> Result<test_down, ParseError> {
Decoder1(input)
}

/// d#1
fn Decoder1(input: &mut Parser<'_>) -> Result<test_down, ParseError> {
Decoder2(input, 0u8)
}

/// d#2
fn Decoder2(input: &mut Parser<'_>, n: u8) -> Result<test_down, ParseError> {
let pad = {
let mut accum = Vec::new();
for _ in 0..n {
let next_elem = {
let b = input.read_byte()?;
if b == 97 {
b
} else {
return Err(ParseError::ExcludedBranch(13646096770106105413u64));
}
};
accum.push(next_elem)
};
accum
};
let rest = {
let tree_index = {
input.open_peek_context();
{
let ret = match input.read_byte()? {
90u8 => {
0
},

83u8 => {
1
},

_ => {
return Err(ParseError::ExcludedBranch(18270091135093349626u64));
}
};
input.close_peek_context()?;
ret
}
};
match tree_index {
0 => {
let inner = {
let b = input.read_byte()?;
if b == 90 {
b
} else {
return Err(ParseError::ExcludedBranch(2206609067086327257u64));
}
};
test_down_rest_S_next_rest::Z(inner)
},

1 => {
let inner = {
let tag = {
let b = input.read_byte()?;
if b == 83 {
b
} else {
return Err(ParseError::ExcludedBranch(11876854719037224982u64));
}
};
let next = (Decoder2(input, n + 1u8))?;
test_down_rest_S { tag, next }
};
test_down_rest_S_next_rest::S(inner)
},

_ => {
return Err(ParseError::ExcludedBranch(6185506036438099345u64));
}
}
};
PResult::Ok(test_down { pad, rest: Box::new(rest) })
}

