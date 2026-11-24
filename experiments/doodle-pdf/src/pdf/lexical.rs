//! Bytes, whitespace, end-of-line, comments and tokens: the lexical part of DaeDaLus `PdfValue.ddl`.

use doodle::{
    BaseType, Expr, Format, FormatModule, FormatRef, ValueType, helper::*, prelude::ByteSet,
};

use super::combinators::{match_str, void};

/// Folds a sequence of ASCII decimal digits into the u64 value it spells out
pub(super) fn decimal_value(digits: Expr) -> Expr {
    left_fold(
        lambda_tuple(
            ["acc", "d"],
            add(
                mul(var("acc"), Expr::U64(10)),
                as_u64(sub(var("d"), Expr::U8(b'0'))),
            ),
        ),
        Expr::U64(0),
        ValueType::Base(BaseType::U64),
        digits,
    )
}

/// Daedalus `NatN len`: exactly `len` decimal digits, read as a u64
pub(super) fn read_nat(len: u32) -> Format {
    map(
        repeat_count(Expr::U32(len), Format::Byte(DIGIT)),
        lambda("ds", decimal_value(var("ds"))),
    )
}

pub(super) const ASCII_LF: u8 = b'\n';
pub(super) const ASCII_CR: u8 = b'\r';

const ASCII_TAB: u8 = b'\t';
const ASCII_FF: u8 = b'\x0c';
const ASCII_SPACE: u8 = b' ';

const __WS_MASK: u64 = 1u64 | 1 << ASCII_TAB | 1 << ASCII_FF | 1 << ASCII_SPACE;

/// Const ByteSet for daedalus `$simpleWS`
pub(super) const SIMPLE_WS: ByteSet = ByteSet::from_bits([__WS_MASK, 0, 0, 0]);

const _: () = {
    let simple_ws = ByteSet::from_bytes(&[b'\0', b'\t', 0x0C, b' ']);
    assert!(SIMPLE_WS.eq_set(&simple_ws));
};

/// Const ByteSet for daedalus Digit
pub(super) const DIGIT: ByteSet = ByteSet::from_bits([0b11_1111_1111 << b'0', 0, 0, 0]);

const _: () = {
    let digit = ByteSet::from_bytes(b"0123456789");
    assert!(DIGIT.eq_set(&digit));
};

pub(super) fn simple_eol(module: &mut FormatModule) -> FormatRef {
    module.define_format(
        "pdf.util.simple_eol",
        Format::UnionNondet(vec![
            void(is_bytes(&[ASCII_CR, ASCII_LF])),
            void(is_byte(ASCII_LF)),
        ]),
    )
}

pub(super) fn eol(module: &mut FormatModule, simple_eol: FormatRef) -> FormatRef {
    module.define_format(
        "pdf.util.eol",
        Format::UnionNondet(vec![simple_eol.call(), void(is_byte(ASCII_CR))]),
    )
}

pub(super) fn comment(module: &mut FormatModule, eol: FormatRef) -> FormatRef {
    let inline_char = Format::Byte(ByteSet::from([ASCII_LF, ASCII_CR]).complement());
    module.define_format(
        "pdf.util.comment",
        monad_seq(is_byte(b'%'), monad_seq(repeat(inline_char), eol.call())),
    )
}

pub(super) fn any_ws(module: &mut FormatModule, eol: FormatRef, comment: FormatRef) -> FormatRef {
    let any_ws = module.define_format(
        "pdf.util.any_ws",
        Format::UnionNondet(vec![
            void(byte_in(SIMPLE_WS)), // $simpleWS
            comment.call(),           // Comment
            eol.call(),               // EOL
        ]),
    );
    any_ws
}

pub(super) fn token(f: Format, any_ws: FormatRef) -> Format {
    chain(
        f,
        "tok",
        monad_seq(repeat(any_ws.call()), compute(var("tok"))),
    )
}

pub(super) fn kw(b: &[u8], any_ws: FormatRef) -> Format {
    token(match_str(b), any_ws)
}

pub(super) fn between(open: &[u8], close: &[u8], f: Format, any_ws: FormatRef) -> Format {
    monad_seq(
        kw(open, any_ws),
        chain(f, "val", monad_seq(kw(close, any_ws), compute(var("val")))),
    )
}

/// DaeDaLus `WhiteTillEOL`: simple whitespace, then an end-of-line
pub(super) fn white_till_eol(eol: FormatRef) -> Format {
    monad_seq(repeat(byte_in(SIMPLE_WS)), eol.call())
}
