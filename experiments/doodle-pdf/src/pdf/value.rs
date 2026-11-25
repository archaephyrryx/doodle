//! PDF values (numbers, strings, names, arrays, dictionaries): DaeDaLus `PdfValue.ddl`, with the
//! dictionary lookups that `PdfDecl.ddl` builds on them.

use std::ops::RangeInclusive;

use doodle::{
    BaseType, Expr, Format, FormatModule, FormatRef, Label, Pattern, ValueType, helper::*,
    prelude::ByteSet,
};
use doodle_numexpr_macro::numexpr;

use super::PdfModule;
use super::combinators::{interpret, record_daedalus, void};
use super::lexical::{DIGIT, between, kw, token};

/// Parses a single case-insensitive ASCII hex-digit into the numeric value of that digit: '0' goes to `0u8`, 'F' and 'f' go to `15u8`
fn hex_val() -> Format {
    const HEX09: RangeInclusive<u8> = b'0'..=b'9';
    const HEX_MAJ: RangeInclusive<u8> = b'A'..=b'F';
    const HEX_MIN: RangeInclusive<u8> = b'a'..=b'f';

    union([
        map(byte_in(HEX09), lambda("b", sub(var("b"), Expr::U8(b'0')))),
        map(
            byte_in(HEX_MIN),
            lambda("b", sub(var("b"), Expr::U8(b'a' - 10))),
        ),
        map(
            byte_in(HEX_MAJ),
            lambda("b", sub(var("b"), Expr::U8(b'A' - 10))),
        ),
    ])
}

/// Reads `len` bytes of hex-digits and returns the u32-value with that hexstring-representation
fn hex_num_u32(len: usize) -> Format {
    let raw = repeat_count(Expr::U32(len as u32), hex_val());
    map(
        raw,
        lambda(
            "raw",
            left_fold(
                lambda_tuple(
                    ["acc", "b"],
                    add(as_u32(var("b")), mul(var("acc"), Expr::U32(16))),
                ),
                Expr::U32(0),
                ValueType::Base(BaseType::U32),
                var("raw"),
            ),
        ),
    )
}

fn octal_val() -> Format {
    const OCTAL: RangeInclusive<u8> = b'0'..=b'7';

    map(byte_in(OCTAL), lambda("b", sub(var("b"), Expr::U8(b'0'))))
}

/// Parses up to three ASCII octal digits (greedily) and interprets them as a u8-typed numeric value with that octal representation.
fn octal_num_u8() -> Format {
    let raw = union([
        repeat_count(Expr::U8(3), octal_val()),
        excluding(
            repeat_count(Expr::U8(3), byte_in(b'0'..=b'7')),
            repeat_count(Expr::U8(2), octal_val()),
        ),
        excluding(
            repeat_count(Expr::U8(2), byte_in(b'0'..=b'7')),
            seq([octal_val()]),
        ),
    ]);

    map(
        raw,
        lambda(
            "raw",
            left_fold(
                lambda_tuple(["acc", "b"], as_u8(numeric(numexpr!("acc" * 8 + "b")))),
                Expr::U8(0),
                ValueType::Base(BaseType::U8),
                var("raw"),
            ),
        ),
    )
}

/// Daedalus `HexString`: hex digits between `<` and `>`, with whitespace allowed between
/// digits, read pairwise into bytes; an odd final digit is read as if followed by `0`.
fn v_hex_string(any_ws: FormatRef) -> Format {
    // The digits are parsed as a flat sequence of nibbles and paired up afterwards. Parsing
    // pairs directly would need unbounded lookahead (past whitespace and comments) to decide
    // whether a digit starts another pair or is the odd final one.
    let nibbles = repeat(token(hex_val(), any_ws));

    // Fold state: (bytes so far, whether a high nibble is pending, the pending high nibble)
    let acc_type = ValueType::Tuple(vec![
        ValueType::Seq(Box::new(ValueType::Base(BaseType::U8))),
        ValueType::Base(BaseType::Bool),
        ValueType::Base(BaseType::U8),
    ]);
    let bytes = || tuple_proj(var("acc"), 0);
    let has_hi = || tuple_proj(var("acc"), 1);
    let hi = || tuple_proj(var("acc"), 2);
    let step = lambda_tuple(
        ["acc", "nib"],
        expr_if_else(
            has_hi(),
            Expr::Tuple(vec![
                append(
                    bytes(),
                    Expr::Seq(vec![add(mul(hi(), Expr::U8(16)), var("nib"))]),
                ),
                Expr::Bool(false),
                Expr::U8(0),
            ]),
            Expr::Tuple(vec![bytes(), Expr::Bool(true), var("nib")]),
        ),
    );
    let init = Expr::Tuple(vec![Expr::Seq(vec![]), Expr::Bool(false), Expr::U8(0)]);
    let finish = expr_if_else(
        has_hi(),
        append(bytes(), Expr::Seq(vec![mul(hi(), Expr::U8(16))])),
        bytes(),
    );

    between(
        b"<",
        b">",
        map(
            map(
                nibbles,
                lambda("nibs", left_fold(step, init, acc_type, var("nibs"))),
            ),
            lambda("acc", finish),
        ),
        any_ws,
    )
}

/// Parses `digits` and then requires that no digit follows, so a run of digits is read as one token.
fn greedy_digits(digits: Format) -> Format {
    chain(
        digits,
        "ds",
        monad_seq(
            Format::PeekNot(Box::new(Format::Byte(DIGIT))),
            compute(var("ds")),
        ),
    )
}

pub(super) fn natural(module: &mut FormatModule) -> FormatRef {
    module.define_format(
        "pdf.util.natural",
        greedy_digits(repeat1(Format::Byte(DIGIT))),
    )
}

// TODO: add support to allow de-stringification of numbers
pub(super) fn number(pm: &mut PdfModule<'_>) -> FormatRef {
    let natural = pm.natural();
    let module = pm.module();
    let unsigned_lead_digits = chain(
        natural.call(),
        "n",
        Format::UnionNondet(vec![
            chain(
                cons(is_byte(b'.'), greedy_digits(repeat(Format::Byte(DIGIT)))),
                "frac",
                compute(append(var("n"), var("frac"))),
            ),
            compute(var("n")),
        ]),
    );

    // TODO - add support to allow de-stringification of numbers
    let unsigned_number = module.define_format(
        "pdf.util.unsigned_number",
        Format::UnionNondet(vec![
            unsigned_lead_digits,
            cons(is_byte(b'.'), greedy_digits(repeat1(Format::Byte(DIGIT)))),
        ]),
    );

    module.define_format(
        "pdf.util.number",
        union([
            monad_seq(
                is_byte(b'-'),
                map(
                    unsigned_number.call(),
                    lambda(
                        "digits",
                        concat(Expr::Seq(vec![
                            Expr::Seq(vec![Expr::U8(b'-')]),
                            var("digits"),
                        ])),
                    ),
                ),
            ),
            monad_seq(optional(is_byte(b'+')), unsigned_number.call()),
        ]),
    )
}

/// DaeDaLus `NumberAsNat`, applied to a `pdf.util.number` token (as a `Seq(u8)`): the value of
/// the token as a `u64`, or `None` if it is not a whole number in `0..=u64::MAX`.
///
/// DaeDaLus `NumberAsNat` accepts a `Number` with `num >= 0 && exp == 0`. At the byte level
/// (where `pdf.util.number` has already dropped any leading `+`), that is a token of the form
/// `-? D+ .?`:
/// - `exp == 0` means no digit follows the `.` (so `12.` is accepted, but `12.0` and `.5`
///   are not);
/// - `num >= 0` means that, after a `-`, every digit is `0` (so `-0` is accepted, as `0`).
///
/// The digits are folded in the Numeric model, with `Auto` rep, so the value isn't bounded by
/// a machine type until the final conversion, which is where a value over `u64::MAX` is
/// rejected (as DaeDaLus does with `as? uint 64`, e.g. in `LookupSize`).
pub(super) fn number_as_nat(number: Expr) -> Expr {
    // Phases of the fold, in the order they can occur
    const START: u8 = 0;
    const SIGN: u8 = 1;
    const INT: u8 = 2;
    const POINT: u8 = 3;
    const BAD: u8 = 4;

    // Each byte as a token: a digit carries its value as an Auto-rep Numeric, so that the
    // arithmetic over it stays in the Numeric model rather than taking on the byte's `u8` rep.
    let token = expr_match(
        var("b"),
        (0..10u8)
            .map(|k| (Pattern::U8(b'0' + k), variant("digit", poly_const(k))))
            .chain([
                (Pattern::U8(b'-'), variant("minus", Expr::UNIT)),
                (Pattern::U8(b'.'), variant("point", Expr::UNIT)),
                (Pattern::Wildcard, variant("other", Expr::UNIT)),
            ]),
    );
    let state = |neg: Expr, val: Expr, phase: u8| Expr::Tuple(vec![neg, val, Expr::U8(phase)]);
    let at = |phase: u8, tok: Pattern| {
        Pattern::Tuple(vec![
            Pattern::Tuple(vec![bind("neg"), bind("val"), Pattern::U8(phase)]),
            tok,
        ])
    };
    let digit = || Pattern::Variant("digit".into(), Box::new(bind("d")));
    let unit = |label: &'static str| Pattern::Variant(label.into(), Box::new(Pattern::Wildcard));

    let step_digit = || state(var("neg"), numeric(numexpr!("val" * 10 + "d")), INT);
    let step = lambda_tuple(
        ["acc", "b"],
        expr_match(
            Expr::Tuple(vec![var("acc"), token]),
            [
                (at(START, digit()), step_digit()),
                (at(SIGN, digit()), step_digit()),
                (at(INT, digit()), step_digit()),
                (
                    at(START, unit("minus")),
                    state(Expr::Bool(true), var("val"), SIGN),
                ),
                (at(INT, unit("point")), state(var("neg"), var("val"), POINT)),
                // a sign that isn't leading, a fraction digit, or anything else
                (
                    Pattern::Wildcard,
                    state(Expr::Bool(false), poly_const(0u8), BAD),
                ),
            ],
        ),
    );
    let init = state(Expr::Bool(false), poly_const(0u8), START);
    let acc_type = ValueType::Tuple(vec![
        ValueType::Base(BaseType::Bool),
        ValueType::NumericHole,
        ValueType::Base(BaseType::U8),
    ]);

    // The only conversion out of the Numeric model, and so the only overflow check
    let to_u64 = numeric_to_u64;
    let finished =
        |neg: Pattern, val: Pattern, phase: u8| Pattern::Tuple(vec![neg, val, Pattern::U8(phase)]);
    let zero = || Pattern::ZConst(0.into());
    expr_match(
        left_fold(step, init, acc_type, number),
        [
            (
                finished(Pattern::Bool(false), bind("v"), INT),
                to_u64(var("v")),
            ),
            (
                finished(Pattern::Bool(false), bind("v"), POINT),
                to_u64(var("v")),
            ),
            (
                finished(Pattern::Bool(true), zero(), INT),
                expr_some(Expr::U64(0)),
            ),
            (
                finished(Pattern::Bool(true), zero(), POINT),
                expr_some(Expr::U64(0)),
            ),
            (Pattern::Wildcard, expr_none()),
        ],
    )
}

/// `Some` of the Numeric value `val` as a `u64`, or `None` if it is negative or too large: the
/// one conversion out of the Numeric model for a computation, and so its only overflow check.
pub(super) fn numeric_to_u64(val: Expr) -> Expr {
    expr_match(
        val.clone(),
        [
            (Pattern::ZRange((0u64..).into()), expr_some(as_u64(val))),
            (Pattern::Wildcard, expr_none()),
        ],
    )
}

/// Whether the value of `key` in `dict` is the name `name` (both written without the leading
/// `/`), as a `Bool`. DaeDaLus `LookupName key dict == name`, without resolving a reference
/// (#355).
pub(super) fn dict_name_is(key: &[u8], name: &[u8], dict: Expr) -> Expr {
    expr_match(
        dict_lookup(key, dict),
        [
            (
                pat_some(Pattern::Variant(
                    "name".into(),
                    Box::new(pattern_bytestring(&[b"/", name].concat())),
                )),
                Expr::Bool(true),
            ),
            (Pattern::Wildcard, Expr::Bool(false)),
        ],
    )
}

/// DaeDaLus `NatValue v`: `v` (a `pdf.value`) must be a number, and [`number_as_nat`] of
/// it must succeed; fails otherwise.
pub(super) fn nat_value(value: Expr) -> Format {
    fmt_match(
        value,
        [
            (
                Pattern::Variant("number".into(), Box::new(bind("n"))),
                fmt_match(
                    number_as_nat(var("n")),
                    [
                        (pat_some(bind("x")), compute(var("x"))),
                        (pat_none(), Format::fail_with("not a natural number")),
                    ],
                ),
            ),
            (Pattern::Wildcard, Format::fail_with("not a number")),
        ],
    )
}

/// DaeDaLus `Default dflt (LookupNat key dict)`: the natural-number value of `key` in `dict`,
/// or `dflt` if `key` is absent or its value is not a natural number.
///
/// DaeDaLus `LookupNat` also resolves an indirect reference (`LookupResolve`). This doesn't
/// (as for the other filter parameters, see [`apply_filters`]), so a reference gives `dflt`.
pub(super) fn lookup_nat_or(key: &[u8], dict: Expr, dflt: u64) -> Expr {
    expr_match(
        dict_lookup(key, dict),
        [
            (
                pat_some(Pattern::Variant("number".into(), Box::new(bind("n")))),
                expr_option_map_or(Expr::U64(dflt), |x| x, number_as_nat(var("n"))),
            ),
            (Pattern::Wildcard, Expr::U64(dflt)),
        ],
    )
}

fn v_string(pm: &mut PdfModule<'_>) -> Format {
    let any_ws = pm.any_ws();
    let eol = pm.eol();
    let module = pm.module();
    let known_esc = interpret([
        (is_byte(b'n'), Expr::Seq(vec![Expr::U8(b'\n')])),
        (is_byte(b'r'), Expr::Seq(vec![Expr::U8(b'\r')])),
        (is_byte(b't'), Expr::Seq(vec![Expr::U8(b'\t')])),
        (is_byte(b'b'), Expr::Seq(vec![Expr::U8(b'\x08')])),
        (is_byte(b'f'), Expr::Seq(vec![Expr::U8(b'\x0c')])),
        (is_byte(b'('), Expr::Seq(vec![Expr::U8(b'(')])),
        (is_byte(b')'), Expr::Seq(vec![Expr::U8(b')')])),
        (is_byte(b'\\'), Expr::Seq(vec![Expr::U8(b'\\')])),
        // A backslash before an end-of-line continues the string onto the next line
        (eol.call(), Expr::Seq(vec![])),
    ]);
    // `\ddd`: one to three octal digits, read greedily (see `octal_num_u8`), so `\0053` is the byte
    // 5 followed by `3`. A value over 255 (e.g. `\777`) fails rather than wrapping.
    let octal_esc = map(octal_num_u8(), lambda("b", Expr::Seq(vec![var("b")])));
    // Any other escaped byte stands for itself (the backslash is ignored). Octal digits are
    // excluded so that this branch does not overlap `octal_esc`.
    let unknown_esc = map(
        byte_in(ByteSet::from(*b"nrtbf()\\\r\n01234567").complement()),
        lambda("b", Expr::Seq(vec![var("b")])),
    );
    let string_esc = monad_seq(is_byte(b'\\'), union([known_esc, octal_esc, unknown_esc]));

    let lim = || vec![(Label::Borrowed("lim"), ValueType::Base(BaseType::U64))];
    // Registration types a call to a *later* batch member as `Any`, which `snoc`'s `Append` and
    // `flat_map` reject, so each member that appends to or flattens a sibling's result comes
    // after that sibling.
    let [_string_chunk, string_chars, _string_in_parens] = module.define_batch_with_args(
        [
            ("pdf.value.string_chunk", lim()),
            ("pdf.value.string_chars", lim()),
            ("pdf.value.string_in_parens", lim()),
        ],
        [
            Box::new(move |&[_, _, string_in_parens]: &[FormatRef; 3]| {
                Format::UnionNondet(vec![
                    string_in_parens.call_args(vec![var("lim")]),
                    string_esc,
                    // One byte per chunk: a `repeat1` here would make `string_chars`'s `repeat`
                    // ambiguous (`aa` is one chunk or two). The flattened result is the same.
                    map(
                        byte_in(ByteSet::from(*b"\\()").complement()),
                        lambda("b", Expr::Seq(vec![var("b")])),
                    ),
                ])
            }),
            Box::new(|&[string_chunk, _, _]: &[FormatRef; 3]| {
                map(
                    repeat(string_chunk.call_args(vec![var("lim")])),
                    lambda("xs", flat_map(lambda("x", var("x")), var("xs"))),
                )
            }),
            Box::new(|&[_, string_chars, _]: &[FormatRef; 3]| {
                // The nesting check follows the '(' rather than preceding it, so that this
                // member always consumes a byte: a leading `Fail` branch counts as matching
                // nothing, which makes `string_chars`'s `repeat` of it a nullable repeat.
                cons(
                    is_byte(b'('),
                    if_then_else(
                        expr_eq(var("lim"), Expr::U64(0)),
                        Format::fail_with("string nesting limit exceeded"),
                        snoc(
                            string_chars.call_args(vec![sub(var("lim"), Expr::U64(1))]),
                            is_byte(b')'),
                        ),
                    ),
                )
            }),
        ],
    );

    record_daedalus([
        ("__open", is_byte(b'(')),
        ("$$", string_chars.call_args(vec![Expr::U64(16)])),
        ("__close", is_byte(b')')),
        ("__skipWS", repeat(any_ws.call())),
    ])
}

pub(super) fn v_name(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let name_char = {
        let ok_raw = ByteSet::from(*b"\0\t\n\x0C\r ()<>[]{}/%#").complement();
        let name_esc = monad_seq(
            is_byte(b'#'),
            where_nonzero::<U8>(map(hex_num_u32(2), lambda("x32", as_u8(var("x32"))))),
        );
        union([Format::Byte(ok_raw), name_esc])
    };
    // A name runs until whitespace or a delimiter, so no name character (raw or `#`-escaped) may follow it
    let name_start = ByteSet::from(*b"\0\t\n\x0C\r ()<>[]{}/%").complement();
    let name = chain(
        cons(is_byte(b'/'), repeat(name_char)),
        "name",
        monad_seq(
            Format::PeekNot(Box::new(Format::Byte(name_start))),
            compute(var("name")),
        ),
    );
    pm.module()
        .define_format("pdf.value.name", token(name, any_ws))
}

/// Daedalus `Value`, as a recursive batch of `pdf.value`, `pdf.value.array` and `pdf.value.dict`.
///
/// Each member takes a nesting limit `lim : u64`; entering an array or dict decrements it, and
/// nesting deeper than the limit fails. Returns `[value, dict]`, both expecting `lim`.
pub(super) fn pdf_value(pm: &mut PdfModule<'_>) -> [FormatRef; 2] {
    let any_ws = pm.any_ws();
    let natural = pm.natural();
    let number = pm.number();
    let v_name = pm.v_name();
    let v_null = void(kw(b"null", any_ws));
    let v_bool = interpret([
        (kw(b"true", any_ws), Expr::Bool(true)),
        (kw(b"false", any_ws), Expr::Bool(false)),
    ]);
    let v_ref = record_auto([
        ("obj", token(natural.call(), any_ws)),
        ("gen", token(natural.call(), any_ws)),
        ("__kw", kw(b"R", any_ws)),
    ]);
    let v_number = token(number.call(), any_ws);

    let v_string = v_string(pm);
    let v_hex_string = v_hex_string(any_ws);

    // Fails once nesting exceeds the limit, otherwise parses `f`. Used after the opening bracket
    // has been consumed, so that the array/dict branch always consumes input.
    let nested = |f: Format| {
        if_then_else(
            expr_eq(var("lim"), Expr::U64(0)),
            Format::fail_with("value nesting limit exceeded"),
            f,
        )
    };
    let inner_lim = || vec![sub(var("lim"), Expr::U64(1))];

    let lim = || vec![(Label::Borrowed("lim"), ValueType::Base(BaseType::U64))];
    let [value, _array, dict] = pm.module().define_batch_with_args(
        [
            ("pdf.value", lim()),
            ("pdf.value.array", lim()),
            ("pdf.value.dict", lim()),
        ],
        [
            Box::new(move |&[_, array, dict]: &[FormatRef; 3]| {
                // `ref` comes before `number`, so that `1 0 R` isn't read as two numbers
                alts_nondet([
                    ("null", v_null),
                    ("bool", v_bool),
                    ("ref", v_ref),
                    ("name", v_name.call()),
                    ("string", v_string),
                    ("string", v_hex_string),
                    ("number", v_number),
                    ("array", array.call_args(vec![var("lim")])),
                    ("dict", dict.call_args(vec![var("lim")])),
                ])
            }),
            Box::new(move |&[value, _, _]: &[FormatRef; 3]| {
                monad_seq(
                    kw(b"[", any_ws),
                    nested(chain(
                        repeat(value.call_args(inner_lim())),
                        "elems",
                        monad_seq(kw(b"]", any_ws), compute(var("elems"))),
                    )),
                )
            }),
            Box::new(move |&[value, _, _]: &[FormatRef; 3]| {
                monad_seq(
                    kw(b"<<", any_ws),
                    nested(chain(
                        repeat(record([
                            ("key", v_name.call()),
                            ("value", value.call_args(inner_lim())),
                        ])),
                        "entries",
                        monad_seq(kw(b">>", any_ws), compute(var("entries"))),
                    )),
                )
            }),
        ],
    );
    [value, dict]
}

/// The value bound to the name `key` in `dict`, as an `Option`, where `dict` is the result
/// of `pdf.value.dict`.
///
/// `key` is written without its leading `/`. Entry keys are compared after `#xx` escapes
/// have been decoded, so `/S#69ze` matches `b"Size"`.
///
/// DaeDaLus builds a dictionary with `insert`, so a later duplicate key replaces an earlier
/// one. `pdf.value.dict` keeps every entry, so this returns the value of the *last* entry
/// whose key is `key` ([`KeySearch::Last`]).
pub(super) fn dict_lookup(key: &[u8], dict: Expr) -> Expr {
    let name = [b"/", key].concat();
    expr_option_map_or(
        expr_none(),
        |entry| expr_some(record_proj(entry, "value")),
        find_by_key(
            KeySearch::Last,
            |entry| record_proj(entry, "key"),
            expr_lift_seq(name, Expr::U8),
            dict,
        ),
    )
}

/// DaeDaLus `Lookup key dict`: like [`dict_lookup`], but as a parser that fails when `dict`
/// has no entry for `key`, so a `Default`-style fallback can catch the failure.
pub(super) fn dict_get(key: &[u8], dict: Expr) -> Format {
    fmt_match(
        dict_lookup(key, dict),
        [
            (pat_some(bind("v")), compute(var("v"))),
            (pat_none(), Format::fail_with("missing dictionary key")),
        ],
    )
}

/// A run of decimal digits (as from `pdf.util.natural`) read as a `u64`, failing if it is too
/// large (DaeDaLus `Natural as? uint 64`).
pub(super) fn natural_u64(natural: FormatRef) -> Format {
    chain(
        natural.call(),
        "digits",
        fmt_match(
            number_as_nat(var("digits")),
            [
                (pat_some(bind("n")), compute(var("n"))),
                (pat_none(), Format::fail_with("number too large")),
            ],
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use doodle::{decoder::Compiler, read::ReadCtxt};

    use doodle::FormatModule;

    use crate::pdf::combinators::only;

    /// Builds `pdf.value` and `pdf.value.dict`, returning the dict format.
    fn dict_module(module: &mut FormatModule) -> FormatRef {
        PdfModule::new(module).pdf_dict()
    }

    /// `dict_lookup` gives the value of the last entry with the given key (after escapes are
    /// decoded), ignores entries of nested dicts and keys that only share a prefix, and gives
    /// `None` when the key is absent. Each case gives the expected digits of a `number` value,
    /// or `None` for an absent key.
    #[test]
    fn dict_lookup_last_match() {
        let cases: &[(&[u8], Option<&[u8]>)] = &[
            (b"<< /Size 7 >>", Some(b"7")),
            (b"<< /Size 3 /Size 7 >>", Some(b"7")),
            (b"<< /Size 3 /Other 5 >>", Some(b"3")),
            (b"<< /S#69ze 7 >>", Some(b"7")),
            (b"<< /A << /Size 9 >> /Size 7 >>", Some(b"7")),
            (b"<< /A << /Size 9 >> >>", None),
            (b"<< /Sizes 7 /Siz 8 >>", None),
            (b"<<>>", None),
        ];
        for (input, expected) in cases {
            let mut module = FormatModule::new();
            let dict = dict_module(&mut module);
            let expected_pat = match expected {
                Some(digits) => pat_some(Pattern::Variant(
                    "number".into(),
                    Box::new(pattern_bytestring(digits)),
                )),
                None => pat_none(),
            };
            let top = module.define_format(
                "test.dict_lookup",
                only(chain(
                    dict.call_args(vec![Expr::U64(32)]),
                    "d",
                    fmt_match(
                        dict_lookup(b"Size", var("d")),
                        [
                            (expected_pat, Format::EMPTY),
                            (Pattern::Wildcard, Format::Fail),
                        ],
                    ),
                )),
            );
            let prog =
                Compiler::compile_program(&module, &top.call()).expect("lookup must compile");
            assert!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                "looking up /Size in {:?}, expecting {:?}",
                String::from_utf8_lossy(input),
                expected.map(String::from_utf8_lossy)
            );
        }
    }

    /// `dict_get` yields the looked-up value and fails when the key is absent.
    #[test]
    fn dict_get_fails_on_missing_key() {
        let cases: &[(&[u8], bool)] = &[
            (b"<< /Size 7 >>", true),
            (b"<< /Size 3 /Size << >> >>", true),
            (b"<< /Other 7 >>", false),
            (b"<<>>", false),
        ];
        let mut module = FormatModule::new();
        let dict = dict_module(&mut module);
        let top = module.define_format(
            "test.dict_get",
            only(chain(
                dict.call_args(vec![Expr::U64(32)]),
                "d",
                dict_get(b"Size", var("d")),
            )),
        );
        let prog = Compiler::compile_program(&module, &top.call()).expect("get must compile");
        for (input, ok) in cases {
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                *ok,
                "decoding {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    /// `number_as_nat` accepts exactly the `pdf.util.number` tokens with no fraction digits
    /// and a non-negative value that fits in a `u64`. Each case gives the expected value, or
    /// `None` where DaeDaLus `NumberAsNat` (with `as? uint 64`) fails.
    #[test]
    fn number_as_nat_cases() {
        let cases: &[(&[u8], Option<u64>)] = &[
            (b"0", Some(0)),
            (b"7", Some(7)),
            (b"+7", Some(7)),
            (b"007", Some(7)),
            (b"12.", Some(12)),
            (b"-0", Some(0)),
            (b"-00.", Some(0)),
            (b"18446744073709551615", Some(u64::MAX)),
            (b"18446744073709551616", None),
            (b"340282366920938463463374607431768211456", None),
            (b"-5", None),
            (b"-0.0", None),
            (b"12.0", None),
            (b"1.5", None),
            (b".5", None),
            (b"-.0", None),
        ];
        for (input, expected) in cases {
            let mut module = FormatModule::new();
            let number = PdfModule::new(&mut module).number();
            let expected_pat = match expected {
                Some(n) => pat_some(Pattern::U64(*n)),
                None => pat_none(),
            };
            let top = module.define_format(
                "test.number_as_nat",
                only(chain(
                    number.call(),
                    "n",
                    fmt_match(
                        number_as_nat(var("n")),
                        [
                            (expected_pat, Format::EMPTY),
                            (Pattern::Wildcard, Format::Fail),
                        ],
                    ),
                )),
            );
            let prog = Compiler::compile_program(&module, &top.call()).expect("must compile");
            assert!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                "number_as_nat({:?}), expecting {expected:?}",
                String::from_utf8_lossy(input),
            );
        }
    }

    /// `nat_value` accepts a `pdf.value` that is a natural number, and fails on a negative or
    /// fractional number and on a value that isn't a number.
    #[test]
    fn nat_value_requires_natural_number() {
        let cases: &[(&[u8], bool)] = &[
            (b"42", true),
            (b"42.", true),
            (b"-0", true),
            (b"-1", false),
            (b"4.2", false),
            (b"/Name", false),
            (b"[ 1 ]", false),
            (b"1 0 R", false),
        ];
        let mut module = FormatModule::new();
        let value = PdfModule::new(&mut module).pdf_value();
        let top = module.define_format(
            "test.nat_value",
            only(chain(
                value.call_args(vec![Expr::U64(32)]),
                "v",
                nat_value(var("v")),
            )),
        );
        let prog = Compiler::compile_program(&module, &top.call()).expect("must compile");
        for (input, ok) in cases {
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                *ok,
                "decoding {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }
}
