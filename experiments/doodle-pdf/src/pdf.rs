use std::ops::RangeInclusive;

use doodle::{
    BaseType, DepFormat, Expr, Format, FormatModule, FormatRef, IntoLabel, Label, Pattern,
    ValueType, helper::*, prelude::ByteSet,
};
use doodle_numexpr_macro::numexpr;

// SECTION - DaeDaLus-PDF-specific helpers
/// Format that parses nothing and returns a byte-sequence meant to be an ascii string
fn const_str(str: &[u8]) -> Format {
    compute(Expr::Seq(str.iter().copied().map(Expr::U8).collect()))
}

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

/// Folds a sequence of ASCII decimal digits into the u64 value it spells out
fn decimal_value(digits: Expr) -> Expr {
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
fn read_nat(len: u32) -> Format {
    map(
        repeat_count(Expr::U32(len), Format::Byte(DIGIT)),
        lambda("ds", decimal_value(var("ds"))),
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

/// Daedalus style record
///
/// Treat `$$` as a singleton-specifier, otherwise equivalent to record-auto
fn record_daedalus<Name: IntoLabel + AsRef<str>>(
    fields: impl IntoIterator<Item = (Name, Format), IntoIter: DoubleEndedIterator>,
) -> Format {
    let mut uniq_ix: Option<usize> = None;
    let mut fields_ext = Vec::new();
    for (_ix, (label, format)) in fields.into_iter().enumerate() {
        let field = match label.as_ref() {
            _nil if _nil.is_empty() || _nil.starts_with("__") => (None, format),
            _tmp if _tmp.starts_with("_") || _tmp.starts_with("@") => {
                (Some((Label::from(_tmp.to_owned()), true)), format)
            }
            uniq if uniq.starts_with("$$") => match uniq_ix.replace(_ix) {
                None => {
                    // patch all previous fields to be temporary
                    for (fld_info, _) in fields_ext.iter_mut() {
                        if let Some((_, is_persist)) = fld_info {
                            *is_persist = false;
                        }
                    }
                    (Some((uniq.replace("$", "x").into(), true)), format)
                }
                Some(old) => {
                    unreachable!("cannot have more than one '$$' field: {} != {}", old, _ix)
                }
            },
            other => (Some((other.to_owned().into(), uniq_ix.is_none())), format),
        };
        fields_ext.push(field)
    }
    record_ext(fields_ext, true)
}

/// Given a sequence of `(f -> e)` mappings, produces a union whose parse-tree is built
/// using `f` but whose parse-output is the computation of `e` for the chosen branch.
///
/// Useful for turning raw byte-parses into meaningful value-level data, e.g. converting
/// byte-strings to interpreted values.
fn interpret(assocs: impl IntoIterator<Item = (Format, Expr)>) -> Format {
    union(assocs.into_iter().map(|(f, e)| monad_seq(f, compute(e))))
}

/// Skips bytes up to the first offset at which `f` matches, then parses `f` there.
///
/// If `f` can be parsed without skipping any bytes, equivalent to parsing `f`.
///
/// Projects the value of `f` out of `Format::SkipTo`'s `(count, value)`.
fn skip_to(f: Format) -> Format {
    map(
        Format::SkipTo(Box::new(f)),
        lambda("skipped", tuple_proj(var("skipped"), 1)),
    )
}

/// Daedalus `CountTo P 0`: like [`skip_to`], but the returned value is the number of
/// leading bytes that were skipped, and the value of parsing `p` is discarded.
///
/// `p` itself is consumed, along with however many leading bytes were skipped.
///
/// If `p` can be parsed immediately, this parse will yield `0`.
///
/// Projects the count out of `Format::SkipTo`'s `(count, value)`, so it is typed as
/// `Format::Pos` is, and `p` may need unbounded lookahead.
fn count_to(p: Format) -> Format {
    map(
        Format::SkipTo(Box::new(p)),
        lambda("skipped", tuple_proj(var("skipped"), 0)),
    )
}

/// Parse `f` and ensure that there is no trailing content
fn only(f: Format) -> Format {
    chain(f, "val", monad_seq(Format::EndOfInput, compute(var("val"))))
}

/// Runs a parser and discards its value, returning `Format::EMPTY`
fn void(f: Format) -> Format {
    monad_seq(f, Format::EMPTY)
}

/// Matches a string (as bytes) exactly, and returns it as a Seq(u8)
#[inline(always)]
fn match_str(bytes: &[u8]) -> Format {
    byte_seq(bytes)
}

/// Parses `format` and silently consumes an EOL token (failing if not the EOL token is not found)
fn then_eol(format: Format, eol: FormatRef) -> Format {
    chain(format, "ret", monad_seq(eol.call(), compute(var("ret"))))
}
// !SECTION

// SECTION - ASCII value and group consts
const ASCII_LF: u8 = b'\n';
const ASCII_CR: u8 = b'\r';

const ASCII_NUL: u8 = b'\0';
const ASCII_TAB: u8 = b'\t';
const ASCII_FF: u8 = b'\x0c';
const ASCII_SPACE: u8 = b' ';

const __WS_MASK: u64 = 1u64 | 1 << ASCII_TAB | 1 << ASCII_FF | 1 << ASCII_SPACE;

/// Const ByteSet for daedalus `$simpleWS`
///
/// ```
/// # use doodle::prelude::ByteSet;
/// # use doodle_pdf::pdf::SIMPLE_WS;
/// let simple_ws = ByteSet::from([b'\0', b'\t', 0x0C, b' ']);
/// assert_eq!(simple_ws, SIMPLE_WS);
/// ```
pub const SIMPLE_WS: ByteSet = ByteSet::from_bits([__WS_MASK, 0, 0, 0]);

/// Const ByteSet for daedalus Digit
///
/// ```
/// # use doodle::prelude::ByteSet;
/// # use doodle_pdf::pdf::DIGIT;
/// let digit = ByteSet::from(b'0'..=b'9');
/// debug_assert_eq!(digit, DIGIT);
/// ```
pub const DIGIT: ByteSet = ByteSet::from_bits([0b11_1111_1111 << b'0', 0, 0, 0]);
// !SECTION

fn simple_eol(module: &mut FormatModule) -> FormatRef {
    module.define_format(
        "pdf.util.simple_eol",
        Format::UnionNondet(vec![
            void(is_bytes(&[ASCII_CR, ASCII_LF])),
            void(is_byte(ASCII_LF)),
        ]),
    )
}

fn eol(module: &mut FormatModule, simple_eol: FormatRef) -> FormatRef {
    module.define_format(
        "pdf.util.eol",
        Format::UnionNondet(vec![simple_eol.call(), void(is_byte(ASCII_CR))]),
    )
}

fn comment(module: &mut FormatModule, eol: FormatRef) -> FormatRef {
    let inline_char = Format::Byte(ByteSet::from([ASCII_LF, ASCII_CR]).complement());
    module.define_format(
        "pdf.util.comment",
        monad_seq(is_byte(b'%'), monad_seq(repeat(inline_char), eol.call())),
    )
}

fn any_ws(module: &mut FormatModule, eol: FormatRef, comment: FormatRef) -> FormatRef {
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

fn natural(module: &mut FormatModule) -> FormatRef {
    module.define_format(
        "pdf.util.natural",
        greedy_digits(repeat1(Format::Byte(DIGIT))),
    )
}

// TODO: add support to allow de-stringification of numbers
fn number(module: &mut FormatModule, natural: FormatRef) -> FormatRef {
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
fn number_as_nat(number: Expr) -> Expr {
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
fn numeric_to_u64(val: Expr) -> Expr {
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
fn dict_name_is(key: &[u8], name: &[u8], dict: Expr, value_type: ValueType) -> Expr {
    expr_match(
        dict_lookup(key, dict, value_type),
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
fn nat_value(value: Expr) -> Format {
    fmt_match(
        value,
        [
            (
                Pattern::Variant("number".into(), Box::new(bind("n"))),
                fmt_match(
                    number_as_nat(var("n")),
                    [
                        (pat_some(bind("x")), compute(var("x"))),
                        (pat_none(), Format::Fail), // "not a natural number"
                    ],
                ),
            ),
            (Pattern::Wildcard, Format::Fail), // "not a number"
        ],
    )
}

/// DaeDaLus `Default dflt (LookupNat key dict)`: the natural-number value of `key` in `dict`,
/// or `dflt` if `key` is absent or its value is not a natural number.
///
/// DaeDaLus `LookupNat` also resolves an indirect reference (`LookupResolve`). That isn't
/// supported yet (#355), so a reference here gives `dflt`.
fn lookup_nat_or(key: &[u8], dict: Expr, dflt: u64, value_type: ValueType) -> Expr {
    expr_match(
        dict_lookup(key, dict, value_type),
        [
            (
                pat_some(Pattern::Variant("number".into(), Box::new(bind("n")))),
                expr_option_map_or(Expr::U64(dflt), |x| x, number_as_nat(var("n"))),
            ),
            (Pattern::Wildcard, Expr::U64(dflt)),
        ],
    )
}

/// DaeDaLus `FlateDecodeParams`: the `predictor`, `colors`, `bpc` and `columns` (all `u64`)
/// of a `/FlateDecode` filter, where `param` is the filter's `/DecodeParms` entry as an
/// `Option` of a `pdf.value.dict` result (DaeDaLus `FilterParam`, which maps `null` to
/// `nothing`). Absent entries, and an absent `param`, take the defaults `1`, `1`, `8` and `1`.
fn flate_decode_params(param: Expr, value_type: ValueType) -> Expr {
    const DEFAULTS: [(&str, &[u8], u64); 4] = [
        ("predictor", b"Predictor", 1),
        ("colors", b"Colors", 1),
        ("bpc", b"BitsPerComponent", 8),
        ("columns", b"Columns", 1),
    ];
    let params = |f: &dyn Fn(&[u8], u64) -> Expr| {
        Expr::Record(
            DEFAULTS
                .iter()
                .map(|(label, key, dflt)| (Label::Borrowed(label), f(key, *dflt)))
                .collect(),
        )
    };
    expr_match(
        param,
        [
            (
                pat_some(bind("ps")),
                params(&|key, dflt| lookup_nat_or(key, var("ps"), dflt, value_type.clone())),
            ),
            (pat_none(), params(&|_, dflt| Expr::U64(dflt))),
        ],
    )
}

/// DaeDaLus `supportedPredictor`, over a [`flate_decode_params`] record: no prediction
/// (`1`), or a PNG predictor (`10..=15`) with sensible `colors`, `bpc` and `columns`.
fn supported_predictor(params: Expr) -> Expr {
    let field = |label: &'static str| record_proj(params.clone(), label);
    let bpc_ok = [1, 2, 4, 8, 16]
        .into_iter()
        .map(|n| expr_eq(field("bpc"), Expr::U64(n)))
        .reduce(or)
        .unwrap();
    or(
        expr_eq(field("predictor"), Expr::U64(1)),
        and(
            and(
                expr_gte(field("predictor"), Expr::U64(10)),
                expr_lte(field("predictor"), Expr::U64(15)),
            ),
            and(
                and(expr_gte(field("colors"), Expr::U64(1)), bpc_ok),
                expr_gte(field("columns"), Expr::U64(1)),
            ),
        ),
    )
}

/// Reverses the PNG row filters selected by PDF predictors `10..=15`, parsing the bytes of a
/// decompressed stream, given a [`flate_decode_params`] record `params`.
///
/// Each row is a filter tag (`0` None, `1` Sub, `2` Up, `3` Average, `4` Paeth) followed by
/// `ceil(colors * bpc * columns / 8)` bytes. The value is the reconstructed bytes, with the tags
/// removed. As in the DaeDaLus host implementation of `FlateDecode`, a tag over `4` or a
/// partial final row fails, an empty input gives an empty output, and the row above the first
/// is taken to be zeros. The bytes per pixel (for Sub, Average and Paeth) is
/// `ceil(colors * bpc / 8)`, or `1` for less than a byte.
///
/// Like the PNG predictors themselves, the PDF predictor value (`10` to `15`) is only a hint:
/// each row's own tag selects its filter.
fn png_unpredict(params: Expr) -> Format {
    let field = |label: &'static str| compute(record_proj(params.clone(), label));
    // Computed in the Numeric model, so that the only overflow check is the conversion to u64
    let bpp = as_u64(numeric(numexpr!(("colors" * "bpc" + 7) / 8)));
    let row_bytes = as_u64(numeric(numexpr!(("colors" * "bpc" * "columns" + 7) / 8)));

    let row = record([
        ("tag", byte_in(0..=4)),
        ("data", repeat_count(var("row_bytes"), Format::ANY_BYTE)),
    ]);

    // Reconstructs one byte `x` of a row, given the bytes of the row so far (`done`) and the
    // previous row (`prev`, empty for the first row, where it counts as zeros).
    let step = {
        let ix = || seq_length(var("done"));
        let has_left = || expr_gte(ix(), var("bpp"));
        let prev_at =
            |i: Expr| expr_option_map_or(Expr::U8(0), |b| b, index_checked(var("prev"), i));
        let left = expr_if_else(
            has_left(),
            index_unchecked(var("done"), sub(ix(), var("bpp"))),
            Expr::U8(0),
        );
        let above = prev_at(ix());
        let upper_left = expr_if_else(has_left(), prev_at(sub(ix(), var("bpp"))), Expr::U8(0));
        // Paeth: of left, above and upper-left, the one closest to `left + above - upper_left`
        // (ties going in that order). The distances simplify to these.
        let paeth = {
            let dist_left = || numeric(numexpr!(abs ("a" into i16 - "c" into i16)));
            let dist_above = || numeric(numexpr!(abs ("l" into i16 - "c" into i16)));
            let dist_ul =
                || numeric(numexpr!(abs ("l" into i16 + "a" into i16 - 2 * "c" into i16)));
            expr_if_else(
                and(
                    expr_lte(dist_left(), dist_above()),
                    expr_lte(dist_left(), dist_ul()),
                ),
                var("l"),
                expr_if_else(expr_lte(dist_above(), dist_ul()), var("a"), var("c")),
            )
        };
        let prediction = expr_match(
            var("tag"),
            [
                (Pattern::U8(0), Expr::U8(0)),
                (Pattern::U8(1), var("l")),
                (Pattern::U8(2), var("a")),
                (
                    Pattern::U8(3),
                    as_u8(numeric(numexpr!(("l" into u16 + "a" into u16) / 2))),
                ),
                // 4, the only other tag the row format accepts
                (Pattern::Wildcard, paeth),
            ],
        );
        // `(x + prediction) mod 256`
        let byte = expr_match(
            prediction,
            [(
                bind("p"),
                as_u8(numeric(numexpr!(("x" into u16 + "p" into u16) % 256))),
            )],
        );
        lambda_tuple(
            ["done", "x"],
            expr_match(
                Expr::Tuple(vec![left, above, upper_left]),
                [(
                    Pattern::Tuple(vec![bind("l"), bind("a"), bind("c")]),
                    append(var("done"), Expr::Seq(vec![byte])),
                )],
            ),
        )
    };
    let bytes_type = || ValueType::Seq(Box::new(ValueType::Base(BaseType::U8)));
    // Each row is reconstructed from the previous reconstructed row, which is carried along
    let unfilter_row = lambda_tuple(
        ["prev", "row"],
        expr_match(
            Expr::Tuple(vec![
                record_proj(var("row"), "tag"),
                record_proj(var("row"), "data"),
            ]),
            [(
                Pattern::Tuple(vec![bind("tag"), bind("data")]),
                expr_match(
                    left_fold(step, Expr::Seq(vec![]), bytes_type(), var("data")),
                    [(bind("cur"), Expr::Tuple(vec![var("cur"), var("cur")]))],
                ),
            )],
        ),
    );

    chain(
        field("colors"),
        "colors",
        chain(
            field("bpc"),
            "bpc",
            chain(
                field("columns"),
                "columns",
                chain(
                    compute(bpp),
                    "bpp",
                    chain(
                        compute(row_bytes),
                        "row_bytes",
                        chain(
                            repeat(row),
                            "rows",
                            monad_seq(
                                Format::EndOfInput,
                                compute(flat_map_accum(
                                    unfilter_row,
                                    Expr::Seq(vec![]),
                                    bytes_type(),
                                    var("rows"),
                                )),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// DaeDaLus `FlateDecode` (a host primitive there): zlib-decodes the bytes `body` with the
/// `zlib` format from `doodle-formats`, given a [`flate_decode_params`] record `params`, then
/// reverses the PNG predictor if `params` names one (see [`png_unpredict`]).
///
/// Fails when `supported_predictor` rejects `params`, the case in which DaeDaLus
/// `TryApplyFilter` reports the filter as unsupported instead of applying it.
fn flate_decode(zlib: FormatRef, params: Expr, body: Expr) -> Format {
    let inflate = decode_bytes(
        body,
        map(
            zlib.call(),
            lambda("zlib", record_lens(var("zlib"), &["data", "inflate"])),
        ),
    );
    if_then_else(
        supported_predictor(params.clone()),
        if_then_else(
            expr_eq(record_proj(params.clone(), "predictor"), Expr::U64(1)),
            inflate.clone(),
            chain(
                inflate,
                "inflated",
                decode_bytes(var("inflated"), png_unpredict(params)),
            ),
        ),
        Format::Fail, // "unsupported predictor"
    )
}

fn v_string(module: &mut FormatModule, any_ws: FormatRef, eol: FormatRef) -> Format {
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
                        Format::Fail, // "string nesting limit exceeded"
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

fn v_name(module: &mut FormatModule, any_ws: FormatRef) -> FormatRef {
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
    module.define_format("pdf.value.name", token(name, any_ws))
}

/// Daedalus `Value`, as a recursive batch of `pdf.value`, `pdf.value.array` and `pdf.value.dict`.
///
/// Each member takes a nesting limit `lim : u64`; entering an array or dict decrements it, and
/// nesting deeper than the limit fails. Returns `[value, dict]`, both expecting `lim`.
fn pdf_value(
    module: &mut FormatModule,
    any_ws: FormatRef,
    eol: FormatRef,
    natural: FormatRef,
    number: FormatRef,
    v_name: FormatRef,
) -> [FormatRef; 2] {
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

    let v_string = v_string(module, any_ws, eol);
    let v_hex_string = v_hex_string(any_ws);

    // Fails once nesting exceeds the limit, otherwise parses `f`. Used after the opening bracket
    // has been consumed, so that the array/dict branch always consumes input.
    let nested = |f: Format| {
        if_then_else(
            expr_eq(var("lim"), Expr::U64(0)),
            Format::Fail, // "value nesting limit exceeded"
            f,
        )
    };
    let inner_lim = || vec![sub(var("lim"), Expr::U64(1))];

    let lim = || vec![(Label::Borrowed("lim"), ValueType::Base(BaseType::U64))];
    let [value, _array, dict] = module.define_batch_with_args(
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
/// of `pdf.value.dict` and `value_type` is the type of `pdf.value`.
///
/// `key` is written without its leading `/`. Entry keys are compared after `#xx` escapes
/// have been decoded, so `/S#69ze` matches `b"Size"`.
///
/// DaeDaLus builds a dictionary with `insert`, so a later duplicate key replaces an earlier
/// one. `pdf.value.dict` keeps every entry, so this returns the value of the *last* entry
/// whose key is `key`.
fn dict_lookup(key: &[u8], dict: Expr, value_type: ValueType) -> Expr {
    let name = [b"/", key].concat();
    left_fold(
        lambda_tuple(
            ["found", "entry"],
            expr_match(
                record_proj(var("entry"), "key"),
                [
                    (
                        pattern_bytestring(&name),
                        expr_some(record_proj(var("entry"), "value")),
                    ),
                    (Pattern::Wildcard, var("found")),
                ],
            ),
        ),
        expr_none(),
        ValueType::Option(Box::new(value_type)),
        dict,
    )
}

/// DaeDaLus `Lookup key dict`: like [`dict_lookup`], but as a parser that fails when `dict`
/// has no entry for `key`, so a `Default`-style fallback can catch the failure.
fn dict_get(key: &[u8], dict: Expr, value_type: ValueType) -> Format {
    fmt_match(
        dict_lookup(key, dict, value_type),
        [
            (pat_some(bind("v")), compute(var("v"))),
            (pat_none(), Format::Fail), // "missing dictionary key"
        ],
    )
}

fn token(f: Format, any_ws: FormatRef) -> Format {
    chain(
        f,
        "tok",
        monad_seq(repeat(any_ws.call()), compute(var("tok"))),
    )
}

fn kw(b: &[u8], any_ws: FormatRef) -> Format {
    token(match_str(b), any_ws)
}

fn between(open: &[u8], close: &[u8], f: Format, any_ws: FormatRef) -> Format {
    monad_seq(
        kw(open, any_ws),
        chain(f, "val", monad_seq(kw(close, any_ws), compute(var("val")))),
    )
}

/// Daedalus `Stream (val : Value)`. `val` is a whole `Value` (as passed by `pdf.top_decl`), and
/// `header = val is dict` narrows it. As in the Daedalus definition, `CountTo` consumes the
/// `endstream` keyword, and `body` is taken from the view saved before it.
fn stream(
    module: &mut FormatModule,
    simple_eol: FormatRef,
    any_ws: FormatRef,
    value_type: ValueType,
) -> DepFormat<1, 0> {
    module.register_format_args(
        "pdf.stream",
        [(Label::Borrowed("val"), value_type)],
        record_daedalus([
            // header = val is dict;
            (
                "header",
                fmt_match(
                    var("val"),
                    [
                        (
                            Pattern::Variant("dict".into(), Box::new(bind("d"))),
                            compute(var("d")),
                        ),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                ),
            ),
            // Match "stream"; SimpleEOL;
            ("__kw_stream", match_str(b"stream")),
            ("__eol", simple_eol.call()),
            // @start = GetStream;
            // @len   = CountTo (KW "endstream") 0;
            // body   = Take len start;
            (
                "body",
                let_view(
                    "start",
                    chain(
                        count_to(kw(b"endstream", any_ws)),
                        "len",
                        with_view(vvar("start"), capture_bytes(var("len"))),
                    ),
                ),
            ),
        ]),
    )
}

/// Cross-reference table: `xref` followed by one or more subsections.
///
/// Prototype: only the classic table form is handled (not cross-reference streams).
fn cross_ref_section(
    module: &mut FormatModule,
    any_ws: FormatRef,
    natural: FormatRef,
) -> FormatRef {
    // Each entry is exactly 20 bytes: `nnnnnnnnnn ggggg f` plus a two-byte end-of-line,
    // where `f` is `n` (in use, `offset` is a byte offset) or `f` (free, `offset` is the
    // next free object number).
    let entry = module.define_format(
        "pdf.xref.entry",
        record_auto([
            ("offset", read_nat(10)),
            ("__sp0", byte_in(SIMPLE_WS)),
            ("gen", read_nat(5)),
            ("__sp1", byte_in(SIMPLE_WS)),
            (
                "in_use",
                interpret([
                    (is_byte(b'n'), Expr::Bool(true)),
                    (is_byte(b'f'), Expr::Bool(false)),
                ]),
            ),
            (
                "__eol",
                // { $simpleWS; $cr <| $lf } <| { $cr; $lf }
                any_of([
                    tuple([byte_in(SIMPLE_WS), byte_in([ASCII_CR, ASCII_LF])]),
                    byte_seq(&[ASCII_CR, ASCII_LF]),
                ]),
            ),
        ]),
    );

    let decimal = || {
        token(
            map(natural.call(), lambda("ds", decimal_value(var("ds")))),
            any_ws,
        )
    };
    let subsection = module.define_format(
        "pdf.xref.subsection",
        record_auto([
            ("first_id", decimal()),
            ("count", decimal()),
            ("entries", repeat_count(as_u32(var("count")), entry.call())),
        ]),
    );

    module.define_format(
        "pdf.xref",
        let_view(
            "xref_view",
            record_auto([
                // omitted: offset = Offset
                ("__marker", kw(b"xref", any_ws)),
                ("entries", repeat1(subsection.call())),
            ]),
        ),
    )
}

/// DaeDaLus `WhiteTillEOL`: simple whitespace, then an end-of-line
fn white_till_eol(eol: FormatRef) -> Format {
    monad_seq(repeat(byte_in(SIMPLE_WS)), eol.call())
}

/// A run of decimal digits (as from `pdf.util.natural`) read as a `u64`, failing if it is too
/// large (DaeDaLus `Natural as? uint 64`).
fn natural_u64(natural: FormatRef) -> Format {
    chain(
        natural.call(),
        "digits",
        fmt_match(
            number_as_nat(var("digits")),
            [
                (pat_some(bind("n")), compute(var("n"))),
                (pat_none(), Format::Fail), // "number too large"
            ],
        ),
    )
}

/// DaeDaLus `PdfEnd`: `startxref`, the offset of the last cross-reference section, and `%%EOF`,
/// each on its own line. Yields the offset.
fn pdf_end(module: &mut FormatModule, eol: FormatRef, natural: FormatRef) -> FormatRef {
    let ws = || repeat(byte_in(SIMPLE_WS));
    module.define_format(
        "pdf.end",
        record_daedalus([
            ("__ws0", ws()),
            ("__startxref", match_str(b"startxref")),
            ("__eol0", white_till_eol(eol)),
            ("__ws1", ws()),
            ("$$", natural_u64(natural)),
            ("__eol1", white_till_eol(eol)),
            ("__ws2", ws()),
            ("__eof", match_str(b"%%EOF")),
        ]),
    )
}

/// The `pdf.end` for the *last* `startxref` in the input, as the DaeDaLus host finds it (it
/// searches backwards from the end of the file for `startxref`, then parses `PdfEnd` there).
///
/// The first offset where `pdf.end` parses and no `startxref` follows is that last occurrence,
/// and this fails exactly when the host's search or parse does. The search runs forward over
/// the whole input; a backward `SkipTo` (#358) would avoid that.
fn last_pdf_end(pdf_end: FormatRef) -> Format {
    // Whether another `startxref` follows. `PeekNot` can't take a `SkipTo` (whose lookahead
    // is unbounded), so this is a `UnionNondet`, which commits to its first branch that
    // succeeds.
    let another_follows = Format::UnionNondet(vec![
        monad_seq(
            Format::Peek(Box::new(Format::SkipTo(Box::new(is_bytes(b"startxref"))))),
            compute(Expr::Bool(true)),
        ),
        compute(Expr::Bool(false)),
    ]);
    skip_to(chain(
        pdf_end.call(),
        "offset",
        chain(
            another_follows,
            "another",
            if_then_else(var("another"), Format::Fail, compute(var("offset"))),
        ),
    ))
}

/// DaeDaLus `TrailerDict`, given a `pdf.value.dict` result `dict`: the `size`, `root`, `prev`
/// and `xrefstm` entries, and the whole dict as `all`. The `/Encrypt` and `/ID` entries
/// (`TrailerDictEncrypt`) aren't extracted.
///
/// `size` is required and must be a natural number. `root` must be a reference if present.
/// `prev` and `xrefstm` are `None` if absent or not a natural number, as DaeDaLus `Optional`
/// gives. DaeDaLus resolves an indirect `/XRefStm`; until #355 that gives `None` here.
fn trailer_dict(dict: Expr, value_type: ValueType) -> Format {
    let optional_nat = |key: &[u8]| {
        expr_match(
            dict_lookup(key, dict.clone(), value_type.clone()),
            [
                (
                    pat_some(Pattern::Variant("number".into(), Box::new(bind("n")))),
                    number_as_nat(var("n")),
                ),
                (Pattern::Wildcard, expr_none()),
            ],
        )
    };
    record_auto([
        (
            "size",
            chain(
                dict_get(b"Size", dict.clone(), value_type.clone()),
                "size",
                nat_value(var("size")),
            ),
        ),
        (
            "root",
            fmt_match(
                dict_lookup(b"Root", dict.clone(), value_type.clone()),
                [
                    (
                        pat_some(Pattern::Variant("ref".into(), Box::new(bind("r")))),
                        compute(expr_some(var("r"))),
                    ),
                    (pat_none(), compute(expr_none())),
                    (Pattern::Wildcard, Format::Fail), // "/Root is not a reference"
                ],
            ),
        ),
        ("prev", compute(optional_nat(b"Prev"))),
        ("xrefstm", compute(optional_nat(b"XRefStm"))),
        ("all", compute(dict)),
    ])
}

/// DaeDaLus `BEBytes n`: `n` bytes read as a big-endian natural number, which must fit in a
/// `u64` (DaeDaLus allows any width, as its integers are unbounded; see #359).
fn be_bytes(n: Expr) -> Format {
    // Each byte as an Auto-rep constant (as `number_as_nat` does with digits), so that the
    // accumulation stays in the Numeric model instead of taking on a machine rep
    let byte = expr_match(
        var("byte"),
        (0..=255u8).map(|k| (Pattern::U8(k), poly_const(k))),
    );
    let step = lambda_tuple(
        ["v", "byte"],
        expr_match(byte, [(bind("b"), numeric(numexpr!("v" * 256 + "b")))]),
    );
    chain(
        repeat_count(n, Format::ANY_BYTE),
        "bytes",
        fmt_match(
            numeric_to_u64(left_fold(
                step,
                poly_const(0u8),
                ValueType::NumericHole,
                var("bytes"),
            )),
            [
                (pat_some(bind("v")), compute(var("v"))),
                (pat_none(), Format::Fail), // "field too wide"
            ],
        ),
    )
}

/// DaeDaLus `XRefFieldWithDefault dflt n`: `dflt` for a field of width `0`, otherwise
/// [`be_bytes`].
fn xref_field_or(dflt: u64, width: Expr) -> Format {
    if_then_else(
        expr_eq(width.clone(), Expr::U64(0)),
        compute(Expr::U64(dflt)),
        be_bytes(width),
    )
}

/// DaeDaLus `XRefFieldRequired n`: [`be_bytes`], failing for a field of width `0`.
fn xref_field_required(width: Expr) -> Format {
    if_then_else(
        expr_eq(width.clone(), Expr::U64(0)),
        Format::Fail, // "required field has width 0"
        be_bytes(width),
    )
}

/// DaeDaLus `XRefObjEntry`: one entry of a cross-reference stream, given the
/// [`xref_widths`] record `widths`. It takes `width` bytes, of which the fields use the first
/// `b1 + b2 + b3`.
///
/// The type field (of width `b1`) defaults to `1`. As in DaeDaLus, type `0` is `free`, `1` is
/// `in_use`, `2` is `compressed`, and any other type is `null` (a reference to it is to the
/// null object).
fn xref_entry(widths: Expr) -> Format {
    let w = |label: &'static str| record_proj(widths.clone(), label);
    let entry = |name: &'static str, field2: &'static str, field3: &'static str| {
        fmt_variant(
            name,
            record_auto([
                (field2, xref_field_required(w("b2"))),
                (field3, xref_field_or(0, w("b3"))),
            ]),
        )
    };
    slice(
        w("width"),
        chain(
            xref_field_or(1, w("b1")),
            "type",
            fmt_match(
                var("type"),
                [
                    (Pattern::U64(0), entry("free", "obj", "gen")),
                    (Pattern::U64(1), entry("in_use", "offset", "gen")),
                    // the generation is implicitly 0
                    (
                        Pattern::U64(2),
                        entry("compressed", "container_obj", "obj_index"),
                    ),
                    (Pattern::Wildcard, fmt_variant("null", compute(Expr::UNIT))),
                ],
            ),
        ),
    )
}

/// DaeDaLus `XRefIndex`, given the stream dictionary `header`: the subsections of a
/// cross-reference stream, as `first_id` and `num` (entry count) pairs. They come from
/// `/Index`, an array of pairs, or if `/Index` is absent or isn't an array of natural
/// numbers, the single pair `0 /Size`. An `/Index` of odd length fails.
///
/// DaeDaLus resolves an indirect `/Size`, `/Index` or element of it; until #355 that makes
/// `/Size` fail and `/Index` take its default.
fn xref_index(header: Expr, value_type: ValueType) -> Format {
    let u64_seq = ValueType::Seq(Box::new(ValueType::Base(BaseType::U64)));
    // DaeDaLus `LookupNats "Index" header`, as an `Option`
    let index_nats = expr_match(
        dict_lookup(b"Index", header.clone(), value_type.clone()),
        [
            (
                pat_some(Pattern::Variant("array".into(), Box::new(bind("vs")))),
                left_fold(
                    lambda_tuple(
                        ["acc", "v"],
                        expr_match(
                            Expr::Tuple(vec![var("acc"), var("v")]),
                            [
                                (
                                    Pattern::Tuple(vec![
                                        pat_some(bind("ns")),
                                        Pattern::Variant("number".into(), Box::new(bind("n"))),
                                    ]),
                                    expr_option_map_or(
                                        expr_none(),
                                        |k| expr_some(append(var("ns"), Expr::Seq(vec![k]))),
                                        number_as_nat(var("n")),
                                    ),
                                ),
                                (Pattern::Wildcard, expr_none()),
                            ],
                        ),
                    ),
                    expr_some(Expr::Seq(vec![])),
                    ValueType::Option(Box::new(u64_seq)),
                    var("vs"),
                ),
            ),
            (Pattern::Wildcard, expr_none()),
        ],
    );
    let ix = |offset: u32| {
        index_unchecked(
            var("arr"),
            add(mul(var("i"), Expr::U32(2)), Expr::U32(offset)),
        )
    };
    chain(
        chain(
            dict_get(b"Size", header, value_type),
            "size",
            nat_value(var("size")),
        ),
        "size",
        chain(
            compute(expr_option_map_or(
                Expr::Seq(vec![Expr::U64(0), var("size")]),
                |ns| ns,
                index_nats,
            )),
            "arr",
            if_then_else(
                expr_eq(rem(seq_length(var("arr")), Expr::U32(2)), Expr::U32(0)),
                for_each(
                    enum_from_to(Expr::U32(0), div(seq_length(var("arr")), Expr::U32(2))),
                    "i",
                    record_auto([("first_id", compute(ix(0))), ("num", compute(ix(1)))]),
                ),
                Format::Fail, // "odd /Index length"
            ),
        ),
    )
}

/// DaeDaLus `XRefFormat`, given the stream dictionary `header`: the widths `b1`, `b2` and `b3`
/// of the fields of an entry (from `/W`, `0` for any it doesn't give), and the `width` of a
/// whole entry, the sum of all of `/W`. `/W` must be an array of natural numbers.
///
/// DaeDaLus resolves an indirect `/W`; until #355 that fails here.
fn xref_widths(header: Expr, value_type: ValueType) -> Format {
    let b = |i: u32| {
        compute(expr_option_map_or(
            Expr::U64(0),
            |x| x,
            index_checked(var("_ws"), Expr::U32(i)),
        ))
    };
    // DaeDaLus sums unbounded integers, then checks the total fits (`as? uint 64`). The widths
    // are already `u64`s here, so the typed model sums in `u64`; the interpreter computes the
    // Numeric sum exactly, and `numeric_to_u64` is the check.
    let sum = left_fold(
        lambda_tuple(["s", "w"], numeric(numexpr!("s" + ("w" into u64)))),
        poly_const(0u8),
        ValueType::NumericHole,
        var("_ws"),
    );
    record_auto([
        (
            "_w",
            fmt_match(
                dict_lookup(b"W", header, value_type),
                [
                    (
                        pat_some(Pattern::Variant("array".into(), Box::new(bind("vs")))),
                        compute(var("vs")),
                    ),
                    (Pattern::Wildcard, Format::Fail), // "/W is not an array"
                ],
            ),
        ),
        ("_ws", for_each(var("_w"), "x", nat_value(var("x")))),
        ("b1", b(0)),
        ("b2", b(1)),
        ("b3", b(2)),
        (
            "width",
            fmt_match(
                numeric_to_u64(sum),
                [
                    (pat_some(bind("n")), compute(var("n"))),
                    (pat_none(), Format::Fail), // "entry too wide"
                ],
            ),
        ),
    ])
}

/// DaeDaLus `ApplyFilters`, given a stream's dictionary `header` and its raw bytes `raw`:
/// `ok` with the decoded bytes, or `unsupported` with the name of the filter that can't be
/// applied (followed by ` (with params)` if it has a `/DecodeParms` entry), as DaeDaLus
/// `ApplyFilter` gives.
///
/// Of the filters, only `/FlateDecode` with a supported predictor is applied (see
/// [`flate_decode`]), and only on its own; no filter gives `ok` with `raw`. Unlike DaeDaLus:
/// - every other filter is `unsupported`, including `/ASCIIHexDecode`, `/ASCII85Decode` and
///   `/DCTDecode`, which DaeDaLus decodes or passes through;
/// - a chain of more than one filter is `unsupported`, naming the first, and nothing is
///   decoded;
/// - nothing is decrypted (DaeDaLus decrypts every stream except a `/Type /XRef` one), so an
///   encrypted file's streams are taken as they are;
/// - an indirect `/Filter` or `/DecodeParms` isn't resolved, and fails.
///
/// A filter that isn't a name, or a `/DecodeParms` that isn't a dict or `null`, fails (DaeDaLus
/// `Filter`, `FilterParam`), as does a `/FlateDecode` whose data doesn't decode.
fn apply_filters(zlib: FormatRef, header: Expr, raw: Expr, value_type: ValueType) -> Format {
    // DaeDaLus `LookupOptArray`: absent is `[]`, and a single value is `[value]`
    let opt_array = |key: &[u8]| {
        expr_match(
            dict_lookup(key, header.clone(), value_type.clone()),
            [
                (pat_none(), Expr::Seq(vec![])),
                (
                    pat_some(Pattern::Variant("array".into(), Box::new(bind("vs")))),
                    var("vs"),
                ),
                (pat_some(bind("v")), Expr::Seq(vec![var("v")])),
            ],
        )
    };
    let null = || Pattern::Variant("null".into(), Box::new(Pattern::Wildcard));
    // DaeDaLus `FilterParam` of the first filter's parameters, which default to `null`
    let param = fmt_match(
        index_checked(var("_params"), Expr::U32(0)),
        [
            (pat_none(), compute(expr_none())),
            (pat_some(null()), compute(expr_none())),
            (
                pat_some(Pattern::Variant("dict".into(), Box::new(bind("d")))),
                compute(expr_some(var("d"))),
            ),
            (Pattern::Wildcard, Format::Fail), // "bad /DecodeParms"
        ],
    );
    let name = fmt_match(
        index_unchecked(var("_filters"), Expr::U32(0)),
        [
            (
                Pattern::Variant("name".into(), Box::new(bind("n"))),
                compute(var("n")),
            ),
            (Pattern::Wildcard, Format::Fail), // "filter is not a name"
        ],
    );
    let unsupported = || {
        let with_params = b" (with params)".iter().map(|b| Expr::U8(*b)).collect();
        compute(variant(
            "unsupported",
            expr_match(
                var("_param"),
                [
                    (pat_none(), var("_name")),
                    (
                        Pattern::Wildcard,
                        append(var("_name"), Expr::Seq(with_params)),
                    ),
                ],
            ),
        ))
    };
    let lone_flate = and(
        expr_eq(seq_length(var("_filters")), Expr::U32(1)),
        expr_match(
            var("_name"),
            [
                (pattern_bytestring(b"/FlateDecode"), Expr::Bool(true)),
                (Pattern::Wildcard, Expr::Bool(false)),
            ],
        ),
    );
    let flate = chain(
        compute(flate_decode_params(var("_param"), value_type.clone())),
        "_fp",
        if_then_else(
            supported_predictor(var("_fp")),
            map(
                flate_decode(zlib, var("_fp"), raw.clone()),
                lambda("decoded", variant("ok", var("decoded"))),
            ),
            unsupported(),
        ),
    );
    chain(
        compute(opt_array(b"Filter")),
        "_filters",
        chain(
            compute(opt_array(b"DecodeParms")),
            "_params",
            fmt_match(
                var("_filters"),
                [
                    (Pattern::Seq(vec![]), compute(variant("ok", raw))),
                    (
                        Pattern::Wildcard,
                        chain(
                            name,
                            "_name",
                            chain(
                                param,
                                "_param",
                                if_then_else(lone_flate, flate, unsupported()),
                            ),
                        ),
                    ),
                ],
            ),
        ),
    )
}

/// [`apply_filters`] for a cross-reference stream, whose filters must all be applied (DaeDaLus
/// `str.body is ok`): the decoded bytes, failing if they're `unsupported`.
fn xref_stream_filters(zlib: FormatRef, header: Expr, raw: Expr, value_type: ValueType) -> Format {
    chain(
        apply_filters(zlib, header, raw, value_type),
        "_filtered",
        fmt_match(
            var("_filtered"),
            [
                (
                    Pattern::Variant("ok".into(), Box::new(bind("bytes"))),
                    compute(var("bytes")),
                ),
                (Pattern::Wildcard, Format::Fail), // "unsupported filter"
            ],
        ),
    )
}

/// DaeDaLus `XRefObj`: a cross-reference stream object (PDF 1.5), with its `xref` subsections
/// (each a `first_id` and its `entries`, see [`xref_entry`]) and its `trailer` (the stream
/// dictionary, as [`trailer_dict`]), like the classic form.
///
/// As DaeDaLus `StreamBody` does, the body is the `/Length` bytes after the `stream` line,
/// decoded by [`xref_stream_filters`], and the table is read from the decoded bytes, ignoring
/// any after the last entry. DaeDaLus resolves an indirect `/Length`; until #355 that fails.
fn xref_obj(
    module: &mut FormatModule,
    any_ws: FormatRef,
    simple_eol: FormatRef,
    natural: FormatRef,
    pdf_value: FormatRef,
    zlib: FormatRef,
    value_type: ValueType,
) -> FormatRef {
    let header = || var("_header");
    module.define_format(
        "pdf.xref_obj",
        record_auto([
            // DaeDaLus `TopDecl`, which must be a `stream`
            ("__ws", repeat(any_ws.call())),
            ("__id", token(natural_u64(natural), any_ws)),
            ("__gen", token(natural_u64(natural), any_ws)),
            ("__kw_obj", kw(b"obj", any_ws)),
            ("_val", pdf_value.call_args(vec![Expr::U64(32)])),
            (
                "_header",
                fmt_match(
                    var("_val"),
                    [
                        (
                            Pattern::Variant("dict".into(), Box::new(bind("d"))),
                            compute(var("d")),
                        ),
                        (Pattern::Wildcard, Format::Fail), // "not a stream"
                    ],
                ),
            ),
            ("__kw_stream", match_str(b"stream")),
            ("__eol", simple_eol.call()),
            (
                "_len",
                chain(
                    dict_get(b"Length", header(), value_type.clone()),
                    "len",
                    nat_value(var("len")),
                ),
            ),
            (
                "_body",
                token(
                    slice(
                        var("_len"),
                        chain(
                            repeat(Format::ANY_BYTE),
                            "raw",
                            xref_stream_filters(zlib, header(), var("raw"), value_type.clone()),
                        ),
                    ),
                    any_ws,
                ),
            ),
            ("__kw_endstream", kw(b"endstream", any_ws)),
            ("__kw_endobj", match_str(b"endobj")),
            // DaeDaLus `XRefMeta`
            (
                "__type",
                if_then_else(
                    dict_name_is(b"Type", b"XRef", header(), value_type.clone()),
                    Format::EMPTY,
                    Format::Fail, // "not /Type /XRef"
                ),
            ),
            ("_index", xref_index(header(), value_type.clone())),
            ("_widths", xref_widths(header(), value_type.clone())),
            // DaeDaLus `XRefObjTable`
            (
                "xref",
                decode_bytes(
                    var("_body"),
                    for_each(
                        var("_index"),
                        "idx",
                        record_auto([
                            ("first_id", compute(record_proj(var("idx"), "first_id"))),
                            (
                                "entries",
                                repeat_count(
                                    record_proj(var("idx"), "num"),
                                    xref_entry(var("_widths")),
                                ),
                            ),
                        ]),
                    ),
                ),
            ),
            ("trailer", trailer_dict(header(), value_type)),
        ]),
    )
}

/// DaeDaLus `CrossRef`: the cross-reference section found at an offset, either `old_xref`
/// (`CrossRefAndTrailer`: an `xref` table, then `trailer` and its dict) or `new_xref` (a
/// cross-reference stream, [`xref_obj`]), trying them in that order (DaeDaLus `First`).
fn cross_ref(
    module: &mut FormatModule,
    any_ws: FormatRef,
    eol: FormatRef,
    xref_table: FormatRef,
    pdf_dict: FormatRef,
    xref_obj: FormatRef,
    value_type: ValueType,
) -> FormatRef {
    let just_white = union([void(byte_in(SIMPLE_WS)), eol.call()]);
    let old_xref = record_auto([
        // DaeDaLus `CrossRefSection` allows whitespace and comments before `xref`
        ("xref", monad_seq(repeat(any_ws.call()), xref_table.call())),
        // ... but only whitespace (no comments) before `trailer`
        ("__ws", repeat(just_white)),
        ("__kw_trailer", kw(b"trailer", any_ws)),
        ("_dict", pdf_dict.call_args(vec![Expr::U64(32)])),
        ("trailer", trailer_dict(var("_dict"), value_type)),
    ]);
    module.define_format(
        "pdf.cross_ref",
        alts_nondet([("old_xref", old_xref), ("new_xref", xref_obj.call())]),
    )
}

/// The cross-reference sections reachable from the one at `offset` (relative to `base`, the
/// position of the `%PDF-` header), through `/Prev` and `/XRefStm` links.
///
/// Follows the DaeDaLus host (`process_xref`): an offset that has already been visited is an
/// error (a cycle, or two links to one section), and for each section the `/Prev` link is
/// followed before `/XRefStm`. Each section's own entries take precedence over those of its
/// `/XRefStm` sections, which take precedence over its `/Prev` sections, so `sections` lists
/// them in that order (highest precedence first). `visited` is threaded from the `/Prev` call
/// into the `/XRefStm` call, as the host's visited-set is.
///
/// `lim` bounds the depth of the links followed; the visited check alone already guarantees
/// termination, so `lim` only guards against a very long chain overflowing the stack.
fn xref_chain(module: &mut FormatModule, cross_ref: FormatRef) -> FormatRef {
    let u64_type = || ValueType::Base(BaseType::U64);
    let args = vec![
        (Label::Borrowed("base"), u64_type()),
        (Label::Borrowed("offset"), u64_type()),
        (
            Label::Borrowed("visited"),
            ValueType::Seq(Box::new(u64_type())),
        ),
        (Label::Borrowed("lim"), u64_type()),
    ];
    let [chain_ref] = module.define_batch_with_args(
        [("pdf.xref_chain", args)],
        [Box::new(move |&[xref_chain]: &[FormatRef; 1]| {
            // Follows `link` (an `Option` of an offset) with the visited offsets `visited`, or
            // yields no sections if there is no link.
            let follow = |link: Expr, visited: Expr| {
                fmt_match(
                    link,
                    [
                        (
                            pat_some(bind("next")),
                            xref_chain.call_args(vec![
                                var("base"),
                                var("next"),
                                visited.clone(),
                                sub(var("lim"), Expr::U64(1)),
                            ]),
                        ),
                        (
                            pat_none(),
                            compute(Expr::Record(vec![
                                (Label::Borrowed("sections"), Expr::Seq(vec![])),
                                (Label::Borrowed("visited"), visited),
                            ])),
                        ),
                    ],
                )
            };
            let trailer = || section_trailer(var("section"));
            let visited_here = || append(var("visited"), Expr::Seq(vec![var("offset")]));
            if_then_else(
                or(
                    expr_eq(var("lim"), Expr::U64(0)), // "cross-reference chain too long"
                    seq_any(|v| expr_eq(v, var("offset")), var("visited")), // "cycle"
                ),
                Format::Fail,
                chain(
                    with_relative_offset(Some(var("base")), var("offset"), cross_ref.call()),
                    "section",
                    chain(
                        follow(record_proj(trailer(), "prev"), visited_here()),
                        "prev",
                        chain(
                            follow(
                                record_proj(trailer(), "xrefstm"),
                                record_proj(var("prev"), "visited"),
                            ),
                            "xrefstm",
                            compute(Expr::Record(vec![
                                (
                                    Label::Borrowed("sections"),
                                    concat(Expr::Seq(vec![
                                        Expr::Seq(vec![var("section")]),
                                        record_proj(var("xrefstm"), "sections"),
                                        record_proj(var("prev"), "sections"),
                                    ])),
                                ),
                                (
                                    Label::Borrowed("visited"),
                                    record_proj(var("xrefstm"), "visited"),
                                ),
                            ])),
                        ),
                    ),
                ),
            )
        })],
    );
    chain_ref
}

/// The trailer of a `pdf.cross_ref` result, of either form.
fn section_trailer(section: Expr) -> Expr {
    expr_match(
        section,
        ["old_xref", "new_xref"].map(|form| {
            (
                Pattern::Variant(form.into(), Box::new(bind("x"))),
                record_proj(var("x"), "trailer"),
            )
        }),
    )
}

/// What the cross-reference sections say of object number `obj` (a `u64`), as the DaeDaLus
/// host's merged table does: `Some` of `at` (an `offset` relative to the `%PDF-` header, and
/// a `gen`), `packed` (in an object stream, at generation `0`), `free` or `null` (an unknown
/// entry type), or `None` if no section has an entry for it.
///
/// `sections` is in precedence order (see [`xref_chain`]), so the first section with an
/// entry decides; the host gets the same by letting each section's entries replace those of
/// the sections it links to, with a free entry removing the object. Within a section, a later
/// subsection's entry replaces an earlier one's.
fn xref_entry_for(sections: Expr, obj: Expr) -> Expr {
    let u64_type = || ValueType::Base(BaseType::U64);
    let kind_type = ValueType::Option(Box::new(ValueType::Union(
        std::collections::BTreeMap::from([
            (
                Label::Borrowed("at"),
                ValueType::Record(vec![
                    (Label::Borrowed("offset"), u64_type()),
                    (Label::Borrowed("gen"), u64_type()),
                ]),
            ),
            (Label::Borrowed("packed"), ValueType::UNIT),
            (Label::Borrowed("free"), ValueType::UNIT),
            (Label::Borrowed("null"), ValueType::UNIT),
        ]),
    )));
    let at = |offset: Expr, gen_: Expr| {
        variant(
            "at",
            Expr::Record(vec![
                (Label::Borrowed("offset"), offset),
                (Label::Borrowed("gen"), gen_),
            ]),
        )
    };
    let unit = |name: &'static str| variant(name, Expr::UNIT);
    // The last subsection of `subs` (with `first`, `count` and `kind` of its entry) that covers `obj`
    let in_section = |subs: Expr,
                      first: &dyn Fn() -> Expr,
                      count: &dyn Fn() -> Expr,
                      kind: &dyn Fn(Expr) -> Expr| {
        left_fold(
            lambda_tuple(
                ["found", "sub"],
                expr_if_else(
                    and(
                        expr_gte(obj.clone(), first()),
                        expr_lt(obj.clone(), add(first(), count())),
                    ),
                    expr_some(kind(index_unchecked(
                        record_proj(var("sub"), "entries"),
                        sub(obj.clone(), first()),
                    ))),
                    var("found"),
                ),
            ),
            expr_none(),
            kind_type.clone(),
            subs,
        )
    };
    let first = || record_proj(var("sub"), "first_id");
    let old = in_section(
        record_lens(var("x"), &["xref", "entries"]),
        &first,
        &|| record_proj(var("sub"), "count"),
        &|e| {
            expr_if_else(
                record_proj(e.clone(), "in_use"),
                at(record_proj(e.clone(), "offset"), record_proj(e, "gen")),
                unit("free"),
            )
        },
    );
    let new = in_section(
        record_proj(var("x"), "xref"),
        &first,
        &|| as_u64(seq_length(record_proj(var("sub"), "entries"))),
        &|e| {
            expr_match(
                e,
                [
                    (
                        Pattern::Variant("in_use".into(), Box::new(bind("e"))),
                        at(
                            record_proj(var("e"), "offset"),
                            record_proj(var("e"), "gen"),
                        ),
                    ),
                    (
                        Pattern::Variant("compressed".into(), Box::new(Pattern::Wildcard)),
                        unit("packed"),
                    ),
                    (
                        Pattern::Variant("free".into(), Box::new(Pattern::Wildcard)),
                        unit("free"),
                    ),
                    (Pattern::Wildcard, unit("null")),
                ],
            )
        },
    );
    left_fold(
        lambda_tuple(
            ["acc", "s"],
            expr_match(
                var("acc"),
                [
                    (pat_none(), {
                        expr_match(
                            var("s"),
                            [
                                (
                                    Pattern::Variant("old_xref".into(), Box::new(bind("x"))),
                                    old,
                                ),
                                (
                                    Pattern::Variant("new_xref".into(), Box::new(bind("x"))),
                                    new,
                                ),
                            ],
                        )
                    }),
                    (Pattern::Wildcard, var("acc")),
                ],
            ),
        ),
        expr_none(),
        kind_type,
        sections,
    )
}

/// DaeDaLus `ResolveVal v`, inside or calling the [`resolve`] batch: the value that `v` refers
/// to if it is a reference, and `v` otherwise. A reference to a stream fails (DaeDaLus
/// `ResolveValRef` is `ResolveDeclRef r is value`), as does an object or generation number
/// over `u64` (as in the DaeDaLus host).
///
/// `args` are `resolve_ref`'s other arguments: `base`, `sections`, `resolving` and `lim`.
fn resolve_val(resolve_ref: FormatRef, args: [Expr; 4], v: Expr) -> Format {
    let [base, sections, resolving, lim] = args;
    fmt_match(
        v.clone(),
        [
            (
                Pattern::Variant("ref".into(), Box::new(bind("r"))),
                fmt_match(
                    Expr::Tuple(vec![
                        number_as_nat(record_proj(var("r"), "obj")),
                        number_as_nat(record_proj(var("r"), "gen")),
                    ]),
                    [
                        (
                            Pattern::Tuple(vec![pat_some(bind("r_obj")), pat_some(bind("r_gen"))]),
                            chain(
                                resolve_ref.call_args(vec![
                                    base,
                                    sections,
                                    var("r_obj"),
                                    var("r_gen"),
                                    resolving,
                                    lim,
                                ]),
                                "r_decl",
                                fmt_match(
                                    var("r_decl"),
                                    [
                                        (
                                            Pattern::Variant("value".into(), Box::new(bind("rv"))),
                                            compute(var("rv")),
                                        ),
                                        (Pattern::Wildcard, Format::Fail), // "is a stream"
                                    ],
                                ),
                            ),
                        ),
                        (Pattern::Wildcard, Format::Fail), // "invalid object number"
                    ],
                ),
            ),
            (Pattern::Wildcard, compute(v)),
        ],
    )
}

/// DaeDaLus `ResolveDeclRef`, restricted to objects at a byte offset (#355): the batch
/// `[pdf.resolve_ref, pdf.resolved_decl]`, both taking `base` (the position of the `%PDF-`
/// header), `sections` (from `pdf.cos`), the object number `obj` and generation `gen` (as
/// `u64`s), `resolving` and `lim`.
///
/// `pdf.resolve_ref` gives the object's DaeDaLus `TopDeclDef`: a `stream` (its `header` and
/// its `body`, see [`apply_filters`]) or a `value`. As in the DaeDaLus host:
/// - an object with no entry, a free entry, a `null` entry, or an entry of another
///   generation is the value `null`;
/// - otherwise the object is parsed at its offset (`pdf.resolved_decl`), and must be numbered
///   `obj gen` there (DaeDaLus `CheckExpected`);
/// - an object that is already being resolved fails (a cycle, such as a stream whose
///   indirect `/Length` is itself); `resolving` holds those objects. `lim` bounds the depth.
///
/// An object in an object stream (a type 2 entry) fails, as decoding object streams (DaeDaLus
/// `ObjStream`) isn't supported yet.
///
/// A stream's body is the `/Length` bytes after the `stream` line (DaeDaLus `StreamBody`),
/// where an indirect `/Length` is resolved within the batch; that is the only nested
/// resolution.
#[allow(clippy::too_many_arguments)]
fn resolve(
    module: &mut FormatModule,
    any_ws: FormatRef,
    simple_eol: FormatRef,
    natural: FormatRef,
    pdf_value: FormatRef,
    zlib: FormatRef,
    sections_type: ValueType,
    value_type: ValueType,
) -> [FormatRef; 2] {
    let u64_type = || ValueType::Base(BaseType::U64);
    let args = || {
        vec![
            (Label::Borrowed("base"), u64_type()),
            (Label::Borrowed("sections"), sections_type.clone()),
            (Label::Borrowed("obj"), u64_type()),
            (Label::Borrowed("gen"), u64_type()),
            (
                Label::Borrowed("resolving"),
                ValueType::Seq(Box::new(u64_type())),
            ),
            (Label::Borrowed("lim"), u64_type()),
        ]
    };
    let pass_on = || {
        vec![
            var("base"),
            var("sections"),
            var("obj"),
            var("gen"),
            var("resolving"),
            var("lim"),
        ]
    };
    let null_decl = || compute(variant("value", variant("null", Expr::UNIT)));
    let vt = value_type.clone();
    module.define_batch_with_args(
        [("pdf.resolve_ref", args()), ("pdf.resolved_decl", args())],
        [
            Box::new(move |&[_, decl]: &[FormatRef; 2]| {
                let entry = || Pattern::Variant("at".into(), Box::new(bind("at")));
                let packed = || Pattern::Variant("packed".into(), Box::new(Pattern::Wildcard));
                if_then_else(
                    or(
                        expr_eq(var("lim"), Expr::U64(0)), // "resolution too deep"
                        // "cycle": the host's check, which fails at once; without it, `lim`
                        // would still end the cycle, with the same result
                        seq_any(|o| expr_eq(o, var("obj")), var("resolving")),
                    ),
                    Format::Fail,
                    fmt_match(
                        xref_entry_for(var("sections"), var("obj")),
                        [
                            (
                                pat_some(entry()),
                                if_then_else(
                                    expr_eq(record_proj(var("at"), "gen"), var("gen")),
                                    with_relative_offset(
                                        Some(var("base")),
                                        record_proj(var("at"), "offset"),
                                        decl.call_args(pass_on()),
                                    ),
                                    null_decl(),
                                ),
                            ),
                            (
                                pat_some(packed()),
                                if_then_else(
                                    expr_eq(var("gen"), Expr::U64(0)),
                                    Format::Fail, // "object streams are not supported yet"
                                    null_decl(),
                                ),
                            ),
                            (Pattern::Wildcard, null_decl()),
                        ],
                    ),
                )
            }),
            Box::new(move |&[resolve_ref, _]: &[FormatRef; 2]| {
                let vt = vt.clone();
                // Nested resolution, with this object added to those being resolved
                let nested = || {
                    [
                        var("base"),
                        var("sections"),
                        append(var("resolving"), Expr::Seq(vec![var("obj")])),
                        sub(var("lim"), Expr::U64(1)),
                    ]
                };
                // DaeDaLus `StreamLen`: `LookupResolve "Length"`, a natural number
                let stream_len = chain(
                    dict_get(b"Length", var("header"), vt.clone()),
                    "_len_v",
                    chain(
                        resolve_val(resolve_ref, nested(), var("_len_v")),
                        "_len_r",
                        nat_value(var("_len_r")),
                    ),
                );
                // DaeDaLus `Stream`
                let stream = record_auto([
                    (
                        "header",
                        fmt_match(
                            var("_val"),
                            [
                                (
                                    Pattern::Variant("dict".into(), Box::new(bind("d"))),
                                    compute(var("d")),
                                ),
                                (Pattern::Wildcard, Format::Fail),
                            ],
                        ),
                    ),
                    ("__kw_stream", match_str(b"stream")),
                    ("__eol", simple_eol.call()),
                    ("_len", stream_len),
                    (
                        "body",
                        token(
                            slice(
                                var("_len"),
                                chain(
                                    repeat(Format::ANY_BYTE),
                                    "raw",
                                    apply_filters(zlib, var("header"), var("raw"), vt.clone()),
                                ),
                            ),
                            any_ws,
                        ),
                    ),
                    ("__kw_endstream", kw(b"endstream", any_ws)),
                ]);
                // DaeDaLus `TopDecl`, then `CheckExpected`
                map(
                    record_auto([
                        ("__ws", repeat(any_ws.call())),
                        ("_id", token(natural_u64(natural), any_ws)),
                        ("_gen", token(natural_u64(natural), any_ws)),
                        (
                            "__check",
                            if_then_else(
                                and(
                                    expr_eq(var("_id"), var("obj")),
                                    expr_eq(var("_gen"), var("gen")),
                                ),
                                Format::EMPTY,
                                Format::Fail, // "object and generation don't match the xref"
                            ),
                        ),
                        ("__kw_obj", kw(b"obj", any_ws)),
                        ("_val", pdf_value.call_args(vec![Expr::U64(32)])),
                        (
                            "decl",
                            alts_nondet([("stream", stream), ("value", compute(var("_val")))]),
                        ),
                        ("__kw_endobj", match_str(b"endobj")),
                    ]),
                    lambda("d", record_proj(var("d"), "decl")),
                )
            }),
        ],
    )
}

/// The cross-reference sections of a PDF, found from its end as the DaeDaLus host does: the
/// `%PDF-` header gives the base for all offsets, the last `startxref` gives the offset of the
/// newest section, and `/Prev` and `/XRefStm` links lead to the rest (see [`xref_chain`]).
///
/// Sits alongside `pdf.main` (a front-to-back parse), and leaves any bytes after the final
/// `%%EOF` unread.
fn pdf_cos(
    module: &mut FormatModule,
    pdf_end: FormatRef,
    xref_chain: FormatRef,
    resolve_ref: FormatRef,
) -> FormatRef {
    module.define_format(
        "pdf.cos",
        record_auto([
            ("header_offset", count_to(is_bytes(b"%PDF-"))),
            ("startxref", last_pdf_end(pdf_end)),
            (
                "_chain",
                xref_chain.call_args(vec![
                    var("header_offset"),
                    var("startxref"),
                    Expr::Seq(vec![]),
                    Expr::U64(64),
                ]),
            ),
            ("sections", compute(record_proj(var("_chain"), "sections"))),
            // the newest trailer's `/Root`, resolved
            (
                "root",
                fmt_match(
                    record_proj(
                        section_trailer(index_unchecked(var("sections"), Expr::U32(0))),
                        "root",
                    ),
                    [
                        (
                            pat_some(bind("root_ref")),
                            fmt_some(chain(
                                resolve_val(
                                    resolve_ref,
                                    [
                                        var("header_offset"),
                                        var("sections"),
                                        Expr::Seq(vec![]),
                                        Expr::U64(256),
                                    ],
                                    variant("ref", var("root_ref")),
                                ),
                                "root_v",
                                compute(var("root_v")),
                            )),
                        ),
                        (pat_none(), compute(expr_none())),
                    ],
                ),
            ),
        ]),
    )
}

pub fn main(module: &mut FormatModule) -> FormatRef {
    let [pdf_main, _pdf_cos, _resolve_ref] = top_formats(module);
    pdf_main
}

/// Defines the module's formats, returning the two top-level ones, `pdf.main` (front to back)
/// and `pdf.cos` (from the end, following the cross-reference chain), and `pdf.resolve_ref`.
fn top_formats(module: &mut FormatModule) -> [FormatRef; 3] {
    let simple_eol = simple_eol(module);
    let eol = eol(module, simple_eol);
    let comment = comment(module, eol);

    let any_ws = any_ws(module, eol, comment);

    let v_name = v_name(module, any_ws);

    let natural = natural(module);
    let number = number(module, natural);

    let [pdf_value, pdf_dict] = pdf_value(module, any_ws, eol, natural, number, v_name);
    let pdf_value_type = module.get_format_type(pdf_value.get_level()).clone();
    let stream = stream(module, simple_eol, any_ws, pdf_value_type.clone());
    let top_decl_def = module.define_format_args(
        "pdf.top_decl",
        vec![(Label::Borrowed("val"), pdf_value_type.clone())],
        alts([
            ("stream", stream.invoke_args([var("val")])),
            ("value", compute(var("val"))),
        ]),
    );
    let obj_decl = module.define_format(
        "pdf.object",
        record_auto([
            ("id", token(natural.call(), any_ws)),
            ("gen", token(natural.call(), any_ws)),
            ("__kw_obj", kw(b"obj", any_ws)),
            ("_val", pdf_value.call_args(vec![Expr::U64(32)])),
            ("obj", top_decl_def.call_args(vec![var("_val")])),
            ("__kw_end", kw(b"endobj", any_ws)),
        ]),
    );
    let cross_ref_section = cross_ref_section(module, any_ws, natural);
    let trailer = module.define_format(
        "pdf.trailer",
        monad_seq(
            kw(b"trailer", any_ws),
            pdf_dict.call_args(vec![Expr::U64(32)]),
        ),
    );

    // `pdf.cos`, the end-driven parse, alongside the front-to-back `pdf.main`
    let pdf_end = pdf_end(module, eol, natural);
    let deflate = doodle_formats::format::deflate::main(module);
    let zlib = doodle_formats::format::zlib::main(module, deflate);
    let xref_obj = xref_obj(
        module,
        any_ws,
        simple_eol,
        natural,
        pdf_value,
        zlib,
        pdf_value_type.clone(),
    );
    let cross_ref = cross_ref(
        module,
        any_ws,
        eol,
        cross_ref_section,
        pdf_dict,
        xref_obj,
        pdf_value_type.clone(),
    );
    let xref_chain = xref_chain(module, cross_ref);
    let sections_type = ValueType::Seq(Box::new(
        module.get_format_type(cross_ref.get_level()).clone(),
    ));
    let [resolve_ref, _resolved_decl] = resolve(
        module,
        any_ws,
        simple_eol,
        natural,
        pdf_value,
        zlib,
        sections_type,
        pdf_value_type.clone(),
    );
    let pdf_cos = pdf_cos(module, pdf_end, xref_chain, resolve_ref);

    let pdf_chunk = module.define_format(
        "pdf.chunk",
        record_auto([
            ("objects", repeat(obj_decl.call())),
            ("xref", cross_ref_section.call()),
            ("trailer", trailer.call()),
            ("__start_xref", then_eol(match_str(b"startxref"), eol)),
            ("declared_start_xref", then_eol(natural.call(), eol)),
            ("__kw_eof", kw(b"%%EOF", any_ws)),
        ]),
    );

    let pdf_main = module.define_format(
        "pdf.main",
        only(record_auto([
            (
                "version",
                skip_to(monad_seq(is_bytes(b"%PDF-"), number.call())),
            ),
            ("__ws", repeat(any_ws.call())),
            ("chunks", repeat(pdf_chunk.call())),
            // adding `Many AnyWS` here breaks matchtree because pdf_chunk can end in whitespace
        ])),
    );
    [pdf_main, pdf_cos, resolve_ref]
}

#[cfg(test)]
mod tests {
    use super::*;
    use doodle::{decoder::Compiler, read::ReadCtxt};

    /// Decodes each input with `skip_to(f)` and checks whether it succeeds.
    fn check_skip_to(module: &mut FormatModule, f: Format, cases: &[(&[u8], bool)]) {
        let top = module.define_format("test.skip_to", skip_to(f));
        let prog = Compiler::compile_program(module, &top.call()).expect("skip_to must compile");
        for (input, ok) in cases {
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                *ok,
                "decoding {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    /// `pdf.stream` accepts a dict followed by `stream`, an EOL, and a body running up to
    /// `endstream`, and rejects a non-dict value.
    #[test]
    fn stream_after_dict() {
        let mut module = FormatModule::new();
        let simple_eol = simple_eol(&mut module);
        let eol = eol(&mut module, simple_eol);
        let comment = comment(&mut module, eol);
        let any_ws = any_ws(&mut module, eol, comment);
        let v_name = v_name(&mut module, any_ws);
        let natural = natural(&mut module);
        let number = number(&mut module, natural);
        let [value, _dict] = pdf_value(&mut module, any_ws, eol, natural, number, v_name);
        let value_type = module.get_format_type(value.get_level()).clone();
        let stream = stream(&mut module, simple_eol, any_ws, value_type);
        let top = module.define_format(
            "test.stream",
            only(chain(
                value.call_args(vec![Expr::U64(32)]),
                "val",
                stream.invoke_args([var("val")]),
            )),
        );
        let prog = Compiler::compile_program(&module, &top.call()).expect("stream must compile");
        let cases: &[(&[u8], bool)] = &[
            (b"<< /Length 5 >>\nstream\r\nhello\nendstream", true),
            (b"<<>>stream\nendstream", true),
            (b"<<>>stream\nend stream endstrea endstream", true),
            (b"<<>>stream\nno terminator", false),
            (b"<<>>streamhelloendstream", false),
            (b"42 stream\nhelloendstream", false),
        ];
        for (input, ok) in cases {
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                *ok,
                "decoding {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    /// `pdf.xref` reads subsections of fixed-width 20-byte entries, with any of the three
    /// two-byte end-of-line forms, and rejects entries of the wrong width or with a bad flag.
    #[test]
    fn xref_section() {
        let mut module = FormatModule::new();
        let simple_eol = simple_eol(&mut module);
        let eol = eol(&mut module, simple_eol);
        let comment = comment(&mut module, eol);
        let any_ws = any_ws(&mut module, eol, comment);
        let natural = natural(&mut module);
        let xref = cross_ref_section(&mut module, any_ws, natural);
        let top = module.define_format("test.xref", only(xref.call()));
        let prog = Compiler::compile_program(&module, &top.call()).expect("xref must compile");
        let cases: &[(&[u8], bool)] = &[
            (b"xref\n0 1\n0000000000 65535 f\r\n", true),
            (
                b"xref\n0 2\n0000000000 65535 f \n0000000017 00000 n \r",
                true,
            ),
            (
                b"xref\n0 1\n0000000000 65535 f\r\n3 1\n0000000123 00002 n\r\n",
                true,
            ),
            (b"xref\n0 0\n", true),
            (b"xref\n", false),
            (b"xref\n0 2\n0000000000 65535 f\r\n", false),
            (b"xref\n0 1\n000000000 65535 f\r\n", false),
            (b"xref\n0 1\n0000000000 65535 x\r\n", false),
            (b"xref\n0 1\n0000000000 65535 f\n", false),
        ];
        for (input, ok) in cases {
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                *ok,
                "decoding {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    /// Builds `pdf.value` and `pdf.value.dict`, returning the dict format and the value type.
    fn dict_module(module: &mut FormatModule) -> (FormatRef, ValueType) {
        let simple_eol = simple_eol(module);
        let eol = eol(module, simple_eol);
        let comment = comment(module, eol);
        let any_ws = any_ws(module, eol, comment);
        let v_name = v_name(module, any_ws);
        let natural = natural(module);
        let number = number(module, natural);
        let [value, dict] = pdf_value(module, any_ws, eol, natural, number, v_name);
        let value_type = module.get_format_type(value.get_level()).clone();
        (dict, value_type)
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
            let (dict, value_type) = dict_module(&mut module);
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
                        dict_lookup(b"Size", var("d"), value_type),
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
        let (dict, value_type) = dict_module(&mut module);
        let top = module.define_format(
            "test.dict_get",
            only(chain(
                dict.call_args(vec![Expr::U64(32)]),
                "d",
                dict_get(b"Size", var("d"), value_type),
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
            let natural = natural(&mut module);
            let number = number(&mut module, natural);
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
        let simple_eol = simple_eol(&mut module);
        let eol = eol(&mut module, simple_eol);
        let comment = comment(&mut module, eol);
        let any_ws = any_ws(&mut module, eol, comment);
        let v_name = v_name(&mut module, any_ws);
        let natural = natural(&mut module);
        let number = number(&mut module, natural);
        let [value, _dict] = pdf_value(&mut module, any_ws, eol, natural, number, v_name);
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

    /// zlib of `hello hello hello hello` (compressed, with back-references)
    const HELLO_Z: &[u8] = &[
        0x78, 0xda, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x57, 0xc8, 0x40, 0x27, 0x01, 0x68, 0x03, 0x08,
        0xb1,
    ];
    /// zlib of `abc` (one stored block)
    const ABC_Z: &[u8] = &[
        0x78, 0x01, 0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63, 0x02, 0x4d, 0x01, 0x27,
    ];

    /// zlib of three 5-byte rows, each filtered with tag 2 (Up), as xref streams usually are
    const UP_Z: &[u8] = &[
        0x78, 0x9c, 0x63, 0x62, 0x64, 0x60, 0x10, 0x64, 0x60, 0x62, 0x60, 0x60, 0x48, 0x67, 0x60,
        0x62, 0x64, 0xe0, 0xec, 0x60, 0x06, 0x00, 0x05, 0xc4, 0x01, 0x15,
    ];
    /// The rows of [`UP_Z`] before filtering
    const UP_RAW: &[u8] = &[1, 0, 0, 17, 0, 1, 0, 0, 120, 0, 2, 0, 9, 0, 3];

    /// Parses a `pdf.value` that is a dict or `null` (as a `/DecodeParms` entry), then `rest`
    /// with the [`flate_decode_params`] record bound to `params`.
    fn with_flate_params(module: &mut FormatModule, rest: Format) -> Format {
        let simple_eol = simple_eol(module);
        let eol = eol(module, simple_eol);
        let comment = comment(module, eol);
        let any_ws = any_ws(module, eol, comment);
        let v_name = v_name(module, any_ws);
        let natural = natural(module);
        let number = number(module, natural);
        let [value, _dict] = pdf_value(module, any_ws, eol, natural, number, v_name);
        let value_type = module.get_format_type(value.get_level()).clone();
        chain(
            value.call_args(vec![Expr::U64(32)]),
            "v",
            chain(
                fmt_match(
                    var("v"),
                    [
                        (
                            Pattern::Variant("dict".into(), Box::new(bind("d"))),
                            compute(expr_some(var("d"))),
                        ),
                        (
                            Pattern::Variant("null".into(), Box::new(Pattern::Wildcard)),
                            compute(expr_none()),
                        ),
                    ],
                ),
                "param",
                chain(
                    compute(flate_decode_params(var("param"), value_type)),
                    "params",
                    rest,
                ),
            ),
        )
    }

    /// `flate_decode_params` takes each entry that is a natural number, and the default for an
    /// absent entry, an absent `/DecodeParms`, or an entry that isn't a natural number
    /// (including an indirect reference, until #355).
    #[test]
    fn flate_decode_params_defaults() {
        let cases: &[(&[u8], [u64; 4])] = &[
            (b"null", [1, 1, 8, 1]),
            (b"<<>>", [1, 1, 8, 1]),
            (b"<< /Predictor 12 /Columns 5 >>", [12, 1, 8, 5]),
            (b"<< /Colors 3 /BitsPerComponent 16 >>", [1, 3, 16, 1]),
            (b"<< /Predictor -2 /Columns 4. >>", [1, 1, 8, 4]),
            (b"<< /Predictor /Twelve /Colors 2.5 >>", [1, 1, 8, 1]),
            (b"<< /Columns 7 0 R >>", [1, 1, 8, 1]),
        ];
        for (input, expected) in cases {
            let mut module = FormatModule::new();
            let fields = ["predictor", "colors", "bpc", "columns"]
                .map(|label| record_proj(var("params"), label));
            let check = fmt_match(
                Expr::Tuple(fields.to_vec()),
                [
                    (
                        Pattern::Tuple(expected.iter().map(|n| Pattern::U64(*n)).collect()),
                        Format::EMPTY,
                    ),
                    (Pattern::Wildcard, Format::Fail),
                ],
            );
            let top = with_flate_params(&mut module, check);
            let top = module.define_format("test.flate_params", only(top));
            let prog = Compiler::compile_program(&module, &top.call()).expect("must compile");
            assert!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                "params of {:?}, expecting {expected:?}",
                String::from_utf8_lossy(input),
            );
        }
    }

    /// `png_unpredict` reconstructs PNG-filtered rows, checked against vectors made by a
    /// forward PNG filter (in Python) and decoded identically by the DaeDaLus host
    /// implementation (`formats/pdf/new/rust/src/filters/predictor.rs`). It fails on a tag
    /// over 4 and on a partial row, and gives nothing for no input.
    #[test]
    fn png_unpredict_cases() {
        let cases: &[([u64; 3], &[u8], Option<&[u8]>)] = &[
            // xref-like: 1 colour, 8 bits, 5 columns, every tag
            (
                [1, 8, 5],
                &[
                    0, 145, 73, 32, 138, 71, 1, 100, 140, 52, 72, 41, 2, 214, 50, 22, 233, 200, 3,
                    122, 121, 150, 251, 86, 4, 173, 133, 196, 255, 115, 2, 69, 2, 251, 180, 209, 4,
                    11, 146, 110, 97, 71,
                ],
                Some(&[
                    145, 73, 32, 138, 71, 100, 240, 36, 108, 149, 58, 34, 58, 85, 93, 151, 213, 29,
                    52, 158, 68, 28, 224, 223, 82, 137, 30, 219, 147, 35, 148, 176, 73, 170, 106,
                ]),
            ),
            // 3 colours (bpp 3), Sub/Average/Paeth need left and upper-left
            (
                [3, 8, 3],
                &[
                    1, 188, 55, 129, 232, 235, 53, 35, 39, 245, 4, 77, 196, 24, 24, 185, 86, 44,
                    178, 201, 3, 7, 145, 21, 6, 225, 160, 147, 127, 136, 4, 104, 242, 88, 192, 9,
                    13, 154, 120, 230, 2, 112, 227, 88, 128, 75, 195, 147, 93, 218,
                ],
                Some(&[
                    188, 55, 129, 164, 34, 182, 199, 73, 171, 9, 251, 153, 33, 180, 12, 77, 102,
                    213, 11, 14, 97, 28, 66, 214, 199, 211, 93, 115, 0, 185, 51, 75, 227, 97, 75,
                    67, 227, 227, 17, 179, 150, 166, 244, 168, 29,
                ]),
            ),
            // 16 bits (bpp 2)
            (
                [1, 16, 4],
                &[
                    4, 117, 34, 130, 24, 168, 179, 134, 184, 1, 232, 245, 88, 31, 216, 84, 122,
                    241, 3, 64, 152, 188, 82, 143, 130, 183, 208, 2, 41, 103, 205, 72, 49, 104,
                    203, 116,
                ],
                Some(&[
                    117, 34, 247, 58, 159, 237, 37, 165, 232, 245, 64, 20, 24, 104, 146, 89, 180,
                    18, 54, 101, 182, 232, 91, 112, 221, 121, 3, 173, 231, 80, 38, 228,
                ]),
            ),
            // 1 bit, 10 columns (row of 2 bytes, bpp 1)
            (
                [1, 1, 10],
                &[2, 201, 77, 4, 129, 90, 1, 152, 231, 3, 81, 110],
                Some(&[201, 77, 74, 164, 152, 127, 157, 252]),
            ),
            // 4 colours of 2 bits (bpp 1), 3 columns
            (
                [4, 2, 3],
                &[3, 222, 82, 135, 4, 140, 72, 176, 4, 17, 239, 84],
                Some(&[222, 193, 231, 106, 178, 151, 123, 161, 235]),
            ),
            // Paeth tie between above and upper-left: left 25, above 10, upper-left 20, so the
            // estimate is 15, at distances 10, 5 and 5, and the tie goes to above (10)
            ([1, 8, 2], &[0, 20, 10, 4, 5, 67], Some(&[20, 10, 25, 77])),
            // Paeth tie between left and upper-left: left 10, above 25, upper-left 20, so the
            // estimate is 15, at distances 5, 10 and 5, and the tie goes to left (10). (A tie
            // between left and above alone needs left == above, so its order isn't observable.)
            ([1, 8, 2], &[0, 20, 25, 4, 246, 89], Some(&[20, 25, 10, 99])),
            // tag 5
            ([1, 8, 2], &[0, 1, 2, 5, 3, 4], None),
            // a partial final row
            ([1, 8, 2], &[0, 1, 2, 0, 3], None),
            ([1, 8, 2], &[], Some(&[])),
        ];
        for ([colors, bpc, columns], input, expected) in cases {
            let params = Expr::Record(vec![
                (Label::Borrowed("predictor"), Expr::U64(12)),
                (Label::Borrowed("colors"), Expr::U64(*colors)),
                (Label::Borrowed("bpc"), Expr::U64(*bpc)),
                (Label::Borrowed("columns"), Expr::U64(*columns)),
            ]);
            let mut module = FormatModule::new();
            let top = module.define_format(
                "test.png_unpredict",
                chain(
                    png_unpredict(params),
                    "out",
                    match expected {
                        Some(bytes) => fmt_match(
                            var("out"),
                            [
                                (pattern_bytestring(bytes), Format::EMPTY),
                                (Pattern::Wildcard, Format::Fail),
                            ],
                        ),
                        None => Format::EMPTY,
                    },
                ),
            );
            let prog = Compiler::compile_program(&module, &top.call()).expect("must compile");
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                expected.is_some(),
                "png_unpredict with colors {colors}, bpc {bpc}, columns {columns} on {input:?}",
            );
        }
    }

    /// `supported_predictor` accepts no prediction, or a PNG predictor with at least one colour
    /// and column and a valid bit depth. Until #352, `flate_decode` fails on every predictor
    /// other than 1 whatever this says, so it is tested on its own.
    #[test]
    fn supported_predictor_cases() {
        let cases: &[([u64; 4], bool)] = &[
            ([1, 0, 3, 0], true),
            ([10, 1, 8, 1], true),
            ([15, 4, 16, 100], true),
            ([12, 3, 1, 5], true),
            ([2, 1, 8, 1], false),
            ([9, 1, 8, 1], false),
            ([16, 1, 8, 1], false),
            ([12, 0, 8, 1], false),
            ([12, 1, 3, 1], false),
            ([12, 1, 32, 1], false),
            ([12, 1, 8, 0], false),
        ];
        for ([predictor, colors, bpc, columns], expected) in cases {
            let params = Expr::Record(vec![
                (Label::Borrowed("predictor"), Expr::U64(*predictor)),
                (Label::Borrowed("colors"), Expr::U64(*colors)),
                (Label::Borrowed("bpc"), Expr::U64(*bpc)),
                (Label::Borrowed("columns"), Expr::U64(*columns)),
            ]);
            let mut module = FormatModule::new();
            let top = module.define_format(
                "test.supported_predictor",
                fmt_match(
                    supported_predictor(params),
                    [
                        (Pattern::Bool(*expected), Format::EMPTY),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                ),
            );
            let prog = Compiler::compile_program(&module, &top.call()).expect("must compile");
            assert!(
                prog.run(ReadCtxt::new(&[])).is_ok(),
                "supported_predictor({predictor}, {colors}, {bpc}, {columns}) should be {expected}"
            );
        }
    }

    /// `flate_decode` inflates zlib data, reverses a PNG predictor, and fails on corrupt data,
    /// on inflated data that isn't predictor rows, and on an unsupported predictor.
    #[test]
    fn flate_decode_inflates() {
        let hello: &[u8] = b"hello hello hello hello";
        let corrupt = [&HELLO_Z[..2], &[0xff, 0xff, 0xff][..]].concat();
        let cases: &[(&[u8], &[u8], Option<&[u8]>)] = &[
            (b"null", HELLO_Z, Some(hello)),
            (b"<<>>", ABC_Z, Some(b"abc")),
            (b"<< /Predictor 1 >>", ABC_Z, Some(b"abc")),
            (b"null", &corrupt, None),
            // the inflated text isn't predictor rows (23 bytes, and `h` is not a tag)
            (b"<< /Predictor 12 /Columns 5 >>", HELLO_Z, None),
            (b"<< /Predictor 12 /Columns 5 >>", UP_Z, Some(UP_RAW)),
            // Columns 3 makes rows of 4 bytes, which 18 is not a multiple of
            (b"<< /Predictor 12 /Columns 3 >>", UP_Z, None),
            (b"<< /Predictor 2 >>", HELLO_Z, None),
            (b"<< /Predictor 12 /Columns 0 >>", HELLO_Z, None),
        ];
        for (param, body, expected) in cases {
            let mut module = FormatModule::new();
            let deflate = doodle_formats::format::deflate::main(&mut module);
            let zlib = doodle_formats::format::zlib::main(&mut module, deflate);
            // `stream` separates the body from the param's trailing whitespace
            let check = chain(
                monad_seq(is_bytes(b"stream\n"), repeat(Format::ANY_BYTE)),
                "body",
                chain(
                    flate_decode(zlib, var("params"), var("body")),
                    "out",
                    // Where decoding should fail, any output is a test failure, so there is
                    // nothing to compare
                    match expected {
                        Some(bytes) => fmt_match(
                            var("out"),
                            [
                                (pattern_bytestring(bytes), Format::EMPTY),
                                (Pattern::Wildcard, Format::Fail),
                            ],
                        ),
                        None => Format::EMPTY,
                    },
                ),
            );
            let top = with_flate_params(&mut module, check);
            let top = module.define_format("test.flate_decode", only(top));
            let prog = Compiler::compile_program(&module, &top.call()).expect("must compile");
            let input = [*param, b" stream\n", *body].concat();
            assert_eq!(
                prog.run(ReadCtxt::new(&input)).is_ok(),
                expected.is_some(),
                "flate_decode with {:?}, expecting {:?}",
                String::from_utf8_lossy(param),
                expected.map(String::from_utf8_lossy),
            );
        }
    }

    /// A cross-reference section for [`build_pdf`], identified by its trailer's `/Size`, with
    /// optional `/Prev` and `/XRefStm` links to other sections by index. An index past the last
    /// section stands for an offset past the end of the file.
    ///
    /// It is a classic section, or with `stream`, a cross-reference stream object.
    struct Sec {
        size: u64,
        prev: Option<usize>,
        xrefstm: Option<usize>,
        stream: Option<Stm>,
    }

    /// The rest of a cross-reference stream's dictionary (other than `/Size` and the links),
    /// and its raw body. `/Length` is the body's length unless `dict` gives one.
    struct Stm {
        dict: String,
        data: Vec<u8>,
    }

    fn sec(size: u64, prev: Option<usize>, xrefstm: Option<usize>) -> Sec {
        Sec {
            size,
            prev,
            xrefstm,
            stream: None,
        }
    }

    fn stm(size: u64, prev: Option<usize>, dict: &str, data: &[u8]) -> Sec {
        Sec {
            size,
            prev,
            xrefstm: None,
            stream: Some(Stm {
                dict: dict.to_string(),
                data: data.to_vec(),
            }),
        }
    }

    /// The fields of each entry, as big-endian numbers of the widths `w`
    fn be_rows(w: &[usize], entries: &[&[u64]]) -> Vec<u8> {
        entries
            .iter()
            .flat_map(|fields| {
                w.iter()
                    .zip(fields.iter())
                    .flat_map(|(&w, &f)| f.to_be_bytes()[8 - w.min(8)..].to_vec())
                    .collect::<Vec<u8>>()
            })
            .collect()
    }

    /// `prefix`, a `%PDF-1.4` header, the sections `secs`, then a `startxref` block for each
    /// index in `startxrefs`, then `suffix`. Offsets are relative to the header, and links are
    /// written with ten digits, so a section's length doesn't depend on where its links point.
    fn build_pdf(prefix: &[u8], secs: &[Sec], startxrefs: &[usize], suffix: &[u8]) -> Vec<u8> {
        const HEADER: &[u8] = b"%PDF-1.4\n";
        let render = |sec: &Sec, offsets: &[usize]| {
            let link = |key: &str, ix: Option<usize>| match ix {
                Some(ix) => format!(
                    " /{key} {:010}",
                    offsets.get(ix).copied().unwrap_or(9_999_999)
                ),
                None => String::new(),
            };
            let links = format!("{}{}", link("Prev", sec.prev), link("XRefStm", sec.xrefstm));
            match &sec.stream {
                None => format!(
                    "xref\n0 1\n0000000000 65535 f\r\ntrailer\n<< /Size {}{links} >>\n",
                    sec.size,
                )
                .into_bytes(),
                Some(Stm { dict, data }) => {
                    let len = if dict.contains("/Length") {
                        String::new()
                    } else {
                        format!(" /Length {}", data.len())
                    };
                    [
                        format!(
                            "9 0 obj\n<< /Size {}{links} {dict}{len} >>\nstream\n",
                            sec.size
                        )
                        .as_bytes(),
                        data,
                        b"\nendstream\nendobj\n",
                    ]
                    .concat()
                }
            }
        };
        let mut offsets = Vec::new();
        let mut at = HEADER.len();
        for sec in secs {
            offsets.push(at);
            at += render(sec, &[]).len();
        }
        let mut out = [prefix, HEADER].concat();
        for sec in secs {
            out.extend(render(sec, &offsets));
        }
        for &ix in startxrefs {
            out.extend(format!("startxref\n{}\n%%EOF\n", offsets[ix]).into_bytes());
        }
        out.extend_from_slice(suffix);
        out
    }

    /// `pdf.cos` finds the last `startxref` (relative to the `%PDF-` header), and lists the
    /// sections reachable from it in precedence order: each section, then its `/XRefStm`
    /// sections, then its `/Prev` sections, as the DaeDaLus host merges them. It fails on a
    /// revisited section, an out-of-range offset, an unparsable final `startxref`, and a chain
    /// longer than its limit. Each case gives the expected `/Size`s, in order, or `None`.
    #[test]
    fn pdf_cos_follows_xref_chain() {
        let long_chain = |n: usize| -> Vec<Sec> {
            (0..n)
                .map(|i| sec(i as u64, i.checked_sub(1), None))
                .collect()
        };
        let cases: Vec<(&str, Vec<u8>, Option<Vec<u64>>)> = vec![
            (
                "one section",
                build_pdf(b"", &[sec(1, None, None)], &[0], b""),
                Some(vec![1]),
            ),
            (
                "a /Prev chain",
                build_pdf(b"", &[sec(1, None, None), sec(2, Some(0), None)], &[1], b""),
                Some(vec![2, 1]),
            ),
            (
                "/XRefStm takes precedence over /Prev",
                build_pdf(
                    b"",
                    &[
                        sec(1, None, None),
                        sec(2, None, None),
                        sec(3, Some(0), Some(1)),
                    ],
                    &[2],
                    b"",
                ),
                Some(vec![3, 2, 1]),
            ),
            (
                "the /Prev subtree comes after the /XRefStm subtree",
                build_pdf(
                    b"",
                    &[
                        sec(1, None, None),
                        sec(2, None, None),
                        sec(3, Some(0), None),
                        sec(4, Some(2), Some(1)),
                    ],
                    &[3],
                    b"",
                ),
                Some(vec![4, 2, 3, 1]),
            ),
            (
                "the last startxref is used",
                build_pdf(
                    b"",
                    &[sec(1, None, None), sec(2, Some(0), None)],
                    &[0, 1],
                    b"",
                ),
                Some(vec![2, 1]),
            ),
            (
                "the last startxref is used, even if older",
                build_pdf(
                    b"",
                    &[sec(1, None, None), sec(2, Some(0), None)],
                    &[1, 0],
                    b"",
                ),
                Some(vec![1]),
            ),
            (
                "bytes after the last %%EOF are ignored",
                build_pdf(b"", &[sec(1, None, None)], &[0], b"\ntrailing junk"),
                Some(vec![1]),
            ),
            (
                "offsets are relative to the %PDF- header",
                build_pdf(b"leading junk\n", &[sec(1, None, None)], &[0], b""),
                Some(vec![1]),
            ),
            (
                "a chain within the limit",
                build_pdf(b"", &long_chain(64), &[63], b""),
                { Some((0..64).rev().collect()) },
            ),
            (
                "a chain over the limit",
                build_pdf(b"", &long_chain(65), &[64], b""),
                None,
            ),
            (
                "a /Prev cycle",
                build_pdf(b"", &[sec(1, Some(0), None)], &[0], b""),
                None,
            ),
            (
                "two links to one section",
                build_pdf(
                    b"",
                    &[sec(1, None, None), sec(2, Some(0), Some(0))],
                    &[1],
                    b"",
                ),
                None,
            ),
            (
                "a /Prev past the end of the file",
                build_pdf(b"", &[sec(1, Some(5), None)], &[0], b""),
                None,
            ),
            (
                "an unparsable final startxref",
                build_pdf(
                    b"",
                    &[sec(1, None, None)],
                    &[0],
                    b"startxref\nnot a number\n%%EOF\n",
                ),
                None,
            ),
            (
                "no startxref",
                build_pdf(b"", &[sec(1, None, None)], &[], b""),
                None,
            ),
        ];
        let mut module = FormatModule::new();
        let [_pdf_main, pdf_cos, _resolve_ref] = top_formats(&mut module);
        for (name, input, expected) in cases {
            let sizes = flat_map(
                lambda(
                    "s",
                    expr_match(
                        var("s"),
                        [(
                            Pattern::Variant("old_xref".into(), Box::new(bind("x"))),
                            Expr::Seq(vec![record_lens(var("x"), &["trailer", "size"])]),
                        )],
                    ),
                ),
                record_proj(var("cos"), "sections"),
            );
            let check = match &expected {
                Some(sizes_expected) => fmt_match(
                    sizes,
                    [
                        (
                            Pattern::Seq(sizes_expected.iter().map(|n| Pattern::U64(*n)).collect()),
                            Format::EMPTY,
                        ),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                ),
                None => Format::EMPTY,
            };
            let top = chain(pdf_cos.call(), "cos", check);
            let prog = Compiler::compile_program(&module, &top).expect("must compile");
            assert_eq!(
                prog.run(ReadCtxt::new(&input)).is_ok(),
                expected.is_some(),
                "{name}: expecting {expected:?} from {:?}",
                String::from_utf8_lossy(&input)
            );
        }
    }

    /// [`HELLO_Z`]-style fixtures: four entries `0 0 0`, `1 15 0`, `1 300 0` and `2 3 1` with
    /// `/W [1 2 1]`, zlib-compressed plainly, and as PNG Up rows (predictor 12, 4 columns).
    const XREF_ROWS_Z: &[u8] = &[
        0x78, 0xda, 0x63, 0x60, 0x60, 0x60, 0x60, 0x64, 0xe0, 0x67, 0x60, 0x64, 0xd4, 0x61, 0x60,
        0x62, 0x60, 0x66, 0x04, 0x00, 0x01, 0xd8, 0x00, 0x45,
    ];
    const XREF_ROWS_UP_Z: &[u8] = &[
        0x78, 0xda, 0x63, 0x62, 0x00, 0x02, 0x26, 0x46, 0x06, 0x7e, 0x06, 0x26, 0x06, 0x46, 0x59,
        0x20, 0xeb, 0xff, 0x75, 0x46, 0x00, 0x06, 0xbd, 0x02, 0x0f,
    ];

    /// `pdf.cos` reads cross-reference streams (DaeDaLus `XRefObj`), alone and linked with
    /// classic sections either way. Each case gives, for each section in precedence order, its
    /// `/Size`, then (for a stream) each subsection's first object number followed by its
    /// entries as `type field2 field3` (`9 0 0` for a `null` entry), or `None` for a failure.
    #[test]
    fn pdf_cos_reads_xref_streams() {
        const W121: &str = "/Type /XRef /W [1 2 1]";
        let four: &[&[u64]] = &[&[0, 0, 0], &[1, 15, 0], &[1, 300, 0], &[2, 3, 1]];
        let four_out: Vec<u64> = vec![0, 0, 0, 0, 1, 15, 0, 1, 300, 0, 2, 3, 1];
        let rows = |w: &[usize], es: &[&[u64]]| be_rows(w, es);
        let one = |dict: &str, data: &[u8]| build_pdf(b"", &[stm(4, None, dict, data)], &[0], b"");
        let with = |head: &[u64], tail: &[u64]| [head, tail].concat();
        let cases: Vec<(&str, Vec<u8>, Option<Vec<u64>>)> = vec![
            (
                "an uncompressed stream, with the default /Index",
                one(W121, &rows(&[1, 2, 1], four)),
                Some(with(&[4], &four_out)),
            ),
            (
                "/FlateDecode",
                one(&format!("{W121} /Filter /FlateDecode"), XREF_ROWS_Z),
                Some(with(&[4], &four_out)),
            ),
            (
                "/FlateDecode in an array, with PNG Up rows",
                one(
                    &format!(
                        "{W121} /Filter [/FlateDecode] /DecodeParms << /Predictor 12 /Columns 4 >>"
                    ),
                    XREF_ROWS_UP_Z,
                ),
                Some(with(&[4], &four_out)),
            ),
            (
                "/DecodeParms in an array",
                one(
                    &format!(
                        "{W121} /Filter [/FlateDecode] /DecodeParms [<< /Predictor 12 /Columns 4 >>]"
                    ),
                    XREF_ROWS_UP_Z,
                ),
                Some(with(&[4], &four_out)),
            ),
            (
                "/Index with two subsections",
                one(
                    &format!("{W121} /Index [5 1 10 2]"),
                    &rows(&[1, 2, 1], &[&[1, 7, 0], &[1, 8, 0], &[2, 3, 4]]),
                ),
                Some(vec![4, 5, 1, 7, 0, 10, 1, 8, 0, 2, 3, 4]),
            ),
            (
                "a type of width 0 defaults to 1, a third field of width 0 to 0",
                one(
                    "/Type /XRef /W [0 2 0] /Index [0 2]",
                    &rows(&[2], &[&[15], &[300]]),
                ),
                Some(vec![4, 0, 1, 15, 0, 1, 300, 0]),
            ),
            (
                "an unknown type is null",
                one(
                    &format!("{W121} /Index [0 1]"),
                    &rows(&[1, 2, 1], &[&[7, 1, 1]]),
                ),
                Some(vec![4, 0, 9, 0, 0]),
            ),
            (
                "a fourth /W width is skipped, and bytes after the entries are ignored",
                one(
                    "/Type /XRef /W [1 2 1 3] /Index [0 2]",
                    &[
                        rows(&[1, 2, 1, 3], &[&[1, 15, 0, 99], &[1, 300, 0, 99]]),
                        b"junk".to_vec(),
                    ]
                    .concat(),
                ),
                Some(vec![4, 0, 1, 15, 0, 1, 300, 0]),
            ),
            (
                "a 9-byte field that fits in a u64",
                one(
                    "/Type /XRef /W [1 9 1] /Index [0 1]",
                    &[&[1, 0][..], &u64::MAX.to_be_bytes(), &[0]].concat(),
                ),
                Some(vec![4, 0, 1, u64::MAX, 0]),
            ),
            (
                "a 9-byte field that doesn't fit in a u64",
                one(
                    "/Type /XRef /W [1 9 1] /Index [0 1]",
                    &[&[1, 1][..], &[0; 8], &[0]].concat(),
                ),
                None,
            ),
            (
                "a required field of width 0",
                one(
                    "/Type /XRef /W [1 0 1] /Index [0 1]",
                    &rows(&[1, 1], &[&[1, 0]]),
                ),
                None,
            ),
            (
                "too few bytes for the entries",
                one(W121, &rows(&[1, 2, 1], &four[..3])),
                None,
            ),
            (
                "an /Index of odd length",
                one(&format!("{W121} /Index [0 4 9]"), &rows(&[1, 2, 1], four)),
                None,
            ),
            (
                "not /Type /XRef",
                one("/Type /ObjStm /W [1 2 1]", &rows(&[1, 2, 1], four)),
                None,
            ),
            (
                "an indirect /Length (until #355)",
                one(&format!("{W121} /Length 5 0 R"), &rows(&[1, 2, 1], four)),
                None,
            ),
            (
                "an unsupported filter",
                one(
                    &format!("{W121} /Filter /ASCIIHexDecode"),
                    &rows(&[1, 2, 1], four),
                ),
                None,
            ),
            (
                "two filters",
                one(
                    &format!("{W121} /Filter [/FlateDecode /FlateDecode]"),
                    XREF_ROWS_Z,
                ),
                None,
            ),
            (
                "a stream's /Prev to a classic section",
                build_pdf(
                    b"",
                    &[
                        sec(1, None, None),
                        stm(4, Some(0), W121, &rows(&[1, 2, 1], four)),
                    ],
                    &[1],
                    b"",
                ),
                Some(with(&with(&[4], &four_out), &[1])),
            ),
            (
                "a classic section's /XRefStm to a stream (a hybrid file)",
                build_pdf(
                    b"",
                    &[
                        stm(4, None, W121, &rows(&[1, 2, 1], four)),
                        sec(2, None, Some(0)),
                    ],
                    &[1],
                    b"",
                ),
                Some(with(&[2, 4], &four_out)),
            ),
        ];
        let mut module = FormatModule::new();
        let [_pdf_main, pdf_cos, _resolve_ref] = top_formats(&mut module);
        let seq1 = |e: Expr| Expr::Seq(vec![e]);
        let entry = |name: &'static str, f2: &'static str, f3: &'static str| {
            (
                Pattern::Variant(name.into(), Box::new(bind("e"))),
                Expr::Seq(vec![
                    Expr::U64(match name {
                        "free" => 0,
                        "in_use" => 1,
                        _ => 2,
                    }),
                    record_proj(var("e"), f2),
                    record_proj(var("e"), f3),
                ]),
            )
        };
        let entries = flat_map(
            lambda(
                "entry",
                expr_match(
                    var("entry"),
                    [
                        entry("free", "obj", "gen"),
                        entry("in_use", "offset", "gen"),
                        entry("compressed", "container_obj", "obj_index"),
                        (
                            Pattern::Variant("null".into(), Box::new(Pattern::Wildcard)),
                            Expr::Seq(vec![Expr::U64(9), Expr::U64(0), Expr::U64(0)]),
                        ),
                    ],
                ),
            ),
            record_proj(var("sub"), "entries"),
        );
        let summary = flat_map(
            lambda(
                "s",
                expr_match(
                    var("s"),
                    [
                        (
                            Pattern::Variant("old_xref".into(), Box::new(bind("x"))),
                            seq1(record_lens(var("x"), &["trailer", "size"])),
                        ),
                        (
                            Pattern::Variant("new_xref".into(), Box::new(bind("x"))),
                            append(
                                seq1(record_lens(var("x"), &["trailer", "size"])),
                                flat_map(
                                    lambda(
                                        "sub",
                                        append(
                                            seq1(record_proj(var("sub"), "first_id")),
                                            entries.clone(),
                                        ),
                                    ),
                                    record_proj(var("x"), "xref"),
                                ),
                            ),
                        ),
                    ],
                ),
            ),
            record_proj(var("cos"), "sections"),
        );
        for (name, input, expected) in cases {
            let check = match &expected {
                Some(out) => fmt_match(
                    summary.clone(),
                    [
                        (
                            Pattern::Seq(out.iter().map(|n| Pattern::U64(*n)).collect()),
                            Format::EMPTY,
                        ),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                ),
                None => Format::EMPTY,
            };
            let top = chain(pdf_cos.call(), "cos", check);
            let prog = Compiler::compile_program(&module, &top).expect("must compile");
            assert_eq!(
                prog.run(ReadCtxt::new(&input)).is_ok(),
                expected.is_some(),
                "{name}: expecting {expected:?} from {:?}",
                String::from_utf8_lossy(&input)
            );
        }
    }

    /// An xref entry for [`build_objects`]: an object with this text between `obj` and
    /// `endobj`, a free entry, or an entry pointing at the offset of another object.
    enum Obj {
        Def(&'static [u8]),
        Free,
        At(u64),
    }

    /// A `%PDF-1.4` file of incremental sections, oldest first: each writes its `Def` objects,
    /// then a classic xref listing all its entries (as `(number, generation, entry)`), and a
    /// trailer with `/Root 1 0 R` and a `/Prev` to the section before; then a `startxref` to
    /// the last. Each object is written as `N G obj\n…\nendobj\n`.
    fn build_objects(sections: &[&[(u64, u64, Obj)]]) -> Vec<u8> {
        let mut out = b"%PDF-1.4\n".to_vec();
        let mut offsets = std::collections::BTreeMap::new();
        let mut prev = None;
        for entries in sections {
            for (n, g, obj) in entries.iter() {
                if let Obj::Def(body) = obj {
                    offsets.insert(*n, out.len());
                    out.extend(format!("{n} {g} obj\n").into_bytes());
                    out.extend_from_slice(body);
                    out.extend_from_slice(b"\nendobj\n");
                }
            }
            let xref_at = out.len();
            out.extend_from_slice(b"xref\n");
            for (n, g, obj) in entries.iter() {
                let line = match obj {
                    Obj::Def(_) => format!("{:010} {g:05} n\r\n", offsets[n]),
                    Obj::At(m) => format!("{:010} {g:05} n\r\n", offsets[m]),
                    Obj::Free => format!("0000000000 {g:05} f\r\n"),
                };
                out.extend(format!("{n} 1\n{line}").into_bytes());
            }
            let prev_link = prev.map_or(String::new(), |p| format!(" /Prev {p}"));
            out.extend(format!("trailer\n<< /Size 100 /Root 1 0 R{prev_link} >>\n").into_bytes());
            prev = Some(xref_at);
        }
        out.extend(format!("startxref\n{}\n%%EOF\n", prev.unwrap()).into_bytes());
        out
    }

    /// What resolving a reference should give, for [`resolve_ref_cases`]
    enum Resolved {
        Null,
        Number(&'static [u8]),
        /// a value of this kind (`pdf.value` variant)
        Kind(&'static str),
        StreamOk(&'static [u8]),
        Unsupported(&'static [u8]),
        Fails,
    }

    /// `pdf.resolve_ref` follows the DaeDaLus host: the newest entry decides; a missing, free
    /// or other-generation object is `null`; an object numbered differently from its xref
    /// entry fails; a stream's body is read by its (possibly indirect) `/Length` and decoded,
    /// or reported `unsupported`; and a cycle, a too-deep resolution, or an object in an
    /// object stream fails. Each case resolves `(number, generation)` with a depth limit.
    #[test]
    fn resolve_ref_cases() {
        use Obj::*;
        use Resolved::*;
        const CATALOG: (u64, u64, Obj) = (1, 0, Def(b"<< /Type /Catalog >>"));
        let flate_dict = format!(
            "<< /Length {} /Filter /FlateDecode >>\nstream\n",
            HELLO_Z.len()
        );
        let flate = [flate_dict.as_bytes(), HELLO_Z, b"\nendstream"]
            .concat()
            .leak();
        let base: Vec<u8> = build_objects(&[&[
            CATALOG,
            (2, 0, Def(b"42")),
            (3, 0, Free),
            (4, 0, At(2)),
            (5, 0, Def(b"<< /Length 5 >>\nstream\nhello\nendstream")),
            (6, 0, Def(b"<< /Length 7 0 R >>\nstream\nhello\nendstream")),
            (7, 0, Def(b"5")),
            (8, 0, Def(flate)),
            (9, 0, Def(b"<< /Length 5 /Filter /DCTDecode >>\nstream\nhello\nendstream")),
            (
                10,
                0,
                Def(b"<< /Length 5 /Filter /FlateDecode /DecodeParms << /Predictor 2 >> >>\nstream\nhello\nendstream"),
            ),
            (
                11,
                0,
                Def(b"<< /Length 5 /Filter [/LZWDecode /FlateDecode] >>\nstream\nhello\nendstream"),
            ),
            (12, 0, Def(b"<< /Length 12 0 R >>\nstream\nhello\nendstream")),
            (13, 0, Def(b"<< /Length 5 0 R >>\nstream\nhello\nendstream")),
            (14, 0, Def(b"<< /Length 99 0 R >>\nstream\nhello\nendstream")),
            (15, 0, Def(b"<< /Length 16 0 R >>\nstream\nhello\nendstream")),
            (16, 0, Def(b"7 0 R")),
            (17, 1, Def(b"(gen 1)")),
            (18, 0, Def(b"<< /Length 5 /Filter /FlateDecode >>\nstream\nhello\nendstream")),
            (
                19,
                0,
                Def(b"<< /Length 5 /Filter [/FlateDecode /DCTDecode] >>\nstream\nhello\nendstream"),
            ),
        ]]);
        let updated: Vec<u8> = build_objects(&[
            &[CATALOG, (2, 0, Def(b"42")), (3, 0, Def(b"3"))],
            &[(2, 0, Def(b"43")), (3, 0, Free)],
        ]);
        let cases: Vec<(&str, &[u8], (u64, u64), u64, Resolved)> = vec![
            ("a direct value", &base, (2, 0), 8, Number(b"42")),
            ("no entry", &base, (50, 0), 8, Null),
            ("a free entry", &base, (3, 0), 8, Null),
            ("another generation", &base, (2, 1), 8, Null),
            ("a generation over 0", &base, (17, 1), 8, Kind("string")),
            ("an entry at another object", &base, (4, 0), 8, Fails),
            ("a stream", &base, (5, 0), 8, StreamOk(b"hello")),
            ("an indirect /Length", &base, (6, 0), 8, StreamOk(b"hello")),
            ("an indirect /Length, too deep", &base, (6, 0), 1, Fails),
            (
                "/FlateDecode",
                &base,
                (8, 0),
                8,
                StreamOk(b"hello hello hello hello"),
            ),
            (
                "an unsupported filter",
                &base,
                (9, 0),
                8,
                Unsupported(b"/DCTDecode"),
            ),
            (
                "an unsupported predictor",
                &base,
                (10, 0),
                8,
                Unsupported(b"/FlateDecode (with params)"),
            ),
            ("two filters", &base, (11, 0), 8, Unsupported(b"/LZWDecode")),
            (
                "two filters, the first /FlateDecode",
                &base,
                (19, 0),
                8,
                Unsupported(b"/FlateDecode"),
            ),
            ("a /Length that is itself", &base, (12, 0), 8, Fails),
            ("a /Length that is a stream", &base, (13, 0), 8, Fails),
            ("a /Length that is null", &base, (14, 0), 8, Fails),
            ("a /Length that is a reference", &base, (15, 0), 8, Fails),
            (
                "/FlateDecode of data that isn't zlib",
                &base,
                (18, 0),
                8,
                Fails,
            ),
            (
                "a newer section's object",
                &updated,
                (2, 0),
                8,
                Number(b"43"),
            ),
            ("a newer section's free entry", &updated, (3, 0), 8, Null),
            (
                "an older section's object",
                &updated,
                (1, 0),
                8,
                Kind("dict"),
            ),
        ];
        let mut module = FormatModule::new();
        let [_pdf_main, pdf_cos, resolve_ref] = top_formats(&mut module);
        for (name, input, (obj, gen_), lim, expected) in cases {
            let value = |p: Pattern| Pattern::Variant("value".into(), Box::new(p));
            let body = |p: Pattern| {
                fmt_match(
                    var("d"),
                    [
                        (
                            Pattern::Variant("stream".into(), Box::new(bind("s"))),
                            fmt_match(
                                record_proj(var("s"), "body"),
                                [(p, Format::EMPTY), (Pattern::Wildcard, Format::Fail)],
                            ),
                        ),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                )
            };
            let is = |p: Pattern| {
                fmt_match(
                    var("d"),
                    [(p, Format::EMPTY), (Pattern::Wildcard, Format::Fail)],
                )
            };
            let (check, ok) = match &expected {
                Null => (
                    is(value(Pattern::Variant(
                        "null".into(),
                        Box::new(Pattern::Wildcard),
                    ))),
                    true,
                ),
                Kind(kind) => (
                    is(value(Pattern::Variant(
                        (*kind).into(),
                        Box::new(Pattern::Wildcard),
                    ))),
                    true,
                ),
                Number(n) => (
                    is(value(Pattern::Variant(
                        "number".into(),
                        Box::new(pattern_bytestring(n)),
                    ))),
                    true,
                ),
                StreamOk(b) => (
                    body(Pattern::Variant(
                        "ok".into(),
                        Box::new(pattern_bytestring(b)),
                    )),
                    true,
                ),
                Unsupported(b) => (
                    body(Pattern::Variant(
                        "unsupported".into(),
                        Box::new(pattern_bytestring(b)),
                    )),
                    true,
                ),
                Fails => (Format::EMPTY, false),
            };
            let top = chain(
                pdf_cos.call(),
                "cos",
                chain(
                    resolve_ref.call_args(vec![
                        record_proj(var("cos"), "header_offset"),
                        record_proj(var("cos"), "sections"),
                        Expr::U64(obj),
                        Expr::U64(gen_),
                        Expr::Seq(vec![]),
                        Expr::U64(lim),
                    ]),
                    "d",
                    check,
                ),
            );
            let prog = Compiler::compile_program(&module, &top).expect("must compile");
            assert_eq!(
                prog.run(ReadCtxt::new(input)).is_ok(),
                ok,
                "{name}: resolving {obj} {gen_} in {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    /// A `%PDF-1.5` file whose only section is a cross-reference stream: object 1 (the text
    /// `obj1`) at its offset, and object 2 packed in object stream 5 (which isn't there, as
    /// resolving a packed object fails before reaching it), with the trailer's `/Root` as
    /// given.
    fn packed_pdf(root: &str, obj1: &str) -> Vec<u8> {
        let header = b"%PDF-1.5\n".to_vec();
        let obj1_at = header.len();
        let obj1 = format!("1 0 obj\n{obj1}\nendobj\n").into_bytes();
        let stream_at = obj1_at + obj1.len();
        let rows = be_rows(
            &[1, 2, 1],
            &[&[0, 0, 0], &[1, obj1_at as u64, 0], &[2, 5, 0]],
        );
        let stream = [
            format!(
                "9 0 obj\n<< /Type /XRef /Size 3 /W [1 2 1] /Root {root} /Length {} >>\nstream\n",
                rows.len()
            )
            .into_bytes(),
            rows,
            b"\nendstream\nendobj\n".to_vec(),
        ]
        .concat();
        [
            header,
            obj1,
            stream,
            format!("startxref\n{stream_at}\n%%EOF\n").into_bytes(),
        ]
        .concat()
    }

    /// `pdf.cos` resolves the newest trailer's `/Root` (here a dict, or `null` for a missing
    /// object), through classic and stream sections alike; and an object packed in an object
    /// stream fails to resolve (until `ObjStream` is supported), unless its generation isn't
    /// `0`, which makes it `null`. Each case gives the expected `root` value's kind (`None`
    /// for no `/Root`), or fails.
    #[test]
    fn pdf_cos_resolves_root() {
        let classic = |root: &str| {
            let mut out = build_objects(&[&[(1, 0, Obj::Def(b"<< /Type /Catalog >>"))]]);
            if root != "1 0 R" {
                let at = out.windows(9).position(|w| w == b"/Root 1 0").unwrap();
                out.splice(at..at + 11, format!("/Root {root}").into_bytes());
            }
            out
        };
        let no_root = build_pdf(b"", &[sec(1, None, None)], &[0], b"");
        let cases: Vec<(&str, Vec<u8>, Option<Option<&str>>)> = vec![
            (
                "a classic file's catalog",
                classic("1 0 R"),
                Some(Some("dict")),
            ),
            (
                "offsets are relative to the %PDF- header",
                [&b"leading junk\n"[..], &classic("1 0 R")].concat(),
                Some(Some("dict")),
            ),
            (
                "a missing /Root object",
                classic("7 0 R"),
                Some(Some("null")),
            ),
            ("no /Root", no_root, Some(None)),
            (
                "an xref stream's /Root at an offset",
                packed_pdf("1 0 R", "<< /Type /Catalog >>"),
                Some(Some("dict")),
            ),
            (
                "a /Root packed in an object stream",
                packed_pdf("2 0 R", "<< /Type /Catalog >>"),
                None,
            ),
            (
                "a packed object of another generation",
                packed_pdf("2 1 R", "<< /Type /Catalog >>"),
                Some(Some("null")),
            ),
            (
                "a /Root that is a stream",
                packed_pdf("1 0 R", "<< /Length 2 >>\nstream\nab\nendstream"),
                None,
            ),
        ];
        let mut module = FormatModule::new();
        let [_pdf_main, pdf_cos, _resolve_ref] = top_formats(&mut module);
        for (name, input, expected) in cases {
            let check = match expected {
                Some(Some(kind)) => fmt_match(
                    record_proj(var("cos"), "root"),
                    [
                        (
                            pat_some(Pattern::Variant(kind.into(), Box::new(Pattern::Wildcard))),
                            Format::EMPTY,
                        ),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                ),
                Some(None) => fmt_match(
                    record_proj(var("cos"), "root"),
                    [
                        (pat_none(), Format::EMPTY),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                ),
                None => Format::EMPTY,
            };
            let top = chain(pdf_cos.call(), "cos", check);
            let prog = Compiler::compile_program(&module, &top).expect("must compile");
            assert_eq!(
                prog.run(ReadCtxt::new(&input)).is_ok(),
                expected.is_some(),
                "{name}: expecting {expected:?} from {:?}",
                String::from_utf8_lossy(&input)
            );
        }
    }

    /// `skip_to` stops at the first offset where its format matches, including offset 0 and
    /// after a partial match, and fails if there is no such offset. The format is the one
    /// `pdf.main` skips to, whose trailing `number` needs unbounded lookahead.
    #[test]
    fn skip_to_finds_first_match() {
        let long = [vec![b'x'; 1000], b"%PDF-7".to_vec()].concat();
        let cases: &[(&[u8], bool)] = &[
            (b"%PDF-1.7", true),
            (b"garbage\n%PDF-4", true),
            (b"%PDF%PDF-2", true),
            (b"%PDF-", false),
            (b"no header here", false),
            (b"", false),
            (&long, true),
        ];
        let mut module = FormatModule::new();
        let natural = natural(&mut module);
        let number = number(&mut module, natural);
        check_skip_to(
            &mut module,
            monad_seq(is_bytes(b"%PDF-"), number.call()),
            cases,
        );
    }
}
