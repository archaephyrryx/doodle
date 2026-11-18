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
fn nat_n(len: u32) -> Format {
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
        excluding(repeat_count(Expr::U8(3), byte_in(b'0'..=b'7')), repeat_count(Expr::U8(2), octal_val())),
        excluding(repeat_count(Expr::U8(2), byte_in(b'0'..=b'7')), seq([octal_val()])),
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
fn skip_to(f: Format) -> Format {
    Format::SkipTo(Box::new(f))
}

/// Daedalus `CountTo P 0`: consumes bytes up to the first offset at which `p` matches,
/// leaving `p` unconsumed, and returns the number of bytes consumed.
///
/// `p` must have bounded lookahead (`PeekNot` rejects unbounded lookahead). Daedalus
/// `CountTo (KW s)` only needs `Match s` here, since the trailing `Many AnyWS` of `KW`
/// always succeeds.
///
/// A recursive `CountTo` (one call per byte) would hit the recursion limit, so this
/// repeats a guarded byte instead and measures the result. The skipped bytes are
/// materialized only to be counted.
fn count_to(p: Format) -> Format {
    chain(
        repeat(monad_seq(Format::PeekNot(Box::new(p)), ANY_BYTE)),
        "_skipped",
        compute(seq_length(var("_skipped"))),
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
/// `header = val is dict` narrows it. Like the Daedalus definition, this leaves the `endstream`
/// keyword unconsumed.
fn stream(
    module: &mut FormatModule,
    simple_eol: FormatRef,
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
                        count_to(match_str(b"endstream")),
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
            ("offset", nat_n(10)),
            ("__sp0", is_byte(b' ')),
            ("gen", nat_n(5)),
            ("__sp1", is_byte(b' ')),
            (
                "in_use",
                interpret([
                    (is_byte(b'n'), Expr::Bool(true)),
                    (is_byte(b'f'), Expr::Bool(false)),
                ]),
            ),
            (
                "__eol",
                union([
                    void(is_bytes(b" \r")),
                    void(is_bytes(b" \n")),
                    void(is_bytes(b"\r\n")),
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
        monad_seq(kw(b"xref", any_ws), repeat1(subsection.call())),
    )
}

pub fn main(module: &mut FormatModule) -> FormatRef {
    let simple_eol = simple_eol(module);
    let eol = eol(module, simple_eol);
    let comment = comment(module, eol);

    let any_ws = any_ws(module, eol, comment);

    let v_name = v_name(module, any_ws);

    let natural = natural(module);
    let number = number(module, natural);

    let [pdf_value, pdf_dict] = pdf_value(module, any_ws, eol, natural, number, v_name);
    let pdf_value_type = module.get_format_type(pdf_value.get_level()).clone();
    let stream = stream(module, simple_eol, pdf_value_type.clone());
    let top_decl_def = module.define_format_args(
        "pdf.top_decl",
        vec![(Label::Borrowed("val"), pdf_value_type)],
        alts([
            ("stream", chain(
                stream.invoke_args([var("val")]),
                "s",
                monad_seq(kw(b"endstream", any_ws), compute(var("s"))),
            )),
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

    module.define_format(
        "pdf.main",
        only(record_auto([
            (
                "version",
                skip_to(monad_seq(is_bytes(b"%PDF-"), number.call())),
            ),
            ("__ws", repeat(any_ws.call())),
            ("chunks", repeat(pdf_chunk.call())),
        ])),
    )
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
    /// `endstream` (consumed by the test, not by `pdf.stream`), and rejects a non-dict value.
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
        let stream = stream(&mut module, simple_eol, value_type);
        let top = module.define_format(
            "test.stream",
            only(chain(
                value.call_args(vec![Expr::U64(32)]),
                "val",
                chain(
                    stream.invoke_args([var("val")]),
                    "s",
                    monad_seq(match_str(b"endstream"), compute(var("s"))),
                ),
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
            (b"xref\n0 2\n0000000000 65535 f \n0000000017 00000 n \r", true),
            (b"xref\n0 1\n0000000000 65535 f\r\n3 1\n0000000123 00002 n\r\n", true),
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
