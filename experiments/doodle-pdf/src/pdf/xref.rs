//! Cross-reference sections and streams and the trailer chain: DaeDaLus `PdfXRef.ddl`.

use doodle::{BaseType, Expr, Format, FormatRef, Label, Pattern, ValueType, helper::*};
use doodle_numexpr_macro::numexpr;

use super::PdfModule;
use super::combinators::{interpret, match_str, void};
use super::filters::apply_filters;
use super::lexical::{ASCII_CR, ASCII_LF, SIMPLE_WS, decimal_value, kw, read_nat, token};
use super::value::{
    dict_get, dict_lookup, dict_name_is, nat_value, natural_u64, number_as_nat, numeric_to_u64,
};

/// Cross-reference table: `xref` followed by one or more subsections.
///
/// Prototype: only the classic table form is handled (not cross-reference streams).
pub(super) fn cross_ref_section(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let natural = pm.natural();
    let module = pm.module();
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

/// DaeDaLus `TrailerDict`, given a `pdf.value.dict` result `dict`: the `size`, `root`, `prev`
/// and `xrefstm` entries, and the whole dict as `all`. The `/Encrypt` and `/ID` entries
/// (`TrailerDictEncrypt`) aren't extracted.
///
/// `size` is required and must be a natural number. `root` must be a reference if present.
/// `prev` and `xrefstm` are `None` if absent or not a natural number, as DaeDaLus `Optional`
/// gives. DaeDaLus resolves an indirect `/XRefStm`; until #355 that gives `None` here.
fn trailer_dict(dict: Expr) -> Format {
    let optional_nat = |key: &[u8]| {
        expr_match(
            dict_lookup(key, dict.clone()),
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
                dict_get(b"Size", dict.clone()),
                "size",
                nat_value(var("size")),
            ),
        ),
        (
            "root",
            fmt_match(
                dict_lookup(b"Root", dict.clone()),
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
fn xref_index(header: Expr) -> Format {
    let u64_seq = ValueType::Seq(Box::new(ValueType::Base(BaseType::U64)));
    // DaeDaLus `LookupNats "Index" header`, as an `Option`
    let index_nats = expr_match(
        dict_lookup(b"Index", header.clone()),
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
        chain(dict_get(b"Size", header), "size", nat_value(var("size"))),
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
fn xref_widths(header: Expr) -> Format {
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
                dict_lookup(b"W", header),
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

/// [`apply_filters`] for a cross-reference stream, whose filters must all be applied (DaeDaLus
/// `str.body is ok`): the decoded bytes, failing if they're `unsupported`.
fn xref_stream_filters(zlib: FormatRef, header: Expr, raw: Expr) -> Format {
    chain(
        apply_filters(zlib, header, raw, Expr::Bool(false)),
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
pub(super) fn xref_obj(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let simple_eol = pm.simple_eol();
    let natural = pm.natural();
    let pdf_value = pm.pdf_value();
    let zlib = pm.zlib();
    let module = pm.module();
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
                chain(dict_get(b"Length", header()), "len", nat_value(var("len"))),
            ),
            (
                "_body",
                token(
                    slice(
                        var("_len"),
                        chain(
                            repeat(Format::ANY_BYTE),
                            "raw",
                            xref_stream_filters(zlib, header(), var("raw")),
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
                    dict_name_is(b"Type", b"XRef", header()),
                    Format::EMPTY,
                    Format::Fail, // "not /Type /XRef"
                ),
            ),
            ("_index", xref_index(header())),
            ("_widths", xref_widths(header())),
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
            ("trailer", trailer_dict(header())),
        ]),
    )
}

/// DaeDaLus `CrossRef`: the cross-reference section found at an offset, either `old_xref`
/// (`CrossRefAndTrailer`: an `xref` table, then `trailer` and its dict) or `new_xref` (a
/// cross-reference stream, [`xref_obj`]), trying them in that order (DaeDaLus `First`).
pub(super) fn cross_ref(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let eol = pm.eol();
    let xref_table = pm.cross_ref_section();
    let pdf_dict = pm.pdf_dict();
    let xref_obj = xref_obj(pm);
    let module = pm.module();
    let just_white = union([void(byte_in(SIMPLE_WS)), eol.call()]);
    let old_xref = record_auto([
        // DaeDaLus `CrossRefSection` allows whitespace and comments before `xref`
        ("xref", monad_seq(repeat(any_ws.call()), xref_table.call())),
        // ... but only whitespace (no comments) before `trailer`
        ("__ws", repeat(just_white)),
        ("__kw_trailer", kw(b"trailer", any_ws)),
        ("_dict", pdf_dict.call_args(vec![Expr::U64(32)])),
        ("trailer", trailer_dict(var("_dict"))),
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
pub(super) fn xref_chain(pm: &mut PdfModule<'_>) -> FormatRef {
    let cross_ref = pm.cross_ref();
    let module = pm.module();
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
pub(super) fn section_trailer(section: Expr) -> Expr {
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

#[cfg(test)]
mod tests {
    use super::*;

    use doodle::{decoder::Compiler, read::ReadCtxt};

    use doodle::FormatModule;

    use crate::pdf::combinators::only;
    use crate::pdf::test_support::{Sec, be_rows, build_pdf, sec, stm};

    /// `pdf.xref` reads subsections of fixed-width 20-byte entries, with any of the three
    /// two-byte end-of-line forms, and rejects entries of the wrong width or with a bad flag.
    #[test]
    fn xref_section() {
        let mut module = FormatModule::new();
        let xref = PdfModule::new(&mut module).cross_ref_section();
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
        let pdf_cos = PdfModule::new(&mut module).cos();
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
        let pdf_cos = PdfModule::new(&mut module).cos();
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
}
