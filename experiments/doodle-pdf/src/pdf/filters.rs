//! Stream filters: DaeDaLus `ApplyFilters` and `FlateDecode` (`PdfDecl.ddl`), with PNG predictors.

use doodle::{BaseType, Expr, Format, FormatRef, Label, Pattern, ValueType, helper::*};
use doodle_numexpr_macro::numexpr;

use super::PdfModule;
use super::value::{dict_lookup, lookup_nat_or};

/// DaeDaLus `FlateDecodeParams`: the `predictor`, `colors`, `bpc` and `columns` (all `u64`)
/// of a `/FlateDecode` filter, where `param` is the filter's `/DecodeParms` entry as an
/// `Option` of a `pdf.value.dict` result (DaeDaLus `FilterParam`, which maps `null` to
/// `nothing`). Absent entries, and an absent `param`, take the defaults `1`, `1`, `8` and `1`.
fn flate_decode_params(param: Expr) -> Expr {
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
                params(&|key, dflt| lookup_nat_or(key, var("ps"), dflt)),
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

/// DaeDaLus `ApplyFilters`, given a stream's dictionary `header`, its raw bytes `raw`, and
/// whether the file is `encrypted` (a `Bool`): one of
/// - `ok` with the decoded bytes;
/// - `unsupported`, a record of `filter`, the name of the filter that can't be applied
///   (followed by ` (with params)` if it has a `/DecodeParms` entry), as DaeDaLus
///   `ApplyFilter` gives, and `raw`;
/// - `encrypted` with `raw`, for a stream of an `encrypted` file other than a `/Type /XRef`
///   one (which DaeDaLus exempts from `Decrypt`); no filter is applied.
///
/// `unsupported` and `encrypted` hand the stream to the host, which decrypts `raw` or applies
/// its filters itself (calling `pdf.flate_decode` for `/FlateDecode`, see
/// [`host_filter_formats`] and `pdf::host`), in place of the DaeDaLus host primitives
/// `Decrypt`, `LZWDecode` and so on.
///
/// Of the filters, only `/FlateDecode` with a supported predictor is applied (see
/// [`flate_decode`]), and only on its own; no filter gives `ok` with `raw`. Unlike DaeDaLus:
/// - every other filter is `unsupported`, including `/ASCIIHexDecode`, `/ASCII85Decode` and
///   `/DCTDecode`, which DaeDaLus decodes or passes through;
/// - a chain of more than one filter is `unsupported`, naming the first, and nothing is
///   decoded;
/// - an indirect `/Filter`, `/DecodeParms` or `/Type` isn't resolved; an indirect `/Filter` or
///   `/DecodeParms` fails.
///
/// A filter that isn't a name, or a `/DecodeParms` that isn't a dict or `null`, fails (DaeDaLus
/// `Filter`, `FilterParam`), as does a `/FlateDecode` whose data doesn't decode.
pub(super) fn apply_filters(zlib: FormatRef, header: Expr, raw: Expr, encrypted: Expr) -> Format {
    let is_xref = expr_match(
        dict_lookup(b"Type", header.clone()),
        [
            (
                pat_some(Pattern::Variant(
                    "name".into(),
                    Box::new(pattern_bytestring(b"/XRef")),
                )),
                Expr::Bool(true),
            ),
            (Pattern::Wildcard, Expr::Bool(false)),
        ],
    );
    if_then_else(
        and(encrypted, expr_not(is_xref)),
        compute(variant("encrypted", raw.clone())),
        decode_filters(zlib, header, raw),
    )
}

/// DaeDaLus `LookupOptArray` of `key` in the dict `header`: absent is `[]`, and a single value
/// is `[value]`
fn opt_array(header: Expr, key: &[u8]) -> Expr {
    expr_match(
        dict_lookup(key, header),
        [
            (pat_none(), Expr::Seq(vec![])),
            (
                pat_some(Pattern::Variant("array".into(), Box::new(bind("vs")))),
                var("vs"),
            ),
            (pat_some(bind("v")), Expr::Seq(vec![var("v")])),
        ],
    )
}

/// DaeDaLus `FilterParam` of a filter's parameters `param` (an `Option` of a `pdf.value`, as
/// `index_checked` gives it from the `/DecodeParms` array, where absent is `null`): `Some` of
/// a dict, or `None` for `null`; anything else fails.
fn filter_param(param: Expr) -> Format {
    let null = Pattern::Variant("null".into(), Box::new(Pattern::Wildcard));
    fmt_match(
        param,
        [
            (pat_none(), compute(expr_none())),
            (pat_some(null), compute(expr_none())),
            (
                pat_some(Pattern::Variant("dict".into(), Box::new(bind("d")))),
                compute(expr_some(var("d"))),
            ),
            (Pattern::Wildcard, Format::Fail), // "bad /DecodeParms"
        ],
    )
}

/// The formats the host calls when a stream is left to it (see `pdf::host`), both taking
/// `pdf.value`s as its `resolve_ref` results hold them:
/// - `pdf.filter_chain`: given `val`, a stream's dictionary (a dict), the record of its
///   `filters` and `params` (DaeDaLus `LookupOptArray` of `/Filter` and `/DecodeParms`), for
///   the host to apply in order;
/// - `pdf.flate_decode`: given `param` (an `Option` of a `pdf.value`, as for `filter_param`)
///   and `bytes`, DaeDaLus `FlateDecode` of `bytes` (see [`flate_decode`]), which fails for
///   an unsupported predictor.
pub(super) fn host_filter_formats(pm: &mut PdfModule<'_>) -> [FormatRef; 2] {
    let zlib = pm.zlib();
    let pdf_value = pm.pdf_value();
    let value_type = pm.format_type(pdf_value);
    let module = pm.module();
    let filter_chain = module.define_format_args(
        "pdf.filter_chain",
        vec![(Label::Borrowed("val"), value_type.clone())],
        fmt_match(
            var("val"),
            [
                (
                    Pattern::Variant("dict".into(), Box::new(bind("header"))),
                    compute(Expr::Record(vec![
                        (
                            Label::Borrowed("filters"),
                            opt_array(var("header"), b"Filter"),
                        ),
                        (
                            Label::Borrowed("params"),
                            opt_array(var("header"), b"DecodeParms"),
                        ),
                    ])),
                ),
                (Pattern::Wildcard, Format::Fail), // "not a dict"
            ],
        ),
    );
    let flate = module.define_format_args(
        "pdf.flate_decode",
        vec![
            (
                Label::Borrowed("param"),
                ValueType::Option(Box::new(value_type)),
            ),
            (
                Label::Borrowed("bytes"),
                ValueType::Seq(Box::new(ValueType::Base(BaseType::U8))),
            ),
        ],
        chain(
            filter_param(var("param")),
            "_param",
            chain(
                compute(flate_decode_params(var("_param"))),
                "_fp",
                flate_decode(zlib, var("_fp"), var("bytes")),
            ),
        ),
    );
    [filter_chain, flate]
}

/// [`apply_filters`] of a stream that isn't to be decrypted
fn decode_filters(zlib: FormatRef, header: Expr, raw: Expr) -> Format {
    // DaeDaLus `FilterParam` of the first filter's parameters, which default to `null`
    let param = filter_param(index_checked(var("_params"), Expr::U32(0)));
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
            Expr::Record(vec![
                (
                    Label::Borrowed("filter"),
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
                ),
                (Label::Borrowed("raw"), raw.clone()),
            ]),
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
        compute(flate_decode_params(var("_param"))),
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
        compute(opt_array(header.clone(), b"Filter")),
        "_filters",
        chain(
            compute(opt_array(header, b"DecodeParms")),
            "_params",
            fmt_match(
                var("_filters"),
                [
                    (Pattern::Seq(vec![]), compute(variant("ok", raw.clone()))),
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

#[cfg(test)]
mod tests {
    use super::*;

    use doodle::{FormatModule, decoder::Compiler, read::ReadCtxt};

    use crate::pdf::PdfModule;
    use crate::pdf::combinators::only;
    use crate::pdf::test_support::HELLO_Z;

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
        let value = PdfModule::new(module).pdf_value();
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
                chain(compute(flate_decode_params(var("param"))), "params", rest),
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
}
