//! Cross-reference sections and streams and the trailer chain: DaeDaLus `PdfXRef.ddl`.

use doodle::{BaseType, Expr, Format, FormatRef, Label, Pattern, ValueType, helper::*};
use doodle_numexpr_macro::numexpr;

use super::PdfModule;
use super::combinators::{interpret, match_str, void};
use super::decl::resolve_val;
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
/// gives.
///
/// Only `/XRefStm` is looked up with resolution in DaeDaLus (`LookupNat`), so it is looked up
/// in `resolved`: `dict` with the [`resolved_entries`] of a cross-reference stream appended,
/// or `dict` itself.
fn trailer_dict(dict: Expr, resolved: Expr) -> Format {
    let optional_nat = |key: &[u8], dict: &Expr| {
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
                    (
                        Pattern::Wildcard,
                        Format::fail_with("/Root is not a reference"),
                    ),
                ],
            ),
        ),
        ("prev", compute(optional_nat(b"Prev", &dict))),
        ("xrefstm", compute(optional_nat(b"XRefStm", &resolved))),
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
                (pat_none(), Format::fail_with("field too wide")),
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
        Format::fail_with("required field has width 0"),
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
/// `/Index` and its elements are as [`resolved_entries`] leaves them. An indirect `/Size`
/// fails, as it does in DaeDaLus, whose `TrailerDict` looks `/Size` up directly.
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
                Format::fail_with("odd /Index length"),
            ),
        ),
    )
}

/// DaeDaLus `XRefFormat`, given the stream dictionary `header`: the widths `b1`, `b2` and `b3`
/// of the fields of an entry (from `/W`, `0` for any it doesn't give), and the `width` of a
/// whole entry, the sum of all of `/W`. `/W` must be an array of natural numbers.
///
/// `/W` is as [`resolved_entries`] leaves it; its elements aren't resolved (DaeDaLus `NatValue`).
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
                    (Pattern::Wildcard, Format::fail_with("/W is not an array")),
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
                    (pat_none(), Format::fail_with("entry too wide")),
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
                (Pattern::Wildcard, Format::fail_with("unsupported filter")),
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
/// any after the last entry.
///
/// It takes `extra`, the [`resolved_entries`] of its dictionary, which are appended to the
/// dictionary (where they take precedence, see [`dict_lookup`]) for the lookups that DaeDaLus
/// resolves: `/Length`, `/Filter`, `/DecodeParms`, `/Type`, `/Index`, `/W` and the trailer's
/// `/XRefStm`. The trailer's other entries are looked up in the dictionary as written.
pub(super) fn xref_obj(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let simple_eol = pm.simple_eol();
    let natural = pm.natural();
    let pdf_value = pm.pdf_value();
    let pdf_dict = pm.pdf_dict();
    let dict_type = pm.format_type(pdf_dict);
    let zlib = pm.zlib();
    let module = pm.module();
    let header = || var("_rheader");
    module.define_format_args(
        "pdf.xref_obj",
        vec![(Label::Borrowed("extra"), dict_type)],
        record_auto([
            ("_header", stream_object_dict(any_ws, natural, pdf_value)),
            (
                "_rheader",
                compute(concat(Expr::Seq(vec![var("_header"), var("extra")]))),
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
                    Format::fail_with("not /Type /XRef"),
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
            ("trailer", trailer_dict(var("_header"), header())),
        ]),
    )
}

/// DaeDaLus `TopDecl` up to the dictionary of a stream object: whitespace, `n g obj`, and the
/// value, which must be a dict (anything else fails, "not a stream"). The numbers aren't
/// checked.
fn stream_object_dict(any_ws: FormatRef, natural: FormatRef, pdf_value: FormatRef) -> Format {
    map(
        record_auto([
            ("__ws", repeat(any_ws.call())),
            ("__id", token(natural_u64(natural), any_ws)),
            ("__gen", token(natural_u64(natural), any_ws)),
            ("__kw_obj", kw(b"obj", any_ws)),
            ("_val", pdf_value.call_args(vec![Expr::U64(32)])),
            (
                "dict",
                fmt_match(
                    var("_val"),
                    [
                        (
                            Pattern::Variant("dict".into(), Box::new(bind("d"))),
                            compute(var("d")),
                        ),
                        (Pattern::Wildcard, Format::fail_with("not a stream")),
                    ],
                ),
            ),
        ]),
        lambda("h", record_proj(var("h"), "dict")),
    )
}

/// The entries of the dictionary `header` (of a cross-reference stream, a `pdf.value.dict`
/// result) that DaeDaLus looks up with resolution, resolved by `resolve` (see [`xref_chain`]),
/// as dictionary entries to append to `header`. A key that `header` lacks gives no entry.
///
/// As in DaeDaLus:
/// - `/Length`, `/W` and `/Type` are resolved (`LookupResolve`), and a failure fails;
/// - `/Index` is resolved, then each element of it if it is an array (`LookupNats`), and a
///   failure gives `null`, for which [`xref_index`] takes its default (`Default`);
/// - `/Filter` and `/DecodeParms` are resolved, and a failure gives `[]` (`LookupOptArray`'s
///   `Default []`);
/// - the trailer's `/XRefStm` is resolved, and a failure gives `null`, which [`trailer_dict`]
///   takes as no link (`Optional`).
///
/// An object that isn't in the table resolves to `null`, as in DaeDaLus, and the lookup then
/// fails or takes its default as it would for a `null` written in place.
fn resolved_entries(resolve: &dyn Fn(Expr) -> Format, header: Expr) -> Format {
    enum Fallback {
        None,
        Null,
        EmptyArray,
    }
    let keys: [(&[u8], Fallback); 7] = [
        (b"Length", Fallback::None),
        (b"W", Fallback::None),
        (b"Type", Fallback::None),
        (b"Index", Fallback::Null),
        (b"Filter", Fallback::EmptyArray),
        (b"DecodeParms", Fallback::EmptyArray),
        (b"XRefStm", Fallback::Null),
    ];
    let fields = keys.into_iter().map(|(key, fallback)| {
        let resolved = if key == b"Index" {
            chain(
                resolve(var("_xv")),
                "_xi",
                fmt_match(
                    var("_xi"),
                    [
                        (
                            Pattern::Variant("array".into(), Box::new(bind("_xis"))),
                            map(
                                for_each(var("_xis"), "_xe", resolve(var("_xe"))),
                                lambda("_xes", variant("array", var("_xes"))),
                            ),
                        ),
                        (Pattern::Wildcard, compute(var("_xi"))),
                    ],
                ),
            )
        } else {
            resolve(var("_xv"))
        };
        let resolved = match fallback {
            Fallback::None => resolved,
            Fallback::Null => union_nondet([resolved, compute(variant("null", Expr::UNIT))]),
            Fallback::EmptyArray => {
                union_nondet([resolved, compute(variant("array", Expr::Seq(vec![])))])
            }
        };
        let name = [b"/", key].concat();
        let label = format!("x_{}", String::from_utf8_lossy(key));
        (
            label,
            fmt_match(
                dict_lookup(key, header.clone()),
                [
                    (
                        pat_some(bind("_xv")),
                        fmt_some(map(
                            resolved,
                            lambda(
                                "_xr",
                                Expr::Record(vec![
                                    (Label::Borrowed("key"), expr_lift_seq(name, Expr::U8)),
                                    (Label::Borrowed("value"), var("_xr")),
                                ]),
                            ),
                        )),
                    ),
                    (pat_none(), fmt_none()),
                ],
            ),
        )
    });
    let fields: Vec<(String, Format)> = fields.collect();
    let labels: Vec<String> = fields.iter().map(|(l, _)| l.clone()).collect();
    map(
        record_auto(fields),
        lambda(
            "_xs",
            concat(Expr::Seq(
                labels
                    .iter()
                    .map(|l| {
                        expr_option_map_or(
                            Expr::Seq(vec![]),
                            |e| Expr::Seq(vec![e]),
                            record_proj(var("_xs"), l.clone()),
                        )
                    })
                    .collect(),
            )),
        ),
    )
}

/// DaeDaLus `CrossRef`: the cross-reference section found at an offset, either `old_xref`
/// (`CrossRefAndTrailer`: an `xref` table, then `trailer` and its dict) or `new_xref` (a
/// cross-reference stream, [`xref_obj`], which gets `extra`), trying them in that order
/// (DaeDaLus `First`).
pub(super) fn cross_ref(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let eol = pm.eol();
    let xref_table = pm.cross_ref_section();
    let pdf_dict = pm.pdf_dict();
    let xref_obj = xref_obj(pm);
    let dict_type = pm.format_type(pdf_dict);
    let module = pm.module();
    let just_white = union([void(byte_in(SIMPLE_WS)), eol.call()]);
    let old_xref = record_auto([
        // DaeDaLus `CrossRefSection` allows whitespace and comments before `xref`
        ("xref", monad_seq(repeat(any_ws.call()), xref_table.call())),
        // ... but only whitespace (no comments) before `trailer`
        ("__ws", repeat(just_white)),
        ("__kw_trailer", kw(b"trailer", any_ws)),
        ("_dict", pdf_dict.call_args(vec![Expr::U64(32)])),
        ("trailer", trailer_dict(var("_dict"), var("_dict"))),
    ]);
    module.define_format_args(
        "pdf.cross_ref",
        vec![(Label::Borrowed("extra"), dict_type)],
        alts_nondet([
            ("old_xref", old_xref),
            ("new_xref", xref_obj.call_args(vec![var("extra")])),
        ]),
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
///
/// `table` is what the host's object table holds when the section is parsed (in precedence
/// order, as `sections`), against which a cross-reference stream's [`resolved_entries`] are
/// resolved (with `pdf.resolve_ref`, as unencrypted). The host registers a section's entries
/// only after following its links, and follows `/Prev` before `/XRefStm`, so `table` is empty
/// for the newest section, a `/Prev` section gets its referrer's `table`, and an `/XRefStm`
/// section gets its referrer's `/Prev` sections ahead of its referrer's `table`. Only an
/// `/XRefStm` stream (as in a hybrid file) can resolve a reference, then; elsewhere every
/// reference is to an object that isn't in the table yet, and resolves to `null`.
pub(super) fn xref_chain(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let natural = pm.natural();
    let pdf_value = pm.pdf_value();
    let cross_ref = pm.cross_ref();
    let resolve_ref = pm.resolve_ref();
    let sections_type = ValueType::Seq(Box::new(pm.format_type(cross_ref)));
    let module = pm.module();
    let u64_type = || ValueType::Base(BaseType::U64);
    let args = vec![
        (Label::Borrowed("base"), u64_type()),
        (Label::Borrowed("offset"), u64_type()),
        (
            Label::Borrowed("visited"),
            ValueType::Seq(Box::new(u64_type())),
        ),
        (Label::Borrowed("table"), sections_type),
        (Label::Borrowed("lim"), u64_type()),
    ];
    let resolve = move |v: Expr| {
        resolve_val(
            resolve_ref,
            [
                var("base"),
                var("table"),
                Expr::Bool(false),
                Expr::Seq(vec![]),
                Expr::U64(256),
            ],
            v,
        )
    };
    // The `resolved_entries` of the cross-reference stream at `offset`, or none if there isn't
    // one there (such as a classic section)
    let extra = chain(
        with_relative_offset(
            Some(var("base")),
            var("offset"),
            union_nondet([
                fmt_some(stream_object_dict(any_ws, natural, pdf_value)),
                fmt_none(),
            ]),
        ),
        "_stm_dict",
        fmt_match(
            var("_stm_dict"),
            [
                (
                    pat_some(bind("_hdr")),
                    resolved_entries(&resolve, var("_hdr")),
                ),
                (pat_none(), compute(Expr::Seq(vec![]))),
            ],
        ),
    );
    let [chain_ref] = module.define_batch_with_args(
        [("pdf.xref_chain", args)],
        [Box::new(move |&[xref_chain]: &[FormatRef; 1]| {
            // Follows `link` (an `Option` of an offset) with the visited offsets `visited` and
            // the object table `table`, or yields no sections if there is no link.
            let follow = |link: Expr, visited: Expr, table: Expr| {
                fmt_match(
                    link,
                    [
                        (
                            pat_some(bind("next")),
                            xref_chain.call_args(vec![
                                var("base"),
                                var("next"),
                                visited.clone(),
                                table,
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
                expr_eq(var("lim"), Expr::U64(0)),
                Format::fail_with("cross-reference chain too long"),
                if_then_else(
                    seq_any(|v| expr_eq(v, var("offset")), var("visited")),
                    Format::fail_with("cross-reference chain revisits a section"),
                    chain(
                        extra,
                        "_extra",
                        chain(
                            with_relative_offset(
                                Some(var("base")),
                                var("offset"),
                                cross_ref.call_args(vec![var("_extra")]),
                            ),
                            "section",
                            chain(
                                follow(
                                    record_proj(trailer(), "prev"),
                                    visited_here(),
                                    var("table"),
                                ),
                                "prev",
                                chain(
                                    follow(
                                        record_proj(trailer(), "xrefstm"),
                                        record_proj(var("prev"), "visited"),
                                        concat(Expr::Seq(vec![
                                            record_proj(var("prev"), "sections"),
                                            var("table"),
                                        ])),
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
                "an indirect /Length in the newest section (an empty table)",
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

    /// A hybrid file: the objects `objs` (number and text), a classic section listing them
    /// (`/Size 10`), a cross-reference stream `9 0` (its dictionary `/Size 3` and `dict`, with
    /// `/Length 12` unless `dict` gives one; its body three in-use entries in `/W [1 2 1]`), and
    /// a classic section (`/Size 1`) whose `/Prev` is the first and whose `/XRefStm` is the
    /// stream. `startxref` is to the last section, or with `direct`, to the stream.
    fn hybrid_pdf(objs: &[(u64, &str)], dict: &str, direct: bool) -> Vec<u8> {
        let mut out = b"%PDF-1.5\n".to_vec();
        let mut offsets = [None; 10];
        for (n, text) in objs {
            offsets[*n as usize] = Some(out.len());
            out.extend(format!("{n} 0 obj\n{text}\nendobj\n").bytes());
        }
        let prev = out.len();
        out.extend(b"xref\n0 10\n");
        for off in offsets {
            out.extend(
                match off {
                    Some(o) => format!("{o:010} 00000 n\r\n"),
                    None => "0000000000 65535 f\r\n".to_string(),
                }
                .bytes(),
            );
        }
        out.extend(b"trailer\n<< /Size 10 >>\n");
        let body = be_rows(&[1, 2, 1], &[&[1, 0, 0], &[1, 0, 0], &[1, 0, 0]]);
        let len = if dict.contains("/Length") {
            String::new()
        } else {
            format!(" /Length {}", body.len())
        };
        let stream = out.len();
        out.extend(format!("9 0 obj\n<< /Size 3 {dict}{len} >>\nstream\n").bytes());
        out.extend(&body);
        out.extend(b"\nendstream\nendobj\n");
        let last = out.len();
        out.extend(
            format!(
                "xref\n0 1\n0000000000 65535 f\r\ntrailer\n<< /Size 1 /Prev {prev} /XRefStm {stream} >>\n"
            )
            .bytes(),
        );
        let start = if direct { stream } else { last };
        out.extend(format!("startxref\n{start}\n%%EOF\n").bytes());
        out
    }

    /// A cross-reference stream resolves the indirect entries that DaeDaLus resolves against
    /// the host's object table at the time (#360): for an `/XRefStm` stream, the sections of
    /// its referrer's `/Prev` chain; for the newest section, nothing, so that a reference
    /// there is to an object that isn't in the table yet, and is `null`. Each case gives, for
    /// each section in precedence order, its `/Size`, then (for a stream) each subsection's
    /// first object number, or `None` for a failure.
    #[test]
    fn xref_stream_resolves_against_older_sections() {
        const TW: &str = "/Type /XRef /W [1 2 1]";
        let hybrid = |first: u64| Some(vec![1, 3, first, 10]);
        let cases: Vec<(&str, Vec<u8>, Option<Vec<u64>>)> = vec![
            ("direct entries", hybrid_pdf(&[], TW, false), hybrid(0)),
            (
                "/Length from the /Prev section",
                hybrid_pdf(&[(7, "12")], &format!("{TW} /Length 7 0 R"), false),
                hybrid(0),
            ),
            (
                "/Length in the newest section",
                hybrid_pdf(&[(7, "12")], &format!("{TW} /Length 7 0 R"), true),
                None,
            ),
            (
                "/Length to an object in no section",
                hybrid_pdf(&[], &format!("{TW} /Length 7 0 R"), false),
                None,
            ),
            (
                "/Length to an object of another generation",
                hybrid_pdf(&[(7, "12")], &format!("{TW} /Length 7 1 R"), false),
                None,
            ),
            (
                "/W from the /Prev section",
                hybrid_pdf(&[(7, "[1 2 1]")], "/Type /XRef /W 7 0 R", false),
                hybrid(0),
            ),
            (
                "/Type from the /Prev section",
                hybrid_pdf(&[(7, "/XRef")], "/Type 7 0 R /W [1 2 1]", false),
                hybrid(0),
            ),
            (
                "/Index from the /Prev section",
                hybrid_pdf(&[(7, "[5 3]")], &format!("{TW} /Index 7 0 R"), false),
                hybrid(5),
            ),
            (
                "an element of /Index from the /Prev section",
                hybrid_pdf(&[(7, "5")], &format!("{TW} /Index [7 0 R 3]"), false),
                hybrid(5),
            ),
            (
                "/Index to an object in no section takes the default",
                hybrid_pdf(&[], &format!("{TW} /Index 7 0 R"), false),
                hybrid(0),
            ),
            (
                "/Index to a stream takes the default",
                hybrid_pdf(
                    &[(7, "<< /Length 0 >>\nstream\n\nendstream")],
                    &format!("{TW} /Index 7 0 R"),
                    false,
                ),
                hybrid(0),
            ),
        ];
        let mut module = FormatModule::new();
        let pdf_cos = PdfModule::new(&mut module).cos();
        let seq1 = |e: Expr| Expr::Seq(vec![e]);
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
                                    lambda("sub", seq1(record_proj(var("sub"), "first_id"))),
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
