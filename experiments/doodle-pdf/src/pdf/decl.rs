//! Top-level declarations: streams and the resolution of indirect references, DaeDaLus `PdfDecl.ddl`.

use doodle::{
    BaseType, DepFormat, Expr, Format, FormatModule, FormatRef, Label, Pattern, ValueType,
    helper::*,
};

use super::combinators::{count_to, match_str, record_daedalus};
use super::filters::apply_filters;
use super::lexical::{kw, token};
use super::value::{dict_get, nat_value, natural_u64, number_as_nat};

/// Daedalus `Stream (val : Value)`. `val` is a whole `Value` (as passed by `pdf.top_decl`), and
/// `header = val is dict` narrows it. As in the Daedalus definition, `CountTo` consumes the
/// `endstream` keyword, and `body` is taken from the view saved before it.
pub(super) fn stream(
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

/// What the cross-reference sections say of object number `obj` (a `u64`), as the DaeDaLus
/// host's merged table does: `Some` of `at` (an `offset` relative to the `%PDF-` header, and
/// a `gen`), `packed` (at index `index` of object stream `container`, at generation `0`),
/// `free` or `null` (an unknown
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
            (
                Label::Borrowed("packed"),
                ValueType::Record(vec![
                    (Label::Borrowed("container"), u64_type()),
                    (Label::Borrowed("index"), u64_type()),
                ]),
            ),
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
                        Pattern::Variant("compressed".into(), Box::new(bind("e"))),
                        variant(
                            "packed",
                            Expr::Record(vec![
                                (
                                    Label::Borrowed("container"),
                                    record_proj(var("e"), "container_obj"),
                                ),
                                (Label::Borrowed("index"), record_proj(var("e"), "obj_index")),
                            ]),
                        ),
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
pub(super) fn resolve_val(resolve_ref: FormatRef, args: [Expr; 4], v: Expr) -> Format {
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

/// DaeDaLus `ResolveDeclRef` (#355): the batch
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
/// An object in an object stream (a type 2 entry, at generation `0`) is read from its
/// container, as the host does: the container is resolved as `container 0` (and fails, rather
/// than being `null`, if it isn't a stream), then DaeDaLus `ObjStream` (`/Type /ObjStm`, a body
/// that decodes, `/N` pairs of object number and offset, the objects from `/First`) and
/// `ObjStreamEntry` give the value at the entry's index, whose object number must be `obj`
/// (`CheckExpected`). `/Extends` (a chain of object streams) is not followed, as in DaeDaLus.
///
/// A stream's body is the `/Length` bytes after the `stream` line (DaeDaLus `StreamBody`),
/// where an indirect `/Length` is resolved within the batch. That, an object stream's container
/// and its indirect `/Type`, `/N` and `/First` are the nested resolutions.
#[allow(clippy::too_many_arguments)]
pub(super) fn resolve(
    module: &mut FormatModule,
    any_ws: FormatRef,
    simple_eol: FormatRef,
    natural: FormatRef,
    pdf_value: FormatRef,
    zlib: FormatRef,
    sections_type: ValueType,
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
    // Nested resolution, with this object added to those being resolved
    let nested = || {
        [
            var("base"),
            var("sections"),
            append(var("resolving"), Expr::Seq(vec![var("obj")])),
            sub(var("lim"), Expr::U64(1)),
        ]
    };
    // DaeDaLus `LookupResolve key dict`, within the batch
    let lookup_resolve = move |resolve_ref: FormatRef, key: &[u8], dict: Expr| {
        chain(
            dict_get(key, dict),
            "_lookup",
            resolve_val(resolve_ref, nested(), var("_lookup")),
        )
    };
    module.define_batch_with_args(
        [("pdf.resolve_ref", args()), ("pdf.resolved_decl", args())],
        [
            Box::new(move |&[resolve_ref, decl]: &[FormatRef; 2]| {
                let entry = || Pattern::Variant("at".into(), Box::new(bind("at")));
                let packed = || Pattern::Variant("packed".into(), Box::new(bind("packed")));
                let nat = |key: &'static [u8], dict: Expr| {
                    chain(
                        lookup_resolve(resolve_ref, key, dict),
                        "_nat_v",
                        nat_value(var("_nat_v")),
                    )
                };
                // DaeDaLus `ObjStream` of the container's stream `_stm`, then `ObjStreamEntry`
                // at the entry's index, then `CheckExpected`
                let header = || record_proj(var("_stm"), "header");
                let obj_stream_entry = record_auto([
                    (
                        "__type",
                        chain(
                            lookup_resolve(resolve_ref, b"Type", header()),
                            "_type",
                            fmt_match(
                                var("_type"),
                                [
                                    (
                                        Pattern::Variant(
                                            "name".into(),
                                            Box::new(pattern_bytestring(b"/ObjStm")),
                                        ),
                                        Format::EMPTY,
                                    ),
                                    (Pattern::Wildcard, Format::Fail), // "not /Type /ObjStm"
                                ],
                            ),
                        ),
                    ),
                    (
                        "_bytes",
                        fmt_match(
                            record_proj(var("_stm"), "body"),
                            [
                                (
                                    Pattern::Variant("ok".into(), Box::new(bind("b"))),
                                    compute(var("b")),
                                ),
                                (Pattern::Wildcard, Format::Fail), // "unsupported filter"
                            ],
                        ),
                    ),
                    ("_n", nat(b"N", header())),
                    ("_first", nat(b"First", header())),
                    (
                        "_index",
                        decode_bytes(
                            var("_bytes"),
                            repeat_count(
                                var("_n"),
                                record_auto([
                                    ("oid", token(natural_u64(natural), any_ws)),
                                    ("off", token(natural_u64(natural), any_ws)),
                                ]),
                            ),
                        ),
                    ),
                    (
                        "_info",
                        fmt_match(
                            index_checked(var("_index"), record_proj(var("packed"), "index")),
                            [
                                (pat_some(bind("info")), compute(var("info"))),
                                (pat_none(), Format::Fail), // "index past /N"
                            ],
                        ),
                    ),
                    (
                        "__check",
                        if_then_else(
                            expr_eq(record_proj(var("_info"), "oid"), var("obj")),
                            Format::EMPTY,
                            Format::Fail, // "object number doesn't match the xref"
                        ),
                    ),
                    (
                        "decl",
                        decode_bytes(
                            var("_bytes"),
                            monad_seq(
                                // `Drop first`, then `Drop off`
                                repeat_count(var("_first"), Format::ANY_BYTE),
                                monad_seq(
                                    repeat_count(
                                        record_proj(var("_info"), "off"),
                                        Format::ANY_BYTE,
                                    ),
                                    map(
                                        pdf_value.call_args(vec![Expr::U64(32)]),
                                        lambda("v", variant("value", var("v"))),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ]);
                let from_container = chain(
                    resolve_ref.call_args(vec![
                        var("base"),
                        var("sections"),
                        record_proj(var("packed"), "container"),
                        Expr::U64(0),
                        append(var("resolving"), Expr::Seq(vec![var("obj")])),
                        sub(var("lim"), Expr::U64(1)),
                    ]),
                    "_container",
                    fmt_match(
                        var("_container"),
                        [
                            (
                                Pattern::Variant("stream".into(), Box::new(bind("_stm"))),
                                map(obj_stream_entry, lambda("e", record_proj(var("e"), "decl"))),
                            ),
                            // including `null`, a missing container (the host fails)
                            (Pattern::Wildcard, Format::Fail), // "container is not a stream"
                        ],
                    ),
                );
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
                                    from_container,
                                    null_decl(),
                                ),
                            ),
                            (Pattern::Wildcard, null_decl()),
                        ],
                    ),
                )
            }),
            Box::new(move |&[resolve_ref, _]: &[FormatRef; 2]| {
                // DaeDaLus `StreamLen`: `LookupResolve "Length"`, a natural number
                let stream_len = chain(
                    dict_get(b"Length", var("header")),
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
                                    apply_filters(zlib, var("header"), var("raw")),
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

#[cfg(test)]
mod tests {
    use super::*;

    use doodle::{decoder::Compiler, read::ReadCtxt};

    use crate::pdf::combinators::only;
    use crate::pdf::lexical::{any_ws, comment, eol, simple_eol};
    use crate::pdf::test_support::{Ent, HELLO_Z, Obj, build_objects, objstm_pdf};
    use crate::pdf::top_formats;
    use crate::pdf::value::{natural, number, pdf_value, v_name};

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

    /// `pdf.resolve_ref` reads an object packed in an object stream (DaeDaLus `ObjStream` and
    /// `ObjStreamEntry`, as the host resolves a type 2 entry): the container (at generation
    /// `0`) must be a stream of `/Type /ObjStm` whose body decodes, the entry's index must be
    /// under `/N`, and the object number there must be the one asked for. `/N` and `/First` may
    /// be indirect. Each case resolves `(number, 0)`.
    #[test]
    fn resolve_packed_objects() {
        use Ent::*;
        use Resolved::*;
        const STM: &str = "/Type /ObjStm /N 2";
        // objects 1 (a dict) and 2 (a number) at offsets 0 and 21 of the values
        const INDEX: &str = "1 0 2 21 ";
        const VALUES: &str = "<< /Type /Catalog >> 42";
        let packed = || vec![Free, Packed(5, 0), Packed(5, 1), Free, Free, At(5)];
        let with6 = |mut e: Vec<Ent>| {
            e.push(At(6));
            e
        };
        let cases: Vec<(&str, Vec<u8>, u64, Resolved)> = vec![
            (
                "the first packed object",
                objstm_pdf(STM, INDEX, VALUES, None, &packed()),
                1,
                Kind("dict"),
            ),
            (
                "the second packed object",
                objstm_pdf(STM, INDEX, VALUES, None, &packed()),
                2,
                Number(b"42"),
            ),
            (
                "an indirect /N",
                objstm_pdf(
                    "/Type /ObjStm /N 6 0 R",
                    INDEX,
                    VALUES,
                    Some("2"),
                    &with6(packed()),
                ),
                2,
                Number(b"42"),
            ),
            (
                "an indirect /First",
                // the index "1 0 2 6 " is 8 bytes, and the number is 6 bytes into the values
                objstm_pdf(
                    "/Type /ObjStm /N 2 /First 6 0 R",
                    "1 0 2 6 ",
                    "<< >> 42",
                    Some("8"),
                    &with6(packed()),
                ),
                2,
                Number(b"42"),
            ),
            (
                "an index past /N",
                objstm_pdf("/Type /ObjStm /N 1", INDEX, VALUES, None, &packed()),
                2,
                Fails,
            ),
            (
                "an object number that doesn't match the entry",
                objstm_pdf(STM, "7 0 2 21 ", VALUES, None, &packed()),
                1,
                Fails,
            ),
            (
                "an offset past the values",
                objstm_pdf(STM, "1 0 2 99 ", VALUES, None, &packed()),
                2,
                Fails,
            ),
            (
                "a container that isn't /Type /ObjStm",
                objstm_pdf("/Type /XObject /N 2", INDEX, VALUES, None, &packed()),
                1,
                Fails,
            ),
            (
                "a container that isn't a stream",
                objstm_pdf(
                    STM,
                    INDEX,
                    VALUES,
                    Some("<< /Type /ObjStm >>"),
                    &[Free, Packed(6, 0), Free, Free, Free, At(5), At(6)],
                ),
                1,
                Fails,
            ),
            (
                "a container that is free",
                objstm_pdf(
                    STM,
                    INDEX,
                    VALUES,
                    None,
                    &[Free, Packed(4, 0), Free, Free, Free, At(5)],
                ),
                1,
                Fails,
            ),
            (
                "a container packed in itself",
                objstm_pdf(
                    STM,
                    INDEX,
                    VALUES,
                    None,
                    &[Free, Packed(5, 0), Free, Free, Free, Packed(5, 0)],
                ),
                1,
                Fails,
            ),
            (
                "a container with an unsupported filter",
                objstm_pdf(
                    "/Type /ObjStm /N 2 /Filter /LZWDecode",
                    INDEX,
                    VALUES,
                    None,
                    &packed(),
                ),
                1,
                Fails,
            ),
        ];
        let mut module = FormatModule::new();
        let [_pdf_main, pdf_cos, resolve_ref] = top_formats(&mut module);
        for (name, input, obj, expected) in cases {
            let is = |p: Pattern| {
                fmt_match(
                    var("d"),
                    [
                        (Pattern::Variant("value".into(), Box::new(p)), Format::EMPTY),
                        (Pattern::Wildcard, Format::Fail),
                    ],
                )
            };
            let (check, ok) = match &expected {
                Kind(kind) => (
                    is(Pattern::Variant(
                        (*kind).into(),
                        Box::new(Pattern::Wildcard),
                    )),
                    true,
                ),
                Number(n) => (
                    is(Pattern::Variant(
                        "number".into(),
                        Box::new(pattern_bytestring(n)),
                    )),
                    true,
                ),
                Fails => (Format::EMPTY, false),
                _ => unreachable!(),
            };
            let top = chain(
                pdf_cos.call(),
                "cos",
                chain(
                    resolve_ref.call_args(vec![
                        record_proj(var("cos"), "header_offset"),
                        record_proj(var("cos"), "sections"),
                        Expr::U64(obj),
                        Expr::U64(0),
                        Expr::Seq(vec![]),
                        Expr::U64(8),
                    ]),
                    "d",
                    check,
                ),
            );
            let prog = Compiler::compile_program(&module, &top).expect("must compile");
            assert_eq!(
                prog.run(ReadCtxt::new(&input)).is_ok(),
                ok,
                "{name}: resolving {obj} 0 in {:?}",
                String::from_utf8_lossy(&input)
            );
        }
    }
}
