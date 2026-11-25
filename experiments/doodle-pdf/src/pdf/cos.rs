//! `pdf.cos`, the parse driven from the end of the file (`startxref`), as the DaeDaLus host does.

use doodle::{Expr, Format, FormatModule, FormatRef, Pattern, helper::*};

use super::combinators::{count_to, match_str, record_daedalus, skip_to};
use super::decl::resolve_decl;
use super::lexical::{SIMPLE_WS, white_till_eol};
use super::value::{dict_lookup, natural_u64};
use super::xref::section_trailer;

/// The trailer of the newest section, in `pdf.cos`
fn newest_trailer() -> Expr {
    section_trailer(index_unchecked(var("sections"), Expr::U32(0)))
}

/// DaeDaLus `PdfEnd`: `startxref`, the offset of the last cross-reference section, and `%%EOF`,
/// each on its own line. Yields the offset.
pub(super) fn pdf_end(module: &mut FormatModule, eol: FormatRef, natural: FormatRef) -> FormatRef {
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

/// The cross-reference sections of a PDF, found from its end as the DaeDaLus host does: the
/// `%PDF-` header gives the base for all offsets, the last `startxref` gives the offset of the
/// newest section, and `/Prev` and `/XRefStm` links lead to the rest (see [`xref_chain`]).
///
/// Sits alongside `pdf.main` (a front-to-back parse), and leaves any bytes after the final
/// `%%EOF` unread.
pub(super) fn pdf_cos(
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
            // DaeDaLus `TrailerDict`'s `encrypt`, taken from the newest trailer as the host
            // does; only whether there is one matters here (see `apply_filters`)
            (
                "encrypted",
                compute(expr_match(
                    dict_lookup(b"Encrypt", record_proj(newest_trailer(), "all")),
                    [
                        (pat_some(Pattern::Wildcard), Expr::Bool(true)),
                        (pat_none(), Expr::Bool(false)),
                    ],
                )),
            ),
            // the newest trailer's `/Root`, resolved: a `value`, or `packed` for the host
            // (see `resolve`); a stream fails
            (
                "root",
                fmt_match(
                    record_proj(newest_trailer(), "root"),
                    [
                        (
                            pat_some(bind("root_ref")),
                            fmt_some(chain(
                                resolve_decl(
                                    resolve_ref,
                                    [
                                        var("header_offset"),
                                        var("sections"),
                                        var("encrypted"),
                                        Expr::Seq(vec![]),
                                        Expr::U64(256),
                                    ],
                                    var("root_ref"),
                                ),
                                "root_d",
                                fmt_match(
                                    var("root_d"),
                                    [
                                        (
                                            Pattern::Variant(
                                                "stream".into(),
                                                Box::new(Pattern::Wildcard),
                                            ),
                                            Format::Fail, // "/Root is a stream"
                                        ),
                                        (Pattern::Wildcard, compute(var("root_d"))),
                                    ],
                                ),
                            )),
                        ),
                        (pat_none(), compute(expr_none())),
                    ],
                ),
            ),
        ]),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use doodle::{decoder::Compiler, read::ReadCtxt};

    use crate::pdf::test_support::{Ent, Obj, be_rows, build_objects, build_pdf, objstm_pdf, sec};
    use crate::pdf::top_formats;

    /// A `%PDF-1.5` file whose only section is a cross-reference stream: object 1 (the text
    /// `obj1`) at its offset, and object 2 packed in object stream 5, which isn't there (see
    /// [`objstm_pdf`] for one that is), with the trailer's `/Root` as given.
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
    /// object), through classic and stream sections alike, and from an object stream, or
    /// leaves it `packed` for the host when that stream's filter is unsupported; an object
    /// packed in a missing object stream fails to resolve, unless its generation isn't `0`,
    /// which makes it `null`. Each case gives the expected `root` value's kind (or `packed`;
    /// `None` for no `/Root`), or fails.
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
                "a /Root packed in a missing object stream",
                packed_pdf("2 0 R", "<< /Type /Catalog >>"),
                None,
            ),
            (
                "a /Root packed in an object stream",
                objstm_pdf(
                    "/Type /ObjStm /N 1",
                    "1 0 ",
                    "<< /Type /Catalog >>",
                    None,
                    &[
                        Ent::Free,
                        Ent::Packed(5, 0),
                        Ent::Free,
                        Ent::Free,
                        Ent::Free,
                        Ent::At(5),
                    ],
                ),
                Some(Some("dict")),
            ),
            (
                "a /Root packed in an object stream left to the host",
                objstm_pdf(
                    "/Type /ObjStm /N 1 /Filter /LZWDecode",
                    "1 0 ",
                    "<< /Type /Catalog >>",
                    None,
                    &[
                        Ent::Free,
                        Ent::Packed(5, 0),
                        Ent::Free,
                        Ent::Free,
                        Ent::Free,
                        Ent::At(5),
                    ],
                ),
                Some(Some("packed")),
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
        let pdf_cos = top_formats(&mut module).cos;
        for (name, input, expected) in cases {
            let check = match expected {
                Some(Some(kind)) => fmt_match(
                    record_proj(var("cos"), "root"),
                    [
                        (
                            pat_some(match kind {
                                "packed" => {
                                    Pattern::Variant(kind.into(), Box::new(Pattern::Wildcard))
                                }
                                _ => Pattern::Variant(
                                    "value".into(),
                                    Box::new(Pattern::Variant(
                                        kind.into(),
                                        Box::new(Pattern::Wildcard),
                                    )),
                                ),
                            }),
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

    /// `pdf.cos` reports whether the newest trailer has an `/Encrypt` entry.
    #[test]
    fn pdf_cos_encrypted() {
        let plain = build_objects(&[&[(1, 0, Obj::Def(b"<< /Type /Catalog >>"))]]);
        let mut encrypted = plain.clone();
        let at = encrypted
            .windows(9)
            .position(|w| w == b"/Root 1 0")
            .unwrap();
        encrypted.splice(at..at, b"/Encrypt << /Filter /Standard >> ".iter().copied());
        let mut module = FormatModule::new();
        let pdf_cos = top_formats(&mut module).cos;
        for (name, input, expected) in [("plain", plain, false), ("encrypted", encrypted, true)] {
            let top = chain(
                pdf_cos.call(),
                "cos",
                if_then_else(
                    record_proj(var("cos"), "encrypted"),
                    if expected {
                        Format::EMPTY
                    } else {
                        Format::Fail
                    },
                    if expected {
                        Format::Fail
                    } else {
                        Format::EMPTY
                    },
                ),
            );
            let prog = Compiler::compile_program(&module, &top).expect("must compile");
            assert!(prog.run(ReadCtxt::new(&input)).is_ok(), "{name}");
        }
    }
}
