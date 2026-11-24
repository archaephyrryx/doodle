mod combinators;
mod cos;
mod decl;
mod filters;
mod lexical;
#[cfg(test)]
mod test_support;
mod value;
mod xref;

use doodle::{Expr, FormatModule, FormatRef, Label, ValueType, helper::*};

use combinators::{match_str, only, skip_to, then_eol};
use cos::{pdf_cos, pdf_end};
use decl::{resolve, stream};
use lexical::{any_ws, comment, eol, kw, simple_eol, token};
use value::{natural, number, pdf_value, v_name};
use xref::{cross_ref, cross_ref_section, xref_chain, xref_obj};

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
    let xref_obj = xref_obj(module, any_ws, simple_eol, natural, pdf_value, zlib);
    let cross_ref = cross_ref(module, any_ws, eol, cross_ref_section, pdf_dict, xref_obj);
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
