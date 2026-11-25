mod combinators;
mod cos;
mod decl;
mod filters;
#[cfg_attr(not(test), allow(dead_code))]
mod host;
mod lexical;
#[cfg(test)]
mod test_support;
mod value;
mod xref;

use doodle::{Expr, FormatModule, FormatRef, Label, ValueType, helper::*};

use combinators::{match_str, only, skip_to, then_eol};
use lexical::{kw, token};

/// Defines all of the module's formats (so that the whole of it is type-checked and dumped),
/// returning `pdf.main`
pub fn main(module: &mut FormatModule) -> FormatRef {
    let mut pm = PdfModule::new(module);
    let _ = (pm.cos(), pm.filter_chain(), pm.obj_stream_entry());
    pm.main()
}

/// Memoized cache of the [`FormatRef`]s that more than one factory (or the host) uses, so
/// that factories take a [`PdfModule`] instead of one parameter per shared sub-format, and each
/// is defined once.
///
/// Each field is filled on first access, through the [`PdfModule`] method of the same name.
/// Unlike the OpenType dictionary's entries, most of these depend on others (`any_ws` on `eol`
/// and `comment`, `pdf.value` on `any_ws`, `natural` and more), so their initializers take the
/// whole [`PdfModule`]; see [`PdfModule::cached`].
#[derive(Default)]
struct PdfDictionary {
    simple_eol: Option<FormatRef>,
    eol: Option<FormatRef>,
    comment: Option<FormatRef>,
    any_ws: Option<FormatRef>,
    natural: Option<FormatRef>,
    number: Option<FormatRef>,
    v_name: Option<FormatRef>,
    /// `pdf.value` and `pdf.value.dict`
    value: Option<[FormatRef; 2]>,
    zlib: Option<FormatRef>,
    cross_ref_section: Option<FormatRef>,
    cross_ref: Option<FormatRef>,
    obj_stream_entry: Option<FormatRef>,
    resolve_ref: Option<FormatRef>,
    /// `pdf.filter_chain` and `pdf.flate_decode`
    host_filters: Option<[FormatRef; 2]>,
    cos: Option<FormatRef>,
    main: Option<FormatRef>,
}

/// Wraps a [`FormatModule`] together with a [`PdfDictionary`] of shared sub-formats, so that
/// factory functions can pull shared [`FormatRef`]s on demand instead of threading them
/// through every call (after `OpentypeModule`, with the `Option` fields of #362).
///
/// Anything that may define a format needs `&mut self`; [`Self::module_ref`] is for reads
/// (such as `get_format_type`). A factory fetches the refs it needs before it defines its own
/// formats: a `define_batch_with_args` closure can't reach the `PdfModule`, since the batch
/// holds the `FormatModule`.
pub(crate) struct PdfModule<'a> {
    module: &'a mut FormatModule,
    dict: PdfDictionary,
}

impl<'a> PdfModule<'a> {
    pub(crate) fn new(module: &'a mut FormatModule) -> Self {
        Self {
            module,
            dict: PdfDictionary::default(),
        }
    }

    pub(crate) fn module(&mut self) -> &mut FormatModule {
        self.module
    }

    pub(crate) fn module_ref(&self) -> &FormatModule {
        self.module
    }

    /// The value type of `format`'s output
    pub(crate) fn format_type(&self, format: FormatRef) -> ValueType {
        self.module_ref()
            .get_format_type(format.get_level())
            .clone()
    }

    /// The dictionary entry that `field` selects, defined by `init` if it isn't yet.
    ///
    /// `init` gets the whole `PdfModule`, so that it can fetch the entries it depends on;
    /// the borrow of `field` ends before it runs, which `Option::get_or_insert_with` (used for
    /// the entries that only need the `FormatModule`) wouldn't allow.
    fn cached<T: Copy>(
        &mut self,
        field: fn(&mut PdfDictionary) -> &mut Option<T>,
        init: fn(&mut PdfModule<'_>) -> T,
    ) -> T {
        if let Some(r) = *field(&mut self.dict) {
            return r;
        }
        let r = init(self);
        *field(&mut self.dict) = Some(r);
        r
    }

    pub(crate) fn simple_eol(&mut self) -> FormatRef {
        *self
            .dict
            .simple_eol
            .get_or_insert_with(|| lexical::simple_eol(self.module))
    }

    pub(crate) fn eol(&mut self) -> FormatRef {
        self.cached(|d| &mut d.eol, lexical::eol)
    }

    pub(crate) fn comment(&mut self) -> FormatRef {
        self.cached(|d| &mut d.comment, lexical::comment)
    }

    pub(crate) fn any_ws(&mut self) -> FormatRef {
        self.cached(|d| &mut d.any_ws, lexical::any_ws)
    }

    pub(crate) fn natural(&mut self) -> FormatRef {
        *self
            .dict
            .natural
            .get_or_insert_with(|| value::natural(self.module))
    }

    pub(crate) fn number(&mut self) -> FormatRef {
        self.cached(|d| &mut d.number, value::number)
    }

    pub(crate) fn v_name(&mut self) -> FormatRef {
        self.cached(|d| &mut d.v_name, value::v_name)
    }

    /// `pdf.value`, which takes a nesting limit
    pub(crate) fn pdf_value(&mut self) -> FormatRef {
        self.cached(|d| &mut d.value, value::pdf_value)[0]
    }

    /// `pdf.value.dict`, which takes a nesting limit
    pub(crate) fn pdf_dict(&mut self) -> FormatRef {
        self.cached(|d| &mut d.value, value::pdf_value)[1]
    }

    /// The `zlib` format of `doodle-formats`
    pub(crate) fn zlib(&mut self) -> FormatRef {
        *self.dict.zlib.get_or_insert_with(|| {
            let deflate = doodle_formats::format::deflate::main(self.module);
            doodle_formats::format::zlib::main(self.module, deflate)
        })
    }

    pub(crate) fn cross_ref_section(&mut self) -> FormatRef {
        self.cached(|d| &mut d.cross_ref_section, xref::cross_ref_section)
    }

    pub(crate) fn cross_ref(&mut self) -> FormatRef {
        self.cached(|d| &mut d.cross_ref, xref::cross_ref)
    }

    pub(crate) fn obj_stream_entry(&mut self) -> FormatRef {
        self.cached(|d| &mut d.obj_stream_entry, decl::obj_stream_entry)
    }

    pub(crate) fn resolve_ref(&mut self) -> FormatRef {
        self.cached(|d| &mut d.resolve_ref, |pm| decl::resolve(pm)[0])
    }

    /// `pdf.filter_chain`, for the host (see `host`)
    pub(crate) fn filter_chain(&mut self) -> FormatRef {
        self.cached(|d| &mut d.host_filters, filters::host_filter_formats)[0]
    }

    /// `pdf.flate_decode`, for the host (see `host`)
    pub(crate) fn flate_decode(&mut self) -> FormatRef {
        self.cached(|d| &mut d.host_filters, filters::host_filter_formats)[1]
    }

    /// `pdf.cos`, the parse from the end, following the cross-reference chain
    pub(crate) fn cos(&mut self) -> FormatRef {
        self.cached(|d| &mut d.cos, cos::pdf_cos)
    }

    /// `pdf.main`, the front-to-back parse
    pub(crate) fn main(&mut self) -> FormatRef {
        self.cached(|d| &mut d.main, pdf_main)
    }
}

/// `pdf.main`: the `%PDF-` header and its version, then each chunk of objects, cross-reference
/// table, trailer and `startxref`, front to back
fn pdf_main(pm: &mut PdfModule<'_>) -> FormatRef {
    let any_ws = pm.any_ws();
    let eol = pm.eol();
    let natural = pm.natural();
    let number = pm.number();
    let pdf_value = pm.pdf_value();
    let pdf_dict = pm.pdf_dict();
    let cross_ref_section = pm.cross_ref_section();
    let pdf_value_type = pm.format_type(pdf_value);
    let stream = decl::stream(pm);
    let module = pm.module();
    let top_decl_def = module.define_format_args(
        "pdf.top_decl",
        vec![(Label::Borrowed("val"), pdf_value_type)],
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
            // adding `Many AnyWS` here breaks matchtree because pdf_chunk can end in whitespace
        ])),
    )
}
