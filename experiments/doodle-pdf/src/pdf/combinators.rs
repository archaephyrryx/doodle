//! General-purpose format combinators in the style of DaeDaLus (Daedalus.ddl and its built-ins).

use doodle::{Expr, Format, FormatRef, IntoLabel, Label, helper::*};

/// Format that parses nothing and returns a byte-sequence meant to be an ascii string
fn const_str(str: &[u8]) -> Format {
    compute(Expr::Seq(str.iter().copied().map(Expr::U8).collect()))
}

/// Daedalus style record
///
/// Treat `$$` as a singleton-specifier, otherwise equivalent to record-auto
pub(super) fn record_daedalus<Name: IntoLabel + AsRef<str>>(
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
pub(super) fn interpret(assocs: impl IntoIterator<Item = (Format, Expr)>) -> Format {
    union(assocs.into_iter().map(|(f, e)| monad_seq(f, compute(e))))
}

/// Skips bytes up to the first offset at which `f` matches, then parses `f` there.
///
/// If `f` can be parsed without skipping any bytes, equivalent to parsing `f`.
///
/// Projects the value of `f` out of `Format::SkipTo`'s `(count, value)`.
pub(super) fn skip_to(f: Format) -> Format {
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
pub(super) fn count_to(p: Format) -> Format {
    map(
        Format::SkipTo(Box::new(p)),
        lambda("skipped", tuple_proj(var("skipped"), 0)),
    )
}

/// Parse `f` and ensure that there is no trailing content
pub(super) fn only(f: Format) -> Format {
    chain(f, "val", monad_seq(Format::EndOfInput, compute(var("val"))))
}

/// Runs a parser and discards its value, returning `Format::EMPTY`
pub(super) fn void(f: Format) -> Format {
    monad_seq(f, Format::EMPTY)
}

/// Matches a string (as bytes) exactly, and returns it as a Seq(u8)
#[inline(always)]
pub(super) fn match_str(bytes: &[u8]) -> Format {
    byte_seq(bytes)
}

/// Parses `format` and silently consumes an EOL token (failing if not the EOL token is not found)
pub(super) fn then_eol(format: Format, eol: FormatRef) -> Format {
    chain(format, "ret", monad_seq(eol.call(), compute(var("ret"))))
}

#[cfg(test)]
mod tests {
    use super::*;

    use doodle::{FormatModule, decoder::Compiler, read::ReadCtxt};

    use crate::pdf::value::{natural, number};

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
