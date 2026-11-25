//! The host's side of the DaeDaLus host primitives (`Decrypt`, `LZWDecode` and the like, #361),
//! as a second pass over what the grammar leaves to the host.
//!
//! DaeDaLus declares such primitives without a body and calls them during the parse. Here the
//! grammar never calls out: where it would need one, it gives a handle instead (an
//! `unsupported` or `encrypted` stream body, see `apply_filters`, or a `packed` object, see
//! `resolve`), and the host finishes the job, calling back into the grammar (`pdf.flate_decode`,
//! `pdf.obj_stream_entry`) for the parts it can do. This is the OpenType approach of a first
//! pass that records offsets (`Phantom` reads relative to a view) and a second, host-driven
//! pass that parses at them (`api_helper::otf_metrics`'s `reify`).
//!
//! The second pass runs on the interpreter: each grammar call compiles a program whose
//! arguments are the first pass's values, turned back into `Expr` literals ([`value_to_expr`]).

use anyhow::{Result, anyhow, bail};
use doodle::{
    Expr, Format, FormatModule, FormatRef,
    decoder::{Compiler, Value},
    helper::*,
    numeric::core::Expr as NumExpr,
    read::ReadCtxt,
};

use super::PdfModule;

/// The formats the host calls, taken from a [`PdfModule`] (defining any not yet defined), so
/// that the host then needs only the `FormatModule`, read-only
#[derive(Clone, Copy)]
pub(crate) struct HostFormats {
    cos: FormatRef,
    resolve_ref: FormatRef,
    filter_chain: FormatRef,
    flate_decode: FormatRef,
    obj_stream_entry: FormatRef,
}

impl HostFormats {
    pub(crate) fn new(pm: &mut PdfModule<'_>) -> Self {
        HostFormats {
            cos: pm.cos(),
            resolve_ref: pm.resolve_ref(),
            filter_chain: pm.filter_chain(),
            flate_decode: pm.flate_decode(),
            obj_stream_entry: pm.obj_stream_entry(),
        }
    }
}

/// What the host supplies: the DaeDaLus host primitives that the grammar leaves to it.
pub(crate) trait HostPrimitives {
    /// Applies the filter named `filter` (such as `/LZWDecode`) with its `/DecodeParms` entry
    /// `params` (a `pdf.value` dict, if there is one) to `bytes`, or `None` if it can't.
    /// `/FlateDecode` never gets here; the grammar applies it.
    fn decode(&self, filter: &[u8], params: Option<&Value>, bytes: &[u8]) -> Option<Vec<u8>>;

    /// DaeDaLus `Decrypt` of a stream body of object `obj gen`, or `None` if it can't.
    fn decrypt(&self, obj: u64, gen_: u64, bytes: &[u8]) -> Option<Vec<u8>> {
        let _ = (obj, gen_, bytes);
        None
    }
}

/// A resolved object: a value, or a stream's decoded body
#[derive(Debug)]
pub(crate) enum HostDecl {
    Value(Value),
    Stream(Vec<u8>),
}

/// The host's driver over one PDF `input`: `pdf.cos` is run once, then [`Host::resolve`]
/// resolves objects, finishing with `prims` what the grammar leaves.
pub(crate) struct Host<'a, P> {
    module: &'a FormatModule,
    formats: HostFormats,
    input: &'a [u8],
    prims: P,
    /// the `pdf.cos` result
    cos: Value,
}

impl<'a, P: HostPrimitives> Host<'a, P> {
    pub(crate) fn new(
        module: &'a FormatModule,
        formats: HostFormats,
        input: &'a [u8],
        prims: P,
    ) -> Result<Self> {
        let mut host = Host {
            module,
            formats,
            input,
            prims,
            cos: Value::Tuple(vec![]),
        };
        host.cos = host.run(&formats.cos.call())?;
        Ok(host)
    }

    /// The `pdf.cos` result
    pub(crate) fn cos(&self) -> &Value {
        &self.cos
    }

    /// Runs `format` over the input, from its start
    fn run(&self, format: &Format) -> Result<Value> {
        let prog = Compiler::compile_program(self.module, format)?;
        let (value, _) = prog
            .run(ReadCtxt::new(self.input))
            .map_err(|e| anyhow!("{e:?}"))?;
        Ok(value)
    }

    /// Object `obj gen`, as DaeDaLus `ResolveDeclRef` gives it, with a stream's body decoded
    /// (by the grammar, or here). Fails where `pdf.resolve_ref` does, or where the host can't
    /// decrypt or decode what is left to it.
    pub(crate) fn resolve(&self, obj: u64, gen_: u64) -> Result<HostDecl> {
        let cos = |name: &str| value_to_expr(field(&self.cos, name)?);
        let decl = self.run(&self.formats.resolve_ref.call_args(vec![
            cos("header_offset")?,
            cos("sections")?,
            cos("encrypted")?,
            Expr::U64(obj),
            Expr::U64(gen_),
            Expr::Seq(vec![]),
            Expr::U64(256),
        ]))?;
        match variant(&decl)? {
            ("value", v) => Ok(HostDecl::Value(v.clone())),
            ("stream", s) => Ok(HostDecl::Stream(self.stream_bytes(obj, gen_, s)?)),
            ("packed", p) => {
                let container = u64_of(field(p, "container")?)?;
                let bytes = self.stream_bytes(container, 0, field(p, "stream")?)?;
                let v = self.run(&self.formats.obj_stream_entry.call_args(vec![
                    bytes_expr(&bytes),
                    value_to_expr(field(p, "n")?)?,
                    value_to_expr(field(p, "first")?)?,
                    Expr::U64(obj),
                    value_to_expr(field(p, "index")?)?,
                ]))?;
                Ok(HostDecl::Value(v))
            }
            (other, _) => bail!("unexpected pdf.resolve_ref result `{other}`"),
        }
    }

    /// The decoded body of `stream` (a `pdf.resolve_ref` stream record) of object `obj gen`
    fn stream_bytes(&self, obj: u64, gen_: u64, stream: &Value) -> Result<Vec<u8>> {
        let header = field(stream, "header")?;
        match variant(field(stream, "body")?)? {
            ("ok", b) => bytes_of(b),
            ("encrypted", raw) => {
                let plain = self
                    .prims
                    .decrypt(obj, gen_, &bytes_of(raw)?)
                    .ok_or_else(|| anyhow!("host can't decrypt {obj} {gen_}"))?;
                self.apply_chain(header, plain)
            }
            ("unsupported", u) => self.apply_chain(header, bytes_of(field(u, "raw")?)?),
            (other, _) => bail!("unexpected stream body `{other}`"),
        }
    }

    /// Applies the filters of the stream dictionary `header` to `bytes`, in order:
    /// `/FlateDecode` by the grammar (`pdf.flate_decode`), the others by the host
    fn apply_chain(&self, header: &Value, mut bytes: Vec<u8>) -> Result<Vec<u8>> {
        let val = variant_expr("dict", value_to_expr(header)?);
        let chain = self.run(&self.formats.filter_chain.call_args(vec![val]))?;
        let params = seq_of(field(&chain, "params")?)?;
        for (i, filter) in seq_of(field(&chain, "filters")?)?.iter().enumerate() {
            let name = match variant(filter)? {
                ("name", n) => bytes_of(n)?,
                _ => bail!("filter is not a name"),
            };
            let param = params.get(i).copied();
            bytes = if name == b"/FlateDecode" {
                let param = match param {
                    Some(p) => expr_some(value_to_expr(p)?),
                    None => expr_none(),
                };
                bytes_of(
                    &self.run(
                        &self
                            .formats
                            .flate_decode
                            .call_args(vec![param, bytes_expr(&bytes)]),
                    )?,
                )?
            } else {
                // DaeDaLus `FilterParam`: `null` is no parameters
                let param = param.filter(|p| !matches!(variant(p), Ok(("null", _))));
                self.prims
                    .decode(&name, param, &bytes)
                    .ok_or_else(|| anyhow!("host can't apply {}", String::from_utf8_lossy(&name)))?
            };
        }
        Ok(bytes)
    }
}

/// `v` as an `Expr` literal, so that the host can pass a value from one grammar call to the
/// next. `Mapped` and `Branch` values give their nominal values.
pub(crate) fn value_to_expr(v: &Value) -> Result<Expr> {
    let all = |vs: &mut dyn Iterator<Item = &Value>| vs.map(value_to_expr).collect::<Result<_>>();
    Ok(match v {
        Value::Bool(b) => Expr::Bool(*b),
        Value::U8(n) => Expr::U8(*n),
        Value::U16(n) => Expr::U16(*n),
        Value::U32(n) => Expr::U32(*n),
        Value::U64(n) => Expr::U64(*n),
        Value::Numeric(c) => Expr::Numeric(Box::new(NumExpr::Const((**c).clone()))),
        Value::Option(None) => expr_none(),
        Value::Option(Some(x)) => expr_some(value_to_expr(x)?),
        Value::Tuple(vs) => Expr::Tuple(all(&mut vs.iter())?),
        Value::Record(fs) => Expr::Record(
            fs.iter()
                .map(|(l, v)| Ok((l.clone(), value_to_expr(v)?)))
                .collect::<Result<_>>()?,
        ),
        Value::Variant(l, x) => Expr::Variant(l.clone(), Box::new(value_to_expr(x)?)),
        Value::Seq(s) => Expr::Seq(all(&mut s.iter())?),
        Value::Mapped(_, x) | Value::Branch(_, x) => value_to_expr(x)?,
        other => bail!("no Expr literal for {other:?}"),
    })
}

fn variant_expr(name: &'static str, x: Expr) -> Expr {
    Expr::Variant(name.into(), Box::new(x))
}

fn bytes_expr(bytes: &[u8]) -> Expr {
    Expr::Seq(bytes.iter().map(|b| Expr::U8(*b)).collect())
}

/// `v` without `Mapped` and `Branch` wrappers
fn nominal(v: &Value) -> &Value {
    match v {
        Value::Mapped(_, x) | Value::Branch(_, x) => nominal(x),
        _ => v,
    }
}

fn field<'v>(v: &'v Value, name: &str) -> Result<&'v Value> {
    match nominal(v) {
        Value::Record(fs) => fs
            .iter()
            .find(|(l, _)| l.as_ref() == name)
            .map(|(_, v)| v)
            .ok_or_else(|| anyhow!("no field `{name}`")),
        other => bail!("not a record (for `{name}`): {other:?}"),
    }
}

fn variant(v: &Value) -> Result<(&str, &Value)> {
    match nominal(v) {
        Value::Variant(l, x) => Ok((l.as_ref(), x)),
        other => bail!("not a variant: {other:?}"),
    }
}

fn seq_of(v: &Value) -> Result<Vec<&Value>> {
    match nominal(v) {
        Value::Seq(s) => Ok(s.iter().collect()),
        other => bail!("not a sequence: {other:?}"),
    }
}

fn bytes_of(v: &Value) -> Result<Vec<u8>> {
    seq_of(v)?
        .into_iter()
        .map(|b| match nominal(b) {
            Value::U8(b) => Ok(*b),
            other => bail!("not a byte: {other:?}"),
        })
        .collect()
}

fn u64_of(v: &Value) -> Result<u64> {
    match nominal(v) {
        Value::U64(n) => Ok(*n),
        other => bail!("not a u64: {other:?}"),
    }
}

/// PDF `LZWDecode` (ISO 32000-1 7.4.4) of `data`: codes from 9 to 12 bits, `256` clears the
/// table and `257` ends the data (as does running out of whole codes). With `early_change`
/// (the default `/EarlyChange 1`), the code width grows one code early. `None` for a code
/// that isn't in the table.
pub(crate) fn lzw_decode(data: &[u8], early_change: bool) -> Option<Vec<u8>> {
    const CLEAR: usize = 256;
    const EOD: usize = 257;
    let fresh = || -> Vec<Vec<u8>> {
        let mut t: Vec<Vec<u8>> = (0..=255u8).map(|b| vec![b]).collect();
        t.extend([vec![], vec![]]);
        t
    };
    let mut table = fresh();
    let mut width = 9;
    let mut prev: Option<Vec<u8>> = None;
    let (mut buf, mut nbits, mut pos) = (0u32, 0, 0);
    let mut out = Vec::new();
    loop {
        while nbits < width {
            let &b = data.get(pos)?;
            pos += 1;
            buf = (buf << 8) | u32::from(b);
            nbits += 8;
        }
        let code = ((buf >> (nbits - width)) & ((1 << width) - 1)) as usize;
        nbits -= width;
        match code {
            CLEAR => {
                table = fresh();
                width = 9;
                prev = None;
                continue;
            }
            EOD => return Some(out),
            _ => {}
        }
        let entry = if code < table.len() {
            table[code].clone()
        } else if code == table.len() {
            let p = prev.as_ref()?;
            let mut e = p.clone();
            e.push(p[0]);
            e
        } else {
            return None;
        };
        out.extend_from_slice(&entry);
        if let Some(mut p) = prev.take()
            && table.len() < 4096
        {
            p.push(entry[0]);
            table.push(p);
        }
        prev = Some(entry);
        if table.len() + usize::from(early_change) >= (1 << width) && width < 12 {
            width += 1;
        }
    }
}

/// A host with `LZWDecode` (default parameters only: `/EarlyChange 1`, no predictor), and an
/// optional `Decrypt`
pub(crate) struct LzwHost<D> {
    pub(crate) decrypt: D,
}

impl<D: Fn(u64, u64, &[u8]) -> Option<Vec<u8>>> HostPrimitives for LzwHost<D> {
    fn decode(&self, filter: &[u8], params: Option<&Value>, bytes: &[u8]) -> Option<Vec<u8>> {
        match (filter, params) {
            (b"/LZWDecode", None) => lzw_decode(bytes, true),
            _ => None,
        }
    }

    fn decrypt(&self, obj: u64, gen_: u64, bytes: &[u8]) -> Option<Vec<u8>> {
        (self.decrypt)(obj, gen_, bytes)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;

    use crate::pdf::test_support::{Ent, HELLO_Z, Obj, build_objects, lzw_encode, objstm_pdf_raw};

    /// Objects 1 and 2 packed in object stream 5, at indexes 0 and 1
    const PACKED_ENTS: [Ent; 6] = [
        Ent::Free,
        Ent::Packed(5, 0),
        Ent::Packed(5, 1),
        Ent::Free,
        Ent::Free,
        Ent::At(5),
    ];
    use crate::pdf::PdfModule;

    /// The example of ISO 32000-1 7.4.4.2: `-----A---B` is the codes
    /// `256 45 258 258 65 259 66 257`, in 9 bits each.
    #[test]
    fn lzw_decode_spec_example() {
        let data = [0x80, 0x0B, 0x60, 0x50, 0x22, 0x0C, 0x0C, 0x85, 0x01];
        assert_eq!(lzw_decode(&data, true).as_deref(), Some(&b"-----A---B"[..]));
        assert_eq!(lzw_encode(b"-----A---B"), data);
    }

    /// [`lzw_decode`] undoes the test encoder across the 9-, 10- and 11-bit code widths, and
    /// rejects a code past the table.
    #[test]
    fn lzw_round_trip() {
        let mut x = 1u32;
        let noisy: Vec<u8> = (0..3000)
            .map(|_| {
                x = x.wrapping_mul(1_103_515_245).wrapping_add(12345);
                b"abcdefgh"[(x >> 16) as usize % 8]
            })
            .collect();
        for data in [&b""[..], b"a", b"abababababababab", &noisy] {
            assert_eq!(lzw_decode(&lzw_encode(data), true).as_deref(), Some(data));
        }
        // 256, then 300 (not yet in the table)
        assert_eq!(lzw_decode(&[0x80, 0x4B, 0x00], true), None);
    }

    /// The decrypting test host: `Decrypt` reverses the bytes, and records which object
    /// asked
    fn host_prims(
        calls: &RefCell<Vec<(u64, u64)>>,
    ) -> LzwHost<impl Fn(u64, u64, &[u8]) -> Option<Vec<u8>> + '_> {
        LzwHost {
            decrypt: move |obj, gen_, bytes: &[u8]| {
                calls.borrow_mut().push((obj, gen_));
                Some(bytes.iter().rev().copied().collect())
            },
        }
    }

    fn stream_obj(dict: &str, body: &[u8]) -> &'static [u8] {
        [
            format!("<< /Length {}{dict} >>\nstream\n", body.len()).as_bytes(),
            body,
            b"\nendstream",
        ]
        .concat()
        .leak()
    }

    fn expect_bytes(decl: HostDecl) -> Vec<u8> {
        match decl {
            HostDecl::Stream(bytes) => bytes,
            other => panic!("not a stream: {other:?}"),
        }
    }

    fn expect_value_kind(decl: &HostDecl) -> &str {
        match decl {
            HostDecl::Value(v) => variant(v).unwrap().0,
            other => panic!("not a value: {other:?}"),
        }
    }

    /// The host finishes what the grammar leaves: an `/LZWDecode` stream, a chain of
    /// `/LZWDecode` then `/FlateDecode` (the host's filter, then the grammar's), and an
    /// object packed in an `/LZWDecode` object stream (through `pdf.obj_stream_entry`);
    /// a filter the host lacks still fails.
    #[test]
    fn host_applies_filters() {
        let mut module = FormatModule::new();
        let formats = HostFormats::new(&mut PdfModule::new(&mut module));
        let calls = RefCell::new(Vec::new());

        let hello = b"hello hello hello hello";
        let input = build_objects(&[&[
            (1, 0, Obj::Def(b"<< /Type /Catalog >>")),
            (
                2,
                0,
                Obj::Def(stream_obj(" /Filter /LZWDecode", &lzw_encode(hello))),
            ),
            (
                3,
                0,
                Obj::Def(stream_obj(
                    " /Filter [/LZWDecode /FlateDecode]",
                    &lzw_encode(HELLO_Z),
                )),
            ),
            (4, 0, Obj::Def(stream_obj(" /Filter /DCTDecode", b"jpeg"))),
        ]]);
        let host = Host::new(&module, formats, &input, host_prims(&calls)).unwrap();
        assert_eq!(expect_bytes(host.resolve(2, 0).unwrap()), hello);
        assert_eq!(expect_bytes(host.resolve(3, 0).unwrap()), hello);
        assert!(host.resolve(4, 0).is_err());
        assert_eq!(expect_value_kind(&host.resolve(1, 0).unwrap()), "dict");

        // objects 1 (a dict) and 2 (a number) in object stream 5, LZW-encoded
        let packed = objstm_pdf_raw(
            "/Type /ObjStm /N 2 /First 9 /Filter /LZWDecode",
            &lzw_encode(b"1 0 2 21 << /Type /Catalog >> 42"),
            &PACKED_ENTS,
        );
        let host = Host::new(&module, formats, &packed, host_prims(&calls)).unwrap();
        assert_eq!(expect_value_kind(&host.resolve(1, 0).unwrap()), "dict");
        assert_eq!(expect_value_kind(&host.resolve(2, 0).unwrap()), "number");
        assert!(calls.borrow().is_empty(), "nothing is encrypted");
    }

    /// In an encrypted file, the host decrypts each stream (as object `obj gen`, or as its
    /// container for a packed object) and then applies its filters; a `/Type /XRef` stream
    /// isn't decrypted.
    #[test]
    fn host_decrypts() {
        let mut module = FormatModule::new();
        let formats = HostFormats::new(&mut PdfModule::new(&mut module));
        let calls = RefCell::new(Vec::new());
        let rev = |b: &[u8]| b.iter().rev().copied().collect::<Vec<u8>>();

        let hello = b"hello hello hello hello";
        let mut input = build_objects(&[&[
            (1, 0, Obj::Def(b"<< /Type /Catalog >>")),
            (2, 0, Obj::Def(stream_obj("", &rev(b"plain text")))),
            (
                3,
                0,
                Obj::Def(stream_obj(" /Filter /FlateDecode", &rev(HELLO_Z))),
            ),
            (
                4,
                0,
                Obj::Def(stream_obj(
                    " /Filter [/LZWDecode /FlateDecode]",
                    &rev(&lzw_encode(HELLO_Z)),
                )),
            ),
            (
                6,
                0,
                Obj::Def(stream_obj(" /Type /XRef /Filter /FlateDecode", HELLO_Z)),
            ),
        ]]);
        let at = input.windows(9).position(|w| w == b"/Root 1 0").unwrap();
        input.splice(at..at, b"/Encrypt << /Filter /Standard >> ".iter().copied());
        let host = Host::new(&module, formats, &input, host_prims(&calls)).unwrap();
        assert_eq!(expect_bytes(host.resolve(2, 0).unwrap()), b"plain text");
        assert_eq!(expect_bytes(host.resolve(3, 0).unwrap()), hello);
        assert_eq!(expect_bytes(host.resolve(4, 0).unwrap()), hello);
        assert_eq!(expect_bytes(host.resolve(6, 0).unwrap()), hello);
        assert_eq!(*calls.borrow(), [(2, 0), (3, 0), (4, 0)]);

        // objects 1 and 2 packed in encrypted object stream 5
        calls.borrow_mut().clear();
        let mut packed = objstm_pdf_raw(
            "/Type /ObjStm /N 2 /First 9",
            &rev(b"1 0 2 21 << /Type /Catalog >> 42"),
            &PACKED_ENTS,
        );
        let at = packed.windows(9).position(|w| w == b"/Root 1 0").unwrap();
        packed.splice(at..at, b"/Encrypt << /Filter /Standard >> ".iter().copied());
        let host = Host::new(&module, formats, &packed, host_prims(&calls)).unwrap();
        let root = match nominal(field(host.cos(), "root").unwrap()) {
            Value::Option(Some(d)) => variant(d).unwrap().0,
            other => panic!("no /Root: {other:?}"),
        };
        assert_eq!(root, "packed");
        assert_eq!(expect_value_kind(&host.resolve(1, 0).unwrap()), "dict");
        assert_eq!(expect_value_kind(&host.resolve(2, 0).unwrap()), "number");
        assert_eq!(*calls.borrow(), [(5, 0), (5, 0)]);
    }
}
