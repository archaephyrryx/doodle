//! PDF builders shared by the tests of several modules.

/// zlib of `hello hello hello hello` (compressed, with back-references)
pub(super) const HELLO_Z: &[u8] = &[
    0x78, 0xda, 0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x57, 0xc8, 0x40, 0x27, 0x01, 0x68, 0x03, 0x08, 0xb1,
];

/// A cross-reference section for [`build_pdf`], identified by its trailer's `/Size`, with
/// optional `/Prev` and `/XRefStm` links to other sections by index. An index past the last
/// section stands for an offset past the end of the file.
///
/// It is a classic section, or with `stream`, a cross-reference stream object.
pub(super) struct Sec {
    size: u64,
    prev: Option<usize>,
    xrefstm: Option<usize>,
    stream: Option<Stm>,
}

/// The rest of a cross-reference stream's dictionary (other than `/Size` and the links),
/// and its raw body. `/Length` is the body's length unless `dict` gives one.
pub(super) struct Stm {
    dict: String,
    data: Vec<u8>,
}

pub(super) fn sec(size: u64, prev: Option<usize>, xrefstm: Option<usize>) -> Sec {
    Sec {
        size,
        prev,
        xrefstm,
        stream: None,
    }
}

pub(super) fn stm(size: u64, prev: Option<usize>, dict: &str, data: &[u8]) -> Sec {
    Sec {
        size,
        prev,
        xrefstm: None,
        stream: Some(Stm {
            dict: dict.to_string(),
            data: data.to_vec(),
        }),
    }
}

/// The fields of each entry, as big-endian numbers of the widths `w`
pub(super) fn be_rows(w: &[usize], entries: &[&[u64]]) -> Vec<u8> {
    entries
        .iter()
        .flat_map(|fields| {
            w.iter()
                .zip(fields.iter())
                .flat_map(|(&w, &f)| f.to_be_bytes()[8 - w.min(8)..].to_vec())
                .collect::<Vec<u8>>()
        })
        .collect()
}

/// `prefix`, a `%PDF-1.4` header, the sections `secs`, then a `startxref` block for each
/// index in `startxrefs`, then `suffix`. Offsets are relative to the header, and links are
/// written with ten digits, so a section's length doesn't depend on where its links point.
pub(super) fn build_pdf(
    prefix: &[u8],
    secs: &[Sec],
    startxrefs: &[usize],
    suffix: &[u8],
) -> Vec<u8> {
    const HEADER: &[u8] = b"%PDF-1.4\n";
    let render = |sec: &Sec, offsets: &[usize]| {
        let link = |key: &str, ix: Option<usize>| match ix {
            Some(ix) => format!(
                " /{key} {:010}",
                offsets.get(ix).copied().unwrap_or(9_999_999)
            ),
            None => String::new(),
        };
        let links = format!("{}{}", link("Prev", sec.prev), link("XRefStm", sec.xrefstm));
        match &sec.stream {
            None => format!(
                "xref\n0 1\n0000000000 65535 f\r\ntrailer\n<< /Size {}{links} >>\n",
                sec.size,
            )
            .into_bytes(),
            Some(Stm { dict, data }) => {
                let len = if dict.contains("/Length") {
                    String::new()
                } else {
                    format!(" /Length {}", data.len())
                };
                [
                    format!(
                        "9 0 obj\n<< /Size {}{links} {dict}{len} >>\nstream\n",
                        sec.size
                    )
                    .as_bytes(),
                    data,
                    b"\nendstream\nendobj\n",
                ]
                .concat()
            }
        }
    };
    let mut offsets = Vec::new();
    let mut at = HEADER.len();
    for sec in secs {
        offsets.push(at);
        at += render(sec, &[]).len();
    }
    let mut out = [prefix, HEADER].concat();
    for sec in secs {
        out.extend(render(sec, &offsets));
    }
    for &ix in startxrefs {
        out.extend(format!("startxref\n{}\n%%EOF\n", offsets[ix]).into_bytes());
    }
    out.extend_from_slice(suffix);
    out
}

/// An xref entry for [`build_objects`]: an object with this text between `obj` and
/// `endobj`, a free entry, or an entry pointing at the offset of another object.
pub(super) enum Obj {
    Def(&'static [u8]),
    Free,
    At(u64),
}

/// A `%PDF-1.4` file of incremental sections, oldest first: each writes its `Def` objects,
/// then a classic xref listing all its entries (as `(number, generation, entry)`), and a
/// trailer with `/Root 1 0 R` and a `/Prev` to the section before; then a `startxref` to
/// the last. Each object is written as `N G obj\n…\nendobj\n`.
pub(super) fn build_objects(sections: &[&[(u64, u64, Obj)]]) -> Vec<u8> {
    let mut out = b"%PDF-1.4\n".to_vec();
    let mut offsets = std::collections::BTreeMap::new();
    let mut prev = None;
    for entries in sections {
        for (n, g, obj) in entries.iter() {
            if let Obj::Def(body) = obj {
                offsets.insert(*n, out.len());
                out.extend(format!("{n} {g} obj\n").into_bytes());
                out.extend_from_slice(body);
                out.extend_from_slice(b"\nendobj\n");
            }
        }
        let xref_at = out.len();
        out.extend_from_slice(b"xref\n");
        for (n, g, obj) in entries.iter() {
            let line = match obj {
                Obj::Def(_) => format!("{:010} {g:05} n\r\n", offsets[n]),
                Obj::At(m) => format!("{:010} {g:05} n\r\n", offsets[m]),
                Obj::Free => format!("0000000000 {g:05} f\r\n"),
            };
            out.extend(format!("{n} 1\n{line}").into_bytes());
        }
        let prev_link = prev.map_or(String::new(), |p| format!(" /Prev {p}"));
        out.extend(format!("trailer\n<< /Size 100 /Root 1 0 R{prev_link} >>\n").into_bytes());
        prev = Some(xref_at);
    }
    out.extend(format!("startxref\n{}\n%%EOF\n", prev.unwrap()).into_bytes());
    out
}

/// An xref entry for [`objstm_pdf`]: free, at the offset of object `5` or `6`, or packed at
/// an index of an object stream.
pub(super) enum Ent {
    Free,
    At(u64),
    Packed(u64, u64),
}

/// A `%PDF-1.5` file with an object stream `5 0` (its dictionary is `stm_dict` plus `/First`
/// and `/Length`, unless `stm_dict` gives them, and its body is `index` then `values`), an
/// optional object `6 0` with the text `obj6`, and a cross-reference stream (`/W [1 2 1]`)
/// with an entry for each object number from `0`, and `/Root 1 0 R`.
pub(super) fn objstm_pdf(
    stm_dict: &str,
    index: &str,
    values: &str,
    obj6: Option<&str>,
    ents: &[Ent],
) -> Vec<u8> {
    let first = if stm_dict.contains("/First") {
        String::new()
    } else {
        format!(" /First {}", index.len())
    };
    objstm_pdf_with(
        &format!("{stm_dict}{first}"),
        format!("{index}{values}").as_bytes(),
        obj6,
        ents,
    )
}

/// [`objstm_pdf`] with the object stream's body given as raw bytes (such as an encoded one),
/// and no object `6`; `stm_dict` must give `/First`
pub(super) fn objstm_pdf_raw(stm_dict: &str, body: &[u8], ents: &[Ent]) -> Vec<u8> {
    objstm_pdf_with(stm_dict, body, None, ents)
}

fn objstm_pdf_with(stm_dict: &str, body: &[u8], obj6: Option<&str>, ents: &[Ent]) -> Vec<u8> {
    let mut out = b"%PDF-1.5\n".to_vec();
    let mut offsets = std::collections::BTreeMap::new();
    let len = if stm_dict.contains("/Length") {
        String::new()
    } else {
        format!(" /Length {}", body.len())
    };
    offsets.insert(5, out.len());
    out.extend(format!("5 0 obj\n<< {stm_dict}{len} >>\nstream\n").into_bytes());
    out.extend_from_slice(body);
    out.extend_from_slice(b"\nendstream\nendobj\n");
    if let Some(text) = obj6 {
        offsets.insert(6, out.len());
        out.extend(format!("6 0 obj\n{text}\nendobj\n").into_bytes());
    }
    let rows: Vec<Vec<u64>> = ents
        .iter()
        .map(|e| match e {
            Ent::Free => vec![0, 0, 0],
            Ent::At(n) => vec![1, offsets[n] as u64, 0],
            Ent::Packed(c, i) => vec![2, *c, *i],
        })
        .collect();
    let rows: Vec<&[u64]> = rows.iter().map(|r| r.as_slice()).collect();
    let data = be_rows(&[1, 2, 1], &rows);
    let xref_at = out.len();
    out.extend(
        format!(
            "9 0 obj\n<< /Type /XRef /Size {} /W [1 2 1] /Root 1 0 R /Length {} >>\nstream\n",
            ents.len(),
            data.len()
        )
        .into_bytes(),
    );
    out.extend(data);
    out.extend(format!("\nendstream\nendobj\nstartxref\n{xref_at}\n%%EOF\n").into_bytes());
    out
}

/// PDF `LZWDecode`'s encoding (ISO 32000-1 7.4.4), with `/EarlyChange 1`: a clear code, the
/// codes of `data` (each the longest run already in the table), then the end code, packed
/// big-endian in 9 to 12 bits. The table is cleared again before it would pass 4096 entries.
pub(super) fn lzw_encode(data: &[u8]) -> Vec<u8> {
    use std::collections::HashMap;
    let mut out = Vec::new();
    let (mut buf, mut nbits) = (0u32, 0u32);
    let mut emit = |code: u32, width: u32, out: &mut Vec<u8>| {
        buf = (buf << width) | code;
        nbits += width;
        while nbits >= 8 {
            out.push((buf >> (nbits - 8)) as u8);
            nbits -= 8;
        }
        buf &= (1 << nbits) - 1;
    };
    let fresh = || {
        (0..=255u8)
            .map(|b| (vec![b], u32::from(b)))
            .collect::<HashMap<_, _>>()
    };
    let mut table = fresh();
    // the next code to add; the decoder's table is one entry behind, so the width grows when
    // `next` reaches the decoder's threshold (`len + 1 >= 2^width`, with `len = next - 1`)
    let mut next = 258u32;
    let width = |next: u32| match next {
        ..512 => 9,
        512..1024 => 10,
        1024..2048 => 11,
        _ => 12,
    };
    emit(256, 9, &mut out);
    let mut w: Vec<u8> = Vec::new();
    for &c in data {
        let mut wc = w.clone();
        wc.push(c);
        if table.contains_key(&wc) {
            w = wc;
            continue;
        }
        emit(table[&w], width(next), &mut out);
        if next == 4095 {
            emit(256, width(next), &mut out);
            table = fresh();
            next = 258;
        } else {
            table.insert(wc, next);
            next += 1;
        }
        w = vec![c];
    }
    if !w.is_empty() {
        emit(table[&w], width(next), &mut out);
        next += 1;
    }
    emit(257, width(next.min(4095)), &mut out);
    if nbits > 0 {
        out.push((buf << (8 - nbits)) as u8);
    }
    out
}
