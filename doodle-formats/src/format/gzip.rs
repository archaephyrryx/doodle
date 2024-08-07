use crate::format::BaseModule;
use doodle::{helper::*, Expr};
use doodle::{Format, FormatModule, FormatRef};

/// gzip
pub fn main(module: &mut FormatModule, deflate: FormatRef, base: &BaseModule) -> FormatRef {
    // NOTE: Packed bits
    //   0 0 0 x x x x x
    // [|7 6 5 4 3 2 1 0|]
    //   ^ ^ ^ | | | | |   reserved [MUST all be zero cf. RFC 1952]
    //         ^ | | | |   FCOMMENT
    //           ^ | | |   FNAME
    //             ^ | |   FEXTRA
    //               ^ |   FHCRC
    //                 ^   FTEXT
    let flg = where_lambda(
        packed_bits_u8(
            [3, 1, 1, 1, 1, 1],
            [
                "__reserved",
                "fcomment",
                "fname",
                "fextra",
                "fhcrc",
                "ftext",
            ],
        ),
        "flags",
        expr_eq(record_proj(var("flags"), "__reserved"), Expr::U8(0)),
    );

    let header = module.define_format(
        "gzip.header",
        record([
            ("magic", is_bytes(b"\x1F\x8B")),
            ("method", base.u8()),
            ("file-flags", flg),
            ("timestamp", base.u32le()),
            ("compression-flags", base.u8()),
            ("os-id", base.u8()),
        ]),
    );

    let footer = module.define_format(
        "gzip.footer",
        record([("crc", base.u32le()), ("length", base.u32le())]),
    );

    let fname_flag = is_nonzero_u8(record_projs(var("header"), &["file-flags", "fname"]));
    let fname = module.define_format("gzip.fname", base.asciiz_string());

    let fextra_flag = is_nonzero_u8(record_projs(var("header"), &["file-flags", "fextra"]));
    let fextra_subfield = module.define_format(
        "gzip.fextra.subfield",
        record([
            ("si1", base.ascii_char()),
            ("si2", base.ascii_char()),
            ("len", base.u16le()),
            ("data", repeat_count(var("len"), base.u8())),
        ]),
    );
    let fextra = module.define_format(
        "gzip.fextra",
        record([
            ("xlen", base.u16le()),
            (
                "subfields",
                Format::Slice(var("xlen"), Box::new(repeat(fextra_subfield.call()))),
            ),
        ]),
    );

    let fcomment_flag = is_nonzero_u8(record_projs(var("header"), &["file-flags", "fcomment"]));

    let fcomment = module.define_format(
        "gzip.fcomment",
        record([
            ("comment", base.asciiz_string()), // actually LATIN-1 but asciiz is good enough for now
        ]),
    );

    let fhcrc_flag = is_nonzero_u8(record_projs(var("header"), &["file-flags", "fhcrc"]));
    let fhcrc = module.define_format(
        "gzip.fhcrc",
        record([
            ("crc", base.u16le()), // two least significant bytes of CRC32 of all prior bytes in the header
        ]),
    );

    module.define_format(
        "gzip.main",
        repeat1(record([
            ("header", header.call()),
            ("fextra", cond_maybe(fextra_flag, fextra.call())),
            ("fname", cond_maybe(fname_flag, fname.call())),
            ("fcomment", cond_maybe(fcomment_flag, fcomment.call())),
            ("fhcrc", cond_maybe(fhcrc_flag, fhcrc.call())),
            ("data", Format::Bits(Box::new(deflate.call()))),
            ("footer", footer.call()),
        ])),
    )
}
