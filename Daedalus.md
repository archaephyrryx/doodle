# Daedalus Notes

## 3.1 (Primitive Parsers)

* `^<value>` is achievable through `compute`
* `Fail <msg>` requires a refactor we have discussed but never implemented
  * This could be a modification of `Fail` itself, or a wrapper using `StyleHint` (see [#329](https://github.com/yeslogic/doodle/issues/329))
* We don't have a notion of character classes for the parser `$[c]`, but we could emulate this with `ByteSet` constants
* `Match <string>` is achievable through `byte_seq`

## 3.2 (Sequential Composition)

The syntax `{ P1; ...; Pn }` can be emulated with `LetFormat`/`MonadSeq`; `pseudo_record` in particular makes this trivial.

### Example Translations

```ddl
def Add2 =
  block
    let x = BEUInt64
    let y = BEUInt64
    ^ x + y

def StatementSemi =
  block
    $$ = Statement
    $[';']
```

```rust
let add2 =
    pseudo_record(
        [("x", u64be()), ("y", u64be())],
        compute(add(var("x"), var("y")))
    );

let statement_semi =
    chain(
        statement, // defined elsewhere,
        "ret",
        monad_seq(
            is_byte(b';'),
            compute(var("ret"))
        )
    );
```

## 3.3 (Parallel Composition)

There is currently no way of performing *unbiased* composition in `doodle`; all parallel compositions
are first-come-first-served and will bias towards the first non-error result.

`First` (`<|`) is therefore supported, while `Choose` (`|`) is not. Adding support for `Choose` is possible but would require
a decent amount of work (e.g. `UnionMultidet`).

## 3.4 (Repetition)

* Kleene Star - `Many <P>` is just `Repeat`, while `Many (1..) <P>` is `Repeat1`; bounded repetition `Many (n..m) <P>` is `RepeatBetween` (or `RepeatRange`)
* Kleene Star with State - At least some cases of `many (x = s) <P>` can be emulated with `Map(Repeat, LeftFold)`, while `AccumUntil` might be usable in other cases. There is no generic `many (x = s) <P>` combinator, and implementing one would require a bespoke `Format`. Any particular instance can instead be written as a self-recursive format that takes the state as an argument (`FormatModule::define_batch_with_args`) and calls itself with the updated state, but this monomorphizes to a specific `P`: since formats cannot be parameterized over other formats, each choice of `P` needs its own recursive definition.
* `map (k,v in c) <P>` and `for (x = s; k,v in c) <P>` could be emulated with `ForEach`, at least in certain instances.

## 3.5 (Branching)

* `case-of` (and, by extension, `if-then-else`) appear one-to-one with `Match`

## 3.6 (Coercions)

* There are no format-level types per-se, but various `Expr`s like `AsU64` and family accomplish much-the-same, albeit in a closed class rather with a constructive syntax.
  * `as?` (dynamic safe coercion) is closest to what `AsU{8,16,32,64}`/`AsChar` provide, since they are runtime-checked
  * The numeric layer (`Expr::Cast`) supports Rust-style `as` casts, including truncating ones, which covers `as!` (static lossy) coercion; whether its arithmetic casts amount to `as` (static safe) coercion has not been checked

## 5.1 (Bitdata)

Through helpers like `bit_fields_u8` and so forth, which can be defined as-needed, we have a plausible
analogue to the `bitdata` declarations in Daedalus.

However, the current implementation of `BitFieldKind` is somewhat restrictive, in the following ways, compared to `bitdata`:

* It does not support type-coercions (e.g. u8 packed in a u16)
* It does not support fixed-bits checking other than all-zero

These are features that could be added with various caveats, if necessary.

### Examples

```ddl
bitdata Packed where
  x: uint 8
  0xFFFF
  y: uint 8

bitdata Uni where
  value = { get: Packed }
  null  = 0
```

```rust
use doodle::helper::BitFieldKind::*;

let packed = bit_fields_u32([
    BitsField { field_name: "x", bit_width: 8 },
    Reserved { bit_width: 16, check_zero: false },
    BitsField { field_name: "y", bit_width: 8 },
]);

let uni = union_nondet([
    ("null", is_bytes(&[0; 4])),
    ("value", packed),
]);
```

This is more of a parse-level directive than a data-type declaration, however,
as while in Daedalus the two are implicitly specified with the same declaration,
in `doodle` the data-type is a synthetic implication of the parse declaration,
and cannot be used in coercions; for that, we would need a separate declaration
of a dependent `u32 -?-> Packed` computation that could then be fed in arbitrary
arguments to interpret as `Packed`.

```rust
use doodle::helper::BitFieldKind::*;
let as_packed = module.define_format_args(
    "Packed-Coerce",
    [(Label::Borrowed("raw"), ValueType::Base(BaseType::U32))],
    cast_u32_bit_fields( // <- also not defined, but furthermore has no archetype
        var("raw"),
        [
            BitsField { field_name: "x", bit_width: 8 },
            Reserved { bit_width: 16, check_zero: false },
            BitsField { field_name: "y", bit_width: 8 },
        ]
    )
);
```

## 5.2 (Automatic ADT Synthesis)

We have no first-class types in the specification language of `doodle`, and all
types are implied through synthesis over the declared formats and expressions.
As a result, type-ascriptions are syntactically unavailable.

Even currently, we can still at least ensure that two parsers have mutually
compatible types, by defining a declaration-check marker-format that we run
through type-checking but discard afterwards:

```rust
let point = module.define_format("types.point", record([("x", base.u8()), ("y", base.u8())]));
let point_x = module.define_format("types.point_x", record([("x", base.u8()), ("y", is_byte(0))]));

let __type_proof = module.define_format(
    "__TYPE_PROOF",
    monad_seq(
        union([point.call(), point_x.call()]),
        /* we can sequence other type-compatibility assertion-formats here as well */
        Format::EMPTY,
    )
);
```

Because every format needs a reified type for the module to be usable, but these
type-ascriptions need not be a bijection, there would be no implicitly-defined
alias `type PointX = Point` as would be synthesized by the corresponding
Daedalus declarations; instead, whichever type-name is preferred would win, and
both formats would receive verbatim-identical type-ascriptions.

Through recursion support, the parsers as written are possible to express monomorphically,
but cannot be polymorphic over parses due to the lack of format-dependent-format support.

```ddl
def List P =
    First
      Cons = Node P
      Nil = Accept

def Node P =
    block
      head = P
      tail = List P
```

would end up as

```rust
let p: FormatRef = /* some monomorphic format */;
let [list_p, node_p] = module.define_batch_with(
    ["list_p", "node_p"],
    [
        Box::new(|list_node|
            alts_nondet([
                ("cons", list_node[1].call()),
                ("nil", Format::EMPTY),
            ])
        ),
        Box::new(|list_node|
            record([
                ("head", p.call()),
                ("tail", list_node[0].call())
            ])
        ),
    ]
);
```

## 6 (Lookahead and Stream Manipulation)

The concept of a `Stream` is effectively one-to-one with `View`s within the `Format` model.

* `GetStream` can be approached with `LetView(<ident>, /* ... */ vvar(<ident>) /* ... */)`
* `Drop n s` is `s.offset(n)` (where `s :~ ViewExpr`)
* `Take n s` has no direct equivalent but `Slice` within `ParseFromView` can simulate it
* `SetStream` has no direct equivalent, but `WithStream` is analogous to `WithView` or `ParseFromView`
* `Chunk n P` is equivalent to `Slice(n, P)`
* `Lookahead P` is equivalent to `Peek(P)`
* `WithStream s P`, where `s` is a computed byte-sequence rather than a sub-stream of the input (e.g. the output of a decompression filter), is `DecodeBytes(s, P)`
* There is no backward search: `SkipTo` finds the *first* match going forward. Finding a structure near the end of the input (e.g. PDF's last `startxref`) can be emulated by taking the input length (`Peek(SkipRemainder; Pos)`), then running `SkipTo` from a fixed-size window before the end via `WithRelativeOffset`

### Example

```ddl
block
  let base = GetStream
  Many block
    let offset = Word64
    let here = GetStream
    SetStream (Drop offset base)
    $$ = ParseObject
    SetStream here
```

```rust
chain(
    Format::Pos,
    "base",
    repeat(
        chain(u64be(), "offset",
            with_relative_offset(Some(var("base")), var("offset"), parse_object)
        )
    )
)
```

or

```rust
let_view(
    "here",
    repeat(
        pseudo_record(
            [("offset", u64be())],
            parse_from_view(vvar("here").offset(var("offset")), parse_object),
        ),
    ),
)
```

## 7 (Eager vs. Lazy)

There is currently no support, at any layer, for parse-level laziness in the
`doodle` processing model; there is some value-level laziness involving
constructed sequences, but that is more of an representation-level optimization
than a feature of the processing model, and aside from performance concerns,
nothing would change if it were eliminated.

Multiple paths cannot be explored in parallel, both for unbounded/indefinite-length
repetitions as well as for more explicit alternations over N branches. Nondeterministic unions
(tried in order, falling back to the next branch on failure) are used in `doodle-formats` in three places:

* At the top-level, for alternating between distinct data-formats (e.g. png, OpenType, gzip);
* To allow fallback to uninterpreted bytes during speculative parsing of zlib-compressed UTF-8 in an `iTXt` PNG-chunk;
* In `text.maybe_gzip`, to try gzip-compressed text before plain text.

The last two usages are more of a band-aid against unwanted parse-failure, and are similar in usage
to `Format::Permit`. The PDF prototype (`experiments/doodle-pdf`) also uses them.

### On-demand resolution

DaeDaLus PDF specifications resolve indirect references (`n g R`) on demand, through the host primitive
`ResolveRef` (`formats/pdf/new/pdf-cos-spec/PdfDecl.ddl`): any lookup into a dictionary may jump
to an arbitrary object elsewhere in the file, and references may form cycles. `doodle` can only
resolve eagerly: parse the cross-reference table first, pass it as an argument, and parse the target
object at its offset with `WithRelativeOffset`. Recursion depth must be bounded explicitly (e.g. a `lim`
argument), and cycles cannot be handled. A reference whose resolution depends on the structure being
parsed (e.g. an xref stream whose own `/Length` is an indirect reference into that same xref stream)
cannot be resolved at all.

## External primitives

DaeDaLus allows bodiless declarations such as `def Decrypt (body : stream) : stream`, whose
implementation is supplied by the host. The PDF specifications use them for `ResolveRef`, `Decrypt`,
`FlateDecode` and `LZWDecode`. `doodle` has no counterpart: every operation must be expressed as a
`Format` or `Expr`. `FlateDecode` is within reach because deflate/zlib are written as `doodle` formats
(`doodle-formats/src/format/{deflate,zlib}.rs`) and can be applied with `DecodeBytes`. The others would
have to be written out in the grammar (LZW, in principle), or are out of reach in practice (decryption).
