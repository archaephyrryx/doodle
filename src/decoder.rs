use crate::byte_set::ByteSet;
use crate::error::{ParseError, ParseResult};
use crate::read::ReadCtxt;
use crate::{DynFormat, Expr, Format, FormatModule, MatchTree, Next, Pattern, ValueType};
use serde::Serialize;
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize)]
#[serde(tag = "tag", content = "data")]
pub enum Value {
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    Char(char),
    Tuple(Vec<Value>),
    Record(Vec<(Cow<'static, str>, Value)>),
    Variant(Cow<'static, str>, Box<Value>),
    Seq(Vec<Value>),
    Mapped(Box<Value>, Box<Value>),
    Branch(usize, Box<Value>),
    Format(Box<Format>),
}

impl Value {
    pub const UNIT: Value = Value::Tuple(Vec::new());

    pub fn record<Label: Into<Cow<'static, str>>>(
        fields: impl IntoIterator<Item = (Label, Value)>,
    ) -> Value {
        Value::Record(
            fields
                .into_iter()
                .map(|(label, value)| (label.into(), value))
                .collect(),
        )
    }

    pub fn variant(label: impl Into<Cow<'static, str>>, value: impl Into<Box<Value>>) -> Value {
        Value::Variant(label.into(), value.into())
    }

    pub fn record_proj(&self, label: &str) -> &Value {
        match self {
            Value::Record(fields) => match fields.iter().find(|(l, _)| label == l) {
                Some((_, v)) => v,
                None => panic!("{label} not found in record"),
            },
            _ => panic!("expected record, found {self:?}"),
        }
    }

    pub fn tuple_proj(&self, index: usize) -> &Value {
        match self.coerce_mapped_value() {
            Value::Tuple(vs) => &vs[index],
            _ => panic!("expected tuple"),
        }
    }

    pub fn coerce_mapped_value(&self) -> &Value {
        match self {
            Value::Mapped(_orig, v) => v.coerce_mapped_value(),
            Value::Branch(_n, v) => v.coerce_mapped_value(),
            v => v,
        }
    }

    fn unwrap_usize(self) -> usize {
        match self {
            Value::U8(n) => usize::from(n),
            Value::U16(n) => usize::from(n),
            Value::U32(n) => usize::try_from(n).unwrap(),
            _ => panic!("value is not a number"),
        }
    }

    fn unwrap_tuple(self) -> Vec<Value> {
        match self {
            Value::Tuple(values) => values,
            _ => panic!("value is not a tuple"),
        }
    }

    fn unwrap_bool(self) -> bool {
        match self {
            Value::Bool(b) => b,
            _ => panic!("value is not a bool"),
        }
    }

    #[allow(dead_code)]
    fn unwrap_char(self) -> char {
        match self {
            Value::Char(c) => c,
            _ => panic!("value is not a char"),
        }
    }

    /// Returns `true` if the pattern successfully matches the value, pushing
    /// any values bound by the pattern onto the scope
    pub fn matches<'a>(&self, scope: &'a Scope<'a>, pattern: &Pattern) -> Option<Scope<'a>> {
        let mut pattern_scope = Scope::child(scope);
        self.coerce_mapped_value()
            .matches_inner(&mut pattern_scope, pattern)
            .then_some(pattern_scope)
    }

    fn matches_inner(&self, scope: &mut Scope<'_>, pattern: &Pattern) -> bool {
        match (pattern, self) {
            (Pattern::Binding(name), head) => {
                scope.push(name.clone(), head.clone());
                true
            }
            (Pattern::Wildcard, _) => true,
            (Pattern::Bool(b0), Value::Bool(b1)) => b0 == b1,
            (Pattern::U8(i0), Value::U8(i1)) => i0 == i1,
            (Pattern::U16(i0), Value::U16(i1)) => i0 == i1,
            (Pattern::U32(i0), Value::U32(i1)) => i0 == i1,
            (Pattern::Char(c0), Value::Char(c1)) => c0 == c1,
            (Pattern::Tuple(ps), Value::Tuple(vs)) | (Pattern::Seq(ps), Value::Seq(vs))
                if ps.len() == vs.len() =>
            {
                for (p, v) in Iterator::zip(ps.iter(), vs.iter()) {
                    if !v.matches_inner(scope, p) {
                        return false;
                    }
                }
                true
            }
            (Pattern::Variant(label0, p), Value::Variant(label1, v)) if label0 == label1 => {
                v.matches_inner(scope, p)
            }
            _ => false,
        }
    }
}

impl Expr {
    pub fn eval<'a>(&'a self, scope: &'a Scope<'a>) -> Cow<'a, Value> {
        match self {
            Expr::Var(name) => Cow::Borrowed(scope.get_value_by_name(name)),
            Expr::Bool(b) => Cow::Owned(Value::Bool(*b)),
            Expr::U8(i) => Cow::Owned(Value::U8(*i)),
            Expr::U16(i) => Cow::Owned(Value::U16(*i)),
            Expr::U32(i) => Cow::Owned(Value::U32(*i)),
            Expr::Tuple(exprs) => Cow::Owned(Value::Tuple(
                exprs.iter().map(|expr| expr.eval_value(scope)).collect(),
            )),
            Expr::TupleProj(head, index) => match head.eval(scope) {
                Cow::Owned(v) => Cow::Owned(v.coerce_mapped_value().tuple_proj(*index).clone()),
                Cow::Borrowed(v) => Cow::Borrowed(v.coerce_mapped_value().tuple_proj(*index)),
            },
            Expr::Record(fields) => Cow::Owned(Value::record(
                fields
                    .iter()
                    .map(|(label, expr)| (label.clone(), expr.eval_value(scope))),
            )),
            Expr::RecordProj(head, label) => match head.eval(scope) {
                Cow::Owned(v) => Cow::Owned(v.coerce_mapped_value().record_proj(label).clone()),
                Cow::Borrowed(v) => Cow::Borrowed(v.coerce_mapped_value().record_proj(label)),
            },
            Expr::Variant(label, expr) => {
                Cow::Owned(Value::variant(label.clone(), expr.eval_value(scope)))
            }
            Expr::Seq(exprs) => Cow::Owned(Value::Seq(
                exprs.iter().map(|expr| expr.eval_value(scope)).collect(),
            )),
            Expr::Match(head, branches) => {
                let head = head.eval(scope);
                for (pattern, expr) in branches {
                    if let Some(pattern_scope) = head.matches(scope, pattern) {
                        let value = expr.eval_value(&pattern_scope);
                        return Cow::Owned(value);
                    }
                }
                panic!("non-exhaustive patterns");
            }
            Expr::Lambda(_, _) => panic!("cannot eval lambda"),

            Expr::BitAnd(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(x & y),
                (Value::U16(x), Value::U16(y)) => Value::U16(x & y),
                (Value::U32(x), Value::U32(y)) => Value::U32(x & y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::BitOr(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(x | y),
                (Value::U16(x), Value::U16(y)) => Value::U16(x | y),
                (Value::U32(x), Value::U32(y)) => Value::U32(x | y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Eq(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::Bool(x == y),
                (Value::U16(x), Value::U16(y)) => Value::Bool(x == y),
                (Value::U32(x), Value::U32(y)) => Value::Bool(x == y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Ne(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::Bool(x != y),
                (Value::U16(x), Value::U16(y)) => Value::Bool(x != y),
                (Value::U32(x), Value::U32(y)) => Value::Bool(x != y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Lt(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::Bool(x < y),
                (Value::U16(x), Value::U16(y)) => Value::Bool(x < y),
                (Value::U32(x), Value::U32(y)) => Value::Bool(x < y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Gt(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::Bool(x > y),
                (Value::U16(x), Value::U16(y)) => Value::Bool(x > y),
                (Value::U32(x), Value::U32(y)) => Value::Bool(x > y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Lte(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::Bool(x <= y),
                (Value::U16(x), Value::U16(y)) => Value::Bool(x <= y),
                (Value::U32(x), Value::U32(y)) => Value::Bool(x <= y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Gte(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::Bool(x >= y),
                (Value::U16(x), Value::U16(y)) => Value::Bool(x >= y),
                (Value::U32(x), Value::U32(y)) => Value::Bool(x >= y),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Mul(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(u8::checked_mul(x, y).unwrap()),
                (Value::U16(x), Value::U16(y)) => Value::U16(u16::checked_mul(x, y).unwrap()),
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_mul(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Div(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(u8::checked_div(x, y).unwrap()),
                (Value::U16(x), Value::U16(y)) => Value::U16(u16::checked_div(x, y).unwrap()),
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_div(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Rem(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(u8::checked_rem(x, y).unwrap()),
                (Value::U16(x), Value::U16(y)) => Value::U16(u16::checked_rem(x, y).unwrap()),
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_rem(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Shl(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => {
                    Value::U8(u8::checked_shl(x, u32::from(y)).unwrap())
                }
                (Value::U16(x), Value::U16(y)) => {
                    Value::U16(u16::checked_shl(x, u32::from(y)).unwrap())
                }
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_shl(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Shr(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => {
                    Value::U8(u8::checked_shr(x, u32::from(y)).unwrap())
                }
                (Value::U16(x), Value::U16(y)) => {
                    Value::U16(u16::checked_shr(x, u32::from(y)).unwrap())
                }
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_shr(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Add(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(u8::checked_add(x, y).unwrap()),
                (Value::U16(x), Value::U16(y)) => Value::U16(u16::checked_add(x, y).unwrap()),
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_add(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),
            Expr::Sub(x, y) => Cow::Owned(match (x.eval_value(scope), y.eval_value(scope)) {
                (Value::U8(x), Value::U8(y)) => Value::U8(u8::checked_sub(x, y).unwrap()),
                (Value::U16(x), Value::U16(y)) => Value::U16(u16::checked_sub(x, y).unwrap()),
                (Value::U32(x), Value::U32(y)) => Value::U32(u32::checked_sub(x, y).unwrap()),
                (x, y) => panic!("mismatched operands {x:?}, {y:?}"),
            }),

            Expr::AsU8(x) => Cow::Owned(match x.eval_value(scope) {
                Value::U8(x) => Value::U8(x),
                Value::U16(x) if x < 256 => Value::U8(x as u8),
                Value::U32(x) if x < 256 => Value::U8(x as u8),
                x => panic!("cannot convert {x:?} to U8"),
            }),
            Expr::AsU16(x) => Cow::Owned(match x.eval_value(scope) {
                Value::U8(x) => Value::U16(u16::from(x)),
                Value::U16(x) => Value::U16(x),
                Value::U32(x) if x < 65536 => Value::U16(x as u16),
                x => panic!("cannot convert {x:?} to U16"),
            }),
            Expr::AsU32(x) => Cow::Owned(match x.eval_value(scope) {
                Value::U8(x) => Value::U32(u32::from(x)),
                Value::U16(x) => Value::U32(u32::from(x)),
                Value::U32(x) => Value::U32(x),
                x => panic!("cannot convert {x:?} to U32"),
            }),

            Expr::U16Be(bytes) => match bytes.eval_value(scope).unwrap_tuple().as_slice() {
                [Value::U8(hi), Value::U8(lo)] => {
                    Cow::Owned(Value::U16(u16::from_be_bytes([*hi, *lo])))
                }
                _ => panic!("U16Be: expected (U8, U8)"),
            },
            Expr::U16Le(bytes) => match bytes.eval_value(scope).unwrap_tuple().as_slice() {
                [Value::U8(lo), Value::U8(hi)] => {
                    Cow::Owned(Value::U16(u16::from_le_bytes([*lo, *hi])))
                }
                _ => panic!("U16Le: expected (U8, U8)"),
            },
            Expr::U32Be(bytes) => match bytes.eval_value(scope).unwrap_tuple().as_slice() {
                [Value::U8(a), Value::U8(b), Value::U8(c), Value::U8(d)] => {
                    Cow::Owned(Value::U32(u32::from_be_bytes([*a, *b, *c, *d])))
                }
                _ => panic!("U32Be: expected (U8, U8, U8, U8)"),
            },
            Expr::U32Le(bytes) => match bytes.eval_value(scope).unwrap_tuple().as_slice() {
                [Value::U8(a), Value::U8(b), Value::U8(c), Value::U8(d)] => {
                    Cow::Owned(Value::U32(u32::from_le_bytes([*a, *b, *c, *d])))
                }
                _ => panic!("U32Le: expected (U8, U8, U8, U8)"),
            },
            Expr::AsChar(bytes) => Cow::Owned(match bytes.eval_value(scope) {
                Value::U8(x) => Value::Char(char::from(x)),
                Value::U16(x) => {
                    Value::Char(char::from_u32(x as u32).unwrap_or(char::REPLACEMENT_CHARACTER))
                }
                Value::U32(x) => {
                    Value::Char(char::from_u32(x).unwrap_or(char::REPLACEMENT_CHARACTER))
                }
                _ => panic!("AsChar: expected U8, U16, or U32"),
            }),
            Expr::SeqLength(seq) => match seq.eval(scope).coerce_mapped_value() {
                Value::Seq(values) => {
                    let len = values.len();
                    Cow::Owned(Value::U32(len as u32))
                }
                _ => panic!("SeqLength: expected Seq"),
            },
            Expr::SubSeq(seq, start, length) => match seq.eval(scope).coerce_mapped_value() {
                Value::Seq(values) => {
                    let start = start.eval_value(scope).unwrap_usize();
                    let length = length.eval_value(scope).unwrap_usize();
                    let values = &values[start..];
                    let values = &values[..length];
                    Cow::Owned(Value::Seq(values.to_vec()))
                }
                _ => panic!("SubSeq: expected Seq"),
            },
            Expr::FlatMap(expr, seq) => match seq.eval_value(scope) {
                Value::Seq(values) => {
                    let mut vs = Vec::new();
                    for v in values {
                        if let Value::Seq(vn) = expr.eval_lambda(scope, v) {
                            vs.extend(vn);
                        } else {
                            panic!("FlatMap: expected Seq");
                        }
                    }
                    Cow::Owned(Value::Seq(vs))
                }
                _ => panic!("FlatMap: expected Seq"),
            },
            Expr::FlatMapAccum(expr, accum, _accum_type, seq) => match seq.eval_value(scope) {
                Value::Seq(values) => {
                    let mut accum = accum.eval_value(scope);
                    let mut vs = Vec::new();
                    for v in values {
                        let ret = expr.eval_lambda(scope, Value::Tuple(vec![accum, v]));
                        accum = match ret.unwrap_tuple().as_mut_slice() {
                            [accum, Value::Seq(vn)] => {
                                vs.extend_from_slice(&vn);
                                accum.clone()
                            }
                            _ => panic!("FlatMapAccum: expected two values"),
                        };
                    }
                    Cow::Owned(Value::Seq(vs))
                }
                _ => panic!("FlatMapAccum: expected Seq"),
            },
            Expr::Dup(count, expr) => {
                let count = count.eval_value(scope).unwrap_usize();
                let v = expr.eval_value(scope);
                let mut vs = Vec::new();
                for _ in 0..count {
                    vs.push(v.clone());
                }
                Cow::Owned(Value::Seq(vs))
            }
            Expr::Inflate(seq) => match seq.eval(scope).coerce_mapped_value() {
                Value::Seq(values) => {
                    let vs = inflate(&values);
                    Cow::Owned(Value::Seq(vs))
                }
                _ => panic!("Inflate: expected Seq"),
            },
        }
    }

    fn eval_value<'a>(&self, scope: &'a Scope<'a>) -> Value {
        self.eval(scope).coerce_mapped_value().clone()
    }

    fn eval_lambda<'a>(&self, scope: &'a Scope<'a>, arg: Value) -> Value {
        match self {
            Expr::Lambda(name, expr) => {
                let mut child_scope = Scope::child(scope);
                child_scope.push(name.clone(), arg);
                expr.eval_value(&child_scope)
            }
            _ => panic!("expected Lambda"),
        }
    }
}

/// Decoders with a fixed amount of lookahead
enum Decoder {
    Call(usize, Vec<(Cow<'static, str>, Expr)>),
    Fail,
    EndOfInput,
    Align(usize),
    Byte(ByteSet),
    Variant(Cow<'static, str>, Box<Decoder>),
    Parallel(Vec<(Cow<'static, str>, Decoder)>),
    Branch(MatchTree, Vec<(Cow<'static, str>, Decoder)>),
    IsoBranch(MatchTree, Vec<Decoder>),
    Tuple(Vec<Decoder>),
    Record(Vec<(Cow<'static, str>, Decoder)>),
    While(MatchTree, Box<Decoder>),
    Until(MatchTree, Box<Decoder>),
    RepeatCount(Expr, Box<Decoder>),
    RepeatUntilLast(Expr, Box<Decoder>),
    RepeatUntilSeq(Expr, Box<Decoder>),
    Peek(Box<Decoder>),
    PeekNot(Box<Decoder>),
    Slice(Expr, Box<Decoder>),
    Bits(Box<Decoder>),
    WithRelativeOffset(Expr, Box<Decoder>),
    Map(Box<Decoder>, Expr),
    Compute(Expr),
    Match(Expr, Vec<(Pattern, Decoder)>),
    MatchVariant(Expr, Vec<(Pattern, Cow<'static, str>, Decoder)>),
    Dynamic(DynFormat),
    Apply(Cow<'static, str>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Serialize)]
pub enum TypeRef {
    Var(usize),
    Empty,
    Bool,
    U8,
    U16,
    U32,
    Tuple(Vec<TypeRef>),
    Seq(Box<TypeRef>),
    Char,
    Format(Box<TypeRef>),
}

pub enum TypeDef {
    //Equiv(TypeRef),
    Union(Vec<(Cow<'static, str>, TypeRef)>),
    Record(Vec<(Cow<'static, str>, TypeRef)>),
}

pub struct Program {
    typedefs: Vec<TypeDef>,
    decoders: Vec<Decoder>,
}

impl Program {
    fn new() -> Self {
        let typedefs = Vec::new();
        let decoders = Vec::new();
        Program { typedefs, decoders }
    }

    pub fn run<'input>(&self, input: ReadCtxt<'input>) -> ParseResult<(Value, ReadCtxt<'input>)> {
        let mut scope = Scope::new();
        self.decoders[0].parse(self, &mut scope, input)
    }
}

pub struct Compiler<'a> {
    module: &'a FormatModule,
    program: Program,
    record_map: HashMap<Vec<(Cow<'static, str>, TypeRef)>, usize>,
    union_map: HashMap<Vec<(Cow<'static, str>, TypeRef)>, usize>,
    decoder_map: HashMap<(usize, Rc<Next<'a>>), usize>,
}

impl<'a> Compiler<'a> {
    fn new(module: &'a FormatModule) -> Self {
        let program = Program::new();
        let record_map = HashMap::new();
        let union_map = HashMap::new();
        let decoder_map = HashMap::new();
        Compiler {
            module,
            program,
            record_map,
            union_map,
            decoder_map,
        }
    }

    pub fn compile(module: &FormatModule, format: &Format) -> Result<Program, String> {
        let mut compiler = Compiler::new(module);
        // type
        /*
        let mut scope = TypeScope::new();
        let t = TypeRef::from_value_type(
            &mut compiler,
            &module.infer_format_type(&mut scope, format)?,
        );
        */
        // decoder
        let n = compiler.program.decoders.len();
        compiler.program.decoders.push(Decoder::Fail);
        let d = Decoder::compile(&mut compiler, format)?;
        compiler.program.decoders[n] = d;
        Ok(compiler.program)
    }

    pub fn add_typedef(&mut self, t: TypeDef) -> TypeRef {
        let n = self.program.typedefs.len();
        self.program.typedefs.push(t);
        TypeRef::Var(n)
    }
}

pub struct Scope<'a> {
    parent: Option<&'a Scope<'a>>,
    names: Vec<Cow<'static, str>>,
    values: Vec<Value>,
    decoders: Vec<RefCell<Option<Decoder>>>,
}

pub struct ScopeIter<'a> {
    parent: Option<&'a Scope<'a>>,
    name_iter: std::iter::Rev<std::slice::Iter<'a, Cow<'static, str>>>,
    value_iter: std::iter::Rev<std::slice::Iter<'a, Value>>,
}

impl<'a> Iterator for ScopeIter<'a> {
    type Item = (&'a Cow<'static, str>, &'a Value);

    fn next(&mut self) -> Option<Self::Item> {
        match (self.name_iter.next(), self.value_iter.next()) {
            (Some(name), Some(value)) => Some((name, value)),
            _ => match self.parent {
                Some(parent) => {
                    *self = parent.into_iter();
                    self.next()
                }
                None => None,
            },
        }
    }
}

impl<'a> IntoIterator for &'a Scope<'a> {
    type Item = (&'a Cow<'static, str>, &'a Value);

    type IntoIter = ScopeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        ScopeIter {
            parent: self.parent,
            name_iter: self.names.iter().rev(),
            value_iter: self.values.iter().rev(),
        }
    }
}

impl<'a> Scope<'a> {
    pub fn new() -> Self {
        let parent = None;
        let names = Vec::new();
        let values = Vec::new();
        let decoders = Vec::new();
        Scope {
            parent,
            names,
            values,
            decoders,
        }
    }

    pub fn child(parent: &'a Scope<'a>) -> Self {
        let names = Vec::new();
        let values = Vec::new();
        let decoders = Vec::new();
        Scope {
            parent: Some(parent),
            names,
            values,
            decoders,
        }
    }

    pub fn iter(&'a self) -> impl Iterator<Item = (&'a Cow<'static, str>, &'a Value)> {
        (&self).into_iter()
    }

    pub fn push(&mut self, name: Cow<'static, str>, v: Value) {
        self.names.push(name);
        self.values.push(v);
        self.decoders.push(RefCell::new(None));
    }

    fn get_index_by_name(&self, name: &str) -> (&Self, usize) {
        for (i, n) in self.names.iter().enumerate().rev() {
            if n == name {
                return (self, i);
            }
        }
        if let Some(parent) = self.parent {
            parent.get_index_by_name(name)
        } else {
            panic!("variable not found: {name}");
        }
    }

    fn get_value_by_name(&self, name: &str) -> &Value {
        let (scope, index) = self.get_index_by_name(name);
        &scope.values[index]
    }

    fn call_decoder_by_name<'input>(
        &self,
        name: &str,
        program: &Program,
        input: ReadCtxt<'input>,
    ) -> ParseResult<(Value, ReadCtxt<'input>)> {
        let (scope, i) = self.get_index_by_name(name);
        let mut od = scope.decoders[i].borrow_mut();
        if od.is_none() {
            let d = match &scope.values[i] {
                Value::Format(f) => Decoder::compile_one(&*f).unwrap(),
                _ => panic!("variable not format: {name}"),
            };
            *od = Some(d);
        }
        let res = od.as_ref().unwrap().parse(program, self, input);
        res
    }
}

impl TypeRef {
    #[allow(dead_code)]
    fn from_value_type<'a>(compiler: &mut Compiler<'a>, t: &ValueType) -> Self {
        match t {
            ValueType::Any => panic!("ValueType::Any"),
            ValueType::Empty => TypeRef::Empty,
            ValueType::Bool => TypeRef::Bool,
            ValueType::U8 => TypeRef::U8,
            ValueType::Char => TypeRef::Char,
            ValueType::U16 => TypeRef::U16,
            ValueType::U32 => TypeRef::U32,
            ValueType::Tuple(ts) => TypeRef::Tuple(
                ts.iter()
                    .map(|t| Self::from_value_type(compiler, t))
                    .collect(),
            ),
            ValueType::Record(fields) => {
                let fs: Vec<_> = fields
                    .iter()
                    .map(|(label, t)| (label.clone(), Self::from_value_type(compiler, t)))
                    .collect();
                let n = if let Some(n) = compiler.record_map.get(&fs) {
                    *n
                } else {
                    let t = TypeDef::Record(fs.clone());
                    let n = compiler.program.typedefs.len();
                    compiler.program.typedefs.push(t);
                    compiler.record_map.insert(fs, n);
                    n
                };
                TypeRef::Var(n)
            }
            ValueType::Union(branches) => {
                let bs: Vec<_> = branches
                    .iter()
                    .map(|(label, t)| (label.clone(), Self::from_value_type(compiler, t)))
                    .collect();
                let n = if let Some(n) = compiler.union_map.get(&bs) {
                    *n
                } else {
                    let t = TypeDef::Union(bs.clone());
                    let n = compiler.program.typedefs.len();
                    compiler.program.typedefs.push(t);
                    compiler.union_map.insert(bs, n);
                    n
                };
                TypeRef::Var(n)
            }
            ValueType::Seq(t) => TypeRef::Seq(Box::new(Self::from_value_type(compiler, &*t))),
            ValueType::Format(t) => TypeRef::Format(Box::new(Self::from_value_type(compiler, &*t))),
        }
    }

    #[allow(dead_code)]
    fn to_value_type(&self, typedefs: &[TypeDef]) -> ValueType {
        match self {
            TypeRef::Var(n) => match &typedefs[*n] {
                //TypeDef::Equiv(t) => t.to_value_type(typedefs),
                TypeDef::Union(ts) => ValueType::Union(
                    ts.iter()
                        .map(|(name, t)| (name.clone(), t.to_value_type(typedefs)))
                        .collect(),
                ),
                TypeDef::Record(ts) => ValueType::Record(
                    ts.iter()
                        .map(|(name, t)| (name.clone(), t.to_value_type(typedefs)))
                        .collect(),
                ),
            },
            TypeRef::Empty => ValueType::Empty,
            TypeRef::Bool => ValueType::Bool,
            TypeRef::U8 => ValueType::U8,
            TypeRef::U16 => ValueType::U16,
            TypeRef::U32 => ValueType::U32,
            TypeRef::Char => ValueType::Char,
            TypeRef::Tuple(ts) => {
                ValueType::Tuple(ts.iter().map(|t| t.to_value_type(typedefs)).collect())
            }
            TypeRef::Seq(t) => ValueType::Seq(Box::new(t.to_value_type(typedefs))),
            TypeRef::Format(t) => ValueType::Format(Box::new(t.to_value_type(typedefs))),
        }
    }
}

impl Decoder {
    pub fn compile_one(format: &Format) -> Result<Decoder, String> {
        let module = FormatModule::new();
        let mut compiler = Compiler::new(&module);
        Decoder::compile(&mut compiler, format)
    }

    pub fn compile<'a>(compiler: &mut Compiler<'a>, format: &'a Format) -> Result<Decoder, String> {
        Decoder::compile_next(compiler, format, Rc::new(Next::Empty))
    }

    fn compile_next<'a>(
        compiler: &mut Compiler<'a>,
        format: &'a Format,
        next: Rc<Next<'a>>,
    ) -> Result<Decoder, String> {
        match format {
            Format::ItemVar(level, arg_exprs) => {
                let next = if compiler
                    .module
                    .get_format(*level)
                    .depends_on_next(compiler.module)
                {
                    next
                } else {
                    Rc::new(Next::Empty)
                };
                let n = if let Some(n) = compiler.decoder_map.get(&(*level, next.clone())) {
                    *n
                } else {
                    let d = Decoder::compile_next(
                        compiler,
                        compiler.module.get_format(*level),
                        next.clone(),
                    )?;
                    let n = compiler.program.decoders.len();
                    compiler.program.decoders.push(d);
                    compiler.decoder_map.insert((*level, next.clone()), n);
                    n
                };
                let arg_names = compiler.module.get_args(*level);
                let mut args = Vec::new();
                for ((name, _type), expr) in Iterator::zip(arg_names.iter(), arg_exprs.iter()) {
                    args.push((name.clone(), expr.clone()));
                }
                Ok(Decoder::Call(n, args))
            }
            Format::Fail => Ok(Decoder::Fail),
            Format::EndOfInput => Ok(Decoder::EndOfInput),
            Format::Align(n) => Ok(Decoder::Align(*n)),
            Format::Byte(bs) => Ok(Decoder::Byte(*bs)),
            Format::Variant(label, f) => {
                let d = Decoder::compile_next(compiler, f, next.clone())?;
                Ok(Decoder::Variant(label.clone(), Box::new(d)))
            }
            Format::UnionVariant(branches) => {
                let mut fs = Vec::with_capacity(branches.len());
                let mut ds = Vec::with_capacity(branches.len());
                for (label, f) in branches {
                    ds.push((
                        label.clone().into(),
                        Decoder::compile_next(compiler, f, next.clone())?,
                    ));
                    fs.push(f.clone());
                }
                if let Some(tree) = MatchTree::build(compiler.module, &fs, next) {
                    Ok(Decoder::Branch(tree, ds))
                } else {
                    Err(format!("cannot build match tree for {:?}", format))
                }
            }
            Format::UnionNondet(branches) => {
                let mut ds = Vec::with_capacity(branches.len());
                for (label, f) in branches {
                    ds.push((
                        label.clone().into(),
                        Decoder::compile_next(compiler, f, next.clone())?,
                    ));
                }
                Ok(Decoder::Parallel(ds))
            }
            Format::Union(branches) => {
                let mut fs = Vec::with_capacity(branches.len());
                let mut ds = Vec::with_capacity(branches.len());
                for f in branches {
                    ds.push(Decoder::compile_next(compiler, f, next.clone())?);
                    fs.push(f.clone());
                }
                if let Some(tree) = MatchTree::build(compiler.module, &fs, next) {
                    Ok(Decoder::IsoBranch(tree, ds))
                } else {
                    Err(format!("cannot build match tree for {:?}", format))
                }
            }
            Format::Tuple(fields) => {
                let mut dfields = Vec::with_capacity(fields.len());
                let mut fields = fields.iter();
                while let Some(f) = fields.next() {
                    let next = Rc::new(Next::Tuple(fields.as_slice(), next.clone()));
                    let df = Decoder::compile_next(compiler, f, next)?;
                    dfields.push(df);
                }
                Ok(Decoder::Tuple(dfields))
            }
            Format::Record(fields) => {
                let mut dfields = Vec::with_capacity(fields.len());
                let mut fields = fields.iter();
                while let Some((name, f)) = fields.next() {
                    let next = Rc::new(Next::Record(fields.as_slice(), next.clone()));
                    let df = Decoder::compile_next(compiler, f, next)?;
                    dfields.push((name.clone(), df));
                }
                Ok(Decoder::Record(dfields))
            }
            Format::Repeat(a) => {
                if a.is_nullable(compiler.module) {
                    return Err(format!("cannot repeat nullable format: {a:?}"));
                }
                let da =
                    Decoder::compile_next(compiler, a, Rc::new(Next::Repeat(a, next.clone())))?;
                let astar = Format::Repeat(a.clone());
                let fa = Format::Tuple(vec![(**a).clone(), astar]);
                let fb = Format::EMPTY;
                if let Some(tree) = MatchTree::build(compiler.module, &[fa, fb], next) {
                    Ok(Decoder::While(tree, Box::new(da)))
                } else {
                    Err(format!("cannot build match tree for {:?}", format))
                }
            }
            Format::Repeat1(a) => {
                if a.is_nullable(compiler.module) {
                    return Err(format!("cannot repeat nullable format: {a:?}"));
                }
                let da =
                    Decoder::compile_next(compiler, a, Rc::new(Next::Repeat(a, next.clone())))?;
                let astar = Format::Repeat(a.clone());
                let fa = Format::EMPTY;
                let fb = Format::Tuple(vec![(**a).clone(), astar]);
                if let Some(tree) = MatchTree::build(compiler.module, &[fa, fb], next) {
                    Ok(Decoder::Until(tree, Box::new(da)))
                } else {
                    Err(format!("cannot build match tree for {:?}", format))
                }
            }
            Format::RepeatCount(expr, a) => {
                // FIXME probably not right
                let da = Box::new(Decoder::compile_next(compiler, a, next)?);
                Ok(Decoder::RepeatCount(expr.clone(), da))
            }
            Format::RepeatUntilLast(expr, a) => {
                // FIXME probably not right
                let da = Box::new(Decoder::compile_next(compiler, a, next)?);
                Ok(Decoder::RepeatUntilLast(expr.clone(), da))
            }
            Format::RepeatUntilSeq(expr, a) => {
                // FIXME probably not right
                let da = Box::new(Decoder::compile_next(compiler, a, next)?);
                Ok(Decoder::RepeatUntilSeq(expr.clone(), da))
            }
            Format::Peek(a) => {
                let da = Box::new(Decoder::compile_next(compiler, a, Rc::new(Next::Empty))?);
                Ok(Decoder::Peek(da))
            }
            Format::PeekNot(a) => {
                const MAX_LOOKAHEAD: usize = 1024;
                match a.match_bounds(compiler.module).max {
                    None => return Err(format!("PeekNot cannot require unbounded lookahead")),
                    Some(n) if n > MAX_LOOKAHEAD => {
                        return Err(format!(
                            "PeekNot cannot require > {MAX_LOOKAHEAD} bytes lookahead"
                        ))
                    }
                    _ => {}
                }
                let da = Box::new(Decoder::compile_next(compiler, a, Rc::new(Next::Empty))?);
                Ok(Decoder::PeekNot(da))
            }
            Format::Slice(expr, a) => {
                let da = Box::new(Decoder::compile_next(compiler, a, Rc::new(Next::Empty))?);
                Ok(Decoder::Slice(expr.clone(), da))
            }
            Format::Bits(a) => {
                let da = Box::new(Decoder::compile_next(compiler, a, Rc::new(Next::Empty))?);
                Ok(Decoder::Bits(da))
            }
            Format::WithRelativeOffset(expr, a) => {
                let da = Box::new(Decoder::compile_next(compiler, a, Rc::new(Next::Empty))?);
                Ok(Decoder::WithRelativeOffset(expr.clone(), da))
            }
            Format::Map(a, expr) => {
                let da = Box::new(Decoder::compile_next(compiler, a, next.clone())?);
                Ok(Decoder::Map(da, expr.clone()))
            }
            Format::Compute(expr) => Ok(Decoder::Compute(expr.clone())),
            Format::Match(head, branches) => {
                let branches = branches
                    .iter()
                    .map(|(pattern, f)| {
                        Ok((
                            pattern.clone(),
                            Decoder::compile_next(compiler, f, next.clone())?,
                        ))
                    })
                    .collect::<Result<_, String>>()?;
                Ok(Decoder::Match(head.clone(), branches))
            }
            Format::MatchVariant(head, branches) => {
                let branches = branches
                    .iter()
                    .map(|(pattern, label, f)| {
                        Ok((
                            pattern.clone(),
                            label.clone().into(),
                            Decoder::compile_next(compiler, f, next.clone())?,
                        ))
                    })
                    .collect::<Result<_, String>>()?;
                Ok(Decoder::MatchVariant(head.clone(), branches))
            }
            Format::Dynamic(d) => Ok(Decoder::Dynamic(d.clone())),
            Format::Apply(name) => Ok(Decoder::Apply(name.clone())),
        }
    }

    pub fn parse<'input>(
        &self,
        program: &Program,
        scope: &Scope<'_>,
        input: ReadCtxt<'input>,
    ) -> ParseResult<(Value, ReadCtxt<'input>)> {
        match self {
            Decoder::Call(n, es) => {
                let mut new_scope = Scope::new();
                for (name, e) in es {
                    let v = e.eval_value(scope);
                    new_scope.push(name.clone(), v);
                }
                program.decoders[*n].parse(program, &mut new_scope, input)
            }
            Decoder::Fail => Err(ParseError::fail(scope, input)),
            Decoder::EndOfInput => match input.read_byte() {
                None => Ok((Value::UNIT, input)),
                Some((b, _)) => Err(ParseError::trailing(b, input.offset)),
            },
            Decoder::Align(n) => {
                let skip = (n - (input.offset % n)) % n;
                let (_, input) = input
                    .split_at(skip)
                    .ok_or(ParseError::overrun(skip, input.offset))?;
                Ok((Value::UNIT, input))
            }
            Decoder::Byte(bs) => {
                let (b, input) = input
                    .read_byte()
                    .ok_or(ParseError::overbyte(input.offset))?;
                if bs.contains(b) {
                    Ok((Value::U8(b), input))
                } else {
                    Err(ParseError::unexpected(b, bs.clone(), input.offset))
                }
            }
            Decoder::Variant(label, d) => {
                let (v, input) = d.parse(program, scope, input)?;
                Ok((Value::Variant(label.clone(), Box::new(v)), input))
            }
            Decoder::Parallel(branches) => {
                for (index, (label, d)) in branches.iter().enumerate() {
                    let res = d.parse(program, scope, input);
                    if let Ok((v, input)) = res {
                        return Ok((
                            Value::Branch(
                                index,
                                Box::new(Value::Variant(label.clone(), Box::new(v))),
                            ),
                            input,
                        ));
                    }
                }
                Err(ParseError::fail(scope, input))
            }
            Decoder::Branch(tree, branches) => {
                let index = tree.matches(input).ok_or(ParseError::NoValidBranch {
                    offset: input.offset,
                })?;
                let (label, d) = &branches[index];
                let (v, input) = d.parse(program, scope, input)?;
                Ok((
                    Value::Branch(index, Box::new(Value::Variant(label.clone(), Box::new(v)))),
                    input,
                ))
            }
            Decoder::IsoBranch(tree, branches) => {
                let index = tree.matches(input).ok_or(ParseError::NoValidBranch {
                    offset: input.offset,
                })?;
                let d = &branches[index];
                let (v, input) = d.parse(program, scope, input)?;
                Ok((Value::Branch(index, Box::new(v)), input))
            }
            Decoder::Tuple(fields) => {
                let mut input = input;
                let mut v = Vec::with_capacity(fields.len());
                for f in fields {
                    let (vf, next_input) = f.parse(program, scope, input)?;
                    input = next_input;
                    v.push(vf.clone());
                }
                Ok((Value::Tuple(v), input))
            }
            Decoder::Record(fields) => {
                let mut input = input;
                let mut v = Vec::with_capacity(fields.len());
                let mut record_scope = Scope::child(scope);
                for (name, f) in fields {
                    let (vf, next_input) = f.parse(program, &record_scope, input)?;
                    input = next_input;
                    v.push((name.clone(), vf.clone()));
                    record_scope.push(name.clone(), vf);
                }
                Ok((Value::Record(v), input))
            }
            Decoder::While(tree, a) => {
                let mut input = input;
                let mut v = Vec::new();
                while tree.matches(input).ok_or(ParseError::NoValidBranch {
                    offset: input.offset,
                })? == 0
                {
                    let (va, next_input) = a.parse(program, scope, input)?;
                    input = next_input;
                    v.push(va);
                }
                Ok((Value::Seq(v), input))
            }
            Decoder::Until(tree, a) => {
                let mut input = input;
                let mut v = Vec::new();
                loop {
                    let (va, next_input) = a.parse(program, scope, input)?;
                    input = next_input;
                    v.push(va);
                    if tree.matches(input).ok_or(ParseError::NoValidBranch {
                        offset: input.offset,
                    })? == 0
                    {
                        break;
                    }
                }
                Ok((Value::Seq(v), input))
            }
            Decoder::RepeatCount(expr, a) => {
                let mut input = input;
                let count = expr.eval_value(scope).unwrap_usize();
                let mut v = Vec::with_capacity(count);
                for _ in 0..count {
                    let (va, next_input) = a.parse(program, scope, input)?;
                    input = next_input;
                    v.push(va);
                }
                Ok((Value::Seq(v), input))
            }
            Decoder::RepeatUntilLast(expr, a) => {
                let mut input = input;
                let mut v = Vec::new();
                loop {
                    let (va, next_input) = a.parse(program, scope, input)?;
                    input = next_input;
                    let done = expr.eval_lambda(scope, va.clone()).unwrap_bool();
                    v.push(va);
                    if done {
                        break;
                    }
                }
                Ok((Value::Seq(v), input))
            }
            Decoder::RepeatUntilSeq(expr, a) => {
                let mut input = input;
                let mut v = Vec::new();
                loop {
                    let (va, next_input) = a.parse(program, scope, input)?;
                    input = next_input;
                    v.push(va);
                    let vs = Value::Seq(v.clone());
                    let done = expr.eval_lambda(scope, vs).unwrap_bool();
                    if done {
                        break;
                    }
                }
                Ok((Value::Seq(v), input))
            }
            Decoder::Peek(a) => {
                let (v, _next_input) = a.parse(program, scope, input)?;
                Ok((v, input))
            }
            Decoder::PeekNot(a) => {
                if a.parse(program, scope, input).is_ok() {
                    Err(ParseError::fail(scope, input))
                } else {
                    Ok((Value::Tuple(vec![]), input))
                }
            }
            Decoder::Slice(expr, a) => {
                let size = expr.eval_value(scope).unwrap_usize();
                let (slice, input) = input
                    .split_at(size)
                    .ok_or(ParseError::overrun(size, input.offset))?;
                let (v, _) = a.parse(program, scope, slice)?;
                Ok((v, input))
            }
            Decoder::Bits(a) => {
                let mut bits = Vec::with_capacity(input.remaining().len() * 8);
                for b in input.remaining() {
                    for i in 0..8 {
                        bits.push((b & (1 << i)) >> i);
                    }
                }
                let (v, bits) = a.parse(program, scope, ReadCtxt::new(&bits))?;
                let bytes_remain = bits.remaining().len() >> 3;
                let bytes_read = input.remaining().len() - bytes_remain;
                let (_, input) = input
                    .split_at(bytes_read)
                    .ok_or(ParseError::overrun(bytes_read, input.offset))?;
                Ok((v, input))
            }
            Decoder::WithRelativeOffset(expr, a) => {
                let offset = expr.eval_value(scope).unwrap_usize();
                let (_, slice) = input
                    .split_at(offset)
                    .ok_or(ParseError::overrun(offset, input.offset))?;
                let (v, _) = a.parse(program, scope, slice)?;
                Ok((v, input))
            }
            Decoder::Map(d, expr) => {
                let (orig, input) = d.parse(program, scope, input)?;
                let v = expr.eval_lambda(scope, orig.clone());
                Ok((Value::Mapped(Box::new(orig), Box::new(v)), input))
            }
            Decoder::Compute(expr) => {
                let v = expr.eval_value(scope);
                Ok((v, input))
            }
            Decoder::Match(head, branches) => {
                let head = head.eval(scope);
                for (index, (pattern, decoder)) in branches.iter().enumerate() {
                    if let Some(pattern_scope) = head.matches(scope, pattern) {
                        let (v, input) = decoder.parse(program, &pattern_scope, input)?;
                        return Ok((Value::Branch(index, Box::new(v)), input));
                    }
                }
                panic!("non-exhaustive patterns");
            }
            Decoder::MatchVariant(head, branches) => {
                let head = head.eval(scope);
                for (index, (pattern, label, decoder)) in branches.iter().enumerate() {
                    if let Some(pattern_scope) = head.matches(scope, pattern) {
                        let (v, input) = decoder.parse(program, &pattern_scope, input)?;
                        return Ok((
                            Value::Branch(
                                index,
                                Box::new(Value::Variant(label.clone(), Box::new(v))),
                            ),
                            input,
                        ));
                    }
                }
                panic!("exhaustive patterns");
            }
            Decoder::Dynamic(DynFormat::Huffman(lengths_expr, opt_values_expr)) => {
                let lengths_val = lengths_expr.eval(scope);
                let lengths = value_to_vec_usize(&lengths_val);
                let lengths = match opt_values_expr {
                    None => lengths,
                    Some(e) => {
                        let values = value_to_vec_usize(&e.eval(scope));
                        let mut new_lengths = [0].repeat(values.len());
                        for i in 0..lengths.len() {
                            new_lengths[values[i]] = lengths[i];
                        }
                        new_lengths
                    }
                };
                let f = make_huffman_codes(&lengths);
                Ok((Value::Format(Box::new(f)), input))
            }
            Decoder::Apply(name) => scope.call_decoder_by_name(name, program, input),
        }
    }
}

fn value_to_vec_usize(v: &Value) -> Vec<usize> {
    let vs = match v {
        Value::Seq(vs) => vs,
        _ => panic!("expected Seq"),
    };
    vs.iter()
        .map(|v| match v.coerce_mapped_value() {
            Value::U8(n) => *n as usize,
            Value::U16(n) => *n as usize,
            _ => panic!("expected U8 or U16"),
        })
        .collect::<Vec<usize>>()
}

fn make_huffman_codes(lengths: &[usize]) -> Format {
    let max_length = *lengths.iter().max().unwrap();
    let mut bl_count = [0].repeat(max_length + 1);

    for len in lengths {
        bl_count[*len] += 1;
    }

    let mut next_code = [0].repeat(max_length + 1);
    let mut code = 0;
    bl_count[0] = 0;

    for bits in 1..max_length + 1 {
        code = (code + bl_count[bits - 1]) << 1;
        next_code[bits] = code;
    }

    let mut codes = Vec::with_capacity(lengths.len());

    for n in 0..lengths.len() {
        let len = lengths[n];
        if len != 0 {
            codes.push(Format::Map(
                Box::new(bit_range(len, next_code[len])),
                Expr::Lambda("_".into(), Box::new(Expr::U16(n.try_into().unwrap()))),
            ));
            //println!("{:?}", codes[codes.len()-1]);
            next_code[len] += 1;
        } else {
            //codes.push((n.to_string(), Format::Fail));
        }
    }

    Format::Union(codes)
}

fn bit_range(n: usize, bits: usize) -> Format {
    let mut fs = Vec::with_capacity(n);
    for i in 0..n {
        let r = n - 1 - i;
        let b = (bits & (1 << r)) >> r != 0;
        fs.push(is_bit(b));
    }
    Format::Tuple(fs)
}

fn is_bit(b: bool) -> Format {
    Format::Byte(ByteSet::from([if b { 1 } else { 0 }]))
}

fn inflate(codes: &[Value]) -> Vec<Value> {
    let mut vs = Vec::new();
    for code in codes {
        match code {
            Value::Variant(name, v) => match (name.as_ref(), v.as_ref()) {
                ("literal", v) => match v.coerce_mapped_value() {
                    Value::U8(b) => vs.push(Value::U8(*b)),
                    _ => panic!("inflate: expected U8"),
                },
                ("reference", Value::Record(fields)) => {
                    let length = &fields
                        .iter()
                        .find(|(label, _)| label == "length")
                        .unwrap()
                        .1;
                    let distance = &fields
                        .iter()
                        .find(|(label, _)| label == "distance")
                        .unwrap()
                        .1;
                    match (length, distance) {
                        (Value::U16(length), Value::U16(distance)) => {
                            let length = *length as usize;
                            let distance = *distance as usize;
                            if distance > vs.len() {
                                panic!("inflate: distance out of range");
                            }
                            let start = vs.len() - distance;
                            for i in 0..length {
                                vs.push(vs[start + i].clone());
                            }
                        }
                        _ => panic!(
                            "inflate: unexpected length/distance {:?} {:?}",
                            length, distance
                        ),
                    }
                }
                _ => panic!("inflate: unknown code"),
            },
            _ => panic!("inflate: expected variant"),
        }
    }
    vs
}

#[cfg(test)]
#[allow(clippy::redundant_clone)]
mod tests {
    use super::*;

    fn alts<Label: Into<Cow<'static, str>>>(
        fields: impl IntoIterator<Item = (Label, Format)>,
    ) -> Format {
        Format::UnionVariant(
            (fields.into_iter())
                .map(|(label, format)| (label.into(), format))
                .collect(),
        )
    }

    fn record<Label: Into<Cow<'static, str>>>(
        fields: impl IntoIterator<Item = (Label, Format)>,
    ) -> Format {
        Format::Record(
            (fields.into_iter())
                .map(|(label, format)| (label.into(), format))
                .collect(),
        )
    }

    fn optional(format: Format) -> Format {
        alts([("some", format), ("none", Format::EMPTY)])
    }

    fn repeat(format: Format) -> Format {
        Format::Repeat(Box::new(format))
    }

    fn repeat1(format: Format) -> Format {
        Format::Repeat1(Box::new(format))
    }

    fn is_byte(b: u8) -> Format {
        Format::Byte(ByteSet::from([b]))
    }

    fn not_byte(b: u8) -> Format {
        Format::Byte(!ByteSet::from([b]))
    }

    fn accepts(d: &Decoder, input: &[u8], tail: &[u8], expect: Value) {
        let program = Program::new();
        let mut scope = Scope::new();
        let (val, remain) = d.parse(&program, &mut scope, ReadCtxt::new(input)).unwrap();
        assert_eq!(val, expect);
        assert_eq!(remain.remaining(), tail);
    }

    fn rejects(d: &Decoder, input: &[u8]) {
        let program = Program::new();
        let mut scope = Scope::new();
        assert!(d.parse(&program, &mut scope, ReadCtxt::new(input)).is_err());
    }

    #[test]
    fn compile_fail() {
        let f = Format::Fail;
        let d = Decoder::compile_one(&f).unwrap();
        rejects(&d, &[]);
        rejects(&d, &[0x00]);
    }

    #[test]
    fn compile_empty() {
        let f = Format::EMPTY;
        let d = Decoder::compile_one(&f).unwrap();
        accepts(&d, &[], &[], Value::UNIT);
        accepts(&d, &[0x00], &[0x00], Value::UNIT);
    }

    #[test]
    fn compile_byte_is() {
        let f = is_byte(0x00);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(&d, &[0x00], &[], Value::U8(0));
        accepts(&d, &[0x00, 0xFF], &[0xFF], Value::U8(0));
        rejects(&d, &[0xFF]);
        rejects(&d, &[]);
    }

    #[test]
    fn compile_byte_not() {
        let f = not_byte(0x00);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(&d, &[0xFF], &[], Value::U8(0xFF));
        accepts(&d, &[0xFF, 0x00], &[0x00], Value::U8(0xFF));
        rejects(&d, &[0x00]);
        rejects(&d, &[]);
    }

    #[test]
    fn compile_alt() {
        let f = alts::<&str>([]);
        let d = Decoder::compile_one(&f).unwrap();
        rejects(&d, &[]);
        rejects(&d, &[0x00]);
    }

    #[test]
    fn compile_alt_byte() {
        let f = alts([("a", is_byte(0x00)), ("b", is_byte(0xFF))]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Branch(0, Box::new(Value::variant("a", Value::U8(0x00)))),
        );
        accepts(
            &d,
            &[0xFF],
            &[],
            Value::Branch(1, Box::new(Value::variant("b", Value::U8(0xFF)))),
        );
        rejects(&d, &[0x11]);
        rejects(&d, &[]);
    }

    #[test]
    fn compile_alt_ambiguous() {
        let f = alts([("a", is_byte(0x00)), ("b", is_byte(0x00))]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_alt_slice_byte() {
        let slice_a = Format::Slice(Expr::U8(1), Box::new(is_byte(0x00)));
        let slice_b = Format::Slice(Expr::U8(1), Box::new(is_byte(0xFF)));
        let f = alts([("a", slice_a), ("b", slice_b)]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Branch(0, Box::new(Value::variant("a", Value::U8(0x00)))),
        );
        accepts(
            &d,
            &[0xFF],
            &[],
            Value::Branch(1, Box::new(Value::variant("b", Value::U8(0xFF)))),
        );
        rejects(&d, &[0x11]);
        rejects(&d, &[]);
    }

    #[test]
    fn compile_alt_slice_ambiguous1() {
        let slice_a = Format::Slice(Expr::U8(1), Box::new(is_byte(0x00)));
        let slice_b = Format::Slice(Expr::U8(1), Box::new(is_byte(0x00)));
        let f = alts([("a", slice_a), ("b", slice_b)]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_alt_slice_ambiguous2() {
        let tuple_a = Format::Tuple(vec![is_byte(0x00), is_byte(0x00)]);
        let tuple_b = Format::Tuple(vec![is_byte(0x00), is_byte(0xFF)]);
        let slice_a = Format::Slice(Expr::U8(1), Box::new(tuple_a));
        let slice_b = Format::Slice(Expr::U8(1), Box::new(tuple_b));
        let f = alts([("a", slice_a), ("b", slice_b)]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_alt_fail() {
        let f = alts([("a", Format::Fail), ("b", Format::Fail)]);
        let d = Decoder::compile_one(&f).unwrap();
        rejects(&d, &[]);
    }

    #[test]
    fn compile_alt_end_of_input() {
        let f = alts([("a", Format::EndOfInput), ("b", Format::EndOfInput)]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_alt_empty() {
        let f = alts([("a", Format::EMPTY), ("b", Format::EMPTY)]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_alt_fail_end_of_input() {
        let f = alts([("a", Format::Fail), ("b", Format::EndOfInput)]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[],
            &[],
            Value::Branch(1, Box::new(Value::variant("b", Value::UNIT))),
        );
    }

    #[test]
    fn compile_alt_end_of_input_or_byte() {
        let f = alts([("a", Format::EndOfInput), ("b", is_byte(0x00))]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[],
            &[],
            Value::Branch(0, Box::new(Value::variant("a", Value::UNIT))),
        );
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Branch(1, Box::new(Value::variant("b", Value::U8(0x00)))),
        );
        accepts(
            &d,
            &[0x00, 0x00],
            &[0x00],
            Value::Branch(1, Box::new(Value::variant("b", Value::U8(0x00)))),
        );
        rejects(&d, &[0x11]);
    }

    #[test]
    fn compile_alt_opt() {
        let f = alts([("a", Format::EMPTY), ("b", is_byte(0x00))]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Branch(1, Box::new(Value::variant("b", Value::U8(0x00)))),
        );
        accepts(
            &d,
            &[],
            &[],
            Value::Branch(0, Box::new(Value::variant("a", Value::UNIT))),
        );
        accepts(
            &d,
            &[0xFF],
            &[0xFF],
            Value::Branch(0, Box::new(Value::variant("a", Value::UNIT))),
        );
    }

    #[test]
    fn compile_alt_opt_next() {
        let f = Format::Tuple(vec![optional(is_byte(0x00)), is_byte(0xFF)]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::Tuple(vec![
                Value::Branch(0, Box::new(Value::variant("some", Value::U8(0)))),
                Value::U8(0xFF),
            ]),
        );
        accepts(
            &d,
            &[0xFF],
            &[],
            Value::Tuple(vec![
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                Value::U8(0xFF),
            ]),
        );
        rejects(&d, &[0x00]);
        rejects(&d, &[]);
    }

    #[test]
    fn compile_alt_opt_opt() {
        let f = Format::Tuple(vec![optional(is_byte(0x00)), optional(is_byte(0xFF))]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::Tuple(vec![
                Value::Branch(0, Box::new(Value::variant("some", Value::U8(0)))),
                Value::Branch(0, Box::new(Value::variant("some", Value::U8(0xFF)))),
            ]),
        );
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Tuple(vec![
                Value::Branch(0, Box::new(Value::variant("some", Value::U8(0)))),
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
            ]),
        );
        accepts(
            &d,
            &[0xFF],
            &[],
            Value::Tuple(vec![
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                Value::Branch(0, Box::new(Value::variant("some", Value::U8(0xFF)))),
            ]),
        );
        accepts(
            &d,
            &[],
            &[],
            Value::Tuple(vec![
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
            ]),
        );
        accepts(
            &d,
            &[],
            &[],
            Value::Tuple(vec![
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
            ]),
        );
        accepts(
            &d,
            &[0x7F],
            &[0x7F],
            Value::Tuple(vec![
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
            ]),
        );
    }

    #[test]
    fn compile_alt_opt_ambiguous() {
        let f = Format::Tuple(vec![optional(is_byte(0x00)), optional(is_byte(0x00))]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_alt_opt_ambiguous_slow() {
        let alt = alts([
            ("0x00", is_byte(0x00)),
            ("0x01", is_byte(0x01)),
            ("0x02", is_byte(0x02)),
            ("0x03", is_byte(0x03)),
            ("0x04", is_byte(0x04)),
            ("0x05", is_byte(0x05)),
            ("0x06", is_byte(0x06)),
            ("0x07", is_byte(0x07)),
        ]);
        let rec = record([
            ("0", alt.clone()),
            ("1", alt.clone()),
            ("2", alt.clone()),
            ("3", alt.clone()),
            ("4", alt.clone()),
            ("5", alt.clone()),
            ("6", alt.clone()),
            ("7", alt.clone()),
        ]);
        let f = alts([("a", rec.clone()), ("b", rec.clone())]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_repeat_alt_repeat1_slow() {
        let f = repeat(alts([
            ("a", repeat1(is_byte(0x00))),
            ("b", is_byte(0x01)),
            ("c", is_byte(0x02)),
        ]));
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_repeat() {
        let f = repeat(is_byte(0x00));
        let d = Decoder::compile_one(&f).unwrap();
        accepts(&d, &[], &[], Value::Seq(vec![]));
        accepts(&d, &[0xFF], &[0xFF], Value::Seq(vec![]));
        accepts(&d, &[0x00], &[], Value::Seq(vec![Value::U8(0x00)]));
        accepts(
            &d,
            &[0x00, 0x00],
            &[],
            Value::Seq(vec![Value::U8(0x00), Value::U8(0x00)]),
        );
    }

    #[test]
    fn compile_repeat_repeat() {
        let f = repeat(repeat(is_byte(0x00)));
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_cat_repeat() {
        let f = Format::Tuple(vec![repeat(is_byte(0x00)), repeat(is_byte(0xFF))]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[],
            &[],
            Value::Tuple(vec![Value::Seq(vec![]), Value::Seq(vec![])]),
        );
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Tuple(vec![Value::Seq(vec![Value::U8(0x00)]), Value::Seq(vec![])]),
        );
        accepts(
            &d,
            &[0xFF],
            &[],
            Value::Tuple(vec![Value::Seq(vec![]), Value::Seq(vec![Value::U8(0xFF)])]),
        );
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::Tuple(vec![
                Value::Seq(vec![Value::U8(0x00)]),
                Value::Seq(vec![Value::U8(0xFF)]),
            ]),
        );
        accepts(
            &d,
            &[0x00, 0xFF, 0x00],
            &[0x00],
            Value::Tuple(vec![
                Value::Seq(vec![Value::U8(0x00)]),
                Value::Seq(vec![Value::U8(0xFF)]),
            ]),
        );
        accepts(
            &d,
            &[0x7F],
            &[0x7F],
            Value::Tuple(vec![Value::Seq(vec![]), Value::Seq(vec![])]),
        );
    }

    #[test]
    fn compile_cat_end_of_input() {
        let f = Format::Tuple(vec![is_byte(0x00), Format::EndOfInput]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00],
            &[],
            Value::Tuple(vec![Value::U8(0x00), Value::UNIT]),
        );
        rejects(&d, &[]);
        rejects(&d, &[0x00, 0x00]);
    }

    #[test]
    fn compile_cat_repeat_end_of_input() {
        let f = Format::Tuple(vec![repeat(is_byte(0x00)), Format::EndOfInput]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[],
            &[],
            Value::Tuple(vec![Value::Seq(vec![]), Value::UNIT]),
        );
        accepts(
            &d,
            &[0x00, 0x00, 0x00],
            &[],
            Value::Tuple(vec![
                Value::Seq(vec![Value::U8(0x00), Value::U8(0x00), Value::U8(0x00)]),
                Value::UNIT,
            ]),
        );
        rejects(&d, &[0x00, 0x10]);
    }

    #[test]
    fn compile_cat_repeat_ambiguous() {
        let f = Format::Tuple(vec![repeat(is_byte(0x00)), repeat(is_byte(0x00))]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_repeat_fields() {
        let f = record([
            ("first", repeat(is_byte(0x00))),
            ("second", repeat(is_byte(0xFF))),
            ("third", repeat(is_byte(0x7F))),
        ]);
        assert!(Decoder::compile_one(&f).is_ok());
    }

    #[test]
    fn compile_repeat_fields_ambiguous() {
        let f = record([
            ("first", repeat(is_byte(0x00))),
            ("second", repeat(is_byte(0xFF))),
            ("third", repeat(is_byte(0x00))),
        ]);
        assert!(Decoder::compile_one(&f).is_err());
    }

    #[test]
    fn compile_repeat_fields_okay() {
        let f = record([
            ("first", repeat(is_byte(0x00))),
            (
                "second-and-third",
                optional(record([
                    (
                        "second",
                        Format::Tuple(vec![is_byte(0xFF), repeat(is_byte(0xFF))]),
                    ),
                    ("third", repeat(is_byte(0x00))),
                ])),
            ),
        ]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[],
            &[],
            Value::record([
                ("first", Value::Seq(vec![])),
                (
                    "second-and-third",
                    Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                ),
            ]),
        );
        accepts(
            &d,
            &[0x00],
            &[],
            Value::record([
                ("first", Value::Seq(vec![Value::U8(0x00)])),
                (
                    "second-and-third",
                    Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                ),
            ]),
        );
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::record([
                ("first", Value::Seq(vec![Value::U8(0x00)])),
                (
                    "second-and-third",
                    Value::Branch(
                        0,
                        Box::new(Value::variant(
                            "some",
                            Value::record([
                                (
                                    "second",
                                    Value::Tuple(vec![Value::U8(0xFF), Value::Seq(vec![])]),
                                ),
                                ("third", Value::Seq(vec![])),
                            ]),
                        )),
                    ),
                ),
            ]),
        );
        accepts(
            &d,
            &[0x00, 0xFF, 0x00],
            &[],
            Value::record(vec![
                ("first", Value::Seq(vec![Value::U8(0x00)])),
                (
                    "second-and-third",
                    Value::Branch(
                        0,
                        Box::new(Value::variant(
                            "some",
                            Value::record(vec![
                                (
                                    "second",
                                    Value::Tuple(vec![Value::U8(0xFF), Value::Seq(vec![])]),
                                ),
                                ("third", Value::Seq(vec![Value::U8(0x00)])),
                            ]),
                        )),
                    ),
                ),
            ]),
        );
        accepts(
            &d,
            &[0x00, 0x7F],
            &[0x7F],
            Value::record(vec![
                ("first", Value::Seq(vec![Value::U8(0x00)])),
                (
                    "second-and-third",
                    Value::Branch(1, Box::new(Value::variant("none", Value::UNIT))),
                ),
            ]),
        );
    }

    #[test]
    fn compile_repeat1() {
        let f = repeat1(is_byte(0x00));
        let d = Decoder::compile_one(&f).unwrap();
        rejects(&d, &[]);
        rejects(&d, &[0xFF]);
        accepts(&d, &[0x00], &[], Value::Seq(vec![Value::U8(0x00)]));
        accepts(
            &d,
            &[0x00, 0xFF],
            &[0xFF],
            Value::Seq(vec![Value::U8(0x00)]),
        );
        accepts(
            &d,
            &[0x00, 0x00],
            &[],
            Value::Seq(vec![Value::U8(0x00), Value::U8(0x00)]),
        );
    }

    #[test]
    fn compile_align1() {
        let f = Format::Tuple(vec![is_byte(0x00), Format::Align(1), is_byte(0xFF)]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::Tuple(vec![Value::U8(0x00), Value::UNIT, Value::U8(0xFF)]),
        );
    }

    #[test]
    fn compile_align2() {
        let f = Format::Tuple(vec![is_byte(0x00), Format::Align(2), is_byte(0xFF)]);
        let d = Decoder::compile_one(&f).unwrap();
        rejects(&d, &[0x00, 0xFF]);
        rejects(&d, &[0x00, 0x99, 0x99, 0xFF]);
        accepts(
            &d,
            &[0x00, 0x99, 0xFF],
            &[],
            Value::Tuple(vec![Value::U8(0x00), Value::UNIT, Value::U8(0xFF)]),
        );
    }

    #[test]
    fn compile_peek_not() {
        let any_byte = Format::Byte(ByteSet::full());
        let a = Format::Tuple(vec![is_byte(0xFF), is_byte(0xFF)]);
        let peek_not = Format::PeekNot(Box::new(a));
        let f = Format::Tuple(vec![peek_not, any_byte.clone(), any_byte.clone()]);
        let d = Decoder::compile_one(&f).unwrap();
        rejects(&d, &[]);
        rejects(&d, &[0xFF]);
        rejects(&d, &[0xFF, 0xFF]);
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::Tuple(vec![Value::Tuple(vec![]), Value::U8(0x00), Value::U8(0xFF)]),
        );
        accepts(
            &d,
            &[0xFF, 0x00],
            &[],
            Value::Tuple(vec![Value::Tuple(vec![]), Value::U8(0xFF), Value::U8(0x00)]),
        );
    }

    #[test]
    fn compile_peek_not_switch() {
        let any_byte = Format::Byte(ByteSet::full());
        let guard = Format::PeekNot(Box::new(Format::Tuple(vec![is_byte(0xFF), is_byte(0xFF)])));
        let a = Format::Tuple(vec![guard, Format::Repeat(Box::new(any_byte.clone()))]);
        let b = Format::Tuple(vec![is_byte(0xFF), is_byte(0xFF)]);
        let f = alts([("a", a), ("b", b)]);
        let d = Decoder::compile_one(&f).unwrap();
        accepts(
            &d,
            &[],
            &[],
            Value::Branch(
                0,
                Box::new(Value::Variant(
                    "a".into(),
                    Box::new(Value::Tuple(vec![Value::Tuple(vec![]), Value::Seq(vec![])])),
                )),
            ),
        );
        accepts(
            &d,
            &[0xFF],
            &[],
            Value::Branch(
                0,
                Box::new(Value::Variant(
                    "a".into(),
                    Box::new(Value::Tuple(vec![
                        Value::Tuple(vec![]),
                        Value::Seq(vec![Value::U8(0xFF)]),
                    ])),
                )),
            ),
        );
        accepts(
            &d,
            &[0x00, 0xFF],
            &[],
            Value::Branch(
                0,
                Box::new(Value::Variant(
                    "a".into(),
                    Box::new(Value::Tuple(vec![
                        Value::Tuple(vec![]),
                        Value::Seq(vec![Value::U8(0x00), Value::U8(0xFF)]),
                    ])),
                )),
            ),
        );
        accepts(
            &d,
            &[0xFF, 0x00],
            &[],
            Value::Branch(
                0,
                Box::new(Value::Variant(
                    "a".into(),
                    Box::new(Value::Tuple(vec![
                        Value::Tuple(vec![]),
                        Value::Seq(vec![Value::U8(0xFF), Value::U8(0x00)]),
                    ])),
                )),
            ),
        );
        accepts(
            &d,
            &[0xFF, 0xFF],
            &[],
            Value::Branch(
                1,
                Box::new(Value::Variant(
                    "b".into(),
                    Box::new(Value::Tuple(vec![Value::U8(0xFF), Value::U8(0xFF)])),
                )),
            ),
        );
    }

    #[test]
    fn compile_peek_not_lookahead() {
        let peek_not = Format::PeekNot(Box::new(repeat1(is_byte(0x00))));
        let any_byte = Format::Byte(ByteSet::full());
        let f = Format::Tuple(vec![peek_not, repeat1(any_byte)]);
        assert!(Decoder::compile_one(&f).is_err());
    }
}