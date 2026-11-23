use crate::alt::{FormatExt, FormatModuleExt, ValueTypeExt};
use crate::bounds::Bounds;
use crate::numeric::core::Bounds as NumBounds;
use crate::{BaseType, Expr, Format, FormatModule, IntoLabel, Label, TypeScope, ValueType};
use anyhow::{Result as AResult, anyhow};
use num_bigint::BigInt;
use serde::Serialize;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(tag = "tag", content = "data")]
pub enum Pattern {
    Binding(Label),
    Wildcard,
    Bool(bool),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Int(Bounds),
    ZConst(#[serde(serialize_with = "crate::numeric::core::ser_bigint")] BigInt),
    ZRange(NumBounds),
    Char(char),
    Tuple(Vec<Pattern>),
    Variant(Label, Box<Pattern>),
    Seq(Vec<Pattern>),
    Option(Option<Box<Pattern>>),
}

/// Returns `true` if `bounds` includes every value of the unsigned-integer type `b`.
fn bounds_cover_base(bounds: &Bounds, b: BaseType) -> bool {
    let type_max = match b {
        BaseType::U8 => u8::MAX as usize,
        BaseType::U16 => u16::MAX as usize,
        BaseType::U32 => u32::MAX as usize,
        BaseType::U64 => u64::MAX as usize,
        BaseType::Bool | BaseType::Char => return false,
    };
    bounds.min() == 0 && bounds.max().is_none_or(|max| max >= type_max)
}

impl Pattern {
    pub const UNIT: Pattern = Pattern::Tuple(Vec::new());

    pub fn z_const<N>(n: N) -> Pattern
    where
        BigInt: From<N>,
    {
        Pattern::ZConst(BigInt::from(n))
    }

    pub fn z_range<N>(min: N, max: N) -> Pattern
    where
        BigInt: From<N>,
    {
        Pattern::ZRange(NumBounds::new(min.into(), max.into()))
    }

    /// Constructs a pattern that matches against literal sequence of bytes.
    pub fn from_bytes(bs: &[u8]) -> Pattern {
        Pattern::Seq(bs.iter().copied().map(Pattern::U8).collect())
    }

    pub fn variant(label: impl IntoLabel, value: impl Into<Box<Self>>) -> Self {
        Pattern::Variant(label.into(), value.into())
    }

    pub fn binding(name: impl IntoLabel) -> Pattern {
        Pattern::Binding(name.into())
    }

    /// The variables bound by `self`, in order.
    fn binding_names(&self) -> Vec<&Label> {
        match self {
            Pattern::Binding(name) => vec![name],
            Pattern::Tuple(ps) | Pattern::Seq(ps) => {
                ps.iter().flat_map(Pattern::binding_names).collect()
            }
            Pattern::Variant(_, p) => p.binding_names(),
            Pattern::Option(Some(p)) => p.binding_names(),
            Pattern::Wildcard
            | Pattern::Bool(_)
            | Pattern::U8(_)
            | Pattern::U16(_)
            | Pattern::U32(_)
            | Pattern::U64(_)
            | Pattern::Int(_)
            | Pattern::ZConst(_)
            | Pattern::ZRange(_)
            | Pattern::Char(_)
            | Pattern::Option(None) => Vec::new(),
        }
    }

    pub(crate) fn build_scope(&self, scope: &mut TypeScope<'_>, t: Rc<ValueType>) -> AResult<()> {
        let t = match t.as_ref() {
            ValueType::Rec(_) => Rc::new(scope.unfold(ValueType::clone(&t))),
            _ => t,
        };
        match (self, t.as_ref()) {
            (Pattern::Binding(name), t) => {
                // FIXME - do we want to store an Rc<ValueType> in the scope instead, perhaps...?
                scope.push(name.clone(), t.clone());
            }
            (Pattern::Wildcard, _) => {}
            (Pattern::Bool(..), ValueType::Base(BaseType::Bool)) => {}
            (Pattern::U8(..), &ValueType::U8) => {}
            (Pattern::U16(..), &ValueType::U16) => {}
            (Pattern::U32(..), &ValueType::U32) => {}
            (Pattern::U64(..), &ValueType::U64) => {}
            // NOTE - an Auto scrutinee is matched against `U8(n)`..`U64(n)` by value
            (
                Pattern::U8(..) | Pattern::U16(..) | Pattern::U32(..) | Pattern::U64(..),
                ValueType::NumericHole,
            ) => {}
            // REVIEW - should we allow `Pattern::Int` to yield matches for ValueType::Signed(..)?
            (
                Pattern::Int(..),
                ValueType::Base(BaseType::U8 | BaseType::U16 | BaseType::U32 | BaseType::U64)
                | ValueType::NumericHole,
            ) => {}
            (Pattern::ZConst(..) | Pattern::ZRange(..), t) if t.is_numeric() => {}
            (Pattern::Tuple(ps), ValueType::Tuple(ts)) if ps.len() == ts.len() => {
                for (p, t) in Iterator::zip(ps.iter(), ts.iter()) {
                    p.build_scope(scope, Rc::new(t.clone()))?;
                }
            }
            (Pattern::Seq(ps), ValueType::Seq(t)) => {
                for p in ps {
                    p.build_scope(scope, Rc::new((**t).clone()))?;
                }
            }
            (Pattern::Option(None), ValueType::Option(_)) => {
                // do nothing
            }
            (Pattern::Option(Some(p)), ValueType::Option(t)) => {
                p.build_scope(scope, Rc::new((**t).clone()))?;
            }
            (Pattern::Variant(label, p), ValueType::Union(branches)) => {
                let Some(t) = branches.get(label) else {
                    return Err(anyhow!("pattern variant {label} not found in {branches:?}"));
                };
                // FIXME - this is pretty bad, but it is hard to do better without more destructive changes
                let tmp = Rc::new(t.clone());
                p.build_scope(scope, tmp)?;
            }
            // `Any` is the placeholder type of a recursive-batch member that registration's
            // first pass has not reached yet (see `FormatModule::infer_batch_types`), which
            // `ValueType::unify` already accepts as-is; the batch is then type-checked
            // properly. So a pattern matches it, with each variable it binds also `Any`.
            (p, ValueType::Any) => {
                for name in p.binding_names() {
                    scope.push(name.clone(), ValueType::Any);
                }
            }
            (l, r) => return Err(anyhow!("pattern {l:?} does not match type {r:?}")),
        }
        Ok(())
    }

    pub(crate) fn build_scope_ext(
        &self,
        scope: &mut TypeScope<'_, ValueTypeExt>,
        t: Rc<ValueTypeExt>,
    ) -> AResult<()> {
        match (self, t.as_ref()) {
            (Pattern::Binding(name), t) => {
                scope.push(name.clone(), t.clone());
            }
            (Pattern::Wildcard, _) => {}
            (Pattern::Bool(..), ValueTypeExt::Base(BaseType::Bool)) => {}
            (Pattern::U8(..), ValueTypeExt::Base(BaseType::U8)) => {}
            (Pattern::U16(..), ValueTypeExt::Base(BaseType::U16)) => {}
            (Pattern::U32(..), ValueTypeExt::Base(BaseType::U32)) => {}
            (Pattern::U64(..), ValueTypeExt::Base(BaseType::U64)) => {}
            // NOTE - an Auto scrutinee is matched against `U8(n)`..`U64(n)` by value
            (
                Pattern::U8(..) | Pattern::U16(..) | Pattern::U32(..) | Pattern::U64(..),
                ValueTypeExt::NumericHole,
            ) => {}
            (
                Pattern::Int(..),
                ValueTypeExt::Base(BaseType::U8 | BaseType::U16 | BaseType::U32 | BaseType::U64)
                | ValueTypeExt::NumericHole,
            ) => {}
            (Pattern::ZConst(..) | Pattern::ZRange(..), t) if t.is_numeric() => {}
            (Pattern::Tuple(ps), ValueTypeExt::Tuple(ts)) if ps.len() == ts.len() => {
                for (p, t) in Iterator::zip(ps.iter(), ts.iter()) {
                    p.build_scope_ext(scope, Rc::new(t.clone()))?;
                }
            }
            (Pattern::Seq(ps), ValueTypeExt::Seq(t)) => {
                for p in ps {
                    p.build_scope_ext(scope, Rc::new((**t).clone()))?;
                }
            }
            (Pattern::Option(None), ValueTypeExt::Option(_)) => {
                // do nothing
            }
            (Pattern::Option(Some(p)), ValueTypeExt::Option(t)) => {
                p.build_scope_ext(scope, Rc::new((**t).clone()))?;
            }
            (Pattern::Variant(label, p), ValueTypeExt::Union(branches)) => {
                let Some(t) = branches.get(label) else {
                    return Err(anyhow!("pattern variant {label} not found in {branches:?}"));
                };
                // FIXME - this is pretty bad, but it is hard to do better without more destructive changes
                let tmp = Rc::new(t.clone());
                p.build_scope_ext(scope, tmp)?;
            }
            // As in `build_scope`
            (p, ValueTypeExt::Any) => {
                for name in p.binding_names() {
                    scope.push(name.clone(), ValueTypeExt::Any);
                }
            }
            (l, r) => return Err(anyhow!("pattern {l:?} does not match type {r:?}")),
        }
        Ok(())
    }

    /// Returns `true` if `self` matches every value of type `t`, as required of the pattern of an
    /// [`Expr::Destructure`].
    ///
    /// Conservative: a pattern other than a binding or wildcard is deemed refutable against a type
    /// whose shape is not known (`Any`, `NumericHole`), and every `Seq` pattern is refutable, as no
    /// `ValueType` fixes the length of a sequence. A union type is taken as the exact set of
    /// variants a value of that type may take, so a variant pattern is irrefutable against a
    /// single-variant union.
    pub(crate) fn is_irrefutable_for(&self, scope: &TypeScope<'_>, t: &ValueType) -> bool {
        let t = scope.unfold(t.clone());
        match (self, &t) {
            (Pattern::Binding(_) | Pattern::Wildcard, _) => true,
            (Pattern::Tuple(ps), ValueType::Tuple(ts)) => {
                ps.len() == ts.len()
                    && Iterator::zip(ps.iter(), ts.iter())
                        .all(|(p, t)| p.is_irrefutable_for(scope, t))
            }
            (Pattern::Variant(label, p), ValueType::Union(branches)) => match branches.get(label) {
                Some(t) if branches.len() == 1 => p.is_irrefutable_for(scope, t),
                _ => false,
            },
            (Pattern::Int(bounds), ValueType::Base(b)) => bounds_cover_base(bounds, *b),
            _ => false,
        }
    }

    /// As [`Pattern::is_irrefutable_for`], but over [`ValueTypeExt`].
    pub(crate) fn is_irrefutable_for_ext(&self, t: &ValueTypeExt) -> bool {
        match (self, t) {
            (Pattern::Binding(_) | Pattern::Wildcard, _) => true,
            (Pattern::Tuple(ps), ValueTypeExt::Tuple(ts)) => {
                ps.len() == ts.len()
                    && Iterator::zip(ps.iter(), ts.iter()).all(|(p, t)| p.is_irrefutable_for_ext(t))
            }
            (Pattern::Variant(label, p), ValueTypeExt::Union(branches)) => {
                match branches.get(label) {
                    Some(t) if branches.len() == 1 => p.is_irrefutable_for_ext(t),
                    _ => false,
                }
            }
            (Pattern::Int(bounds), ValueTypeExt::Base(b)) => bounds_cover_base(bounds, *b),
            _ => false,
        }
    }

    pub(crate) fn infer_expr_branch_type(
        &self,
        scope: &TypeScope<'_>,
        head_type: Rc<ValueType>,
        expr: &Expr,
    ) -> AResult<ValueType> {
        let mut pattern_scope = TypeScope::child(scope);
        self.build_scope(&mut pattern_scope, head_type)?;
        expr.infer_type(&pattern_scope)
    }

    pub(crate) fn infer_expr_branch_type_ext(
        &self,
        scope: &TypeScope<'_, ValueTypeExt>,
        head_type: Rc<ValueTypeExt>,
        expr: &Expr,
    ) -> AResult<ValueTypeExt> {
        let mut pattern_scope = TypeScope::child(scope);
        self.build_scope_ext(&mut pattern_scope, head_type)?;
        expr.infer_type_ext(&pattern_scope)
    }
    pub(crate) fn infer_format_branch_type(
        &self,
        scope: &TypeScope<'_>,
        head_type: Rc<ValueType>,
        module: &FormatModule,
        format: &Format,
    ) -> AResult<ValueType> {
        let mut pattern_scope = TypeScope::child(scope);
        self.build_scope(&mut pattern_scope, head_type)?;
        module.infer_format_type(&pattern_scope, format)
    }

    pub(crate) fn infer_format_branch_type_ext(
        &self,
        scope: &TypeScope<'_, ValueTypeExt>,
        head_type: Rc<ValueTypeExt>,
        module: &FormatModuleExt,
        format: &FormatExt,
    ) -> AResult<ValueTypeExt> {
        let mut pattern_scope = TypeScope::child(scope);
        self.build_scope_ext(&mut pattern_scope, head_type)?;
        module.infer_format_ext_type(&pattern_scope, format)
    }

    /// Returns `true` if the pattern shadows the given name.
    pub(crate) fn shadows(&self, name: &str) -> bool {
        match self {
            Pattern::Binding(n) => n == name,
            Pattern::Wildcard => false,
            Pattern::Bool(_)
            | Pattern::U8(_)
            | Pattern::U16(_)
            | Pattern::U32(_)
            | Pattern::U64(_)
            | Pattern::Int(_)
            | Pattern::ZConst(_)
            | Pattern::ZRange(_)
            | Pattern::Char(_) => false,
            Pattern::Tuple(ts) => ts.iter().any(|p| p.shadows(name)),
            Pattern::Variant(_, p) => p.shadows(name),
            Pattern::Seq(ps) => ps.iter().any(|p| p.shadows(name)),
            Pattern::Option(opt_p) => opt_p.as_ref().is_some_and(|p| p.shadows(name)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::helper::{bind, compute, expr_destruct, variant};
    use crate::{Expr, FormatModule, Pattern};

    fn register(value: Expr, pattern: Pattern) {
        let mut module = FormatModule::new();
        module.define_format(
            "destructure",
            compute(expr_destruct(value, pattern, Expr::U8(0))),
        );
    }

    #[test]
    #[should_panic(expected = "is refutable")]
    fn refutable_literal_destructure_is_rejected_at_registration() {
        register(Expr::U8(1), Pattern::U8(2));
    }

    #[test]
    #[should_panic(expected = "is refutable")]
    fn seq_destructure_is_rejected_at_registration() {
        register(Expr::Seq(vec![Expr::U8(1)]), Pattern::Seq(vec![bind("x")]));
    }

    #[test]
    fn tuple_destructure_is_accepted() {
        register(
            Expr::Tuple(vec![Expr::U8(1), Expr::U16(2)]),
            Pattern::Tuple(vec![bind("x"), Pattern::Wildcard]),
        );
    }

    #[test]
    fn single_variant_destructure_is_accepted() {
        register(variant("A", Expr::U8(1)), Pattern::variant("A", bind("x")));
    }
}
