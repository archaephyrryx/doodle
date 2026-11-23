use crate::Expr;
use crate::decoder::{
    EvalError, Value,
    seq_kind::{SeqKind, ValueSeq},
};

/// Trait providing key-comparison functionality used in binary search to an interpreter value-node,
/// notably `Value` and `ParsedValue`. Used to implement `find_index_by_key_sorted`
pub(crate) trait AsKey {
    /// Compares two values as keys, using natural order on the types being represented: numeric
    /// order on integers, and lexicographic order on byte strings (`Seq(U8)`, a proper prefix
    /// ordered first).
    ///
    /// Returns an error if a `Numeric` key cannot be coerced to the type of the other key
    /// (e.g. `-1` against a `U8`).
    fn compare_as_key(&self, other: &Self) -> Result<std::cmp::Ordering, EvalError>;

    /// Tests equality over two values as keys, mirroring `compare_as_key`.
    ///
    /// Returns an error under the same conditions as `compare_as_key`.
    fn eq_key(&self, other: &Self) -> Result<bool, EvalError>;
}

/// The elements of a byte-string key, or `None` if `v` is not a sequence.
fn key_elems(v: &Value) -> Option<&SeqKind<Value>> {
    match v.get_sequence()? {
        ValueSeq::ValueSeq(elems) => Some(elems),
        ValueSeq::IntRange(..) => unimplemented!("FindByKey: unimplemented on IntRange keys"),
    }
}

impl AsKey for Value {
    fn compare_as_key(&self, other: &Self) -> Result<std::cmp::Ordering, EvalError> {
        // A key read from parsed data may be wrapped (e.g. `Mapped` or `Branch`), as may each of
        // its bytes.
        let (this, that) = (
            self.coerce_mapped_value().into_inner(),
            other.coerce_mapped_value().into_inner(),
        );
        if let (Some(xs), Some(ys)) = (key_elems(this), key_elems(that)) {
            for (x, y) in xs.iter().zip(ys.iter()) {
                let ord = x.compare_as_key(y)?;
                if ord.is_ne() {
                    return Ok(ord);
                }
            }
            return Ok(xs.len().cmp(&ys.len()));
        }
        let (this, that) =
            Value::to_uniform_integer_pair(this, that).map_err(EvalError::NumericConvert)?;
        Ok(match (this.as_ref(), that.as_ref()) {
            (Value::U8(a), Value::U8(b)) => a.cmp(b),
            (Value::U16(a), Value::U16(b)) => a.cmp(b),
            (Value::U32(a), Value::U32(b)) => a.cmp(b),
            (Value::U64(a), Value::U64(b)) => a.cmp(b),
            (Value::Numeric(a), Value::Numeric(b)) => {
                log::debug!("Value::compare_as_key called on numeric/numeric pair: ({a}, {b})");
                Ord::cmp(a.as_raw_value(), b.as_raw_value())
            }
            _ => panic!("Value::compare_as_key: Can't compare {self:?} and {other:?} as keys"),
        })
    }

    fn eq_key(&self, other: &Self) -> Result<bool, EvalError> {
        let (this, that) = (
            self.coerce_mapped_value().into_inner(),
            other.coerce_mapped_value().into_inner(),
        );
        if let (Some(xs), Some(ys)) = (key_elems(this), key_elems(that)) {
            if xs.len() != ys.len() {
                return Ok(false);
            }
            for (x, y) in xs.iter().zip(ys.iter()) {
                if !x.eq_key(y)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        let (this, that) =
            Value::to_uniform_integer_pair(this, that).map_err(EvalError::NumericConvert)?;
        Ok(match (this.as_ref(), that.as_ref()) {
            (Value::U8(a), Value::U8(b)) => a == b,
            (Value::U16(a), Value::U16(b)) => a == b,
            (Value::U32(a), Value::U32(b)) => a == b,
            (Value::U64(a), Value::U64(b)) => a == b,
            (Value::Numeric(a), Value::Numeric(b)) => {
                log::debug!("Value::eq_key called on numeric/numeric pair: ({a}, {b})");
                a.eq_val(b)
            }
            _ => panic!("Value::eq_key: can't compare {self:?} and {other:?} as keys"),
        })
    }
}

/// Helper struct to avoid evaluating key-values at the same index more than once
pub(crate) struct KeyCache<T>(Vec<std::cell::OnceCell<T>>);

impl<T> KeyCache<T> {
    pub(crate) fn new(len: usize) -> Self {
        let store = (0..len).map(|_| std::cell::OnceCell::new()).collect();
        Self(store)
    }

    pub(crate) fn get_or_init(&self, index: usize, f: impl FnOnce() -> T) -> &T {
        self.0[index].get_or_init(f)
    }
}

/// Binary search for `query` in `values`, which are sorted (ascending) by key. Of several matching
/// elements, returns the index of the first (leftmost), as `KeySearch::Sorted` specifies.
pub(crate) fn find_index_by_key_sorted<'a, V, V0, Eval>(
    f_get_key: &Expr,
    query: &V,
    values: &SeqKind<V0>,
    evaluate: Eval,
) -> Result<Option<usize>, EvalError>
where
    Eval: 'a + Fn(&Expr, &V0) -> V,
    V: AsKey,
    V0: Clone,
{
    use std::cmp::Ordering;
    let len = values.len();

    // cache to store keys we have seen after computing them once
    let cache = KeyCache::<V>::new(len);
    // helper closure to keep code below lightweight and more implementation-agnostic
    let get_key_at_index = |ix: usize| cache.get_or_init(ix, || evaluate(f_get_key, &values[ix]));

    // The partition point: the first index whose key is not less than `query`.
    let (mut lo, mut hi) = (0, len);
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        match get_key_at_index(mid).compare_as_key(query)? {
            Ordering::Less => lo = mid + 1,
            Ordering::Equal | Ordering::Greater => hi = mid,
        }
    }
    if lo < len && get_key_at_index(lo).eq_key(query)? {
        Ok(Some(lo))
    } else {
        Ok(None)
    }
}

/// Linear search for `query` in `values`, returning the index of the first match, or of the last if
/// `from_end` is set (`KeySearch::First` and `KeySearch::Last`). Stops at the match it returns.
pub(crate) fn find_index_by_key_linear<'a, V, V0, Eval>(
    f_get_key: &'a Expr,
    query: &V,
    values: &SeqKind<V0>,
    evaluate: Eval,
    from_end: bool,
) -> Result<Option<usize>, EvalError>
where
    Eval: 'a + Fn(&Expr, &V0) -> V,
    V: AsKey,
    V0: Clone,
{
    let len = values.len();
    for i in 0..len {
        let ix = if from_end { len - 1 - i } else { i };
        let key = evaluate(f_get_key, &values[ix]);
        if query.eq_key(&key)? {
            return Ok(Some(ix));
        }
    }
    Ok(None)
}
