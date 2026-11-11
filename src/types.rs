//! Finite types. A variable's type comes from TypeOK. The Rust representation of a value depends
//! only on the kind of its type; only sets (bitmasks) and functions (arrays) depend on element
//! order (the layout).

use crate::lexer::R;
use crate::value::Value;
use std::collections::BTreeSet;

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Ty {
    Bool,
    Int(i64, i64),
    /// Strings and model values, as ascending ids
    Enum(Vec<u32>),
    /// Integers lo..hi together with model values (ascending ids), as in `1..4 \cup {None}`. Stored
    /// as i64; model value a is i64::MIN + a, below every integer the checker stores, so it never
    /// equals an integer and every integer type's `enc` rejects it. The model values come first in
    /// the enumeration order, as TLC orders them before integers
    IntAtom(i64, i64, Vec<u32>),
    /// Sorted by field name
    Rec(Vec<(String, Ty)>),
    /// Domain (an enumerable type) and range
    Fun(Box<Ty>, Box<Ty>),
    /// Element type. A u128 bitmask if the element type has at most 128 values, otherwise a bounded
    /// sequence (SSet)
    Set(Box<Ty>),
    /// A sequence (a tuple whose length varies) of elements of this type, up to QCAP long
    Seq(Box<Ty>),
    /// A bag (Bags module) of elements of this (enumerable) type: a count per element, 0 for an
    /// element not in it. As a TLA+ value it is the function from its elements to their counts
    Bag(Box<Ty>),
    /// An optional record field (arises when records whose fields differ by variant are merged into
    /// one type). Represented as (present, value); an absent field holds the default value
    Opt(Box<Ty>),
}

/// Unbounded integers (Nat / Int), stored as 64-bit
pub const BIG: i64 = 1 << 62;

/// Whether this is a sparse set (SSet)
pub fn is_sparse(t: &Ty) -> bool {
    matches!(t, Ty::Set(e) if e.size().is_none_or(|n| n > SET_BITS))
}

pub const SET_BITS: u64 = 128;

/// Number of integers in lo..hi
fn int_count(lo: i64, hi: i64) -> Option<u64> {
    u64::try_from((hi as i128 - lo as i128 + 1).max(0)).ok()
}

/// Whether coercing `from` to `to` turns an integer-or-model-value into a model value somewhere.
/// That conversion fails at run time on an integer, so a comparison has to be made in the joined
/// type instead.
pub fn narrows(from: &Ty, to: &Ty) -> bool {
    match (from, to) {
        (Ty::IntAtom(..), Ty::Enum(_)) => true,
        // A sequence converted to a tuple or a function over 1..n fails unless the length matches
        (Ty::Seq(_), t) if !matches!(t, Ty::Seq(_)) => true,
        (Ty::Seq(a), Ty::Seq(b)) => narrows(a, b),
        (Ty::Rec(a), Ty::Rec(b)) => a.iter().any(|(n, t)| b.iter().find(|(m, _)| m == n).is_some_and(|(_, u)| narrows(t, u))),
        (Ty::Opt(a), Ty::Opt(b)) => narrows(a, b),
        (Ty::Opt(a), b) => narrows(a, b),
        (a, Ty::Opt(b)) => narrows(a, b),
        (Ty::Fun(_, a), Ty::Fun(_, b)) | (Ty::Set(a), Ty::Set(b)) => narrows(a, b),
        _ => false,
    }
}

/// A tuple `<<e1, ..., en>>` has the type of a record whose fields are named #01, #02, ... (no TLA+
/// field name starts with `#`, and the names sort in element order). Tuples of different lengths
/// are different types, so sequences (tuples whose length changes) are not expressible.
pub fn tuple_field(i: usize) -> String {
    format!("#{:02}", i + 1)
}

pub fn tuple_ty(elems: Vec<Ty>) -> R<Ty> {
    if elems.len() > 99 {
        return Err("tuples of more than 99 elements are not supported".into());
    }
    Ok(Ty::Rec(elems.into_iter().enumerate().map(|(i, t)| (tuple_field(i), t)).collect()))
}

/// Whether record fields are those of a tuple
pub fn is_tuple_fields(fs: &[(String, Ty)]) -> bool {
    fs.iter().all(|(n, _)| n.starts_with('#'))
}

/// The element types of a tuple type
pub fn tuple_elems(t: &Ty) -> Option<Vec<&Ty>> {
    match t {
        Ty::Rec(fs) if is_tuple_fields(fs) => Some(fs.iter().map(|(_, t)| t).collect()),
        _ => None,
    }
}

impl Ty {
    /// Number of values of an enumerable type
    pub fn size(&self) -> Option<u64> {
        match self {
            Ty::Bool => Some(2),
            Ty::Int(lo, hi) => int_count(*lo, *hi),
            Ty::Enum(v) => Some(v.len() as u64),
            Ty::IntAtom(lo, hi, v) => int_count(*lo, *hi)?.checked_add(v.len() as u64),
            Ty::Rec(fs) => fs.iter().try_fold(1u64, |acc, (_, t)| acc.checked_mul(t.size()?)),
            Ty::Opt(t) => t.size()?.checked_add(1),
            Ty::Fun(..) | Ty::Set(..) | Ty::Seq(_) | Ty::Bag(_) => None,
        }
    }

    pub fn repr(&self) -> String {
        match self {
            Ty::Bool => "bool".into(),
            Ty::Int(..) | Ty::IntAtom(..) => "i64".into(),
            Ty::Enum(_) => "u16".into(),
            Ty::Rec(fs) => format!("({})", fs.iter().map(|(_, t)| t.repr() + ",").collect::<String>()),
            Ty::Fun(d, c) => format!("[{}; {}]", c.repr(), d.size().unwrap_or(0)),
            Ty::Set(e) if is_sparse(self) => format!("SSet<{}, SCAP>", e.repr()),
            Ty::Seq(e) => format!("Sq<{}, QCAP>", e.repr()),
            Ty::Bag(e) => format!("[i64; {}]", e.size().unwrap_or(0)),
            Ty::Set(_) => "u128".into(),
            Ty::Opt(t) => format!("(bool, {})", t.repr()),
        }
    }

    /// Whether the representation is layout-independent (i.e. retyping needs no conversion code)
    pub fn is_scalar(&self) -> bool {
        match self {
            Ty::Bool | Ty::Int(..) | Ty::Enum(_) | Ty::IntAtom(..) => true,
            Ty::Rec(fs) => fs.iter().all(|(_, t)| t.is_scalar()),
            Ty::Opt(t) => t.is_scalar(),
            _ => false,
        }
    }

    pub fn kind_eq(&self, o: &Ty) -> bool {
        match (self, o) {
            (Ty::Bool, Ty::Bool) | (Ty::Enum(_), Ty::Enum(_)) => true,
            // The same i64 representation
            (Ty::Int(..) | Ty::IntAtom(..), Ty::Int(..) | Ty::IntAtom(..)) => true,
            (Ty::Rec(a), Ty::Rec(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|((x, s), (y, t))| x == y && s.kind_eq(t))
            }
            (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) => d1 == d2 && c1.kind_eq(c2),
            (Ty::Set(_), Ty::Set(_)) => is_sparse(self) == is_sparse(o),
            (Ty::Seq(a), Ty::Seq(b)) => a.kind_eq(b),
            (Ty::Bag(a), Ty::Bag(b)) => a == b,
            (Ty::Opt(a), Ty::Opt(b)) => a.kind_eq(b),
            _ => false,
        }
    }

    /// Values in enumeration order (the inverse of enc)
    pub fn enumerate(&self) -> Vec<Value> {
        match self {
            Ty::Bool => vec![Value::Bool(false), Value::Bool(true)],
            Ty::Int(lo, hi) => (*lo..=*hi).map(Value::Int).collect(),
            Ty::Enum(v) => v.iter().map(|&a| Value::Atom(a)).collect(),
            Ty::IntAtom(lo, hi, v) => v.iter().map(|&a| Value::Atom(a)).chain((*lo..=*hi).map(Value::Int)).collect(),
            Ty::Rec(fs) if is_tuple_fields(fs) => {
                // The first element varies slowest, as in enc
                let mut out: Vec<Vec<Value>> = vec![vec![]];
                for (_, t) in fs {
                    let vals = t.enumerate();
                    out = out.iter().flat_map(|r| vals.iter().map(move |v| [r.as_slice(), &[v.clone()]].concat())).collect();
                }
                out.into_iter().map(Value::Tuple).collect()
            }
            Ty::Rec(fs) => {
                let mut out = vec![std::collections::BTreeMap::new()];
                for (k, t) in fs {
                    let (vals, opt) = match t {
                        Ty::Opt(i) => (i.enumerate(), true),
                        t => (t.enumerate(), false),
                    };
                    let mut next = vec![];
                    for r in &out {
                        if opt {
                            next.push(r.clone());
                        }
                        for v in &vals {
                            let mut r2 = r.clone();
                            r2.insert(k.clone(), v.clone());
                            next.push(r2);
                        }
                    }
                    out = next;
                }
                out.into_iter().map(Value::Rec).collect()
            }
            _ => vec![],
        }
    }

    pub fn enc(&self, v: &Value) -> Option<u64> {
        match (self, v) {
            (Ty::Bool, Value::Bool(b)) => Some(*b as u64),
            (Ty::Int(lo, hi), Value::Int(i)) if lo <= i && i <= hi => Some((i - lo) as u64),
            (Ty::Enum(d), Value::Atom(a)) => d.iter().position(|x| x == a).map(|p| p as u64),
            (Ty::IntAtom(lo, hi, d), Value::Int(i)) if lo <= i && i <= hi => Some(d.len() as u64 + (i - lo) as u64),
            (Ty::IntAtom(_, _, d), Value::Atom(a)) => d.iter().position(|x| x == a).map(|p| p as u64),
            (Ty::Rec(fs), Value::Tuple(xs)) if is_tuple_fields(fs) => {
                if xs.len() != fs.len() {
                    return None;
                }
                let mut acc = 0u64;
                for ((_, t), x) in fs.iter().zip(xs) {
                    acc = acc * t.size()? + t.enc(x)?;
                }
                Some(acc)
            }
            (Ty::Rec(fs), Value::Rec(m)) if !is_tuple_fields(fs) => {
                if m.keys().any(|k| !fs.iter().any(|(n, _)| n == k)) {
                    return None;
                }
                let mut acc = 0u64;
                for (k, t) in fs {
                    let e = match (t, m.get(k)) {
                        (Ty::Opt(_), None) => 0,
                        (Ty::Opt(i), Some(v)) => 1 + i.enc(v)?,
                        (t, Some(v)) => t.enc(v)?,
                        (_, None) => return None,
                    };
                    acc = acc * t.size()? + e;
                }
                Some(acc)
            }
            _ => None,
        }
    }

    /// Whether the value fits this type (layout)
    pub fn conforms(&self, v: &Value) -> bool {
        match (self, v) {
            (Ty::Set(e), Value::Set(s)) => s.iter().all(|x| e.enc(x).is_some()),
            (Ty::Fun(d, c), Value::Fun(m)) => {
                let keys: Vec<Value> = m.keys().cloned().collect();
                let mut dom = d.enumerate();
                dom.sort();
                keys == dom && m.values().all(|x| c.conforms(x))
            }
            (Ty::Rec(fs), Value::Tuple(xs)) if is_tuple_fields(fs) => {
                xs.len() == fs.len() && fs.iter().zip(xs).all(|((_, t), x)| t.conforms(x))
            }
            (Ty::Fun(d, c), Value::Tuple(xs)) if seq_domain(d) == Some(xs.len()) => xs.iter().all(|x| c.conforms(x)),
            (Ty::Seq(e), Value::Tuple(xs)) => xs.iter().all(|x| e.conforms(x)),
            (Ty::Bag(e), v) => crate::value::as_fun(v)
                .is_some_and(|m| m.iter().all(|(k, c)| e.enc(k).is_some() && matches!(c, Value::Int(n) if *n > 0))),
            (Ty::Rec(fs), Value::Rec(m)) if !is_tuple_fields(fs) => {
                m.keys().all(|k| fs.iter().any(|(n, _)| n == k))
                    && fs.iter().all(|(k, t)| match (t, m.get(k)) {
                        (Ty::Opt(i), Some(x)) => i.conforms(x),
                        (Ty::Opt(_), None) => true,
                        (t, Some(x)) => t.conforms(x),
                        (_, None) => false,
                    })
            }
            _ => self.enc(v).is_some(),
        }
    }
}

pub fn join(a: &Ty, b: &Ty) -> R<Ty> {
    Ok(match (a, b) {
        (Ty::Enum(x), t) if x.is_empty() && !matches!(t, Ty::Enum(_)) => t.clone(),
        (t, Ty::Enum(x)) if x.is_empty() && !matches!(t, Ty::Enum(_)) => t.clone(),
        (Ty::Bool, Ty::Bool) => Ty::Bool,
        (Ty::Int(a, b), Ty::Int(c, d)) => Ty::Int(*a.min(c), *b.max(d)),
        (Ty::Enum(x), Ty::Enum(y)) => {
            let s: BTreeSet<u32> = x.iter().chain(y).copied().collect();
            Ty::Enum(s.into_iter().collect())
        }
        (Ty::Int(a, b), Ty::Enum(x)) | (Ty::Enum(x), Ty::Int(a, b)) => Ty::IntAtom(*a, *b, x.clone()),
        (Ty::IntAtom(a, b, x), Ty::Int(c, d)) | (Ty::Int(c, d), Ty::IntAtom(a, b, x)) => Ty::IntAtom(*a.min(c), *b.max(d), x.clone()),
        (Ty::IntAtom(a, b, x), Ty::Enum(y)) | (Ty::Enum(y), Ty::IntAtom(a, b, x)) => {
            Ty::IntAtom(*a, *b, x.iter().chain(y).copied().collect::<BTreeSet<u32>>().into_iter().collect())
        }
        (Ty::IntAtom(a, b, x), Ty::IntAtom(c, d, y)) => {
            Ty::IntAtom(*a.min(c), *b.max(d), x.iter().chain(y).copied().collect::<BTreeSet<u32>>().into_iter().collect())
        }
        (Ty::Opt(a), Ty::Opt(b)) => Ty::Opt(join(a, b)?.into()),
        (Ty::Opt(a), b) | (b, Ty::Opt(a)) => Ty::Opt(join(a, b)?.into()),
        (Ty::Rec(x), Ty::Rec(y)) if is_tuple_fields(x) || is_tuple_fields(y) => {
            if !is_tuple_fields(x) || !is_tuple_fields(y) {
                return Err(format!("type mismatch: a tuple and a record: {a:?} vs {b:?}"));
            }
            if x.len() != y.len() {
                // Tuples of different lengths are values of one sequence type
                return Ok(Ty::Seq(seq_elem_join(&[a, b])?.into()));
            }
            Ty::Rec(x.iter().zip(y).map(|((n, s), (_, t))| Ok((n.clone(), join(s, t)?))).collect::<R<_>>()?)
        }
        (Ty::Rec(x), Ty::Rec(y)) => {
            // Union of the fields; a field present on only one side becomes optional
            let mut names: Vec<String> = x.iter().chain(y).map(|f| f.0.clone()).collect();
            names.sort();
            names.dedup();
            let mut fs = vec![];
            for n in names {
                let a = x.iter().find(|f| f.0 == n).map(|f| &f.1);
                let b = y.iter().find(|f| f.0 == n).map(|f| &f.1);
                let t = match (a, b) {
                    (Some(a), Some(b)) => join(a, b)?,
                    (Some(t), None) | (None, Some(t)) => match t {
                        Ty::Opt(_) => t.clone(),
                        t => Ty::Opt(t.clone().into()),
                    },
                    (None, None) => unreachable!(),
                };
                fs.push((n, t));
            }
            Ty::Rec(fs)
        }
        (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) if d1 == d2 => Ty::Fun(d1.clone(), join(c1, c2)?.into()),
        // A function over 1..n is a tuple of length n (TLA+ identifies them): with a tuple of the
        // same length it stays such a function, otherwise the two are sequences
        (Ty::Fun(d, c), Ty::Rec(fs)) | (Ty::Rec(fs), Ty::Fun(d, c)) if is_tuple_fields(fs) && seq_domain(d).is_some() => {
            if seq_domain(d) == Some(fs.len()) {
                let mut e = c.as_ref().clone();
                for (_, t) in fs {
                    e = join(&e, t)?;
                }
                Ty::Fun(d.clone(), e.into())
            } else {
                Ty::Seq(seq_elem_join(&[a, b])?.into())
            }
        }
        (Ty::Fun(d1, _), Ty::Fun(d2, _)) if seq_domain(d1).is_some() && seq_domain(d2).is_some() => Ty::Seq(seq_elem_join(&[a, b])?.into()),
        (Ty::Seq(_), t) | (t, Ty::Seq(_)) if seq_elems(t).is_some() => Ty::Seq(seq_elem_join(&[a, b])?.into()),
        (Ty::Set(x), Ty::Set(y)) => Ty::Set(join(x, y)?.into()),
        (Ty::Bag(x), Ty::Bag(y)) => Ty::Bag(join(x, y)?.into()),
        // <<>> is the empty function, so also the empty bag
        (Ty::Bag(x), Ty::Rec(fs)) | (Ty::Rec(fs), Ty::Bag(x)) if fs.is_empty() => Ty::Bag(x.clone()),
        // A bag over 1..n is a tuple of counts (SetToBag({1}) = <<1>>)
        (Ty::Bag(x), Ty::Rec(fs)) | (Ty::Rec(fs), Ty::Bag(x)) if is_tuple_fields(fs) && fs.iter().all(|(_, t)| matches!(t, Ty::Int(..))) => {
            Ty::Bag(join(x, &Ty::Int(1, fs.len() as i64))?.into())
        }
        _ => return Err(format!("type mismatch: {a:?} vs {b:?}")),
    })
}

/// n when the type `d` of a function domain is 1..n (an empty 1..0 included)
pub fn seq_domain(d: &Ty) -> Option<usize> {
    match d {
        Ty::Int(1, hi) if *hi >= 0 && *hi < 1 << 16 => Some(*hi as usize),
        _ => None,
    }
}

/// The element types of a value that is a sequence in TLA+: a tuple, a function over 1..n, or a
/// sequence
pub fn seq_elems(t: &Ty) -> Option<Vec<Ty>> {
    match t {
        Ty::Seq(e) => Some(vec![e.as_ref().clone()]),
        Ty::Fun(d, c) if seq_domain(d).is_some() => Some(vec![c.as_ref().clone()]),
        Ty::Rec(fs) if is_tuple_fields(fs) => Some(fs.iter().map(|(_, t)| t.clone()).collect()),
        _ => None,
    }
}

/// The element type of a sequence that can hold the elements of all of `ts`
pub fn seq_elem_join(ts: &[&Ty]) -> R<Ty> {
    let mut e = Ty::Enum(vec![]);
    for t in ts {
        for x in seq_elems(t).ok_or(format!("{t:?} is not a sequence"))? {
            e = join(&e, &x)?;
        }
    }
    Ok(e)
}

pub fn ty_of_value(v: &Value) -> R<Ty> {
    Ok(match v {
        Value::Bool(_) => Ty::Bool,
        Value::Int(i) => Ty::Int(*i, *i),
        Value::Atom(a) => Ty::Enum(vec![*a]),
        Value::Set(s) => {
            let mut t = Ty::Enum(vec![]);
            for x in s {
                t = join(&t, &ty_of_value(x)?)?;
            }
            Ty::Set(t.into())
        }
        Value::Rec(m) => Ty::Rec(m.iter().map(|(k, x)| Ok((k.clone(), ty_of_value(x)?))).collect::<R<_>>()?),
        Value::Fun(m) => {
            let dom = elem_ty_of_domain(&m.keys().cloned().collect())?;
            let mut c = Ty::Enum(vec![]);
            for x in m.values() {
                c = join(&c, &ty_of_value(x)?)?;
            }
            Ty::Fun(dom.into(), c.into())
        }
        Value::Tuple(xs) => tuple_ty(xs.iter().map(ty_of_value).collect::<R<_>>()?)?,
    })
}

/// Element type of a set used as a function domain. Enumerating the type must yield exactly that
/// set.
pub fn elem_ty_of_domain(s: &BTreeSet<Value>) -> R<Ty> {
    let t = match ty_of_value(&Value::Set(s.clone()))? {
        Ty::Set(t) => *t,
        _ => unreachable!(),
    };
    let mut e = t.enumerate();
    e.sort();
    if e.into_iter().collect::<BTreeSet<_>>() != *s {
        return Err(format!("function domain must be a full finite type (e.g. a set of model values or a..b), got {s:?}"));
    }
    Ok(t)
}
