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
    /// Sorted by field name
    Rec(Vec<(String, Ty)>),
    /// Domain (an enumerable type) and range
    Fun(Box<Ty>, Box<Ty>),
    /// Element type. A u128 bitmask if the element type has at most 128 values, otherwise a bounded
    /// sequence (SSet)
    Set(Box<Ty>),
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

/// A tuple `<<e1, ..., en>>` has the type of a record whose fields are named #01, #02, ... (no TLA+
/// field name starts with `#`, and the names sort in element order). Tuples of different lengths
/// are different types, so sequences (tuples whose length changes) are not expressible.
pub fn tuple_field(i: usize) -> String {
    format!("#{:02}", i + 1)
}

/// Operators of the Sequences module. Sequences (tuples whose length changes) are not supported, so
/// these are rejected by name.
pub const SEQ_OPS: &[&str] = &["Seq", "Len", "Append", "Head", "Tail", "SubSeq", "SelectSeq", "\\o"];

pub fn seq_op_error(f: &str) -> String {
    format!("sequences are not supported yet (`{f}`); fixed-length tuples are")
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
            Ty::Int(lo, hi) => u64::try_from((*hi as i128 - *lo as i128 + 1).max(0)).ok(),
            Ty::Enum(v) => Some(v.len() as u64),
            Ty::Rec(fs) => fs.iter().try_fold(1u64, |acc, (_, t)| acc.checked_mul(t.size()?)),
            Ty::Opt(t) => t.size()?.checked_add(1),
            Ty::Fun(..) | Ty::Set(..) => None,
        }
    }

    pub fn repr(&self) -> String {
        match self {
            Ty::Bool => "bool".into(),
            Ty::Int(..) => "i64".into(),
            Ty::Enum(_) => "u16".into(),
            Ty::Rec(fs) => format!("({})", fs.iter().map(|(_, t)| t.repr() + ",").collect::<String>()),
            Ty::Fun(d, c) => format!("[{}; {}]", c.repr(), d.size().unwrap_or(0)),
            Ty::Set(e) if is_sparse(self) => format!("SSet<{}, SCAP>", e.repr()),
            Ty::Set(_) => "u128".into(),
            Ty::Opt(t) => format!("(bool, {})", t.repr()),
        }
    }

    /// Whether the representation is layout-independent (i.e. retyping needs no conversion code)
    pub fn is_scalar(&self) -> bool {
        match self {
            Ty::Bool | Ty::Int(..) | Ty::Enum(_) => true,
            Ty::Rec(fs) => fs.iter().all(|(_, t)| t.is_scalar()),
            Ty::Opt(t) => t.is_scalar(),
            _ => false,
        }
    }

    pub fn kind_eq(&self, o: &Ty) -> bool {
        match (self, o) {
            (Ty::Bool, Ty::Bool) | (Ty::Int(..), Ty::Int(..)) | (Ty::Enum(_), Ty::Enum(_)) => true,
            (Ty::Rec(a), Ty::Rec(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|((x, s), (y, t))| x == y && s.kind_eq(t))
            }
            (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) => d1 == d2 && c1.kind_eq(c2),
            (Ty::Set(_), Ty::Set(_)) => is_sparse(self) == is_sparse(o),
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
        (Ty::Opt(a), Ty::Opt(b)) => Ty::Opt(join(a, b)?.into()),
        (Ty::Opt(a), b) | (b, Ty::Opt(a)) => Ty::Opt(join(a, b)?.into()),
        (Ty::Rec(x), Ty::Rec(y)) if is_tuple_fields(x) || is_tuple_fields(y) => {
            if !is_tuple_fields(x) || !is_tuple_fields(y) {
                return Err(format!("type mismatch: a tuple and a record: {a:?} vs {b:?}"));
            }
            if x.len() != y.len() {
                return Err(format!(
                    "tuples of different lengths ({} and {}); sequences are not supported yet",
                    x.len(),
                    y.len()
                ));
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
        (Ty::Fun(d, _), Ty::Rec(fs)) | (Ty::Rec(fs), Ty::Fun(d, _)) if is_tuple_fields(fs) && matches!(**d, Ty::Int(1, _)) => {
            return Err(format!("comparing a function over 1..n with a tuple is not supported: {a:?} vs {b:?}"))
        }
        (Ty::Set(x), Ty::Set(y)) => Ty::Set(join(x, y)?.into()),
        _ => return Err(format!("type mismatch: {a:?} vs {b:?}")),
    })
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
