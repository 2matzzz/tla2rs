//! Finite types. A variable's type comes from TypeOK. The Rust representation of a value depends
//! only on the kind of its type; only sets (bitmasks) and functions (arrays) depend on element
//! order (the layout).

use crate::lexer::R;
use crate::value::Value;
use std::collections::{BTreeSet, HashMap};

/// The largest record type with optional fields whose values are numbered in TLC's order (see
/// `Ty::tlc_perm`; the generated checker holds the permutation as a table)
pub const PERM_MAX: u64 = 4096;

thread_local! {
    static PERMS: std::cell::RefCell<HashMap<Ty, std::rc::Rc<Vec<u32>>>> = std::cell::RefCell::new(HashMap::new());
    /// The order in which TLC creates each name (see `compile::tlc_string_ranks`)
    static FIELD_RANKS: std::cell::RefCell<HashMap<String, usize>> = std::cell::RefCell::new(HashMap::new());
}

pub fn set_field_ranks(r: HashMap<String, usize>) {
    FIELD_RANKS.with(|f| *f.borrow_mut() = r);
}

/// The order of record fields. TLC keeps a record's fields sorted by when it first created each
/// name (its normal form), and compares and prints records in that order; names it creates only
/// while exploring come last, alphabetically.
pub fn field_cmp(a: &str, b: &str) -> std::cmp::Ordering {
    FIELD_RANKS.with(|f| {
        let f = f.borrow();
        let r = |x: &str| f.get(x).copied().unwrap_or(usize::MAX);
        r(a).cmp(&r(b)).then_with(|| a.cmp(b))
    })
}

thread_local! {
    /// Pairs of field names that some record in the spec writes in the order opposite to TLC's
    static DISORDERED: std::cell::RefCell<Vec<(String, String)>> = const { std::cell::RefCell::new(vec![]) };
}

/// Notes the record constructors (`[a |-> ..]`, `[a : ..]`) whose fields are written in an order
/// other than TLC's: TLC prints such a record in the written order until it first compares it
/// (which puts it in its normal form), so ToString of it depends on evaluation history
pub fn note_written_fields(e: &crate::ast::Expr) {
    if let crate::ast::Expr::RecLit(fs) | crate::ast::Expr::RecSet(fs) = e {
        for i in 0..fs.len() {
            for j in i + 1..fs.len() {
                if field_cmp(&fs[i].0, &fs[j].0).is_gt() {
                    DISORDERED.with(|d| d.borrow_mut().push((fs[i].0.clone(), fs[j].0.clone())));
                }
            }
        }
    }
    for c in e.children() {
        note_written_fields(c);
    }
}

pub fn clear_written_fields() {
    DISORDERED.with(|d| d.borrow_mut().clear());
}

/// For a record with these fields, a pair written in the order opposite to TLC's, if any
pub fn disordered_fields(names: &[&str]) -> Option<(String, String)> {
    DISORDERED.with(|d| d.borrow().iter().find(|(a, b)| names.contains(&a.as_str()) && names.contains(&b.as_str())).cloned())
}

/// The error for ToString of such a record
pub fn disordered_error(a: &str, b: &str) -> String {
    format!(
        "ToString of a record with fields `{a}` and `{b}`, which the spec writes as `{a}` before `{b}`: TLC prints a record in the order it was written \
         until it first compares it, then as `{b}` before `{a}`, so the string depends on when TLC compared it. Write `{b}` before `{a}` to make it definite"
    )
}

/// A record's fields in TLC's order
pub fn sorted_fields<T>(mut fs: Vec<(String, T)>) -> Vec<(String, T)> {
    fs.sort_by(|a, b| field_cmp(&a.0, &b.0));
    fs
}

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
    /// A function whose domain is a subset of an enumerable type (built over a set from the state,
    /// or by :> and @@): stored as an optional value per element of the type
    PFun(Box<Ty>, Box<Ty>),
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

/// A function over part of a type (or a bag) whose domain type has at most this many values is an
/// array over the whole type; over a larger or unbounded type it is sparse
pub const DENSE_MAX: u64 = 1 << 16;

/// Whether a function over part of a type, or a bag, is sparse: held as the sorted set of its
/// (key, value) pairs (`fun_pairs`) instead of an array over its whole domain type
pub fn is_sparse_fun(t: &Ty) -> bool {
    match t {
        Ty::PFun(d, _) | Ty::Bag(d) => d.size().is_none_or(|n| n > DENSE_MAX),
        _ => false,
    }
}

/// The type a sparse function or bag is held as: a sparse set of <<key, value>> pairs, which sorts
/// by key first, so a key's pair is found by binary search (a bag holds only positive counts)
pub fn fun_pairs(t: &Ty) -> Ty {
    match t {
        Ty::PFun(d, c) => Ty::Set(Ty::Rec(vec![(tuple_field(0), d.as_ref().clone()), (tuple_field(1), c.as_ref().clone())]).into()),
        Ty::Bag(e) => Ty::Set(Ty::Rec(vec![(tuple_field(0), e.as_ref().clone()), (tuple_field(1), Ty::Int(1, BIG))]).into()),
        _ => unreachable!(),
    }
}

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

/// A tuple `<<e1, ..., en>>` has the type of a record whose fields are named #00001, #00002, ... (no TLA+
/// field name starts with `#`, and the names sort in element order). Tuples of different lengths
/// are different types, so sequences (tuples whose length changes) are not expressible.
pub fn tuple_field(i: usize) -> String {
    format!("#{:05}", i + 1)
}

/// Rust implements Eq, Hash, and Ord for tuples of at most 12 elements, so a record or tuple with
/// more fields is stored as nested tuples: groups of 12, grouped again while there are more than
/// 12 groups. `rec_build` builds a value (or type) from its fields in order, and `rec_field` is
/// the path to field i of n.
pub const REC_GROUP: usize = 12;

pub fn rec_build(parts: &[String]) -> String {
    if parts.len() <= REC_GROUP {
        return format!("({})", parts.iter().map(|p| format!("{p},")).collect::<String>());
    }
    let groups: Vec<String> = parts.chunks(REC_GROUP).map(rec_build).collect();
    rec_build(&groups)
}

pub fn rec_field(n: usize, i: usize) -> String {
    if n <= REC_GROUP {
        return format!(".{i}");
    }
    format!("{}.{}", rec_field(n.div_ceil(REC_GROUP), i / REC_GROUP), i % REC_GROUP)
}

pub fn tuple_ty(elems: Vec<Ty>) -> R<Ty> {
    if elems.len() > 99_999 {
        return Err("tuples of more than 99,999 elements are not supported".into());
    }
    Ok(Ty::Rec(elems.into_iter().enumerate().map(|(i, t)| (tuple_field(i), t)).collect()))
}

/// Whether record fields are those of a tuple
pub fn is_tuple_fields(fs: &[(String, Ty)]) -> bool {
    fs.iter().all(|(n, _)| n.starts_with('#'))
}

/// The field of a record type that also holds model values (a value that is a record or a model
/// value, as `[op : S] \cup {NoVal}`): present, it holds the model value, and no other field is
/// present. Every field of such a type is optional. The name is no TLA+ identifier
pub const ATOM_FIELD: &str = "(atom)";

/// Whether a record type also holds model values (see ATOM_FIELD)
pub fn has_atoms(fs: &[(String, Ty)]) -> bool {
    fs.iter().any(|(n, _)| n == ATOM_FIELD)
}

/// Whether `t` has a record type that also holds model values inside. Packing a value of it does
/// not check that each value is one of the records or model values a type invariant lists
pub fn mixes_atoms(t: &Ty) -> bool {
    match t {
        Ty::Rec(fs) => has_atoms(fs) || fs.iter().any(|(_, t)| mixes_atoms(t)),
        Ty::Opt(e) | Ty::Set(e) | Ty::Seq(e) | Ty::Bag(e) => mixes_atoms(e),
        Ty::Fun(d, c) | Ty::PFun(d, c) => mixes_atoms(d) || mixes_atoms(c),
        _ => false,
    }
}

/// A value of a record type: a model value when it has only ATOM_FIELD
pub fn rec_value(m: std::collections::BTreeMap<String, Value>) -> Value {
    if m.len() == 1 {
        if let Some(v) = m.get(ATOM_FIELD) {
            return v.clone();
        }
    }
    Value::Rec(m)
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
            Ty::Fun(..) | Ty::Set(..) | Ty::Seq(_) | Ty::Bag(_) | Ty::PFun(..) => None,
        }
    }

    pub fn repr(&self) -> String {
        match self {
            Ty::Bool => "bool".into(),
            Ty::Int(..) | Ty::IntAtom(..) => "i64".into(),
            Ty::Enum(_) => "u16".into(),
            Ty::Rec(fs) => rec_build(&fs.iter().map(|(_, t)| t.repr()).collect::<Vec<_>>()),
            Ty::Fun(d, c) => format!("[{}; {}]", c.repr(), d.size().unwrap_or(0)),
            Ty::Set(e) if is_sparse(self) => format!("SSet<{}, SCAP>", e.repr()),
            Ty::Seq(e) => format!("Sq<{}, QCAP>", e.repr()),
            Ty::Bag(_) | Ty::PFun(..) if is_sparse_fun(self) => fun_pairs(self).repr(),
            Ty::Bag(e) => format!("[i64; {}]", e.size().unwrap_or(0)),
            Ty::PFun(d, c) => format!("[(bool, {}); {}]", c.repr(), d.size().unwrap_or(0)),
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
            (Ty::PFun(d1, c1), Ty::PFun(d2, c2)) => d1 == d2 && c1.kind_eq(c2),
            (Ty::Opt(a), Ty::Opt(b)) => a.kind_eq(b),
            _ => false,
        }
    }

    /// Values in enumeration order (the inverse of enc)
    /// For a record type with optional fields (records of different fields) of at most
    /// `PERM_MAX` values: the rank in TLC's order of each value by its mixed-radix index (first
    /// field slowest, an absent field first). TLC compares records by their number of fields
    /// first, so that index is not its order; `enumerate` and `enc` follow TLC's order instead
    pub fn tlc_perm(&self) -> Option<std::rc::Rc<Vec<u32>>> {
        let Ty::Rec(fs) = self else { return None };
        if is_tuple_fields(fs) || !fs.iter().any(|(_, t)| matches!(t, Ty::Opt(_))) || self.size()? > PERM_MAX {
            return None;
        }
        PERMS.with(|m| {
            if let Some(p) = m.borrow().get(self) {
                return Some(p.clone());
            }
            let vals = self.enumerate_mixed();
            let mut order: Vec<usize> = (0..vals.len()).collect();
            order.sort_by(|&a, &b| vals[a].cmp(&vals[b]));
            let mut perm = vec![0u32; vals.len()];
            for (rank, &i) in order.iter().enumerate() {
                perm[i] = rank as u32;
            }
            let p = std::rc::Rc::new(perm);
            m.borrow_mut().insert(self.clone(), p.clone());
            Some(p)
        })
    }

    pub fn enumerate(&self) -> Vec<Value> {
        let vals = self.enumerate_mixed();
        match self.tlc_perm() {
            Some(perm) => {
                let mut out = vals.clone();
                for (i, v) in vals.into_iter().enumerate() {
                    out[perm[i] as usize] = v;
                }
                out
            }
            None => vals,
        }
    }

    /// The values of the type by their mixed-radix index (see `tlc_perm`)
    fn enumerate_mixed(&self) -> Vec<Value> {
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
                out.into_iter().map(rec_value).collect()
            }
            _ => vec![],
        }
    }

    pub fn enc(&self, v: &Value) -> Option<u64> {
        let i = self.enc_mixed(v)?;
        match self.tlc_perm() {
            Some(perm) => Some(perm[i as usize] as u64),
            None => Some(i),
        }
    }

    /// The mixed-radix index of a value (see `tlc_perm`)
    fn enc_mixed(&self, v: &Value) -> Option<u64> {
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
            (Ty::Rec(fs), Value::Atom(a)) if has_atoms(fs) => {
                self.enc_mixed(&Value::Rec([(ATOM_FIELD.to_string(), Value::Atom(*a))].into_iter().collect()))
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
            (Ty::PFun(d, c), v) => crate::value::as_fun(v).is_some_and(|m| m.iter().all(|(k, x)| d.conforms(k) && c.conforms(x))),
            (Ty::Bag(e), v) => crate::value::as_fun(v)
                .is_some_and(|m| m.iter().all(|(k, c)| e.conforms(k) && matches!(c, Value::Int(n) if *n > 0))),
            (Ty::Rec(fs), Value::Atom(a)) if has_atoms(fs) => {
                self.conforms(&Value::Rec([(ATOM_FIELD.to_string(), Value::Atom(*a))].into_iter().collect()))
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
            names.sort_by(|a, b| field_cmp(a, b));
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
        // Records and model values: a record type whose fields are all optional, with the model
        // values in ATOM_FIELD
        (Ty::Rec(fs), Ty::Enum(x)) | (Ty::Enum(x), Ty::Rec(fs)) if !is_tuple_fields(fs) => {
            let mut out: Vec<(String, Ty)> = fs
                .iter()
                .filter(|(n, _)| n != ATOM_FIELD)
                .map(|(n, t)| (n.clone(), if matches!(t, Ty::Opt(_)) { t.clone() } else { Ty::Opt(t.clone().into()) }))
                .collect();
            let atoms = match fs.iter().find(|(n, _)| n == ATOM_FIELD) {
                Some((_, t)) => join(t, &Ty::Enum(x.clone()))?,
                None => Ty::Opt(Ty::Enum(x.clone()).into()),
            };
            out.push((ATOM_FIELD.to_string(), atoms));
            out.sort_by(|a, b| field_cmp(&a.0, &b.0));
            Ty::Rec(out)
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
        // A function over part of a type joins with one over all of it (or with the empty one)
        (Ty::PFun(d1, c1), Ty::PFun(d2, c2)) => Ty::PFun(join(d1, d2)?.into(), join(c1, c2)?.into()),
        (Ty::PFun(d1, c1), Ty::Fun(d2, c2)) | (Ty::Fun(d2, c2), Ty::PFun(d1, c1)) => Ty::PFun(join(d1, d2)?.into(), join(c1, c2)?.into()),
        (Ty::PFun(d, c), Ty::Rec(fs)) | (Ty::Rec(fs), Ty::PFun(d, c)) if fs.is_empty() => Ty::PFun(d.clone(), c.clone()),
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
        Value::Rec(m) => Ty::Rec(sorted_fields(m.iter().map(|(k, x)| Ok((k.clone(), ty_of_value(x)?))).collect::<R<_>>()?)),
        Value::Fun(m) => {
            let mut c = Ty::Enum(vec![]);
            for x in m.values() {
                c = join(&c, &ty_of_value(x)?)?;
            }
            match elem_ty_of_domain(&m.keys().cloned().collect()) {
                Ok(dom) => Ty::Fun(dom.into(), c.into()),
                // A domain that is only part of a type: a function over part of that type
                Err(_) => match ty_of_value(&Value::Set(m.keys().cloned().collect()))? {
                    Ty::Set(k) => Ty::PFun(k, c.into()),
                    _ => unreachable!(),
                },
            }
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

/// Every value of type `t`, for types whose values can be listed: sets of at most `scap`
/// elements (when held as arrays), sequences of at most `qcap` elements. None when there are more
/// than `limit` values or the type is unbounded.
pub fn all_values(t: &Ty, qcap: usize, scap: usize, limit: usize) -> Option<Vec<Value>> {
    use crate::value::fun_value;
    let out: Vec<Value> = match t {
        _ if t.size().is_some() && !matches!(t, Ty::Rec(_)) => {
            if t.size()? > limit as u64 {
                return None;
            }
            t.enumerate()
        }
        Ty::Rec(fs) => {
            let tuple = is_tuple_fields(fs);
            let mut rows: Vec<Vec<Option<Value>>> = vec![vec![]];
            for (_, ft) in fs {
                let (vals, opt) = match ft {
                    Ty::Opt(i) => (all_values(i, qcap, scap, limit)?, true),
                    ft => (all_values(ft, qcap, scap, limit)?, false),
                };
                let mut next = vec![];
                for r in &rows {
                    if opt {
                        next.push([r.as_slice(), &[None]].concat());
                    }
                    for v in &vals {
                        next.push([r.as_slice(), &[Some(v.clone())]].concat());
                    }
                    if next.len() > limit {
                        return None;
                    }
                }
                rows = next;
            }
            rows.into_iter()
                .map(|r| {
                    if tuple {
                        Value::Tuple(r.into_iter().flatten().collect())
                    } else {
                        rec_value(fs.iter().zip(r).filter_map(|((k, _), v)| v.map(|v| (k.clone(), v))).collect())
                    }
                })
                .collect()
        }
        Ty::Set(e) => {
            let elems = all_values(e, qcap, scap, limit)?;
            let cap = if is_sparse(t) { scap.min(elems.len()) } else { elems.len() };
            let mut out: Vec<BTreeSet<Value>> = vec![BTreeSet::new()];
            for x in &elems {
                let mut more = vec![];
                for s in &out {
                    if s.len() < cap {
                        let mut s2 = s.clone();
                        s2.insert(x.clone());
                        more.push(s2);
                    }
                }
                out.extend(more);
                if out.len() > limit {
                    return None;
                }
            }
            out.into_iter().map(Value::Set).collect()
        }
        Ty::Fun(d, c) | Ty::PFun(d, c) => {
            if d.size().is_none_or(|n| n > limit as u64) {
                return None;
            }
            let keys = d.enumerate();
            let vals = all_values(c, qcap, scap, limit)?;
            let partial = matches!(t, Ty::PFun(..));
            let mut maps: Vec<std::collections::BTreeMap<Value, Value>> = vec![Default::default()];
            for k in &keys {
                let mut next = vec![];
                for m in &maps {
                    if partial {
                        next.push(m.clone());
                    }
                    for v in &vals {
                        let mut m2 = m.clone();
                        m2.insert(k.clone(), v.clone());
                        next.push(m2);
                    }
                    if next.len() > limit {
                        return None;
                    }
                }
                maps = next;
            }
            maps.into_iter().map(fun_value).collect()
        }
        Ty::Seq(e) => {
            let elems = all_values(e, qcap, scap, limit)?;
            let mut out = vec![Value::Tuple(vec![])];
            let mut last = vec![vec![]];
            for _ in 0..qcap {
                let mut next = vec![];
                for s in &last {
                    for x in &elems {
                        next.push([s.as_slice(), &[x.clone()]].concat());
                    }
                    if out.len() + next.len() > limit {
                        return None;
                    }
                }
                out.extend(next.iter().cloned().map(Value::Tuple));
                last = next;
            }
            out
        }
        _ => return None,
    };
    (out.len() <= limit).then_some(out)
}
