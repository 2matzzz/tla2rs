//! Generates a Rust model checker from fully expanded expressions.
//!
//! - A state is a `Copy` struct with one field per variable
//! - Init / Next are compiled in continuation-passing style, threading the remaining conjuncts
//!   through and emitting a nested block for each branch
//! - Constant subexpressions are evaluated at compile time and emitted as literals

use crate::ast::*;
use crate::lexer::R;
use crate::types::*;
use crate::value::*;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

#[derive(Clone, Default)]
pub struct Env {
    /// Bound variables and `@`: name -> (Rust expression, type)
    locals: HashMap<String, (String, Ty)>,
    /// Primed variables that have already been assigned
    primed: HashMap<String, (String, Ty)>,
    init: bool,
    label: Option<u32>,
    /// Whether the label is settled (for a dispatching definition such as Next, the label is
    /// overwritten by the inner definition's name)
    label_final: bool,
    /// Bound variables whose index within their type is known.
    /// Used as a function argument, they skip the conversion from atom value to index.
    idx: HashMap<String, (Ty, String)>,
    /// Variable holding the successor state under construction; created from `*s` on the first
    /// assignment
    work: Option<String>,
}

/// A single WF_v(A(args)) instance
pub struct FairInst {
    pub name: String,
    pub args: Vec<Value>,
    pub display: String,
    /// Variables occurring in the subscript v
    pub sub: Vec<String>,
}

pub struct Gen<'a> {
    pub atoms: &'a Atoms,
    pub ce: ConstEval<'a>,
    pub vars: Vec<(String, Ty)>,
    tys: Vec<Ty>,
    ty_ids: HashMap<Ty, usize>,
    convs: BTreeSet<(usize, usize)>,
    pub labels: Vec<String>,
    tmp: usize,
    /// Fairness instances
    pub fair: Vec<FairInst>,
    fair_param_tys: Vec<Vec<Ty>>,
    /// Maximum cardinality of a sparse set (SSet)
    pub scap: usize,
    /// During type inference, collects the types of assigned values
    pub infer: Option<HashMap<String, Ty>>,
}

fn rid(n: &str) -> String {
    format!("l_{}", n.replace(|c: char| !c.is_ascii_alphanumeric() && c != '_', "_"))
}

impl<'a> Gen<'a> {
    pub fn new(atoms: &'a Atoms, constants: &'a HashMap<String, Value>) -> Self {
        Gen {
            atoms,
            ce: ConstEval { atoms, constants },
            vars: vec![],
            tys: vec![],
            ty_ids: HashMap::new(),
            convs: BTreeSet::new(),
            labels: vec!["Init".into(), "Next".into()],
            tmp: 0,
            fair: vec![],
            fair_param_tys: vec![],
            scap: 8,
            infer: None,
        }
    }

    fn fresh(&mut self, p: &str) -> String {
        self.tmp += 1;
        format!("__{p}{}", self.tmp)
    }

    pub fn label_id(&mut self, n: &str) -> u32 {
        if let Some(i) = self.labels.iter().position(|x| x == n) {
            return i as u32;
        }
        self.labels.push(n.into());
        (self.labels.len() - 1) as u32
    }

    /// Registers a type (along with its element, domain and codomain types) so helpers are
    /// emitted for it.
    fn ty_id(&mut self, t: &Ty) -> R<usize> {
        if let Some(&i) = self.ty_ids.get(t) {
            return Ok(i);
        }
        match t {
            Ty::Set(e) => {
                self.ty_id(e)?;
            }
            Ty::Opt(e) => {
                self.ty_id(e)?;
            }
            Ty::Fun(d, c) => {
                d.size().ok_or("function domain must be a finite scalar type")?;
                self.ty_id(d)?;
                self.ty_id(c)?;
            }
            Ty::Rec(fs) => {
                for (_, f) in fs {
                    self.ty_id(f)?;
                }
            }
            Ty::IntAtom(_, _, d) => self.check_model_values(d)?,
            _ => {}
        }
        let i = self.tys.len();
        self.tys.push(t.clone());
        self.ty_ids.insert(t.clone(), i);
        Ok(i)
    }

    /// Only model values can share a type with integers: TLC compares a model value with anything,
    /// but stops with an error when comparing a string with an integer
    fn check_model_values(&self, atoms: &[u32]) -> R<()> {
        match atoms.iter().find(|&&a| !self.atoms.list[a as usize].0) {
            Some(&a) => Err(format!(
                "the string {} is mixed with integers in one value; only model values can be (TLC reports comparing a string with an integer as an error)",
                self.atoms.show(a)
            )),
            None => Ok(()),
        }
    }

    /// How TLC compares values of types `a` and `b` when a tuple meets something else. A tuple of
    /// another length or a model value is unequal to it; an integer, boolean, string, record, set,
    /// or function makes TLC stop with an error. A function over 1..n is not compiled (Err).
    fn tuple_cmp(&self, a: &Ty, b: &Ty) -> R<Cmp> {
        // Several parts: an error anywhere wins, then a part that is never equal
        let all = |parts: Vec<Cmp>| {
            parts.iter().find(|c| matches!(c, Cmp::Fails(_))).cloned().unwrap_or(if parts.contains(&Cmp::Unequal) {
                Cmp::Unequal
            } else {
                Cmp::Normal
            })
        };
        Ok(match (tuple_elems(a), tuple_elems(b)) {
            (Some(x), Some(y)) if x.len() != y.len() => Cmp::Unequal,
            (Some(x), Some(y)) => all(x.iter().zip(&y).map(|(s, t)| self.tuple_cmp(s, t)).collect::<R<_>>()?),
            (Some(_), None) => self.tuple_vs(b)?,
            (None, Some(_)) => self.tuple_vs(a)?,
            (None, None) => match (a, b) {
                (Ty::Rec(x), Ty::Rec(y)) => all(
                    x.iter()
                        .filter_map(|(n, s)| y.iter().find(|(m, _)| m == n).map(|(_, t)| self.tuple_cmp(s, t)))
                        .collect::<R<_>>()?,
                ),
                // Only an error carries over: empty sets or absent fields can still be equal
                (Ty::Opt(_), _) | (_, Ty::Opt(_)) | (Ty::Set(_), Ty::Set(_)) | (Ty::Fun(..), Ty::Fun(..)) => {
                    let (x, y): (&Ty, &Ty) = match (a, b) {
                        (Ty::Opt(x), y) | (y, Ty::Opt(x)) => (x, y),
                        (Ty::Set(x), Ty::Set(y)) | (Ty::Fun(_, x), Ty::Fun(_, y)) => (x, y),
                        _ => unreachable!(),
                    };
                    match self.tuple_cmp(x, y)? {
                        Cmp::Fails(m) => Cmp::Fails(m),
                        _ => Cmp::Normal,
                    }
                }
                _ => Cmp::Normal,
            },
        })
    }

    /// `tuple_cmp` of a tuple against a value of the non-tuple type `t`
    fn tuple_vs(&self, t: &Ty) -> R<Cmp> {
        Ok(match t {
            Ty::Enum(v) if v.is_empty() => Cmp::Normal,
            Ty::Enum(v) if v.iter().all(|&a| self.atoms.list[a as usize].0) => Cmp::Unequal,
            _ if seq_like_fun(t) => return Err("comparing a function over 1..n with a tuple is not supported".into()),
            _ => Cmp::Fails(format!("Attempted to compare a tuple with a value of type {t:?}")),
        })
    }

    pub fn ty_id_pub(&mut self, t: &Ty) -> R<usize> {
        self.ty_id(t)
    }

    /// Rewrites (e)' as e with every variable in it primed
    fn prime_vars(&self, e: &Expr) -> Expr {
        match e {
            Expr::Ident(n) if self.is_var(n) => Expr::Prime(e.clone().b()),
            Expr::Prime(_) => e.clone(),
            _ => map_children(e, &|c| self.prime_vars(c)),
        }
    }

    fn is_var(&self, n: &str) -> bool {
        self.vars.iter().any(|(v, _)| v == n)
    }

    fn var_ty(&self, n: &str) -> Ty {
        self.vars.iter().find(|(v, _)| v == n).unwrap().1.clone()
    }

    fn is_const(&self, e: &Expr, env: &Env) -> bool {
        !e.any(&|x| match x {
            Expr::Prime(_) | Expr::At | Expr::Un(UOp::Unchanged | UOp::Enabled, _) => true,
            Expr::Ident(n) => self.is_var(n) || env.locals.contains_key(n),
            _ => false,
        })
    }

    fn try_const(&self, e: &Expr, env: &Env) -> Option<Value> {
        if self.is_const(e, env) {
            self.ce.eval(e, &HashMap::new()).ok()
        } else {
            None
        }
    }

    // ---------------------------------------------------------------- Sets (bitmasks and SSet)

    /// 0-based position of the constant index `i` into a tuple of `n` elements
    fn tuple_index(&self, i: &Expr, env: &Env, n: usize) -> R<usize> {
        match self.try_const(i, env) {
            Some(Value::Int(k)) if k >= 1 && k as u64 <= n as u64 => Ok(k as usize - 1),
            Some(Value::Int(k)) => Err(format!("tuple index {k} is outside 1..{n}")),
            _ => Err(format!("a tuple can only be indexed by a constant integer (got {})", short(i))),
        }
    }

    /// Rewrites the steps of an EXCEPT path that index into a tuple (`![k][1]`) as steps into the
    /// field the element is stored in
    fn resolve_path(&self, t: &Ty, path: &[Path], env: &Env) -> R<Vec<Path>> {
        let mut cur = Some(t.clone());
        let mut out = vec![];
        for p in path {
            let step = match (p, &cur) {
                (Path::Idx(i), Some(Ty::Rec(fs))) if is_tuple_fields(fs) => Path::Field(tuple_field(self.tuple_index(i, env, fs.len())?)),
                _ => p.clone(),
            };
            cur = match &cur {
                Some(c) => Self::path_type(c, std::slice::from_ref(&step)),
                None => None,
            };
            out.push(step);
        }
        Ok(out)
    }

    /// Type at the end of an EXCEPT path
    fn path_type(t: &Ty, path: &[Path]) -> Option<Ty> {
        let mut cur = t.clone();
        for p in path {
            cur = match (p, &cur) {
                (Path::Field(k), _) if k.starts_with('@') => continue,
                (Path::Idx(_), Ty::Fun(_, c)) => c.as_ref().clone(),
                (Path::Field(k), Ty::Rec(fs)) => match &fs.iter().find(|(n, _)| n == k)?.1 {
                    Ty::Opt(i) => i.as_ref().clone(),
                    t => t.clone(),
                },
                _ => return None,
            };
        }
        Some(cur)
    }

    /// `t` with the type at the end of the EXCEPT path replaced by `new`
    fn set_path_type(t: &Ty, path: &[Path], new: &Ty) -> Ty {
        let Some((p, rest)) = path.split_first() else { return new.clone() };
        match (p, t) {
            (Path::Field(k), _) if k.starts_with('@') => Self::set_path_type(t, rest, new),
            (Path::Idx(_), Ty::Fun(d, c)) => Ty::Fun(d.clone(), Self::set_path_type(c, rest, new).into()),
            (Path::Field(k), Ty::Rec(fs)) => Ty::Rec(
                fs.iter()
                    .map(|(n, ft)| {
                        if n != k {
                            return (n.clone(), ft.clone());
                        }
                        let nt = match ft {
                            Ty::Opt(i) => Ty::Opt(Self::set_path_type(i, rest, new).into()),
                            ft => Self::set_path_type(ft, rest, new),
                        };
                        (n.clone(), nt)
                    })
                    .collect(),
            ),
            _ => t.clone(),
        }
    }

    fn elem_of(st: &Ty) -> Ty {
        match st {
            Ty::Set(e) => e.as_ref().clone(),
            _ => unreachable!(),
        }
    }

    fn s_empty(&mut self, st: &Ty) -> R<String> {
        self.ty_id(st)?;
        Ok(if is_sparse(st) { format!("{}::new()", st.repr().replace('<', "::<")) } else { "0u128".into() })
    }

    /// Statement adding element x (in the element type's representation) to acc
    fn s_add(&mut self, acc: &str, x: &str, st: &Ty) -> R<String> {
        let eid = self.ty_id(&Self::elem_of(st))?;
        Ok(if is_sparse(st) { format!("{acc}.insert({x});") } else { format!("{acc} |= bit_{eid}({x});") })
    }

    fn s_iter(&mut self, c: &str, st: &Ty) -> R<String> {
        let eid = self.ty_id(&Self::elem_of(st))?;
        Ok(if is_sparse(st) { format!("({c}).iter()") } else { format!("bits({c}).map(dec_{eid})") })
    }

    fn s_card(&mut self, c: &str, st: &Ty) -> String {
        if is_sparse(st) {
            // `len` is a field (u8), not a method
            format!("(({c}).len as i64)")
        } else {
            format!("(({c}).count_ones() as i64)")
        }
    }

    /// Whether x (of type xt) is a member of set c (of type st)
    fn s_has(&mut self, c: &str, st: &Ty, x: &str, xt: &Ty) -> R<String> {
        let et = Self::elem_of(st);
        match self.tuple_cmp(xt, &et)? {
            Cmp::Normal => {}
            Cmp::Unequal => return Ok("false".into()),
            // TLC compares only against the elements present, so an empty set is no error
            Cmp::Fails(m) => {
                let empty = if is_sparse(st) { format!("(({c}).len == 0)") } else { format!("({c} == 0)") };
                return Ok(format!("(if {empty} {{ false }} else {{ {} }})", eval_error_bool(&m)));
            }
        }
        if matches!(&et, Ty::Enum(v) if v.is_empty()) {
            return Ok("false".into());
        }
        if narrows(xt, &et) {
            // x may hold a model value stored as an integer-or-model-value: compare in the joined
            // type rather than convert x (which fails at run time on an integer)
            let jst = Ty::Set(join(xt, &et)?.into());
            let cc = self.coerce(c.to_string(), st, &jst)?;
            let v = self.fresh("s");
            let inner = self.s_has(&v, &jst, x, xt)?;
            return Ok(format!("{{ let {v} = {cc}; {inner} }}"));
        }
        if is_sparse(st) {
            let Ok(xc) = self.coerce_soft(x.to_string(), xt, &et) else { return Ok("false".into()) };
            return Ok(format!("({c}).contains(&{xc})"));
        }
        let widens = join(xt, &et).ok().as_ref() == Some(&et);
        if !xt.is_scalar() || !(xt.kind_eq(&et) || widens || matches!((xt, &et), (Ty::Rec(_), Ty::Rec(_)))) {
            return Ok("false".into());
        }
        let eid = self.ty_id(&et)?;
        let Ok(xc) = self.coerce_soft(x.to_string(), xt, &et) else { return Ok("false".into()) };
        Ok(format!("{{ let __i = enc_{eid}({xc}); __i != u64::MAX && ({c} >> __i) & 1 == 1 }}"))
    }

    /// Type coercion that returns Err when the value might not fit the target type (e.g. a field
    /// the target requires is absent)
    fn coerce_soft(&mut self, code: String, from: &Ty, to: &Ty) -> R<String> {
        if let (Ty::Rec(a), Ty::Rec(b)) = (from, to) {
            // It does not fit if `from` has a field that `to` lacks
            if a.iter().any(|(n, _)| !b.iter().any(|(m, _)| m == n)) {
                return Err("record fields do not fit".into());
            }
        }
        if narrows(from, to) {
            return Err("an integer does not fit a model value".into());
        }
        self.coerce(code, from, to)
    }

    fn s_bin(&mut self, op: BOp, a: &str, b: &str, st: &Ty) -> String {
        if is_sparse(st) {
            match op {
                BOp::Cup => format!("({a}).union({b})"),
                BOp::Cap => format!("({a}).inter({b})"),
                _ => format!("({a}).minus({b})"),
            }
        } else {
            match op {
                BOp::Cup => format!("({a} | {b})"),
                BOp::Cap => format!("({a} & {b})"),
                _ => format!("({a} & !{b})"),
            }
        }
    }

    /// Default value of a type (used for omitted fields and unused SSet slots)
    fn default_code(t: &Ty) -> String {
        match t {
            Ty::Bool => "false".into(),
            Ty::Int(..) | Ty::IntAtom(..) => "0i64".into(),
            Ty::Enum(_) => "0u16".into(),
            Ty::Rec(fs) => format!("({})", fs.iter().map(|(_, t)| Self::default_code(t) + ",").collect::<String>()),
            Ty::Opt(t) => format!("(false, {})", Self::default_code(t)),
            Ty::Fun(d, c) => format!("[{}; {}]", Self::default_code(c), d.size().unwrap_or(0)),
            Ty::Set(_) if is_sparse(t) => format!("{}::new()", t.repr().replace('<', "::<")),
            Ty::Set(_) => "0u128".into(),
        }
    }

    // ---------------------------------------------------------------- Value literals

    fn lit(&mut self, v: &Value, t: &Ty) -> R<String> {
        Ok(match (v, t) {
            (Value::Bool(b), _) => b.to_string(),
            (Value::Int(i), _) => format!("{i}i64"),
            (Value::Atom(a), Ty::IntAtom(..)) => {
                self.check_model_values(&[*a])?;
                format!("(i64::MIN + {a}i64)")
            }
            (Value::Atom(a), _) => format!("{a}u16"),
            (Value::Tuple(xs), Ty::Rec(fs)) if is_tuple_fields(fs) && xs.len() == fs.len() => {
                let mut s = String::from("(");
                for (x, (_, ft)) in xs.iter().zip(fs) {
                    s += &self.lit(x, ft)?;
                    s += ",";
                }
                s + ")"
            }
            (Value::Rec(m), Ty::Rec(fs)) if !is_tuple_fields(fs) => {
                let mut s = String::from("(");
                for (k, ft) in fs {
                    s += &match (ft, m.get(k)) {
                        (Ty::Opt(i), Some(v)) => format!("(true, {})", self.lit(v, i)?),
                        (Ty::Opt(_), None) => Self::default_code(ft),
                        (ft, Some(v)) => self.lit(v, ft)?,
                        (_, None) => return Err("record field mismatch".into()),
                    };
                    s += ",";
                }
                s + ")"
            }
            (Value::Set(xs), Ty::Set(e)) if is_sparse(t) => {
                let mut c = self.s_empty(t)?;
                for x in xs {
                    c = format!("{c}.with({})", self.lit(x, e)?);
                }
                c
            }
            (Value::Set(xs), Ty::Set(e)) => {
                self.ty_id(t)?;
                let mut m: u128 = 0;
                for x in xs {
                    m |= 1u128 << e.enc(x).ok_or("set element outside its type")?;
                }
                format!("{m}u128")
            }
            (Value::Fun(m), Ty::Fun(d, c)) => {
                self.ty_id(t)?;
                let mut s = String::from("[");
                for k in d.enumerate() {
                    s += &self.lit(m.get(&k).ok_or("function domain mismatch")?, c)?;
                    s += ",";
                }
                s + "]"
            }
            _ => return Err(format!("cannot write {v:?} as {t:?}")),
        })
    }

    /// Writes the value using the expected type's layout if given, otherwise a type derived from
    /// the value
    fn lit_auto(&mut self, v: &Value, want: Option<&Ty>) -> R<(String, Ty)> {
        if let Some(w) = want {
            if w.conforms(v) {
                return Ok((self.lit(v, w)?, w.clone()));
            }
        }
        let t = ty_of_value(v)?;
        Ok((self.lit(v, &t)?, t))
    }

    // ---------------------------------------------------------------- Type coercion

    fn trivial(from: &Ty, to: &Ty) -> bool {
        match (from, to) {
            (Ty::Set(_), Ty::Set(_)) => from == to,
            (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) => d1 == d2 && Self::trivial(c1, c2),
            (Ty::Rec(a), Ty::Rec(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.0 == y.0 && Self::trivial(&x.1, &y.1))
            }
            (Ty::Opt(a), Ty::Opt(b)) => Self::trivial(a, b),
            (Ty::Opt(_), _) | (_, Ty::Opt(_)) => false,
            _ => true,
        }
    }

    fn coerce(&mut self, code: String, from: &Ty, to: &Ty) -> R<String> {
        if let (Some(a), Some(b)) = (tuple_elems(from), tuple_elems(to)) {
            if a.len() != b.len() {
                return Err(format!(
                    "tuples of different lengths ({} and {}); sequences are not supported yet",
                    a.len(),
                    b.len()
                ));
            }
        }
        if from == to || (from.kind_eq(to) && Self::trivial(from, to)) {
            return Ok(code);
        }
        // The empty type (e.g. the element type of {}) coerces to any type
        if let (Ty::Set(e), Ty::Set(_)) = (from, to) {
            if matches!(e.as_ref(), Ty::Enum(v) if v.is_empty()) {
                return self.s_empty(to);
            }
        }
        if matches!(from, Ty::Enum(v) if v.is_empty()) && !matches!(to, Ty::Enum(_)) {
            return Ok(format!("{{ let __u: {} = unreachable!(); __u }}", to.repr()));
        }
        match (from, to) {
            (Ty::Set(a), Ty::Set(b)) if !is_sparse(from) && !is_sparse(to) && a.kind_eq(b) && Self::trivial(a, b) => {
                let (a, b) = (self.ty_id(from)?, self.ty_id(to)?);
                self.convs.insert((a, b));
                Ok(format!("conv_{a}_{b}({code})"))
            }
            (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) if d1 == d2 => {
                let f = self.fresh("f");
                let o = self.fresh("o");
                let inner = self.coerce(format!("{f}[__i]"), c1, c2)?;
                // Annotate the type explicitly: context does not always determine from_fn's type
                Ok(format!(
                    "{{ let {f} = {code}; let {o}: {} = std::array::from_fn(|__i| {inner}); {o} }}",
                    to.repr()
                ))
            }
            (Ty::Rec(a), Ty::Rec(b)) => {
                // Per field of b: coerce from a if present, else leave it absent (if optional)
                let r = self.fresh("r");
                let mut s = format!("{{ let {r} = {code}; (");
                for (n, bt) in b {
                    let part = match a.iter().position(|(m, _)| m == n) {
                        Some(i) => {
                            let at = &a[i].1;
                            match (at, bt) {
                                (Ty::Opt(x), Ty::Opt(y)) => {
                                    let o = self.fresh("o");
                                    let inner = self.coerce(format!("{o}.1"), x, y)?;
                                    format!("{{ let {o} = {r}.{i}; if {o}.0 {{ (true, {inner}) }} else {{ {} }} }}", Self::default_code(bt))
                                }
                                (x, Ty::Opt(y)) => format!("(true, {})", self.coerce(format!("{r}.{i}"), x, y)?),
                                (Ty::Opt(x), y) => {
                                    let o = self.fresh("o");
                                    let inner = self.coerce(format!("{o}.1"), x, y)?;
                                    format!("{{ let {o} = {r}.{i}; if !{o}.0 {{ type_error(\"record without field\", \"{n}\") }} {inner} }}")
                                }
                                (x, y) => self.coerce(format!("{r}.{i}"), x, y)?,
                            }
                        }
                        None => match bt {
                            Ty::Opt(_) => Self::default_code(bt),
                            _ => return Err(format!("record has no field `{n}`")),
                        },
                    };
                    s += &part;
                    s += ",";
                }
                Ok(s + ") }")
            }
            (Ty::Set(_), Ty::Set(_)) => {
                // Coerce element by element and rebuild the set
                let et = Self::elem_of(from);
                let tt = Self::elem_of(to);
                let x = self.fresh("x");
                let acc = self.fresh("acc");
                let it = self.s_iter(&code, from)?;
                let xc = self.coerce(x.clone(), &et, &tt)?;
                let add = self.s_add(&acc, &xc, to)?;
                let empty = self.s_empty(to)?;
                Ok(format!("{{ let mut {acc} = {empty}; for {x} in {it} {{ {add} }} {acc} }}"))
            }
            (Ty::Enum(x), Ty::Set(_) | Ty::Fun(..)) if x.is_empty() => Err("empty enum".into()),
            (Ty::Enum(x), Ty::IntAtom(..)) => {
                self.check_model_values(x)?;
                Ok(format!("(i64::MIN + ({code}) as i64)"))
            }
            (Ty::IntAtom(..), Ty::Enum(_)) => {
                let a = self.fresh("a");
                Ok(format!(
                    "{{ let {a} = {code}; if {a} >= i64::MIN + 65536 {{ eval_error(format!(\"the integer {{}} is used where a model value is expected\", {a})) }} ({a} - i64::MIN) as u16 }}"
                ))
            }
            _ if from.kind_eq(to) => Ok(code),
            _ => Err(format!("type mismatch: cannot use {from:?} as {to:?}")),
        }
    }

    pub fn gen_as(&mut self, e: &Expr, env: &Env, t: &Ty) -> R<String> {
        let (c, got) = self.gen(e, env, Some(t))?;
        self.coerce(c, &got, t)
    }

    /// Uses the expected type if it subsumes the join, otherwise the join itself
    fn layout(want: Option<&Ty>, j: Ty) -> Ty {
        if let Some(w) = want {
            if join(w, &j).ok().as_ref() == Some(w) {
                return w.clone();
            }
        }
        j
    }

    // ---------------------------------------------------------------- Expressions

    pub fn gen(&mut self, e: &Expr, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        self.gen_inner(e, env, want)
    }

    fn gen_inner(&mut self, e: &Expr, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        use Expr::*;
        let e = e.strip();
        if let Some(v) = self.try_const(e, env) {
            return self.lit_auto(&v, want);
        }
        Ok(match e {
            Ident(n) => {
                if let Some((c, t)) = env.locals.get(n) {
                    (c.clone(), t.clone())
                } else if self.is_var(n) {
                    if env.init {
                        env.primed.get(n).cloned().ok_or(format!("Init reads `{n}` before assigning it"))?
                    } else {
                        (format!("s.v_{n}"), self.var_ty(n))
                    }
                } else {
                    return Err(format!("unknown identifier `{n}` (missing CONSTANT in cfg?)"));
                }
            }
            At => env.locals.get("@").cloned().ok_or("`@` outside EXCEPT")?,
            Prime(x) => match x.strip() {
                Ident(n) if self.is_var(n) => match env.primed.get(n) {
                    Some(x) => x.clone(),
                    // As in TLC, fail only on evaluation (harmless if the branch is never reached)
                    None => {
                        let t = self.var_ty(n);
                        (format!("{{ let __v: {} = eval_error(\"{n}' is read before the action determines it\".into()); __v }}", t.repr()), t)
                    }
                },
                x => {
                    let primed = self.prime_vars(x);
                    return self.gen(&primed, env, want);
                }
            },
            Call(f, args) => match (f.as_str(), args.as_slice()) {
                ("Cardinality", [s]) => {
                    let (c, t) = self.gen(s, env, None)?;
                    let Ty::Set(el) = &t else { return Err("Cardinality of a non-set".into()) };
                    let hi = if is_sparse(&t) { BIG } else { el.size().unwrap_or(0) as i64 };
                    (self.s_card(&c, &t), Ty::Int(0, hi))
                }
                ("\\X", _) => {
                    return Err(format!(
                        "the cartesian product \\X over state-dependent sets is only supported on the right of \\in: {}",
                        short(e)
                    ))
                }
                (f, _) if SEQ_OPS.contains(&f) => return Err(seq_op_error(f)),
                _ => return Err(format!("unknown operator `{f}`")),
            },
            Un(UOp::Not, x) => (format!("(!{})", self.gen_as(x, env, &Ty::Bool)?), Ty::Bool),
            Un(UOp::Neg, x) => {
                let (c, t) = self.gen(x, env, None)?;
                let Ty::Int(lo, hi) = t else { return Err("negation of a non-integer".into()) };
                (format!("(-{c})"), Ty::Int(-hi, -lo))
            }
            Un(UOp::Domain, f) => {
                let (_, ft) = self.gen(f, env, None)?;
                if let Some(el) = tuple_elems(&ft) {
                    // A tuple of n elements is a function over 1..n
                    let n = el.len();
                    let st = Ty::Set(Ty::Int(1, n as i64).into());
                    self.ty_id(&st)?;
                    let mask: u128 = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
                    return Ok((format!("{mask}u128"), st));
                }
                let Ty::Fun(d, _) = ft else { return Err("DOMAIN of a non-function".into()) };
                let st = Ty::Set(d.clone());
                self.ty_id(&st)?;
                let n = d.size().unwrap();
                let mask: u128 = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
                (format!("{mask}u128"), st)
            }
            Un(UOp::Unchanged, x) => {
                let mut names = vec![];
                Self::unchanged_vars(x, &mut names)?;
                let mut parts = vec![];
                for v in names {
                    let (p, _) = env.primed.get(&v).ok_or(format!("UNCHANGED {v} before {v}' is decided"))?;
                    parts.push(format!("{p} == s.v_{v}"));
                }
                (format!("({})", if parts.is_empty() { "true".into() } else { parts.join(" && ") }), Ty::Bool)
            }
            Un(op, _) => return Err(format!("{op:?} is not supported here")),
            Bin(op, a, b) => self.gen_bin(*op, a, b, env, want)?,
            And(xs) | Or(xs) => {
                let sep = if matches!(e, And(_)) { " && " } else { " || " };
                let parts: Vec<String> = xs.iter().map(|x| self.gen_as(x, env, &Ty::Bool)).collect::<R<_>>()?;
                (format!("({})", parts.join(sep)), Ty::Bool)
            }
            If(c, a, b) => {
                let c = self.gen_as(c, env, &Ty::Bool)?;
                let (ac, at) = self.gen(a, env, want)?;
                let (bc, bt) = self.gen(b, env, want.or(Some(&at)))?;
                let t = Self::layout(want, join(&at, &bt)?);
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                (format!("(if {c} {{ {ac} }} else {{ {bc} }})"), t)
            }
            Case(arms, other) => {
                let mut parts = vec![];
                let mut t = Ty::Enum(vec![]);
                for (p, v) in arms {
                    let pc = self.gen_as(p, env, &Ty::Bool)?;
                    let (vc, vt) = self.gen(v, env, want)?;
                    t = join(&t, &vt)?;
                    parts.push((pc, vc, vt));
                }
                let oth = match other {
                    Some(o) => {
                        let (oc, ot) = self.gen(o, env, want)?;
                        t = join(&t, &ot)?;
                        Some((oc, ot))
                    }
                    None => None,
                };
                let t = Self::layout(want, t);
                let mut s = String::from("(");
                for (pc, vc, vt) in parts {
                    let vc = self.coerce(vc, &vt, &t)?;
                    write!(s, "if {pc} {{ {vc} }} else ").unwrap();
                }
                match oth {
                    Some((oc, ot)) => s += &format!("{{ {} }})", self.coerce(oc, &ot, &t)?),
                    None => s += "{ eval_error(\"Attempted to evaluate a CASE with no conditions true.\".into()) })",
                }
                (s, t)
            }
            Quant(ex, bs, body) => {
                if bs.iter().any(|(_, s)| self.try_const(s, env).is_some_and(|v| v.as_set().is_ok_and(|x| x.is_empty()))) {
                    return Ok(((!*ex).to_string(), Ty::Bool));
                }
                let mut env2 = env.clone();
                let mut heads = vec![];
                for (x, s) in bs {
                    let (it, et, ix) = self.iter_of_indexed(s, &env2)?;
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    heads.push((it, lx));
                }
                let mut code = self.gen_as(body, &env2, &Ty::Bool)?;
                let m = if *ex { "any" } else { "all" };
                for (it, lx) in heads.into_iter().rev() {
                    code = format!("({it}).{m}(|{lx}| {code})");
                }
                (code, Ty::Bool)
            }
            SetLit(xs) => {
                let mut parts = vec![];
                let mut et = Ty::Enum(vec![]);
                let we = match want {
                    Some(Ty::Set(w)) => Some(w.as_ref().clone()),
                    _ => None,
                };
                let mut tys = vec![];
                for x in xs {
                    let (c, t) = self.gen(x, env, we.as_ref())?;
                    et = join(&et, &t)?;
                    parts.push(c);
                    tys.push(t);
                }
                let st = Self::layout(want, Ty::Set(et.into()));
                let el = Self::elem_of(&st);
                let acc = self.fresh("acc");
                let mut body = format!("let mut {acc} = {}; ", self.s_empty(&st)?);
                for (c, t) in parts.iter().zip(&tys) {
                    let c = self.coerce(c.clone(), t, &el)?;
                    body += &self.s_add(&acc, &c, &st)?;
                }
                (format!("{{ {body} {acc} }}"), st)
            }
            SetFilter(x, s, p) => {
                let (it, et, ix) = self.iter_of_indexed(s, env)?;
                let st = Ty::Set(et.clone().into());
                let mut env2 = env.clone();
                let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                let pc = self.gen_as(p, &env2, &Ty::Bool)?;
                let acc = self.fresh("acc");
                let empty = self.s_empty(&st)?;
                let elem = env2.locals[x].0.clone();
                let add = self.s_add(&acc, &elem, &st)?;
                (format!("{{ let mut {acc} = {empty}; for {lx} in {it} {{ if {pc} {{ {add} }} }} {acc} }}"), st)
            }
            SetMap(f, bs) => {
                let mut env2 = env.clone();
                let mut heads = vec![];
                for (x, s) in bs {
                    let (it, et, ix) = self.iter_of_indexed(s, &env2)?;
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    heads.push((it, lx));
                }
                let we = match want {
                    Some(Ty::Set(w)) => Some(w.as_ref().clone()),
                    _ => None,
                };
                let (fc, ft) = self.gen(f, &env2, we.as_ref())?;
                let st = Self::layout(want, Ty::Set(ft.clone().into()));
                let el = Self::elem_of(&st);
                let fc = self.coerce(fc, &ft, &el)?;
                let acc = self.fresh("acc");
                let mut body = self.s_add(&acc, &fc, &st)?;
                for (it, lx) in heads.into_iter().rev() {
                    body = format!("for {lx} in {it} {{ {body} }}");
                }
                let empty = self.s_empty(&st)?;
                (format!("{{ let mut {acc} = {empty}; {body} {acc} }}"), st)
            }
            FunCons(x, s, body) => {
                let dv = self.ce.eval(s, &HashMap::new()).map_err(|m| format!("function domain must be constant: {m}"))?;
                let dt = elem_ty_of_domain(dv.as_set()?)?;
                let did = self.ty_id(&dt)?;
                let wc = match want {
                    Some(Ty::Fun(wd, wc)) if **wd == dt => Some(wc.as_ref().clone()),
                    _ => None,
                };
                let mut env2 = env.clone();
                let lx = rid(x);
                env2.locals.insert(x.clone(), (lx.clone(), dt.clone()));
                let (bc, bt) = self.gen(body, &env2, wc.as_ref())?;
                let ct = match &wc {
                    Some(w) if join(w, &bt).ok().as_ref() == Some(w) => w.clone(),
                    _ => bt.clone(),
                };
                let bc = self.coerce(bc, &bt, &ct)?;
                let ft = Ty::Fun(dt.clone().into(), ct.clone().into());
                self.ty_id(&ft)?;
                (
                    format!(
                        "{{ let __f: {} = std::array::from_fn(|__i| {{ let {lx}: {} = dec_{did}(__i as u64); {bc} }}); __f }}",
                        ft.repr(),
                        dt.repr()
                    ),
                    ft,
                )
            }
            RecLit(fs) => {
                let mut fs: Vec<(String, Expr)> = fs.clone();
                fs.sort_by(|a, b| a.0.cmp(&b.0));
                let wf: Option<Vec<(String, Ty)>> = match want {
                    Some(Ty::Rec(w)) => Some(w.clone()),
                    _ => None,
                };
                let mut code = String::from("(");
                let mut tys = vec![];
                for (k, v) in &fs {
                    let w = wf.as_ref().and_then(|w| w.iter().find(|(n, _)| n == k).map(|x| match &x.1 {
                        Ty::Opt(i) => i.as_ref().clone(),
                        t => t.clone(),
                    }));
                    let (c, t) = self.gen(v, env, w.as_ref())?;
                    // Adopt the requested type only when the value's range fits within it (widening
                    // only, so always sound). Never narrow: the requested type is not necessarily
                    // the declared one and may come from a record built in a sibling branch (an
                    // `epoch |-> 0` branch once narrowed it and dropped the `epoch |-> 1` states)
                    let t = match (&w, &t) {
                        (Some(Ty::Int(wl, wh)), Ty::Int(l, h)) if wl <= l && h <= wh => w.clone().unwrap(),
                        _ => t,
                    };
                    code += &c;
                    code += ",";
                    tys.push((k.clone(), t));
                }
                (code + ")", Ty::Rec(tys))
            }
            App(f, x) => {
                let (fc, ft) = self.gen(f, env, None)?;
                if let Ty::Rec(fs) = &ft {
                    if is_tuple_fields(fs) {
                        let k = self.tuple_index(x, env, fs.len())?;
                        return Ok((format!("({fc}).{k}"), fs[k].1.clone()));
                    }
                }
                let Ty::Fun(d, c) = ft else { return Err(format!("applying a non-function: {f:?}")) };
                // If the argument is a bound variable with a known index, use it without conversion
                if let Ident(n) = x.strip() {
                    if let Some((t, iv)) = env.idx.get(n) {
                        if *t == *d {
                            return Ok((format!("{fc}[{iv} as usize]"), *c));
                        }
                    }
                }
                let did = self.ty_id(&d)?;
                let xc = self.gen_as(x, env, &d)?;
                (format!("{fc}[idx_{did}({xc})]"), *c)
            }
            Field(r, k) => {
                let (rc, rt) = self.gen(r, env, None)?;
                let Ty::Rec(fs) = rt else { return Err(format!("field .{k} of a non-record")) };
                let i = fs.iter().position(|(n, _)| n == k).ok_or(format!("no field {k}"))?;
                match &fs[i].1 {
                    Ty::Opt(t) => {
                        let o = self.fresh("o");
                        (
                            format!("{{ let {o} = ({rc}).{i}; if !{o}.0 {{ eval_error(\"Attempted to access a nonexistent field `{k}` of a record\".into()) }} {o}.1 }}"),
                            t.as_ref().clone(),
                        )
                    }
                    t => (format!("({rc}).{i}"), t.clone()),
                }
            }
            Except(f, ups) => {
                let (fc, ft0) = self.gen(f, env, want)?;
                let ups: Vec<(Vec<Path>, Expr)> =
                    ups.iter().map(|(p, v)| Ok((self.resolve_path(&ft0, p, env)?, v.clone()))).collect::<R<_>>()?;
                let ups = &ups;
                // Widen to include the types of the written values (when writing a wider value into
                // a narrower function; type inference relies on this too)
                let mut ft = ft0.clone();
                for (path, val) in ups {
                    let Some(cur) = Self::path_type(&ft, path) else { continue };
                    let mut env2 = env.clone();
                    env2.locals.insert("@".into(), ("__at".into(), cur.clone()));
                    if let Some(Path::Field(n)) = path.iter().find(|p| matches!(p, Path::Field(k) if k.starts_with('@'))) {
                        env2.locals.insert(n.clone(), ("__at".into(), cur.clone()));
                    }
                    if let Ok((_, vt)) = self.gen(val, &env2, Some(&cur)) {
                        if let Ok(j) = join(&cur, &vt) {
                            if j != cur {
                                ft = Self::set_path_type(&ft, path, &j);
                            }
                        }
                    }
                }
                let fc = if ft != ft0 { self.coerce(fc, &ft0, &ft)? } else { fc };
                let t = self.fresh("t");
                let mut s = format!("{{ let mut {t} = {fc}; ");
                for (path, val) in ups {
                    let mut place = t.clone();
                    let mut cur = ft.clone();
                    let mut conds = vec![];
                    let mut at_name = None;
                    for p in path {
                        match (p, &cur) {
                            // Name of this EXCEPT's @, attached during expansion
                            (Path::Field(k), _) if k.starts_with('@') => at_name = Some(k.clone()),
                            (Path::Idx(i), Ty::Fun(d, c)) => {
                                // A bound variable with a known index needs neither conversion nor
                                // a bounds check
                                let known = match i.strip() {
                                    Expr::Ident(n) => env.idx.get(n).filter(|(t, _)| *t == **d).map(|(_, v)| v.clone()),
                                    _ => None,
                                };
                                match known {
                                    Some(iv) => place = format!("{place}[{iv} as usize]"),
                                    None => {
                                        let did = self.ty_id(d)?;
                                        let ic = self.gen_as(i, env, d)?;
                                        let iv = self.fresh("i");
                                        // An index outside the domain is a no-op (as in TLC)
                                        write!(s, "let {iv} = enc_{did}({ic}); ").unwrap();
                                        conds.push(format!("{iv} != u64::MAX"));
                                        place = format!("{place}[{iv} as usize]");
                                    }
                                }
                                cur = c.as_ref().clone();
                            }
                            (Path::Field(k), Ty::Rec(fs)) => {
                                let i = fs.iter().position(|(n, _)| n == k).ok_or(format!("no field {k}"))?;
                                match &fs[i].1 {
                                    // EXCEPT on an absent field is a no-op
                                    Ty::Opt(t) => {
                                        conds.push(format!("{place}.{i}.0"));
                                        place = format!("{place}.{i}.1");
                                        cur = t.as_ref().clone();
                                    }
                                    t => {
                                        place = format!("{place}.{i}");
                                        cur = t.clone();
                                    }
                                }
                            }
                            _ => return Err("EXCEPT path does not match the value's type".into()),
                        }
                    }
                    let at = self.fresh("at");
                    let mut env2 = env.clone();
                    env2.locals.insert("@".into(), (at.clone(), cur.clone()));
                    if let Some(n) = at_name {
                        env2.locals.insert(n, (at.clone(), cur.clone()));
                    }
                    let vc = self.gen_as(val, &env2, &cur)?;
                    let read_at = if vc.contains(&at) { format!("let {at} = {place}; ") } else { String::new() };
                    if conds.is_empty() {
                        write!(s, "{read_at}{place} = {vc}; ").unwrap();
                    } else {
                        write!(s, "if {} {{ {read_at}{place} = {vc}; }} ", conds.join(" && ")).unwrap();
                    }
                }
                (s + &t + " }", ft)
            }
            Tuple(xs) => {
                // Tuples are represented as records with fields #01, #02, ...
                let mut code = String::from("(");
                let mut tys = vec![];
                for (i, x) in xs.iter().enumerate() {
                    let w = match want {
                        Some(Ty::Rec(fs)) => fs.get(i).map(|f| f.1.clone()),
                        _ => None,
                    };
                    let (c, t) = self.gen(x, env, w.as_ref())?;
                    code += &c;
                    code += ",";
                    tys.push((format!("#{:02}", i + 1), t));
                }
                (code + ")", Ty::Rec(tys))
            }
            Choose(..) => return Err("CHOOSE over state-dependent sets is not supported yet".into()),
            FunSet(..) | RecSet(..) => {
                return Err("this set is only supported on the right of \\in (or must be constant)".into())
            }
            Let(..) | Label(..) => unreachable!(),
            BoxAction(..) | Fair(..) => return Err("temporal formula in a state expression".into()),
            Num(_) | Str(_) | Bool(_) => unreachable!("constants are folded"),
        })
    }

    fn gen_bin(&mut self, op: BOp, a: &Expr, b: &Expr, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        use BOp::*;
        Ok(match op {
            Implies | Equiv => {
                let ac = self.gen_as(a, env, &Ty::Bool)?;
                let bc = self.gen_as(b, env, &Ty::Bool)?;
                let s = if op == Implies { format!("(!{ac} || {bc})") } else { format!("({ac} == {bc})") };
                (s, Ty::Bool)
            }
            Eq | Neq => {
                let (ac, at) = self.gen(a, env, None)?;
                let (bc, bt) = self.gen(b, env, Some(&at))?;
                // Still evaluate both sides, which may stop with an error as in TLC
                match self.tuple_cmp(&at, &bt)? {
                    Cmp::Normal => {}
                    Cmp::Unequal => return Ok((format!("{{ let _ = {ac}; let _ = {bc}; {} }}", op == Neq), Ty::Bool)),
                    Cmp::Fails(m) => return Ok((format!("{{ let _ = {ac}; let _ = {bc}; {} }}", eval_error_bool(&m)), Ty::Bool)),
                }
                let t = join(&at, &bt)?;
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                (format!("({ac} {} {bc})", if op == Eq { "==" } else { "!=" }), Ty::Bool)
            }
            Lt | Le | Gt | Ge => {
                let (ac, _) = self.gen_int(a, env)?;
                let (bc, _) = self.gen_int(b, env)?;
                let o = match op {
                    Lt => "<",
                    Le => "<=",
                    Gt => ">",
                    _ => ">=",
                };
                (format!("({ac} {o} {bc})"), Ty::Bool)
            }
            In | NotIn if matches!(b.strip(), Expr::Un(UOp::Domain, _)) && matches!(a.strip(), Expr::Str(_)) => {
                // "f" \in DOMAIN r: whether the record has that field
                let (Expr::Str(k), Expr::Un(_, r)) = (a.strip(), b.strip()) else { unreachable!() };
                let (rc, rt) = self.gen(r, env, None)?;
                let has = match &rt {
                    Ty::Rec(fs) => match fs.iter().position(|(n, _)| n == k) {
                        Some(i) if matches!(fs[i].1, Ty::Opt(_)) => format!("({rc}).{i}.0"),
                        Some(_) => "true".into(),
                        None => "false".into(),
                    },
                    _ => return Err("only `\"field\" \\in DOMAIN record` and DOMAIN of functions are supported".into()),
                };
                (if op == NotIn { format!("!{has}") } else { has }, Ty::Bool)
            }
            In | NotIn => {
                let (xc, xt) = self.gen(a, env, None)?;
                let x = self.fresh("x");
                let m = self.gen_member(&x, &xt, b, env)?;
                let neg = if op == NotIn { "!" } else { "" };
                (format!("{neg}{{ let {x} = {xc}; {m} }}"), Ty::Bool)
            }
            Subseteq => {
                let (ac, at) = self.gen(a, env, None)?;
                let (bc, bt) = self.gen(b, env, Some(&at))?;
                let t = join(&at, &bt)?;
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                if is_sparse(&t) {
                    (format!("({ac}).subseteq(&{bc})"), Ty::Bool)
                } else {
                    (format!("(({ac}) & !({bc}) == 0)"), Ty::Bool)
                }
            }
            Cup | Cap | SetMinus => {
                let (ac, at) = self.gen(a, env, want)?;
                let (bc, bt) = self.gen(b, env, want.or(Some(&at)))?;
                let t = Self::layout(want, join(&at, &bt)?);
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                (self.s_bin(op, &ac, &bc, &t), t)
            }
            LeadsTo => return Err("~> in a state expression".into()),
            Range => return Err("a..b with state-dependent bounds is only supported after \\in or \\E".into()),
            Add | Sub | Mul | Div | Mod => {
                let (ac, (alo, ahi)) = self.gen_int(a, env)?;
                let (bc, (blo, bhi)) = self.gen_int(b, env)?;
                // Compute ranges in i128 and clamp to BIG. Otherwise an operation such as
                // subtracting two unbounded integers (Nat / Int) overflows i64, corrupting the
                // range into a type that admits only a single value
                let clamp = |x: i128| x.clamp(-(BIG as i128), BIG as i128) as i64;
                let (al, ah, bl, bh) = (alo as i128, ahi as i128, blo as i128, bhi as i128);
                let (s, t) = match op {
                    Add => (format!("({ac} + {bc})"), Ty::Int(clamp(al + bl), clamp(ah + bh))),
                    Sub => (format!("({ac} - {bc})"), Ty::Int(clamp(al - bh), clamp(ah - bl))),
                    Mul => {
                        let c = [al * bl, al * bh, ah * bl, ah * bh];
                        (format!("({ac} * {bc})"), Ty::Int(clamp(*c.iter().min().unwrap()), clamp(*c.iter().max().unwrap())))
                    }
                    Div => {
                        let m = alo.abs().max(ahi.abs());
                        (format!("tla_div({ac}, {bc})"), Ty::Int(-m, m))
                    }
                    _ => (format!("tla_mod({ac}, {bc})"), Ty::Int(0, clamp((bh - 1).max(0)))),
                };
                (s, t)
            }
        })
    }

    fn gen_int(&mut self, e: &Expr, env: &Env) -> R<(String, (i64, i64))> {
        let (c, t) = self.gen(e, env, None)?;
        match t {
            Ty::Int(lo, hi) => Ok((c, (lo, hi))),
            t => Err(format!("expected an integer, got {t:?} in {e:?}")),
        }
    }

    /// Iterator expression over a set, and its element type
    fn iter_of(&mut self, s: &Expr, env: &Env) -> R<(String, Ty)> {
        let (it, et, _) = self.iter_of_indexed(s, env)?;
        Ok((it, et))
    }

    /// Iterator and element type. When the set is the element type's full domain, iterates over
    /// indices instead (using them as function arguments avoids converting from atom values)
    fn iter_of_indexed(&mut self, s: &Expr, env: &Env) -> R<(String, Ty, Option<String>)> {
        let s = s.strip();
        if let Some(v) = self.try_const(s, env) {
            let set = v.as_set()?;
            let Ty::Set(et) = ty_of_value(&v)? else { unreachable!() };
            if set.is_empty() {
                return Ok(("std::iter::empty::<u16>()".into(), Ty::Enum(vec![]), None));
            }
            // If this set covers the whole element type, iterate over 0..n and carry the index
            if let Some(n) = et.size() {
                let mut all = et.enumerate();
                all.sort();
                if all.into_iter().collect::<BTreeSet<_>>() == *set {
                    return Ok((format!("(0..{n}u64)"), *et, Some(String::new())));
                }
            }
            let mut parts = vec![];
            for x in set {
                parts.push(self.lit(x, &et)?);
            }
            return Ok((format!("[{}].into_iter()", parts.join(", ")), *et, None));
        }
        if let Expr::Bin(BOp::Range, a, b) = s {
            let (ac, (alo, _)) = self.gen_int(a, env)?;
            let (bc, (_, bhi)) = self.gen_int(b, env)?;
            return Ok((format!("({ac}..={bc})"), Ty::Int(alo, bhi), None));
        }
        let (c, t) = self.gen(s, env, None)?;
        let Ty::Set(et) = &t else { return Err(format!("cannot iterate over {t:?}")) };
        let it = self.s_iter(&c, &t)?;
        Ok((it, et.as_ref().clone(), None))
    }

    /// Binds a variable in the environment, also recording its index when iterating by index
    fn bind_iter(&mut self, env: &mut Env, name: &str, et: &Ty, indexed: bool) -> R<(String, String)> {
        let lx = rid(name);
        if indexed {
            let id = self.ty_id(et)?;
            // The loop variable is an index; decode it via table lookup where the value is needed
            env.locals.insert(name.to_string(), (format!("dec_{id}({lx})"), et.clone()));
            env.idx.insert(name.to_string(), (et.clone(), lx.clone()));
            return Ok((lx.clone(), lx));
        }
        env.locals.insert(name.to_string(), (lx.clone(), et.clone()));
        env.idx.remove(name);
        Ok((lx.clone(), lx))
    }

    /// `x \in S`, where the value of x is already held in the variable named by `x`.
    fn gen_member(&mut self, x: &str, xt: &Ty, s: &Expr, env: &Env) -> R<String> {
        use Expr::*;
        let s = s.strip();
        // TLC stops with an error on a tuple in SUBSET S, [a : S], BOOLEAN, Nat, Int, or a..b, and
        // treats it as a function in [S -> T]; none of these is compiled
        if tuple_elems(xt).is_some() {
            if matches!(s, FunSet(..)) {
                return Err(format!("membership of a tuple in a set of functions is not supported: {}", short(s)));
            }
            if matches!(s, Un(UOp::Subset, _) | RecSet(_) | Bin(BOp::Range, ..))
                || matches!(s, Ident(n) if ["BOOLEAN", "Nat", "Int"].contains(&n.as_str()))
            {
                return Ok(eval_error_bool(&format!("Attempted to check if the tuple {x} is an element of {}", short(s))));
            }
        }
        match s {
            Un(UOp::Subset, t) => {
                let Ty::Set(et) = xt else { return Ok("false".into()) };
                let e = self.fresh("e");
                let inner = self.gen_member(&e, et, t, env)?;
                let it = self.s_iter(x, xt)?;
                return Ok(format!("{it}.all(|{e}| {inner})"));
            }
            FunSet(d, r) => {
                let Ty::Fun(dt, ct) = xt else { return Ok("false".into()) };
                let dv = self.ce.eval(d, &HashMap::new())?;
                let mut dom = dt.enumerate();
                dom.sort();
                if dom.into_iter().collect::<BTreeSet<_>>() != *dv.as_set()? {
                    return Ok("false".into());
                }
                let e = self.fresh("e");
                let inner = self.gen_member(&e, ct, r, env)?;
                return Ok(format!("{x}.iter().all(|&{e}| {inner})"));
            }
            RecSet(fs) => {
                let Ty::Rec(xf) = xt else { return Ok("false".into()) };
                let mut fs = fs.clone();
                fs.sort_by(|a, b| a.0.cmp(&b.0));
                if fs.len() != xf.len() || fs.iter().zip(xf).any(|(a, b)| a.0 != b.0) {
                    return Ok("false".into());
                }
                let mut parts = vec![];
                for (i, ((_, se), (_, ft))) in fs.iter().zip(xf).enumerate() {
                    let e = self.fresh("e");
                    let inner = self.gen_member(&e, ft, se, env)?;
                    parts.push(format!("{{ let {e} = {x}.{i}; {inner} }}"));
                }
                return Ok(format!("({})", parts.join(" && ")));
            }
            // Membership in A \X B is decided element by element, also for constant sets (that
            // avoids enumerating a large product)
            Call(f, parts) if f == "\\X" => {
                let Some(el) = tuple_elems(xt) else {
                    // TLC answers FALSE for a string or model value and stops with an error for
                    // anything else that is not a tuple
                    if matches!(xt, Ty::Enum(_)) {
                        return Ok("false".into());
                    }
                    if seq_like_fun(xt) {
                        return Err(format!("comparing a function over 1..n with a tuple is not supported: {}", short(s)));
                    }
                    return Ok(eval_error_bool(&format!("Attempted to check if a non-tuple value of type {xt:?} is an element of a cartesian product")));
                };
                if el.len() != parts.len() {
                    return Ok("false".into());
                }
                let el: Vec<Ty> = el.into_iter().cloned().collect();
                let mut conj = vec![];
                for (i, (part, et)) in parts.iter().zip(&el).enumerate() {
                    let e = self.fresh("e");
                    let inner = self.gen_member(&e, et, part, env)?;
                    conj.push(format!("{{ let {e} = {x}.{i}; {inner} }}"));
                }
                return Ok(format!("({})", conj.join(" && ")));
            }
            Ident(n) if n == "BOOLEAN" => return Ok(matches!(xt, Ty::Bool).to_string()),
            Ident(n) if n == "Nat" => {
                return Ok(if matches!(xt, Ty::Int(..) | Ty::IntAtom(..)) { format!("({x} >= 0)") } else { "false".into() })
            }
            Ident(n) if n == "Int" => {
                return Ok(match xt {
                    Ty::Int(..) => "true".into(),
                    Ty::IntAtom(..) => format!("({x} >= i64::MIN + 65536)"),
                    _ => "false".into(),
                })
            }
            Bin(BOp::Range, a, b) => {
                let (ac, _) = self.gen_int(a, env)?;
                let (bc, _) = self.gen_int(b, env)?;
                return Ok(format!("({ac} <= {x} && {x} <= {bc})"));
            }
            Bin(op @ (BOp::Cup | BOp::Cap | BOp::SetMinus), a, b) if self.try_const(s, env).is_none() => {
                let l = self.gen_member(x, xt, a, env)?;
                let r = self.gen_member(x, xt, b, env)?;
                return Ok(match op {
                    BOp::Cup => format!("({l} || {r})"),
                    BOp::Cap => format!("({l} && {r})"),
                    _ => format!("({l} && !{r})"),
                });
            }
            SetFilter(y, t, p) if self.try_const(s, env).is_none() => {
                let m = self.gen_member(x, xt, t, env)?;
                let mut env2 = env.clone();
                env2.locals.insert(y.clone(), (x.to_string(), xt.clone()));
                let pc = self.gen_as(p, &env2, &Ty::Bool)?;
                return Ok(format!("({m} && {pc})"));
            }
            _ => {}
        }
        if let Some(v) = self.try_const(s, env) {
            let set = v.as_set()?;
            let mut fits: Vec<&Value> = vec![];
            let mut clash = None;
            for e in set {
                match self.tuple_cmp(xt, &ty_of_value(e)?).map_err(|m| format!("{m}: {}", short(s)))? {
                    Cmp::Normal if xt.conforms(e) => fits.push(e),
                    Cmp::Normal | Cmp::Unequal => {}
                    Cmp::Fails(m) => clash = Some(m),
                }
            }
            if let Some(m) = clash {
                // TLC stops comparing x with an element it cannot compare it with. If other
                // elements might match first, whether it stops depends on its order: reject
                if !fits.is_empty() {
                    return Err(format!("{m}: {}", short(s)));
                }
                return Ok(eval_error_bool(&m));
            }
            if fits.is_empty() {
                return Ok("false".into());
            }
            if fits.len() <= 8 || !xt.is_scalar() {
                let parts: Vec<String> =
                    fits.iter().map(|e| Ok(format!("{x} == {}", self.lit(e, xt)?))).collect::<R<_>>()?;
                return Ok(format!("({})", parts.join(" || ")));
            }
            let Ty::Set(mut et) = ty_of_value(&v)? else { unreachable!() };
            if narrows(xt, &et) {
                et = join(xt, &et)?.into();
            }
            let st = Ty::Set(et.clone());
            let mask = self.lit(&v, &st)?;
            let eid = self.ty_id(&et)?;
            let xc = self.coerce(x.to_string(), xt, &et)?;
            return Ok(format!("{{ let __i = enc_{eid}({xc}); __i != u64::MAX && ({mask} >> __i) & 1 == 1 }}"));
        }
        if let SetLit(xs) = s {
            let mut parts = vec![];
            let mut clash = None;
            let mut comparable = false;
            for e in xs {
                let (c, t) = self.gen(e, env, Some(xt))?;
                match self.tuple_cmp(xt, &t)? {
                    Cmp::Normal => comparable = true,
                    Cmp::Unequal => {
                        parts.push(format!("{{ let _ = {c}; false }}"));
                        continue;
                    }
                    Cmp::Fails(m) => {
                        clash = Some(m);
                        parts.push(format!("{{ let _ = {c}; false }}"));
                        continue;
                    }
                }
                if narrows(&t, xt) {
                    // Compare in the joined type (converting the element could fail at run time)
                    let j = join(xt, &t)?;
                    let xc = self.coerce(x.to_string(), xt, &j)?;
                    let c = self.coerce(c, &t, &j)?;
                    parts.push(format!("{xc} == {c}"));
                } else if let Ok(c) = self.coerce_soft(c, &t, xt) {
                    parts.push(format!("{x} == {c}"));
                }
            }
            if let Some(m) = clash {
                if comparable {
                    return Err(format!("{m}: {}", short(s)));
                }
                return Ok(format!("({} || {})", parts.join(" || "), eval_error_bool(&m)));
            }
            return Ok(if parts.is_empty() { "false".into() } else { format!("({})", parts.join(" || ")) });
        }
        let (sc, st) = self.gen(s, env, None)?;
        if !matches!(st, Ty::Set(_)) {
            return Err(format!("\\in a non-set: {s:?}"));
        }
        self.s_has(&sc, &st, x, xt)
    }

    // ---------------------------------------------------------------- Actions

    /// Processes the conjuncts in `work` in order. Once all are consumed, emits code that pushes
    /// the successor state onto `out`.
    pub fn gen_action(&mut self, work: &[Expr], env: &Env, out: &mut String) -> R<()> {
        use Expr::*;
        let Some((h, rest)) = work.split_first() else {
            return self.emit_state(env, out);
        };
        let with = |x: Vec<Expr>| -> Vec<Expr> { x.into_iter().chain(rest.iter().cloned()).collect() };
        // As in TLC, \/ and \E branch while some variables are still unassigned (so the number of
        // generated successors matches TLC). Once all are assigned, the rest is evaluated as a
        // boolean expression.
        let open = env.primed.len() < self.vars.len();
        let action = open && (h.is_action() || env.init);
        if !open && h.is_action() && !self.only_reads_assigned(h, env) {
            return Err(format!("unsupported action form: {}", short(h)));
        }
        match h {
            Label(name, _, body) => {
                let mut env2 = env.clone();
                if !env.label_final && action && !env.init {
                    env2.label = Some(self.label_id(name));
                    env2.label_final = !matches!(body.strip(), Or(_) | Quant(..));
                }

                return self.gen_action(&with(vec![body.as_ref().clone()]), &env2, out);
            }
            And(xs) => return self.gen_action(&with(xs.clone()), env, out),
            Or(xs) if open => {
                for x in xs {
                    out.push_str("{\n");
                    // Renew per branch so writes in one branch do not leak into the others
                    let env2 = self.renew_work(env, out);
                    self.gen_action(&with(vec![x.clone()]), &env2, out)?;
                    out.push_str("}\n");
                }
                return Ok(());
            }
            Quant(true, bs, body) if open => {
                if bs.iter().any(|(_, s)| self.try_const(s, env).is_some_and(|v| v.as_set().is_ok_and(|x| x.is_empty()))) {
                    return Ok(());
                }
                let mut env2 = env.clone();
                let mut closes = 0;
                for (x, s) in bs {
                    let (it, et, ix) = match self.iter_of_indexed(s, &env2) {
                        Ok(x) => x,
                        // During inference, proceed past sets of still-unknown type, treating the
                        // bound variable as an element of some type
                        Err(_) if self.infer.is_some() => (String::new(), Ty::Enum(vec![]), None),
                        Err(e) => return Err(e),
                    };
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    writeln!(out, "for {lx} in {it} {{").unwrap();
                    closes += 1;
                    // Renew on every iteration so writes from the previous one do not carry over
                    env2 = self.renew_work(&env2, out);
                }
                self.gen_action(&with(vec![body.as_ref().clone()]), &env2, out)?;
                out.push_str(&"}\n".repeat(closes));
                return Ok(());
            }
            If(c, a, b) if action => {
                let cc = match self.gen_as(c, env, &Ty::Bool) {
                    Err(_) if self.infer.is_some() => "true".into(),
                    r => r?,
                };
                writeln!(out, "if {cc} {{").unwrap();
                let e1 = self.renew_work(env, out);
                self.gen_action(&with(vec![a.as_ref().clone()]), &e1, out)?;
                out.push_str("} else {\n");
                let e2 = self.renew_work(env, out);
                self.gen_action(&with(vec![b.as_ref().clone()]), &e2, out)?;
                out.push_str("}\n");
                return Ok(());
            }
            Case(arms, other) if action => {
                for (i, (p, v)) in arms.iter().enumerate() {
                    let pc = match self.gen_as(p, env, &Ty::Bool) {
                        Err(_) if self.infer.is_some() => "true".into(),
                        r => r?,
                    };
                    writeln!(out, "{}if {pc} {{", if i > 0 { "else " } else { "" }).unwrap();
                    let e = self.renew_work(env, out);
                    self.gen_action(&with(vec![v.clone()]), &e, out)?;
                    out.push_str("}\n");
                }
                out.push_str("else {\n");
                let eo = self.renew_work(env, out);
                match other {
                    Some(o) => self.gen_action(&with(vec![o.as_ref().clone()]), &eo, out)?,
                    None => out.push_str("eval_error(\"Attempted to evaluate a CASE with no conditions true.\".into());\n"),
                }
                out.push_str("}\n");
                return Ok(());
            }
            Bin(BOp::Implies, a, b) if action => {
                // a => B is IF a THEN B ELSE TRUE
                let e = If(a.clone(), b.clone(), Bool(true).b());
                return self.gen_action(&with(vec![e]), env, out);
            }
            Bin(BOp::Eq, lhs, rhs) => {
                if let Some(v) = self.target(lhs, env) {
                    let t = self.var_ty(&v);
                    if self.infer.is_some() {
                        if let Ok((_, rt)) = self.gen(rhs, env, Some(&t)) {
                            self.record(&v, rt);
                        }
                        let mut env2 = env.clone();
                        env2.primed.insert(v, ("__inferred".into(), t));
                        return self.gen_action(rest, &env2, out);
                    }
                    let mut env2 = env.clone();
                    let w = self.work_var(&mut env2, out);
                    let place = format!("{w}.v_{v}");
                    // x' = [x EXCEPT ...] updates the state under construction in place
                    // (avoiding a copy out and back in)
                    match rhs.strip() {
                        Except(base, ups) if matches!(base.strip(), Ident(n) if *n == v) => {
                            self.gen_except_into(&place, ups, &t, &env2, out)?;
                        }
                        _ => match self.gen_set_update(&place, &v, rhs, &t, env) {
                            Some(code) => out.push_str(&code),
                            None => {
                                let c = self.gen_as(rhs, env, &t)?;
                                writeln!(out, "{place} = {c};").unwrap();
                            }
                        },
                    }
                    env2.primed.insert(v, (place, t));
                    return self.gen_action(rest, &env2, out);
                }
            }
            Bin(BOp::In, lhs, s) => {
                if let Some(v) = self.target(lhs, env) {
                    let t = self.var_ty(&v);
                    if self.infer.is_some() {
                        if let Ok((_, et)) = self.iter_of(s, env) {
                            self.record(&v, et);
                        }
                        let mut env2 = env.clone();
                        env2.primed.insert(v, ("__inferred".into(), t));
                        return self.gen_action(rest, &env2, out);
                    }
                    let (it, et, ix) = self.iter_of_indexed(s, env)?;
                    let x = self.fresh("x");
                    let p = self.fresh(&format!("p_{v}_"));
                    // When iterating by index, decode back to the value
                    let val = match ix {
                        Some(_) => format!("dec_{}({x})", self.ty_id(&et)?),
                        None => x.clone(),
                    };
                    let c = self.coerce(val, &et, &t)?;
                    writeln!(out, "for {x} in {it} {{ let {p}: {} = {c};", t.repr()).unwrap();
                    let mut env2 = self.renew_work(env, out);
                    let w = self.work_var(&mut env2, out);
                    writeln!(out, "{w}.v_{v} = {p};").unwrap();
                    let place = format!("{w}.v_{v}");
                    env2.primed.insert(v, (place, t));
                    self.gen_action(rest, &env2, out)?;
                    out.push_str("}\n");
                    return Ok(());
                }
            }
            Un(UOp::Unchanged, x) => {
                let mut names = vec![];
                Self::unchanged_vars(x, &mut names)?;
                let mut env2 = env.clone();
                let mut guards = vec![];
                for v in names {
                    if !self.is_var(&v) {
                        return Err(format!("UNCHANGED of non-variable `{v}`"));
                    }
                    if let Some((p, _)) = env2.primed.get(&v) {
                        guards.push(format!("{p} == s.v_{v}"));
                    } else {
                        let t = self.var_ty(&v);
                        // The state under construction is a copy of *s, so nothing needs writing
                        let p = match &env2.work {
                            Some(w) => format!("{w}.v_{v}"),
                            None => format!("s.v_{v}"),
                        };
                        env2.primed.insert(v.clone(), (p, t));
                    }
                }
                if guards.is_empty() {
                    return self.gen_action(rest, &env2, out);
                }
                writeln!(out, "if {} {{", guards.join(" && ")).unwrap();
                self.gen_action(rest, &env2, out)?;
                out.push_str("}\n");
                return Ok(());
            }
            _ => {}
        }
        if h.is_action() && !matches!(h, Bin(..) | Un(UOp::Not, _)) && !self.only_reads_assigned(h, env) {
            return Err(format!("unsupported action form: {}", short(h)));
        }
        if let Some(Value::Bool(b)) = self.try_const(h, env) {
            return if b { self.gen_action(rest, env, out) } else { Ok(()) };
        }
        let c = match self.gen_as(h, env, &Ty::Bool) {
            Err(_) if self.infer.is_some() => "true".into(),
            r => r.map_err(|m| format!("{m}\n  in: {}", short(h)))?,
        };
        writeln!(out, "if {c} {{").unwrap();
        self.gen_action(rest, env, out)?;
        out.push_str("}\n");
        Ok(())
    }

    fn record(&mut self, v: &str, t: Ty) {
        let m = self.infer.as_mut().unwrap();
        let cur = m.remove(v).unwrap_or(Ty::Enum(vec![]));
        let j = join(&cur, &t).unwrap_or(t);
        m.insert(v.to_string(), j);
    }

    /// The assignment target (x' in Next, x in Init), if it is not yet assigned
    fn target(&self, e: &Expr, env: &Env) -> Option<String> {
        let n = match (e.strip(), env.init) {
            (Expr::Prime(x), false) => match x.strip() {
                Expr::Ident(n) => n.clone(),
                _ => return None,
            },
            (Expr::Ident(n), true) => n.clone(),
            _ => return None,
        };
        (self.is_var(&n) && !env.primed.contains_key(&n)).then_some(n)
    }

    fn only_reads_assigned(&self, e: &Expr, env: &Env) -> bool {
        !e.any(&|x| match x {
            Expr::Prime(p) => matches!(p.strip(), Expr::Ident(n) if !env.primed.contains_key(n)),
            Expr::Un(UOp::Unchanged, v) => {
                let mut names = vec![];
                Self::unchanged_vars(v, &mut names).is_err() || names.iter().any(|n| !env.primed.contains_key(n))
            }
            _ => false,
        })
    }

    fn unchanged_vars(e: &Expr, out: &mut Vec<String>) -> R<()> {
        match e.strip() {
            Expr::Ident(n) => out.push(n.clone()),
            Expr::Tuple(xs) => {
                for x in xs {
                    Self::unchanged_vars(x, out)?;
                }
            }
            e => return Err(format!("UNCHANGED of {}", short(e))),
        }
        Ok(())
    }

    /// Statements that turn `place`, which holds the value of the sparse set variable `v`, into
    /// `e`, if `e` only adds elements to `v` and removes elements from it (`(v \ a) \cup b`).
    /// Building the new set elsewhere would copy the whole array out and back in.
    fn gen_set_update(&mut self, place: &str, v: &str, e: &Expr, st: &Ty, env: &Env) -> Option<String> {
        use Expr::*;
        if env.init || !is_sparse(st) {
            return None;
        }
        match e.strip() {
            Ident(n) if n == v => Some(String::new()),
            Bin(op @ (BOp::Cup | BOp::SetMinus), a, b) => {
                let base = self.gen_set_update(place, v, a, st, env)?;
                let method = if *op == BOp::Cup { "insert" } else { "remove" };
                Some(base + &self.gen_set_change(place, method, b, st, env)?)
            }
            _ => None,
        }
    }

    /// Statements that call `method` (insert or remove) on `place` for each element of the set `e`.
    /// None if an element may not fit the element type of `st`: coercing it would drop a field,
    /// and it could then equal an element it differs from.
    fn gen_set_change(&mut self, place: &str, method: &str, e: &Expr, st: &Ty, env: &Env) -> Option<String> {
        use Expr::*;
        let fits = |want: &Ty, got: &Ty| join(want, got).ok().as_ref() == Some(want);
        match e.strip() {
            SetLit(xs) => {
                let el = Self::elem_of(st);
                let mut code = String::new();
                for x in xs {
                    let (c, t) = self.gen(x, env, Some(&el)).ok()?;
                    if !fits(&el, &t) {
                        return None;
                    }
                    writeln!(code, "{place}.{method}({});", self.coerce(c, &t, &el).ok()?).unwrap();
                }
                Some(code)
            }
            If(c, x, y) => {
                let c = self.gen_as(c, env, &Ty::Bool).ok()?;
                let x = self.gen_set_change(place, method, x, st, env)?;
                let y = self.gen_set_change(place, method, y, st, env)?;
                Some(format!("if {c} {{\n{x}}} else {{\n{y}}}\n"))
            }
            _ => {
                let (c, t) = self.gen(e, env, Some(st)).ok()?;
                if !fits(st, &t) {
                    return None;
                }
                let c = self.coerce(c, &t, st).ok()?;
                let x = self.fresh("x");
                Some(format!("for {x} in ({c}).iter() {{ {place}.{method}({x}); }}\n"))
            }
        }
    }

    /// Applies EXCEPT updates directly to `place`; `@` refers to the original value at `place`.
    fn gen_except_into(
        &mut self,
        place: &str,
        ups: &[(Vec<Path>, Expr)],
        ft: &Ty,
        env: &Env,
        out: &mut String,
    ) -> R<()> {
        for (path, val) in ups {
            let path = &self.resolve_path(ft, path, env)?;
            let mut p = place.to_string();
            let mut cur = ft.clone();
            let mut conds = vec![];
            let mut at_name = None;
            for step in path {
                match (step, &cur) {
                    // Name of this EXCEPT's @, attached during expansion
                    (Path::Field(k), _) if k.starts_with('@') => at_name = Some(k.clone()),
                    (Path::Idx(i), Ty::Fun(d, c)) => {
                        let known = match i.strip() {
                            Expr::Ident(n) => env.idx.get(n).filter(|(t, _)| *t == **d).map(|(_, v)| v.clone()),
                            _ => None,
                        };
                        match known {
                            Some(iv) => p = format!("{p}[{iv} as usize]"),
                            None => {
                                let did = self.ty_id(d)?;
                                let ic = self.gen_as(i, env, d)?;
                                let iv = self.fresh("i");
                                // An index outside the domain is a no-op (as in TLC)
                                writeln!(out, "let {iv} = enc_{did}({ic});").unwrap();
                                conds.push(format!("{iv} != u64::MAX"));
                                p = format!("{p}[{iv} as usize]");
                            }
                        }
                        cur = c.as_ref().clone();
                    }
                    (Path::Field(k), Ty::Rec(fs)) => {
                        let i = fs.iter().position(|(n, _)| n == k).ok_or(format!("no field {k}"))?;
                        match &fs[i].1 {
                            // EXCEPT on an absent field is a no-op
                            Ty::Opt(t) => {
                                conds.push(format!("{p}.{i}.0"));
                                p = format!("{p}.{i}.1");
                                cur = t.as_ref().clone();
                            }
                            t => {
                                p = format!("{p}.{i}");
                                cur = t.clone();
                            }
                        }
                    }
                    _ => return Err("EXCEPT path does not match the value's type".into()),
                }
            }
            let at = self.fresh("at");
            let mut env2 = env.clone();
            env2.locals.insert("@".into(), (at.clone(), cur.clone()));
            if let Some(n) = at_name {
                env2.locals.insert(n, (at.clone(), cur.clone()));
            }
            let vc = self.gen_as(val, &env2, &cur)?;
            // Skip reading the original value unless @ is used
            let read_at = if vc.contains(&at) { format!("let {at} = {p}; ") } else { String::new() };
            if conds.is_empty() {
                writeln!(out, "{read_at}{p} = {vc};").unwrap();
            } else {
                writeln!(out, "if {} {{ {read_at}{p} = {vc}; }}", conds.join(" && ")).unwrap();
            }
        }
        Ok(())
    }

    /// Renews the state under construction on entering a branch or loop. If it has already been
    /// written to, copies its current value into a fresh variable so inner writes do not leak out.
    fn renew_work(&mut self, env: &Env, out: &mut String) -> Env {
        let mut env2 = env.clone();
        let Some(old) = env.work.clone() else { return env2 };
        let w = self.fresh("w");
        writeln!(out, "let mut {w} = {old};").unwrap();
        env2.work = Some(w.clone());
        // Repoint the slots of already-assigned variables to the new copy
        for (v, slot) in env2.primed.iter_mut() {
            if slot.0 == format!("{old}.v_{v}") {
                slot.0 = format!("{w}.v_{v}");
            }
        }
        env2
    }

    /// Creates the state under construction from `*s` on first use only
    fn work_var(&mut self, env: &mut Env, out: &mut String) -> String {
        if let Some(w) = &env.work {
            return w.clone();
        }
        let w = self.fresh("w");
        if env.init {
            // An initial state has no predecessor, so start from default values
            let fields: Vec<String> =
                self.vars.iter().map(|(v, t)| format!("v_{v}: {}", Self::default_code(t))).collect();
            writeln!(out, "let mut {w} = State {{ {} }};", fields.join(", ")).unwrap();
        } else {
            writeln!(out, "let mut {w} = *s;").unwrap();
        }
        env.work = Some(w.clone());
        w
    }

    fn emit_state(&mut self, env: &Env, out: &mut String) -> R<()> {
        for (v, _) in &self.vars {
            if env.primed.contains_key(v) {
                continue;
            }
            // Fail only if this branch is reached (TLC: Successor state is not completely specified)
            let what = if env.init { "Initial state" } else { "Successor state" };
            writeln!(out, "eval_error(\"{what} is not completely specified: {v} is not assigned\".into());").unwrap();
            return Ok(());
        }
        // All assignments are already in the state under construction, so emit it as is
        let st = match &env.work {
            Some(w) => w.clone(),
            None => {
                let fields: Vec<String> =
                    self.vars.iter().map(|(v, _)| format!("v_{v}: {}", env.primed[v].0)).collect();
                format!("State {{ {} }}", fields.join(", "))
            }
        };
        if env.init {
            writeln!(out, "out.push({st});").unwrap();
        } else {
            writeln!(out, "out.push(({st}, {}));", env.label.unwrap_or(1)).unwrap();
        }
        Ok(())
    }

    /// Compiles the fair operator `name` into a standalone successor function
    pub fn gen_fair_fn(&mut self, k: usize, name: &str, params: &[String], body: &Expr) -> R<String> {
        let mut tys: Vec<Ty> = vec![Ty::Enum(vec![]); params.len()];
        for f in self.fair.iter().filter(|f| f.name == name) {
            for (i, v) in f.args.iter().enumerate() {
                tys[i] = join(&tys[i], &ty_of_value(v)?)?;
            }
        }
        let mut env = Env::default();
        let mut sig = String::from("s: &State, ");
        for (i, (p, t)) in params.iter().zip(&tys).enumerate() {
            if !t.is_scalar() {
                return Err("fairness arguments must be scalar values".into());
            }
            env.locals.insert(p.clone(), (format!("a{i}"), t.clone()));
            write!(sig, "a{i}: {}, ", t.repr()).unwrap();
        }
        let mut code = String::new();
        self.gen_action(&[body.clone()], &env, &mut code)?;
        self.fair_param_tys.push(tys);
        Ok(format!("fn fa_{k}({sig}out: &mut Vec<(State, u32)>) {{\n{code}}}\n"))
    }

    /// fair_succ (successors of instance i) and fair_sub_changed (whether the subscript changed)
    pub fn gen_fair_dispatch(&mut self, ops: &[String]) -> R<String> {
        let mut succ = String::from("fn fair_succ(s: &State, i: usize, out: &mut Vec<(State, u32)>) {\n    match i {\n");
        let mut sub = String::from("fn fair_sub_changed(i: usize, s: &State, t: &State) -> bool {\n    match i {\n");
        let fair: Vec<(String, Vec<Value>, Vec<String>)> =
            self.fair.iter().map(|f| (f.name.clone(), f.args.clone(), f.sub.clone())).collect();
        for (i, (name, args, sv)) in fair.iter().enumerate() {
            let k = ops.iter().position(|o| o == name).unwrap();
            let tys = self.fair_param_tys[k].clone();
            let mut lits = vec![];
            for (v, t) in args.iter().zip(&tys) {
                lits.push(self.lit(v, t)?);
            }
            lits.push("out".into());
            writeln!(succ, "        {i} => fa_{k}(s, {}),", lits.join(", ")).unwrap();
            let cmp: Vec<String> = sv.iter().map(|v| format!("s.v_{v} != t.v_{v}")).collect();
            let cmp = if cmp.is_empty() { "false".to_string() } else { cmp.join(" || ") };
            writeln!(sub, "        {i} => {cmp},").unwrap();
        }
        succ += "        _ => {}\n    }\n}\n";
        sub += "        _ => false,\n    }\n}\n";
        Ok(succ + &sub)
    }

    /// Environment for expressions over a transition (s, t): x' is t.v_x
    pub fn env_step(&self, mut env: Env) -> Env {
        for (v, t) in &self.vars {
            env.primed.insert(v.clone(), (format!("t.v_{v}"), t.clone()));
        }
        env
    }

    pub fn env_init() -> Env {
        Env { init: true, ..Default::default() }
    }

    pub fn env_next() -> Env {
        Env::default()
    }

    // ---------------------------------------------------------------- Helpers

    pub fn helpers(&mut self) -> R<String> {
        let mut s = String::new();
        // fmt is needed for every type reachable from the variables' types, so register those first
        for (_, t) in self.vars.clone() {
            self.ty_id(&t)?;
        }
        let mut i = 0;
        while i < self.tys.len() {
            let t = self.tys[i].clone();
            let r = t.repr();
            if let Some(n) = t.size() {
                // enc / dec / bit / idx
                let enc_body = match &t {
                    Ty::Bool => "v as u64".to_string(),
                    Ty::Int(lo, hi) => format!("if v >= {lo} && v <= {hi} {{ (v as i128 - {lo} as i128) as u64 }} else {{ u64::MAX }}"),
                    Ty::Enum(d) => {
                        let arms: String = d.iter().enumerate().map(|(p, a)| format!("{a} => {p}, ")).collect();
                        format!("match v {{ {arms}_ => u64::MAX }}")
                    }
                    Ty::IntAtom(lo, hi, d) => {
                        // Model values first, then the integers
                        let k = d.len();
                        let arms: String = d.iter().enumerate().map(|(p, a)| format!("{a} => {p}, ")).collect();
                        format!(
                            "if v >= {lo} && v <= {hi} {{ (v as i128 - {lo} as i128) as u64 + {k} }} else {{ match (v as i128 - i64::MIN as i128) as u64 {{ {arms}_ => u64::MAX }} }}"
                        )
                    }
                    Ty::Rec(fs) => {
                        let mut b = String::from("let mut acc: u64 = 0; ");
                        for (k, (_, ft)) in fs.iter().enumerate() {
                            let fid = self.ty_id(ft)?;
                            write!(
                                b,
                                "let e = enc_{fid}(v.{k}); if e == u64::MAX {{ return u64::MAX; }} acc = acc * {} + e; ",
                                ft.size().unwrap()
                            )
                            .unwrap();
                        }
                        b + "acc"
                    }
                    Ty::Opt(inner) => {
                        let iid = self.ty_id(inner)?;
                        format!("if v.0 {{ let e = enc_{iid}(v.1); if e == u64::MAX {{ u64::MAX }} else {{ e + 1 }} }} else {{ 0 }}")
                    }
                    _ => unreachable!(),
                };
                let dec_body = match &t {
                    Ty::Bool => "i == 1".to_string(),
                    Ty::Int(lo, _) => format!("({lo} as i128 + i as i128) as i64"),
                    Ty::Enum(d) => {
                        let list: Vec<String> = d.iter().map(|a| format!("{a}u16")).collect();
                        format!("const T: [u16; {}] = [{}]; T[i as usize]", d.len(), list.join(", "))
                    }
                    Ty::IntAtom(lo, _, d) => {
                        let k = d.len();
                        let list: Vec<String> = d.iter().map(|a| format!("{a}u16")).collect();
                        format!(
                            "if i >= {k} {{ ({lo} as i128 + (i - {k}) as i128) as i64 }} else {{ const T: [u16; {k}] = [{}]; i64::MIN + T[i as usize] as i64 }}",
                            list.join(", ")
                        )
                    }
                    Ty::Rec(fs) => {
                        let mut b = String::from("let mut i = i; ");
                        let mut parts = vec![];
                        for (k, (_, ft)) in fs.iter().enumerate().rev() {
                            let fid = self.ty_id(ft)?;
                            let sz = ft.size().unwrap();
                            write!(b, "let f{k} = dec_{fid}(i % {sz}); i /= {sz}; ").unwrap();
                            parts.push(k);
                        }
                        parts.reverse();
                        b + &format!("({})", parts.iter().map(|k| format!("f{k},")).collect::<String>())
                    }
                    Ty::Opt(inner) => {
                        let iid = self.ty_id(inner)?;
                        format!("if i == 0 {{ {} }} else {{ (true, dec_{iid}(i - 1)) }}", Self::default_code(&t))
                    }
                    _ => unreachable!(),
                };
                writeln!(s, "#[inline] fn enc_{i}(v: {r}) -> u64 {{ {enc_body} }}").unwrap();
                writeln!(s, "#[inline] fn dec_{i}(i: u64) -> {r} {{ {dec_body} }}").unwrap();
                writeln!(
                    s,
                    "#[inline] fn bit_{i}(v: {r}) -> u128 {{ let e = enc_{i}(v); if e >= 128 {{ type_error(\"set element\", &fmt_{i}(&v)) }} 1u128 << e }}"
                )
                .unwrap();
                writeln!(
                    s,
                    "#[inline] fn idx_{i}(v: {r}) -> usize {{ let e = enc_{i}(v); if e == u64::MAX {{ type_error(\"function argument\", &fmt_{i}(&v)) }} e as usize }}"
                )
                .unwrap();
                let _ = n;
            }
            // fmt
            let fmt_body = match &t {
                Ty::Bool => "if *v { \"TRUE\".into() } else { \"FALSE\".into() }".to_string(),
                Ty::Int(..) => "v.to_string()".into(),
                Ty::Enum(_) => "ATOMS[*v as usize].to_string()".into(),
                Ty::IntAtom(..) => "if *v < i64::MIN + 65536 { ATOMS[(*v - i64::MIN) as usize].to_string() } else { v.to_string() }".into(),
                Ty::Rec(fs) if fs.iter().all(|(n, _)| n.starts_with('#')) => {
                    // Tuple
                    let mut parts = vec![];
                    for (k, (_, ft)) in fs.iter().enumerate() {
                        let fid = self.ty_id(ft)?;
                        parts.push(format!("fmt_{fid}(&v.{k})"));
                    }
                    format!("format!(\"<<{{}}>>\", [{}].join(\", \"))", parts.join(", "))
                }
                Ty::Rec(fs) => {
                    let mut b = String::from("let mut ps: Vec<String> = vec![]; ");
                    for (k, (name, ft)) in fs.iter().enumerate() {
                        match ft {
                            Ty::Opt(inner) => {
                                let fid = self.ty_id(inner)?;
                                write!(b, "if v.{k}.0 {{ ps.push(format!(\"{name} |-> {{}}\", fmt_{fid}(&v.{k}.1))); }} ").unwrap();
                            }
                            ft => {
                                let fid = self.ty_id(ft)?;
                                write!(b, "ps.push(format!(\"{name} |-> {{}}\", fmt_{fid}(&v.{k}))); ").unwrap();
                            }
                        }
                    }
                    b + "format!(\"[{}]\", ps.join(\", \"))"
                }
                Ty::Opt(inner) => {
                    let fid = self.ty_id(inner)?;
                    format!("if v.0 {{ fmt_{fid}(&v.1) }} else {{ \"<none>\".into() }}")
                }
                Ty::Fun(d, c) => {
                    let (did, cid) = (self.ty_id(d)?, self.ty_id(c)?);
                    if let Ty::Int(1, _) = d.as_ref() {
                        format!("format!(\"<<{{}}>>\", v.iter().map(|x| fmt_{cid}(x)).collect::<Vec<_>>().join(\", \"))")
                    } else {
                        format!(
                            "format!(\"({{}})\", v.iter().enumerate().map(|(i, x)| format!(\"{{}} :> {{}}\", fmt_{did}(&dec_{did}(i as u64)), fmt_{cid}(x))).collect::<Vec<_>>().join(\" @@ \"))"
                        )
                    }
                }
                Ty::Set(e) if is_sparse(&t) => {
                    let eid = self.ty_id(e)?;
                    format!("format!(\"{{{{{{}}}}}}\", v.iter().map(|x| fmt_{eid}(&x)).collect::<Vec<_>>().join(\", \"))")
                }
                Ty::Set(e) => {
                    let eid = self.ty_id(e)?;
                    format!("format!(\"{{{{{{}}}}}}\", bits(*v).map(|i| fmt_{eid}(&dec_{eid}(i))).collect::<Vec<_>>().join(\", \"))")
                }
            };
            writeln!(s, "fn fmt_{i}(v: &{r}) -> String {{ {fmt_body} }}").unwrap();
            i += 1;
        }
        for (a, b) in self.convs.clone() {
            let (Ty::Set(ea), Ty::Set(eb)) = (&self.tys[a], &self.tys[b]) else { unreachable!() };
            let (ia, ib) = (self.ty_ids[&**ea], self.ty_ids[&**eb]);
            writeln!(
                s,
                "fn conv_{a}_{b}(x: u128) -> u128 {{ let mut o = 0u128; for i in bits(x) {{ o |= bit_{ib}(dec_{ia}(i)); }} o }}"
            )
            .unwrap();
        }
        Ok(s)
    }

    // ---------------------------------------------------------------- Bit packing

    fn bits_for(n: u64) -> u32 {
        if n <= 1 {
            0
        } else {
            64 - (n - 1).leading_zeros()
        }
    }

    /// Statement writing `bits` bits at constant offset `at` (spanning up to 3 words); the value
    /// is treated as u128.
    fn put_at(v: &str, bits: u32, at: u32) -> String {
        let (i, sh) = ((at / 64) as usize, at % 64);
        let mut s = format!("{{ let __v = {v} as u128; w[{i}] |= (__v << {sh}) as u64; ");
        let mut covered = 64 - sh;
        let mut word = i + 1;
        while covered < bits {
            write!(s, "w[{word}] |= (__v >> {}) as u64; ", covered).unwrap();
            covered += 64;
            word += 1;
        }
        s + "}; "
    }

    /// Expression reading `bits` bits at constant offset `at` (as u128)
    fn get_at(bits: u32, at: u32) -> String {
        let (i, sh) = ((at / 64) as usize, at % 64);
        let mut parts = vec![format!("((w[{i}] as u128) >> {sh})")];
        let mut covered = 64 - sh;
        let mut word = i + 1;
        while covered < bits {
            parts.push(format!("((w[{word}] as u128) << {covered})"));
            covered += 64;
            word += 1;
        }
        let mask = if bits >= 128 { "u128::MAX".to_string() } else { format!("((1u128 << {bits}) - 1)") };
        format!("(({}) & {mask})", parts.join(" | "))
    }

    /// Code that writes a state into the bit string. When `at` is Some the offset is a constant,
    /// so shift amounts are baked in. After the first value whose size is only known at runtime
    /// (a sparse set), `at` becomes None and the code falls back to threading the offset.
    fn pack_value(&mut self, c: &str, t: &Ty, out: &mut String, at: &mut Option<u32>) -> R<u32> {
        if let Some(n) = t.size() {
            let id = self.ty_id(t)?;
            let b = Self::bits_for(n);
            let e = self.fresh("e");
            write!(out, "let {e} = enc_{id}({c}); if {e} == u64::MAX {{ return None; }} ").unwrap();
            if b > 0 {
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(&e, b, *o));
                        *o += b;
                    }
                    None => write!(out, "put(&mut w, &mut p, {e} as u128, {b}); ").unwrap(),
                }
            }
            return Ok(b);
        }
        Ok(match t {
            Ty::Set(e) if is_sparse(t) => {
                // The count, followed by that many elements (the rest stay 0). The offset is only
                // known at runtime from here on, so thread it
                let lb = Self::bits_for(self.scap as u64 + 1);
                let k = self.fresh("k");
                let n = self.fresh("n");
                if let Some(o) = at {
                    write!(out, "let mut p = {o}u32; ").unwrap();
                }
                *at = None;
                write!(out, "let {n} = ({c}).len as usize; put(&mut w, &mut p, {n} as u128, {lb}); for {k} in 0..{n} {{ ").unwrap();
                let b = self.pack_value(&format!("({c}).items[{k}]"), e, out, &mut None)?;
                out.push_str("} ");
                lb + b * self.scap as u32
            }
            Ty::Set(e) => {
                let n = e.size().unwrap() as u32;
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(c, n, *o));
                        *o += n;
                    }
                    None => write!(out, "put(&mut w, &mut p, {c}, {n}); ").unwrap(),
                }
                n
            }
            Ty::Opt(inner) => {
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(&format!("({c}).0 as u128"), 1, *o));
                        *o += 1;
                    }
                    None => write!(out, "put(&mut w, &mut p, ({c}).0 as u128, 1); ").unwrap(),
                }
                1 + self.pack_value(&format!("({c}).1"), inner, out, at)?
            }
            Ty::Fun(d, cod) => {
                let n = d.size().unwrap();
                if at.is_some() {
                    // The size is known, so unroll at generation time
                    let mut total = 0;
                    for k in 0..n {
                        total += self.pack_value(&format!("{c}[{k}]"), cod, out, at)?;
                    }
                    return Ok(total);
                }
                let k = self.fresh("k");
                write!(out, "for {k} in 0..{n} {{ ").unwrap();
                let b = self.pack_value(&format!("{c}[{k}]"), cod, out, &mut None)?;
                out.push_str("} ");
                b * n as u32
            }
            Ty::Rec(fs) => {
                let mut total = 0;
                for (i, (_, ft)) in fs.iter().enumerate() {
                    total += self.pack_value(&format!("{c}.{i}"), ft, out, at)?;
                }
                total
            }
            _ => unreachable!(),
        })
    }

    /// Same layout as `pack_value`, but writes perm(c) (`pm`, inverse `pi`) without building the
    /// permuted value. A function's entry j is read from the argument that `pm` maps to j, and a
    /// sparse set's elements are written in the order of their permuted values.
    fn pack_perm(&mut self, c: &str, t: &Ty, out: &mut String, at: &mut Option<u32>) -> R<u32> {
        let inv_key = |d: &Ty, k: &str| match d {
            Ty::Enum(_) => Some(format!("pi[({k}) as usize]")),
            Ty::Bool | Ty::Int(..) => Some(k.to_string()),
            _ => None,
        };
        match t {
            _ if t.size().is_some() => {
                let pc = self.perm_code(c, t)?;
                self.pack_value(&format!("({pc})"), t, out, at)
            }
            Ty::Rec(fs) => {
                let mut total = 0;
                for (i, (_, ft)) in fs.iter().enumerate() {
                    total += self.pack_perm(&format!("{c}.{i}"), ft, out, at)?;
                }
                Ok(total)
            }
            Ty::Opt(inner) => {
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(&format!("({c}).0 as u128"), 1, *o));
                        *o += 1;
                    }
                    None => write!(out, "put(&mut w, &mut p, ({c}).0 as u128, 1); ").unwrap(),
                }
                Ok(1 + self.pack_perm(&format!("({c}).1"), inner, out, at)?)
            }
            Ty::Set(e) if is_sparse(t) => {
                let lb = Self::bits_for(self.scap as u64 + 1);
                let (n, ord, a, b, k) = (self.fresh("n"), self.fresh("ord"), self.fresh("a"), self.fresh("b"), self.fresh("k"));
                let lhs = self.perm_code(&format!("({c}).items[{ord}[{b} - 1] as usize]"), e)?;
                let rhs = self.perm_code(&format!("({c}).items[{ord}[{b}] as usize]"), e)?;
                // Sorting is the costly part, so give up first if the words written so far
                // already exceed the best key
                match at {
                    Some(o) => write!(out, "if prune(&w, __best, {}, &mut __cw) {{ return Some(None); }} let mut p = {o}u32; ", *o / 64).unwrap(),
                    None => out.push_str("if prune(&w, __best, (p / 64) as usize, &mut __cw) { return Some(None); } "),
                }
                *at = None;
                write!(
                    out,
                    "let {n} = ({c}).len as usize; let mut {ord} = [0u8; {}]; for {k} in 0..{n} {{ {ord}[{k}] = {k} as u8; }} \
                     for {a} in 1..{n} {{ let mut {b} = {a}; while {b} > 0 && {lhs} > {rhs} {{ {ord}.swap({b} - 1, {b}); {b} -= 1; }} }} \
                     put(&mut w, &mut p, {n} as u128, {lb}); for {k} in 0..{n} {{ ",
                    self.scap
                )
                .unwrap();
                let eb = self.pack_perm(&format!("({c}).items[{ord}[{k}] as usize]"), e, out, &mut None)?;
                out.push_str("} ");
                Ok(lb + eb * self.scap as u32)
            }
            Ty::Fun(d, cod) if inv_key(d, "").is_some() => {
                let n = d.size().unwrap();
                let did = self.ty_id(d)?;
                if at.is_some() {
                    let mut total = 0;
                    for k in 0..n {
                        let src = inv_key(d, &format!("dec_{did}({k}u64)")).unwrap();
                        let words = at.map(|o| o / 64);
                        total += self.pack_perm(&format!("{c}[idx_{did}({src})]"), cod, out, at)?;
                        // The permutation decides which entry lands here, so a key often loses
                        // to the best one within the first entries
                        if let (Some(before), Some(o)) = (words, *at) {
                            if o / 64 > before {
                                write!(out, "if prune(&w, __best, {}, &mut __cw) {{ return Some(None); }} ", o / 64).unwrap();
                            }
                        }
                    }
                    return Ok(total);
                }
                let k = self.fresh("k");
                let src = inv_key(d, &format!("dec_{did}({k} as u64)")).unwrap();
                write!(out, "for {k} in 0..{n} {{ ").unwrap();
                let b = self.pack_perm(&format!("{c}[idx_{did}({src})]"), cod, out, &mut None)?;
                out.push_str("} ");
                Ok(b * n as u32)
            }
            _ => {
                let pv = self.fresh("pv");
                let pc = self.perm_code(c, t)?;
                write!(out, "let {pv} = {pc}; ").unwrap();
                self.pack_value(&pv, t, out, at)
            }
        }
    }

    fn unpack_value(&mut self, t: &Ty, at: &mut Option<u32>) -> R<String> {
        if let Some(n) = t.size() {
            let id = self.ty_id(t)?;
            let b = Self::bits_for(n);
            if b == 0 {
                return Ok(format!("dec_{id}(0)"));
            }
            return Ok(match at {
                Some(o) => {
                    let e = Self::get_at(b, *o);
                    *o += b;
                    format!("dec_{id}({e} as u64)")
                }
                None => format!("dec_{id}(get(w, &mut p, {b}) as u64)"),
            });
        }
        Ok(match t {
            Ty::Set(e) if is_sparse(t) => {
                let lb = Self::bits_for(self.scap as u64 + 1);
                // Thread the offset from here on, assigning to the outer p (a fresh `let` inside
                // the block would reset the offset to 0 on leaving it, so later fields would be
                // read from the start)
                let pre = match at {
                    Some(o) => format!("p = {o}u32; "),
                    None => String::new(),
                };
                *at = None;
                let inner = self.unpack_value(e, &mut None)?;
                format!(
                    "{{ {pre}let n = get(w, &mut p, {lb}) as usize; let mut ss = {}; for k in 0..n {{ ss.items[k] = {inner}; }} ss.len = n as u8; ss }}",
                    Self::default_code(t)
                )
            }
            Ty::Set(e) => {
                let n = e.size().unwrap() as u32;
                match at {
                    Some(o) => {
                        let e = Self::get_at(n, *o);
                        *o += n;
                        e
                    }
                    None => format!("get(w, &mut p, {n})"),
                }
            }
            Ty::Opt(inner) => {
                let flag = match at {
                    Some(o) => {
                        let e = Self::get_at(1, *o);
                        *o += 1;
                        format!("{e} == 1")
                    }
                    None => "get(w, &mut p, 1) == 1".into(),
                };
                format!("({flag}, {})", self.unpack_value(inner, at)?)
            }
            Ty::Fun(d, cod) => {
                let n = d.size().unwrap();
                if at.is_some() {
                    let mut parts = vec![];
                    for _ in 0..n {
                        parts.push(self.unpack_value(cod, at)?);
                    }
                    return Ok(format!("[{}]", parts.join(", ")));
                }
                format!("std::array::from_fn(|_| {})", self.unpack_value(cod, &mut None)?)
            }
            Ty::Rec(fs) => {
                let mut s = String::from("(");
                for (_, ft) in fs {
                    s += &self.unpack_value(ft, at)?;
                    s += ",";
                }
                s + ")"
            }
            _ => unreachable!(),
        })
    }

    /// pack / unpack and the word count
    pub fn gen_pack(&mut self) -> R<String> {
        let mut body = String::new();
        let mut total = 0;
        let mut at = Some(0u32);
        for (v, t) in self.vars.clone() {
            total += self.pack_value(&format!("s.v_{v}"), &t, &mut body, &mut at)?;
        }
        // If the offset stayed constant, p is unused; omit it to avoid an unused-variable warning
        let pack_p = if at.is_some() { "" } else { "let mut p = 0u32; " };
        let words = total.div_ceil(64).max(1);
        let mut at = Some(0u32);
        let mut un = String::from("State { ");
        for (v, t) in self.vars.clone() {
            write!(un, "v_{v}: {}, ", self.unpack_value(&t, &mut at)?).unwrap();
        }
        un += "}";
        let unpack_p = if at.is_some() { "" } else { "let mut p = 0u32; " };
        Ok(format!(
            "// {total} bits per state\nconst WORDS: usize = {words};\ntype Packed = [u64; WORDS];\n\
             fn pack(s: &State) -> Option<Packed> {{ let mut w: Packed = [0; WORDS]; {pack_p}{body}Some(w) }}\n\
             fn unpack(w: &Packed) -> State {{ {unpack_p}{un} }}\n"
        ))
    }

    // ---------------------------------------------------------------- VIEW and SYMMETRY

    /// Function that packs the deduplication key (the VIEW value if there is one, otherwise the
    /// state) into a bit string
    /// state) into a bit string. With `equiv` (see `view_is_equivariant`), also emits `view_perm`,
    /// which permutes an already computed view value.
    pub fn gen_key(&mut self, view: Option<&Expr>, equiv: bool) -> R<String> {
        let Some(view) = view else {
            return Ok("const HAS_VIEW: bool = false;\ntype Key = Packed;\nfn key_of(s: &State) -> Option<Key> { pack(s) }\n\
                       const VIEW_EQUIV: bool = false;\ntype View = ();\nfn view_val(_: &State) -> View {}\n\
                       fn view_perm_pack(_: &View, _: &[u16], _: &[u16], _: Option<&Key>) -> Option<Option<Key>> { unreachable!() }\nfn view_pack_v(_: &View) -> Option<Key> { unreachable!() }\n"
                .into());
        };
        let (vc, vt) = self.gen(view, &Gen::env_next(), None).map_err(|e| format!("VIEW: {e}"))?;
        let mut body = String::new();
        let mut at = Some(0u32);
        let bits = self.pack_value("(*__v)", &vt, &mut body, &mut at)?;
        let vp = if at.is_some() { "" } else { "let mut p = 0u32; " };
        let words = bits.div_ceil(64).max(1);
        let mut pbody = String::new();
        let mut pat = Some(0u32);
        if equiv {
            self.pack_perm("(*__v)", &vt, &mut pbody, &mut pat)?;
        }
        let pvp = if pat.is_some() { "" } else { "let mut p = 0u32; " };
        Ok(format!(
            "const HAS_VIEW: bool = true;\nconst VWORDS: usize = {words};\ntype Key = [u64; VWORDS];\n\
             const VIEW_EQUIV: bool = {equiv};\ntype View = {};\n\
             fn view_val(s: &State) -> View {{ {vc} }}\n\
             fn view_pack_v(__v: &View) -> Option<Key> {{ let mut w: Key = [0; VWORDS]; {vp}{body}Some(w) }}\n\
             fn view_perm_pack(__v: &View, pm: &[u16], pi: &[u16], __best: Option<&Key>) -> Option<Option<Key>> {{ let mut w: Key = [0; VWORDS]; let mut __cw = 0usize; {pvp}{pbody}Some(Some(w)) }}\n\
             fn key_of(s: &State) -> Option<Key> {{ view_pack_v(&view_val(s)) }}\n",
            vt.repr()
        ))
    }

    /// Expression applying the model-value permutation pm to value c of type t
    fn perm_code(&mut self, c: &str, t: &Ty) -> R<String> {
        Ok(match t {
            Ty::Bool | Ty::Int(..) => c.to_string(),
            Ty::Enum(_) => format!("pm[({c}) as usize]"),
            Ty::IntAtom(..) => {
                let x = self.fresh("x");
                format!("{{ let {x} = {c}; if {x} < i64::MIN + 65536 {{ i64::MIN + pm[({x} - i64::MIN) as usize] as i64 }} else {{ {x} }} }}")
            }
            Ty::Rec(fs) => {
                let r = self.fresh("r");
                let mut s = format!("{{ let {r} = &({c}); (");
                for (i, (_, ft)) in fs.iter().enumerate() {
                    s += &self.perm_code(&format!("{r}.{i}"), ft)?;
                    s += ",";
                }
                s + ") }"
            }
            Ty::Opt(inner) => {
                let o = self.fresh("o");
                format!("{{ let {o} = &({c}); ({o}.0, {}) }}", self.perm_code(&format!("{o}.1"), inner)?)
            }
            Ty::Fun(d, cod) => {
                let did = self.ty_id(d)?;
                let (f, o, i) = (self.fresh("f"), self.fresh("o"), self.fresh("i"));
                let k = self.perm_code(&format!("dec_{did}({i} as u64)"), d)?;
                let v = self.perm_code(&format!("{f}[{i}]"), cod)?;
                format!("{{ let {f} = &({c}); let mut {o} = *{f}; for {i} in 0..{} {{ {o}[idx_{did}({k})] = {v}; }} {o} }}", d.size().unwrap())
            }
            // A permutation is a bijection, so permuting the elements of a sorted array in place
            // leaves them distinct and one sort restores the order.
            Ty::Set(e) if is_sparse(t) => {
                let (acc, i, y) = (self.fresh("acc"), self.fresh("i"), self.fresh("y"));
                let py = self.perm_code(&format!("{acc}.items[{i}]"), e)?;
                format!(
                    "{{ let mut {acc} = {c}; for {i} in 0..{acc}.len as usize {{ let {y} = {py}; {acc}.items[{i}] = {y}; }} \
                     {acc}.items[..{acc}.len as usize].sort_unstable(); {acc} }}"
                )
            }
            Ty::Set(e) => {
                let x = self.fresh("x");
                let acc = self.fresh("acc");
                let it = self.s_iter(c, t)?;
                let px = self.perm_code(&x, e)?;
                let add = self.s_add(&acc, &px, t)?;
                let empty = self.s_empty(t)?;
                format!("{{ let mut {acc} = {empty}; for {x} in {it} {{ {add} }} {acc} }}")
            }
        })
    }

    /// Permutation tables and perm_state. Each entry of `perms` maps atom -> atom.
    pub fn gen_perms(&mut self, perms: &[Vec<u16>]) -> R<String> {
        let mut s = String::new();
        let tables: Vec<String> = perms
            .iter()
            .map(|p| format!("&[{}]", p.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")))
            .collect();
        writeln!(s, "static PERMS: &[&[u16]] = &[{}];", tables.join(", ")).unwrap();
        let mut fields = vec![];
        for (v, t) in self.vars.clone() {
            fields.push(format!("v_{v}: {}", self.perm_code(&format!("s.v_{v}"), &t)?));
        }
        writeln!(s, "fn perm_state(s: &State, pm: &[u16]) -> State {{ State {{ {} }} }}", fields.join(", ")).unwrap();
        Ok(s)
    }

    pub fn atoms_table(&self) -> String {
        let names: Vec<String> = self.atoms.list.iter().enumerate().map(|(i, _)| format!("{:?}", self.atoms.show(i as u32))).collect();
        format!("static ATOMS: [&str; {}] = [{}];\n", names.len(), names.join(", "))
    }
}

/// How a comparison involving tuples turns out in TLC (see `Gen::tuple_cmp`)
#[derive(Clone, PartialEq)]
enum Cmp {
    /// Compare the values
    Normal,
    /// Never equal
    Unequal,
    /// TLC stops with this error when it evaluates the comparison
    Fails(String),
}

/// A boolean expression that stops with an evaluation error when it is evaluated (TLC stops only
/// when it evaluates the comparison, so a branch never taken must not be an error)
fn eval_error_bool(msg: &str) -> String {
    format!("{{ let __b: bool = eval_error({msg:?}.to_string()); __b }}")
}

/// A function whose domain is 1..n, which TLA+ considers equal to the tuple of its values. Mixing
/// the two is rejected rather than compared as unequal.
fn seq_like_fun(t: &Ty) -> bool {
    matches!(t, Ty::Fun(d, _) if matches!(d.as_ref(), Ty::Int(1, _)))
}

/// Turns a constant value into a literal (for \\A bindings in properties)
pub fn lit_for(g: &Gen, v: &Value) -> R<(String, Ty)> {
    let t = ty_of_value(v)?;
    if !t.is_scalar() {
        return Err("quantifying a property over non-scalar values is not supported yet".into());
    }
    let code = match v {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => format!("{i}i64"),
        Value::Atom(a) => format!("{a}u16"),
        _ => return Err("quantifying a property over records is not supported yet".into()),
    };
    let _ = g;
    Ok((code, t))
}

impl Env {
    pub fn bind(&mut self, name: &str, code: String, t: Ty) {
        self.locals.insert(name.to_string(), (code, t));
    }
}

/// Rebuilds e with each child replaced by f(child), preserving its structure
pub fn map_children(e: &Expr, f: &dyn Fn(&Expr) -> Expr) -> Expr {
    use Expr::*;
    let m = |x: &Expr| f(x);
    let mb = |x: &Expr| f(x).b();
    match e {
        Num(_) | Str(_) | Bool(_) | Ident(_) | At => e.clone(),
        Call(n, a) => Call(n.clone(), a.iter().map(m).collect()),
        Prime(x) => Prime(mb(x)),
        Un(o, x) => Un(*o, mb(x)),
        Bin(o, a, b) => Bin(*o, mb(a), mb(b)),
        And(xs) => And(xs.iter().map(m).collect()),
        Or(xs) => Or(xs.iter().map(m).collect()),
        If(a, b, c) => If(mb(a), mb(b), mb(c)),
        Case(arms, o) => Case(arms.iter().map(|(p, v)| (m(p), m(v))).collect(), o.as_ref().map(|x| mb(x))),
        Quant(q, bs, b) => Quant(*q, bs.iter().map(|(x, s)| (x.clone(), m(s))).collect(), mb(b)),
        Choose(x, s, p) => Choose(x.clone(), mb(s), mb(p)),
        SetLit(xs) => SetLit(xs.iter().map(m).collect()),
        SetFilter(x, s, p) => SetFilter(x.clone(), mb(s), mb(p)),
        SetMap(g, bs) => SetMap(mb(g), bs.iter().map(|(x, s)| (x.clone(), m(s))).collect()),
        FunCons(x, s, b) => FunCons(x.clone(), mb(s), mb(b)),
        FunSet(a, b) => FunSet(mb(a), mb(b)),
        RecLit(fs) => RecLit(fs.iter().map(|(k, v)| (k.clone(), m(v))).collect()),
        RecSet(fs) => RecSet(fs.iter().map(|(k, v)| (k.clone(), m(v))).collect()),
        App(a, b) => App(mb(a), mb(b)),
        Field(r, k) => Field(mb(r), k.clone()),
        Except(g, ups) => Except(
            mb(g),
            ups.iter()
                .map(|(path, v)| {
                    let path = path
                        .iter()
                        .map(|p| match p {
                            Path::Idx(i) => Path::Idx(m(i)),
                            Path::Field(k) => Path::Field(k.clone()),
                        })
                        .collect();
                    (path, m(v))
                })
                .collect(),
        ),
        Tuple(xs) => Tuple(xs.iter().map(m).collect()),
        Let(ds, b) => Let(ds.clone(), mb(b)),
        BoxAction(a, b) => BoxAction(mb(a), mb(b)),
        Fair(w, a, b) => Fair(*w, mb(a), mb(b)),
        Label(n, a, b) => Label(n.clone(), a.iter().map(m).collect(), mb(b)),
    }
}

pub fn short(e: &Expr) -> String {
    let s = format!("{e:?}");
    if s.len() > 200 {
        format!("{}…", &s[..s.char_indices().nth(200).map(|x| x.0).unwrap_or(s.len())])
    } else {
        s
    }
}
