//! Compile-time values and an evaluator for constant expressions (used to fold state-free
//! expressions).

use crate::ast::*;
use crate::lexer::R;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Strings and model values. At runtime they are u16 ids.
#[derive(Default, Debug)]
pub struct Atoms {
    pub list: Vec<(bool, String)>, // (is model value, name)
    map: HashMap<(bool, String), u32>,
}

impl Atoms {
    pub fn intern(&mut self, model: bool, s: &str) -> u32 {
        if let Some(&i) = self.map.get(&(model, s.to_string())) {
            return i;
        }
        let i = self.list.len() as u32;
        self.list.push((model, s.to_string()));
        self.map.insert((model, s.to_string()), i);
        i
    }
    pub fn get(&self, model: bool, s: &str) -> Option<u32> {
        self.map.get(&(model, s.to_string())).copied()
    }
    pub fn show(&self, a: u32) -> String {
        let (m, s) = &self.list[a as usize];
        if *m {
            s.clone()
        } else {
            format!("{s:?}")
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Atom(u32),
    Set(BTreeSet<Value>),
    Fun(BTreeMap<Value, Value>),
    Rec(BTreeMap<String, Value>),
    Tuple(Vec<Value>),
}

impl Value {
    fn rank(&self) -> u8 {
        match self {
            // TLC orders a model value before any other value. Atoms mix only with integers in one
            // type (strings never do), so this matters for `1..3 \cup {None}`
            Value::Atom(_) => 0,
            Value::Bool(_) => 1,
            Value::Int(_) => 2,
            Value::Set(_) => 3,
            Value::Fun(_) => 4,
            Value::Rec(_) => 5,
            Value::Tuple(_) => 6,
        }
    }
}

/// Ordering that follows TLC. Smaller sets sort first (so SUBSET enumerates in TLC's order).
impl Ord for Value {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        use Value::*;
        match (self, o) {
            (Bool(a), Bool(b)) => a.cmp(b),
            (Int(a), Int(b)) => a.cmp(b),
            (Atom(a), Atom(b)) => a.cmp(b),
            (Set(a), Set(b)) => a.len().cmp(&b.len()).then_with(|| a.iter().cmp(b.iter())),
            (Fun(a), Fun(b)) => a.iter().cmp(b.iter()),
            (Rec(a), Rec(b)) => a.iter().cmp(b.iter()),
            (Tuple(a), Tuple(b)) => a.len().cmp(&b.len()).then_with(|| a.iter().cmp(b.iter())),
            _ => self.rank().cmp(&o.rank()),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

impl Value {
    pub fn as_set(&self) -> R<&BTreeSet<Value>> {
        match self {
            Value::Set(s) => Ok(s),
            v => Err(format!("expected a set, got {v:?}")),
        }
    }
    fn as_int(&self) -> R<i64> {
        match self {
            Value::Int(i) => Ok(*i),
            v => Err(format!("expected an integer, got {v:?}")),
        }
    }
    fn as_bool(&self) -> R<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            v => Err(format!("expected a boolean, got {v:?}")),
        }
    }
}

pub const ENUM_LIMIT: usize = 1 << 20;

/// How deep a recursive operator may call itself, both when evaluated at compile time and in the
/// generated checker. TLC stops with a stack overflow at a depth that depends on its JVM stack and
/// on the operator's body: measured between 800 and 900 levels for `1 + Sum(k - 1)`, and between
/// 500 and 700 for a body with two LETs. Erring on the side of an error, deeper is an error here.
pub const REC_LIMIT: u32 = 500;

thread_local! {
    static REC_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// The starts of the error messages for failures that TLC raises too when it evaluates the same
/// expression (as opposed to expressions tla2rs cannot evaluate here).
const EVAL_FAILURES: [&str; 7] = [
    "The second argument of \\div is 0.",
    "The second argument of % should be a positive number",
    "Attempted to evaluate a CASE with no conditions true.",
    "CHOOSE: no element satisfies the predicate",
    "function applied outside its domain",
    "tuple index out of range",
    "no field ",
];

/// Whether an error from `ConstEval::eval` is an evaluation failure of the spec itself.
pub fn is_eval_failure(e: &str) -> bool {
    EVAL_FAILURES.iter().any(|p| e.starts_with(p))
}

#[derive(Clone)]
pub struct ConstEval<'a> {
    pub atoms: &'a Atoms,
    pub constants: &'a HashMap<String, Value>,
}

impl ConstEval<'_> {
    pub fn eval(&self, e: &Expr, env: &HashMap<String, Value>) -> R<Value> {
        use Expr::*;
        Ok(match e {
            Num(n) => Value::Int(*n),
            Bool(b) => Value::Bool(*b),
            Str(s) => Value::Atom(self.atoms.get(false, s).ok_or("unknown string")?),
            Ident(n) => {
                if let Some(v) = env.get(n) {
                    v.clone()
                } else if let Some(v) = self.constants.get(n) {
                    v.clone()
                } else if let Some(m) = n.strip_prefix("@model:") {
                    Value::Atom(self.atoms.get(true, m).ok_or("unknown model value")?)
                } else if n == "BOOLEAN" {
                    Value::Set([Value::Bool(false), Value::Bool(true)].into())
                } else {
                    return Err(format!("`{n}` is not a constant"));
                }
            }
            Label(_, _, b) => self.eval(b, env)?,
            Call(f, args) => match (f.as_str(), args.as_slice()) {
                ("Cardinality", [s]) => Value::Int(self.eval(s, env)?.as_set()?.len() as i64),
                ("IsFiniteSet", [s]) => {
                    self.eval(s, env)?.as_set()?;
                    Value::Bool(true)
                }
                ("^", [a, b]) => {
                    let (a, b) = (self.eval(a, env)?.as_int()?, self.eval(b, env)?.as_int()?);
                    if b < 0 {
                        return Err(format!("{a}^{b}: the exponent must be a natural number"));
                    }
                    Value::Int(int_pow(a, b).ok_or(format!("{a}^{b} overflows"))?)
                }
                ("Assert", [p, m]) => {
                    if !self.eval(p, env)?.as_bool()? {
                        return Err(format!("The first argument of Assert evaluated to FALSE; the second argument was: {:?}", self.eval(m, env)?));
                    }
                    Value::Bool(true)
                }
                // The TLC module: d :> e is the function {d} -> e, and f @@ g joins two functions,
                // taking f where both are defined
                (":>", [d, e]) => fun_value([(self.eval(d, env)?, self.eval(e, env)?)].into()),
                ("@@", [f, g]) => match (self.eval(f, env)?, self.eval(g, env)?) {
                    (Value::Fun(mut a), Value::Fun(b)) => {
                        for (k, v) in b {
                            a.entry(k).or_insert(v);
                        }
                        fun_value(a)
                    }
                    (a, b) if as_fun(&a).is_some() && as_fun(&b).is_some() => {
                        let mut a = as_fun(&a).unwrap();
                        for (k, v) in as_fun(&b).unwrap() {
                            a.entry(k).or_insert(v);
                        }
                        fun_value(a)
                    }
                    _ => return Err("@@ of values that are not functions".into()),
                },
                // Sequences are tuples here; strings are sequences of characters in TLC, which only
                // Len reads here (an operator building a new string has no atom for it)
                ("Len", [q]) => match self.eval(q, env)? {
                    Value::Tuple(t) => Value::Int(t.len() as i64),
                    Value::Atom(a) if !self.atoms.list[a as usize].0 => Value::Int(self.atoms.list[a as usize].1.chars().count() as i64),
                    v => return Err(format!("Len of {v:?}, which is not a sequence")),
                },
                ("Append", [q, x]) => {
                    let mut t = self.seq(q, env, "Append")?;
                    t.push(self.eval(x, env)?);
                    Value::Tuple(t)
                }
                ("Head", [q]) => {
                    let t = self.seq(q, env, "Head")?;
                    t.first().cloned().ok_or("Attempted to apply Head to the empty sequence.")?
                }
                ("Tail", [q]) => {
                    let t = self.seq(q, env, "Tail")?;
                    if t.is_empty() {
                        return Err("Attempted to apply Tail to the empty sequence.".into());
                    }
                    Value::Tuple(t[1..].to_vec())
                }
                ("SubSeq", [q, m, n]) => {
                    let t = self.seq(q, env, "SubSeq")?;
                    let (m, n) = (self.eval(m, env)?.as_int()?, self.eval(n, env)?.as_int()?);
                    if m > n {
                        Value::Tuple(vec![])
                    } else if m < 1 || m > t.len() as i64 {
                        return Err("The second argument of SubSeq must be in the domain of its first argument.".into());
                    } else if n > t.len() as i64 {
                        return Err("The third argument of SubSeq must be in the domain of its first argument.".into());
                    } else {
                        Value::Tuple(t[(m - 1) as usize..n as usize].to_vec())
                    }
                }
                ("\\o", [a, b]) => {
                    let mut t = self.seq(a, env, "\\o")?;
                    t.extend(self.seq(b, env, "\\o")?);
                    Value::Tuple(t)
                }
                ("SelectSeq", [q, Lambda(ps, body)]) if ps.len() == 1 => {
                    let t = self.seq(q, env, "SelectSeq")?;
                    let mut out = vec![];
                    for x in t {
                        let mut env2 = env.clone();
                        env2.insert(ps[0].clone(), x.clone());
                        if self.eval(body, &env2)?.as_bool()? {
                            out.push(x);
                        }
                    }
                    Value::Tuple(out)
                }
                ("PrintT", [x]) => {
                    self.eval(x, env)?;
                    Value::Bool(true)
                }
                ("Print", [x, v]) => {
                    self.eval(x, env)?;
                    self.eval(v, env)?
                }
                ("\\X", parts) => {
                    let mut out: Vec<Vec<Value>> = vec![vec![]];
                    for s in parts {
                        let s = self.eval(s, env)?;
                        let s = s.as_set()?;
                        if out.len().saturating_mul(s.len()) > ENUM_LIMIT {
                            return Err("cartesian product too large to enumerate".into());
                        }
                        out = out.iter().flat_map(|t| s.iter().map(move |x| [t.as_slice(), &[x.clone()]].concat())).collect();
                    }
                    Value::Set(out.into_iter().map(Value::Tuple).collect())
                }
                ("Permutations", [x]) => {
                    let elems: Vec<Value> = self.eval(x, env)?.as_set()?.iter().cloned().collect();
                    if elems.len() > 8 {
                        return Err("Permutations of more than 8 elements".into());
                    }
                    let mut out = BTreeSet::new();
                    let mut idx: Vec<usize> = (0..elems.len()).collect();
                    loop {
                        out.insert(Value::Fun(elems.iter().cloned().zip(idx.iter().map(|&i| elems[i].clone())).collect()));
                        // Next permutation (lexicographic)
                        let Some(k) = (0..idx.len().saturating_sub(1)).rev().find(|&k| idx[k] < idx[k + 1]) else { break };
                        let l = (k + 1..idx.len()).rev().find(|&l| idx[k] < idx[l]).unwrap();
                        idx.swap(k, l);
                        idx[k + 1..].reverse();
                    }
                    Value::Set(out)
                }
                _ => return Err(format!("operator `{f}` is not supported in constant expressions")),
            },
            Un(op, x) => {
                let v = self.eval(x, env)?;
                match op {
                    UOp::Not => Value::Bool(!v.as_bool()?),
                    UOp::Neg => Value::Int(-v.as_int()?),
                    UOp::Subset => {
                        let elems: Vec<Value> = v.as_set()?.iter().cloned().collect();
                        if elems.len() > 20 {
                            return Err("SUBSET of a large set".into());
                        }
                        let mut out = BTreeSet::new();
                        for mask in 0u64..(1 << elems.len()) {
                            out.insert(Value::Set(
                                elems.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 1).map(|(_, v)| v.clone()).collect(),
                            ));
                        }
                        Value::Set(out)
                    }
                    UOp::Union => {
                        let mut out = BTreeSet::new();
                        for s in v.as_set()? {
                            out.extend(s.as_set()?.iter().cloned());
                        }
                        Value::Set(out)
                    }
                    UOp::Domain => match v {
                        Value::Fun(m) => Value::Set(m.keys().cloned().collect()),
                        Value::Tuple(t) => Value::Set((1..=t.len() as i64).map(Value::Int).collect()),
                        _ => return Err("DOMAIN of a non-function".into()),
                    },
                    _ => return Err(format!("{op:?} is not a constant operator")),
                }
            }
            // `x \in Nat` / `x \in Int` (common in assumptions). The set itself can't be built, so
            // only test membership
            Bin(op @ (BOp::In | BOp::NotIn), x, set)
                if matches!(set.strip(), Ident(n) if (n == "Nat" || n == "Int")
                    && !env.contains_key(n) && !self.constants.contains_key(n)) =>
            {
                let Ident(n) = set.strip() else { unreachable!() };
                let inside = match self.eval(x, env)? {
                    Value::Int(v) => n == "Int" || v >= 0,
                    _ => false,
                };
                Value::Bool(inside == matches!(op, BOp::In))
            }
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if matches!(set.strip(), Call(f, a) if f == "Seq" && a.len() == 1) => {
                let Call(_, a) = set.strip() else { unreachable!() };
                let inside = match self.eval(x, env)? {
                    Value::Tuple(t) => {
                        let s = self.eval(&a[0], env)?;
                        let s = s.as_set()?;
                        t.iter().all(|e| s.contains(e))
                    }
                    _ => false,
                };
                Value::Bool(inside == matches!(op, BOp::In))
            }
            Bin(op, a, b) => {
                let a = self.eval(a, env)?;
                let b = self.eval(b, env)?;
                self.bin(*op, a, b)?
            }
            And(xs) => {
                for x in xs {
                    if !self.eval(x, env)?.as_bool()? {
                        return Ok(Value::Bool(false));
                    }
                }
                Value::Bool(true)
            }
            Or(xs) => {
                for x in xs {
                    if self.eval(x, env)?.as_bool()? {
                        return Ok(Value::Bool(true));
                    }
                }
                Value::Bool(false)
            }
            If(c, a, b) => {
                if self.eval(c, env)?.as_bool()? {
                    self.eval(a, env)?
                } else {
                    self.eval(b, env)?
                }
            }
            Case(arms, other) => {
                for (p, v) in arms {
                    if self.eval(p, env)?.as_bool()? {
                        return self.eval(v, env);
                    }
                }
                match other {
                    Some(o) => self.eval(o, env)?,
                    None => return Err(EVAL_FAILURES[2].into()),
                }
            }
            Quant(ex, bs, body) => {
                let mut found = !*ex;
                self.each_binding(bs, env, &mut |env2| {
                    let v = self.eval(body, env2)?.as_bool()?;
                    if *ex && v {
                        found = true;
                        return Ok(false);
                    }
                    if !*ex && !v {
                        found = false;
                        return Ok(false);
                    }
                    Ok(true)
                })?;
                Value::Bool(found)
            }
            Choose(x, s, p) => {
                let s = self.eval(s, env)?;
                for v in s.as_set()? {
                    let mut env2 = env.clone();
                    env2.insert(x.clone(), v.clone());
                    if self.eval(p, &env2)?.as_bool()? {
                        return Ok(v.clone());
                    }
                }
                return Err(EVAL_FAILURES[3].into());
            }
            SetLit(xs) => Value::Set(xs.iter().map(|x| self.eval(x, env)).collect::<R<_>>()?),
            SetFilter(x, s, p) => {
                let s = self.eval(s, env)?;
                let mut out = BTreeSet::new();
                for v in s.as_set()? {
                    let mut env2 = env.clone();
                    env2.insert(x.clone(), v.clone());
                    if self.eval(p, &env2)?.as_bool()? {
                        out.insert(v.clone());
                    }
                }
                Value::Set(out)
            }
            SetMap(f, bs) => {
                let mut out = BTreeSet::new();
                self.each_binding(bs, env, &mut |env2| {
                    out.insert(self.eval(f, env2)?);
                    Ok(true)
                })?;
                Value::Set(out)
            }
            FunCons(x, s, body) => {
                let s = self.eval(s, env)?;
                let mut m = BTreeMap::new();
                for v in s.as_set()? {
                    let mut env2 = env.clone();
                    env2.insert(x.clone(), v.clone());
                    m.insert(v.clone(), self.eval(body, &env2)?);
                }
                fun_value(m)
            }
            FunSet(d, r) => {
                let d: Vec<Value> = self.eval(d, env)?.as_set()?.iter().cloned().collect();
                let r: Vec<Value> = self.eval(r, env)?.as_set()?.iter().cloned().collect();
                let total = (r.len() as f64).powi(d.len() as i32);
                if total > ENUM_LIMIT as f64 {
                    return Err("function set too large to enumerate".into());
                }
                let mut out = BTreeSet::new();
                let mut idx = vec![0usize; d.len()];
                if r.is_empty() && !d.is_empty() {
                    return Ok(Value::Set(out));
                }
                loop {
                    out.insert(fun_value(d.iter().cloned().zip(idx.iter().map(|&i| r[i].clone())).collect()));
                    let mut k = 0;
                    while k < idx.len() {
                        idx[k] += 1;
                        if idx[k] < r.len() {
                            break;
                        }
                        idx[k] = 0;
                        k += 1;
                    }
                    if k == idx.len() {
                        break;
                    }
                }
                Value::Set(out)
            }
            RecLit(fs) => Value::Rec(fs.iter().map(|(k, v)| Ok((k.clone(), self.eval(v, env)?))).collect::<R<_>>()?),
            RecSet(fs) => {
                let mut out = vec![BTreeMap::new()];
                for (k, s) in fs {
                    let s = self.eval(s, env)?;
                    let mut next = vec![];
                    for r in &out {
                        for v in s.as_set()? {
                            let mut r2: BTreeMap<String, Value> = r.clone();
                            r2.insert(k.clone(), v.clone());
                            next.push(r2);
                        }
                    }
                    out = next;
                    if out.len() > ENUM_LIMIT {
                        return Err("record set too large".into());
                    }
                }
                Value::Set(out.into_iter().map(Value::Rec).collect())
            }
            App(f, x) => {
                let f = self.eval(f, env)?;
                let x = self.eval(x, env)?;
                match f {
                    Value::Fun(m) => m.get(&x).cloned().ok_or("function applied outside its domain")?,
                    Value::Tuple(t) => {
                        let i = x.as_int()?;
                        t.get((i - 1) as usize).cloned().ok_or("tuple index out of range")?
                    }
                    _ => return Err("application of a non-function".into()),
                }
            }
            Field(r, k) => match self.eval(r, env)? {
                Value::Rec(m) => m.get(k).cloned().ok_or(format!("no field {k}"))?,
                _ => return Err("field of a non-record".into()),
            },
            Tuple(xs) => Value::Tuple(xs.iter().map(|x| self.eval(x, env)).collect::<R<_>>()?),
            Except(f, ups) => {
                let mut v = self.eval(f, env)?;
                for (path, val) in ups {
                    // The expander appends the name of this update's @ as a field step starting with @
                    let at = path.iter().find_map(|p| match p {
                        Path::Field(k) if k.starts_with('@') => Some(k.clone()),
                        _ => None,
                    });
                    let steps: Vec<&Path> = path.iter().filter(|p| !matches!(p, Path::Field(k) if k.starts_with('@'))).collect();
                    v = self.except_at(v, &steps, val, at.as_deref(), env)?;
                }
                v
            }
            RecCall(i, args) => {
                let rd = crate::expand::rec_def(*i);
                let mut env2 = env.clone();
                for (p, a) in rd.params.iter().zip(args) {
                    env2.insert(p.clone(), self.eval(a, env)?);
                }
                let depth = REC_DEPTH.with(|d| {
                    d.set(d.get() + 1);
                    d.get()
                });
                let r = if depth > REC_LIMIT {
                    Err(format!("`{}` recursed more than {REC_LIMIT} levels deep (TLC overflows its stack)", rd.name))
                } else {
                    self.eval(&rd.body, &env2)
                };
                REC_DEPTH.with(|d| d.set(d.get() - 1));
                r?
            }
            At | Let(..) | Prime(_) | BoxAction(..) | Fair(..) | Lambda(..) => {
                return Err("not a constant expression".into())
            }
        })
    }

    /// `[v EXCEPT !<steps> = val]` for one update. As in TLC, an index outside the domain leaves the
    /// value unchanged
    fn except_at(&self, v: Value, steps: &[&Path], val: &Expr, at: Option<&str>, env: &HashMap<String, Value>) -> R<Value> {
        let Some((step, rest)) = steps.split_first() else {
            let mut env2 = env.clone();
            if let Some(a) = at {
                env2.insert(a.to_string(), v);
            }
            return self.eval(val, &env2);
        };
        Ok(match (step, v) {
            (Path::Idx(i), Value::Fun(mut m)) => {
                let k = self.eval(i, env)?;
                if let Some(old) = m.remove(&k) {
                    m.insert(k, self.except_at(old, rest, val, at, env)?);
                }
                Value::Fun(m)
            }
            (Path::Idx(i), Value::Tuple(mut t)) => {
                let k = self.eval(i, env)?.as_int()?;
                if k >= 1 && (k as usize) <= t.len() {
                    let old = t[k as usize - 1].clone();
                    t[k as usize - 1] = self.except_at(old, rest, val, at, env)?;
                }
                Value::Tuple(t)
            }
            (Path::Field(n), Value::Rec(mut m)) => {
                if let Some(old) = m.remove(n) {
                    m.insert(n.clone(), self.except_at(old, rest, val, at, env)?);
                }
                Value::Rec(m)
            }
            (_, v) => return Err(format!("EXCEPT path does not match the value {v:?}")),
        })
    }

    /// The elements of a sequence value (a tuple)
    fn seq(&self, q: &Expr, env: &HashMap<String, Value>, op: &str) -> R<Vec<Value>> {
        match self.eval(q, env)? {
            Value::Tuple(t) => Ok(t),
            Value::Atom(a) if !self.atoms.list[a as usize].0 => {
                Err(format!("`{op}` on strings is not supported (only Len of a string is)"))
            }
            v => Err(format!("`{op}` of {v:?}, which is not a sequence")),
        }
    }

    /// Iterates over bindings one at a time, stopping when f returns false.
    pub fn each_binding(
        &self,
        bs: &[(String, Expr)],
        env: &HashMap<String, Value>,
        f: &mut dyn FnMut(&HashMap<String, Value>) -> R<bool>,
    ) -> R<bool> {
        if bs.is_empty() {
            return f(env);
        }
        let (x, s) = &bs[0];
        let s = self.eval(s, env)?;
        for v in s.as_set()? {
            let mut env2 = env.clone();
            env2.insert(x.clone(), v.clone());
            if !self.each_binding(&bs[1..], &env2, f)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn bin(&self, op: BOp, a: Value, b: Value) -> R<Value> {
        use BOp::*;
        Ok(match op {
            Implies => Value::Bool(!a.as_bool()? || b.as_bool()?),
            Equiv => Value::Bool(a.as_bool()? == b.as_bool()?),
            LeadsTo => return Err("~> is temporal".into()),
            Eq => Value::Bool(a == b),
            Neq => Value::Bool(a != b),
            Lt => Value::Bool(a.as_int()? < b.as_int()?),
            Le => Value::Bool(a.as_int()? <= b.as_int()?),
            Gt => Value::Bool(a.as_int()? > b.as_int()?),
            Ge => Value::Bool(a.as_int()? >= b.as_int()?),
            In => Value::Bool(b.as_set()?.contains(&a)),
            NotIn => Value::Bool(!b.as_set()?.contains(&a)),
            Subseteq => Value::Bool(a.as_set()?.is_subset(b.as_set()?)),
            Cup => Value::Set(a.as_set()?.union(b.as_set()?).cloned().collect()),
            Cap => Value::Set(a.as_set()?.intersection(b.as_set()?).cloned().collect()),
            SetMinus => Value::Set(a.as_set()?.difference(b.as_set()?).cloned().collect()),
            Range => {
                let (lo, hi) = (a.as_int()?, b.as_int()?);
                if hi - lo > ENUM_LIMIT as i64 {
                    return Err("range too large".into());
                }
                Value::Set((lo..=hi).map(Value::Int).collect())
            }
            Add => Value::Int(a.as_int()? + b.as_int()?),
            Sub => Value::Int(a.as_int()? - b.as_int()?),
            Mul => Value::Int(a.as_int()? * b.as_int()?),
            Div => {
                let (a, b) = (a.as_int()?, b.as_int()?);
                if b == 0 {
                    return Err(EVAL_FAILURES[0].into());
                }
                Value::Int(floor_div(a, b))
            }
            Mod => {
                let (a, b) = (a.as_int()?, b.as_int()?);
                if b <= 0 {
                    return Err(format!("{}, but instead it is: {b}", EVAL_FAILURES[1]));
                }
                Value::Int(a.rem_euclid(b))
            }
        })
    }
}

/// A function value. A function over 1..n is the tuple of its values (TLA+ identifies them, and the
/// empty function is <<>>), so equal values have one form.
pub fn fun_value(m: BTreeMap<Value, Value>) -> Value {
    if m.keys().enumerate().all(|(i, k)| *k == Value::Int(i as i64 + 1)) {
        return Value::Tuple(m.into_values().collect());
    }
    Value::Fun(m)
}

/// The entries of a function value, also of a tuple
pub fn as_fun(v: &Value) -> Option<BTreeMap<Value, Value>> {
    match v {
        Value::Fun(m) => Some(m.clone()),
        Value::Tuple(t) => Some(t.iter().enumerate().map(|(i, x)| (Value::Int(i as i64 + 1), x.clone())).collect()),
        _ => None,
    }
}

/// a^b for b >= 0, or None on overflow
pub fn int_pow(a: i64, b: i64) -> Option<i64> {
    a.checked_pow(u32::try_from(b).ok()?)
}

/// TLA+ \div is floor division
pub fn floor_div(a: i64, b: i64) -> i64 {
    let q = a / b;
    if a % b != 0 && ((a < 0) != (b < 0)) {
        q - 1
    } else {
        q
    }
}
