//! Compile-time values and an evaluator for constant expressions (used to fold state-free
//! expressions).

use crate::ast::*;
use crate::lexer::R;
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// Strings and model values. At runtime they are u16 ids. Interning goes through a shared
/// reference, since evaluating a constant expression can build a new string (`"ab" \o "c"`).
#[derive(Default, Debug)]
pub struct Atoms {
    list: std::cell::RefCell<Vec<(bool, String)>>, // (is model value, name)
    map: std::cell::RefCell<HashMap<(bool, String), u32>>,
}

impl Atoms {
    pub fn intern(&self, model: bool, s: &str) -> u32 {
        if let Some(&i) = self.map.borrow().get(&(model, s.to_string())) {
            return i;
        }
        let mut list = self.list.borrow_mut();
        let i = list.len() as u32;
        list.push((model, s.to_string()));
        self.map.borrow_mut().insert((model, s.to_string()), i);
        i
    }
    pub fn get(&self, model: bool, s: &str) -> Option<u32> {
        self.map.borrow().get(&(model, s.to_string())).copied()
    }
    pub fn len(&self) -> usize {
        self.list.borrow().len()
    }
    pub fn is_model(&self, a: u32) -> bool {
        self.list.borrow()[a as usize].0
    }
    pub fn name(&self, a: u32) -> String {
        self.list.borrow()[a as usize].1.clone()
    }
    pub fn show(&self, a: u32) -> String {
        let l = self.list.borrow();
        let (m, s) = &l[a as usize];
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
            // As TLC: by the size of the domain, then key and value pair by pair
            (Fun(a), Fun(b)) => a.len().cmp(&b.len()).then_with(|| a.iter().cmp(b.iter())),
            // As TLC: by the number of fields, then name and value pair by pair, in TLC's order of
            // field names
            (Rec(a), Rec(b)) => a.len().cmp(&b.len()).then_with(|| {
                let fa = crate::types::sorted_fields(a.iter().map(|(k, v)| (k.clone(), v)).collect());
                let fb = crate::types::sorted_fields(b.iter().map(|(k, v)| (k.clone(), v)).collect());
                for ((ka, va), (kb, vb)) in fa.iter().zip(&fb) {
                    let c = crate::types::field_cmp(ka, kb).then_with(|| va.cmp(vb));
                    if c.is_ne() {
                        return c;
                    }
                }
                std::cmp::Ordering::Equal
            }),
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

/// How deep a recursive operator may call itself when evaluated at compile time (on a thread with
/// a 1 GB stack). TLC stops with a stack overflow at a depth that depends on its JVM stack and on
/// the operator's body (measured between 500 and 900 levels for small bodies). The limit here only
/// has to catch a recursion that never ends: a recursion that ends computes the value TLA+ gives
/// it, so tla2rs should not stop where TLC succeeds. It goes deeper than TLC instead, which means
/// a recursion between TLC's depth and this one passes here where TLC reports a stack overflow.
/// The generated checker limits by the stack it uses rather than by depth (see REC_STACK_BYTES).
pub const REC_LIMIT: u32 = 50_000;

/// How much stack recursive operators may use in the generated checker, on top of where the
/// first call started: well under the 2 MB a worker thread has, and enough for thousands of
/// levels (more than TLC reaches)
pub const REC_STACK_BYTES: usize = 1 << 20;

thread_local! {
    static REC_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    /// While set, what Print and PrintT print: one line each, as the values printed on it (TLC
    /// prints those of the constant definitions and ASSUMEs when it starts)
    pub static PRINTED: std::cell::RefCell<Option<Vec<Vec<Value>>>> = const { std::cell::RefCell::new(None) };
}

fn record_print(line: Vec<Value>) {
    PRINTED.with(|p| {
        if let Some(v) = p.borrow_mut().as_mut() {
            v.push(line);
        }
    });
}

/// The starts of the error messages for failures that TLC raises too when it evaluates the same
/// expression (as opposed to expressions tla2rs cannot evaluate here).
const EVAL_FAILURES: [&str; 10] = [
    "Attempted to check equality of string ",
    "The first argument of BagOfAll should be an operator",
    "Attempted to check if ",
    "The second argument of \\div is 0.",
    "The second argument of % should be a positive number",
    "Attempted to evaluate a CASE with no conditions true.",
    "CHOOSE: no element satisfies the predicate",
    "function applied outside its domain",
    "tuple index out of range",
    "no field ",
];

/// TLC passes an operator whose body is a number or string literal to BagOfAll as that value, and
/// BagOfAll then stops with this error
pub fn bag_of_all_literal(atoms: &Atoms, body: &Expr) -> Option<String> {
    let v = match body.strip() {
        Expr::Num(n) => Value::Int(*n),
        Expr::Str(s) => Value::Atom(atoms.intern(false, s)),
        _ => return None,
    };
    Some(format!("The first argument of BagOfAll should be an operator, but instead it is:\n{}", crate::compile::show_value(atoms, &v)))
}

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
                } else if n == "EmptyBag" {
                    Value::Tuple(vec![])
                } else {
                    return Err(format!("`{n}` is not a constant"));
                }
            }
            Label(_, _, b) => self.eval(b, env)?,
            Call(f, args) => match (f.as_str(), args.as_slice()) {
                ("Cardinality", [s]) => Value::Int(self.eval(s, env)?.as_set()?.len() as i64),
                // TLC picks an element of its own choosing; only a single element is the same in
                // every run
                ("RandomElement", [s]) => {
                    let v = self.eval(s, env)?;
                    let set = v.as_set()?;
                    if set.len() != 1 {
                        return Err(format!("RandomElement of a set of {} elements: TLC picks one at random, so it is not supported", set.len()));
                    }
                    set.iter().next().unwrap().clone()
                }
                ("IsFiniteSet", [s]) if matches!(s.strip(), Ident(n) if ["Nat", "Int", "STRING"].contains(&n.as_str()) && !env.contains_key(n) && !self.constants.contains_key(n)) => {
                    Value::Bool(false)
                }
                ("IsFiniteSet", [s]) => {
                    self.eval(s, env)?.as_set()?;
                    Value::Bool(true)
                }
                // A function (tuples and records included) whose values are positive integers
                ("IsABag", [b]) => {
                    let pos = |v: &Value| matches!(v, Value::Int(n) if *n > 0);
                    Value::Bool(match self.eval(b, env)? {
                        Value::Rec(m) => m.values().all(pos),
                        v => as_fun(&v).is_some_and(|m| m.values().all(pos)),
                    })
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
                    Value::Atom(a) if !self.atoms.is_model(a) => Value::Int(self.atoms.name(a).chars().count() as i64),
                    v => return Err(format!("Len of {v:?}, which is not a sequence")),
                },
                // TLC treats a string as a sequence of characters for these operators, and their
                // results are strings again
                ("Append" | "Head" | "Tail" | "SubSeq" | "\\o", _) if self.is_str(&args[0], env) => {
                    let a = self.str_arg(&args[0], env)?;
                    let chars: Vec<char> = a.chars().collect();
                    let out: String = match (f.as_str(), args.as_slice()) {
                        ("Append", [_, x]) => a.clone() + &self.str_arg(x, env)?,
                        ("\\o", [_, b]) => a.clone() + &self.str_arg(b, env)?,
                        ("Head", _) => chars.first().ok_or("Attempted to apply Head to the empty sequence.")?.to_string(),
                        ("Tail", _) => {
                            if chars.is_empty() {
                                return Err("Attempted to apply Tail to the empty sequence.".into());
                            }
                            chars[1..].iter().collect()
                        }
                        ("SubSeq", [_, m, n]) => {
                            let (m, n) = (self.eval(m, env)?.as_int()?, self.eval(n, env)?.as_int()?);
                            if m > n {
                                String::new()
                            } else if m < 1 || m > chars.len() as i64 {
                                return Err("The second argument of SubSeq must be in the domain of its first argument.".into());
                            } else if n > chars.len() as i64 {
                                return Err("The third argument of SubSeq must be in the domain of its first argument.".into());
                            } else {
                                chars[(m - 1) as usize..n as usize].iter().collect()
                            }
                        }
                        _ => return Err(format!("`{f}` with {} arguments", args.len())),
                    };
                    Value::Atom(self.atoms.intern(false, &out))
                }
                ("ToString", [x]) => {
                    let v = self.eval(x, env)?;
                    if let Some((a, b)) = disordered_in(&v) {
                        return Err(crate::types::disordered_error(&a, &b));
                    }
                    Value::Atom(self.atoms.intern(false, &crate::compile::show_value(self.atoms, &v)))
                }
                ("TLCEval", [x]) => self.eval(x, env)?,
                // Bags: functions from elements to their (positive) counts
                ("SetToBag", [s]) => fun_value(self.eval(s, env)?.as_set()?.iter().map(|x| (x.clone(), Value::Int(1))).collect()),
                ("BagToSet", [b]) => Value::Set(self.bag(b, env)?.into_keys().collect()),
                ("BagIn", [x, b]) => Value::Bool(self.bag(b, env)?.contains_key(&self.eval(x, env)?)),
                ("CopiesIn", [x, b]) => self.bag(b, env)?.get(&self.eval(x, env)?).cloned().unwrap_or(Value::Int(0)),
                ("\\oplus", [a, b]) => {
                    let mut m = self.bag(a, env)?;
                    for (k, c) in self.bag(b, env)? {
                        let n = m.get(&k).map_or(Ok(0), |v| v.as_int())? + c.as_int()?;
                        m.insert(k, Value::Int(n));
                    }
                    fun_value(m)
                }
                ("\\ominus", [a, b]) => {
                    let mut m = self.bag(a, env)?;
                    for (k, c) in self.bag(b, env)? {
                        if let Some(v) = m.get(&k).cloned() {
                            let n = v.as_int()? - c.as_int()?;
                            if n > 0 {
                                m.insert(k, Value::Int(n));
                            } else {
                                m.remove(&k);
                            }
                        }
                    }
                    fun_value(m)
                }
                ("BagUnion", [s]) => {
                    let mut m: BTreeMap<Value, Value> = BTreeMap::new();
                    for b in self.eval(s, env)?.as_set()? {
                        for (k, c) in as_fun(b).ok_or("BagUnion of a set holding a value that is not a bag")? {
                            let n = m.get(&k).map_or(Ok(0), |v| v.as_int())? + c.as_int()?;
                            m.insert(k, Value::Int(n));
                        }
                    }
                    fun_value(m)
                }
                ("\\sqsubseteq", [a, b]) => {
                    let (a, b) = (self.bag(a, env)?, self.bag(b, env)?);
                    let mut ok = true;
                    for (k, c) in &a {
                        ok &= c.as_int()? <= b.get(k).map_or(Ok(0), |v| v.as_int())?;
                    }
                    Value::Bool(ok)
                }
                ("SubBag", [b]) => {
                    let b: Vec<(Value, i64)> = self.bag(b, env)?.into_iter().map(|(k, c)| Ok((k, c.as_int()?))).collect::<R<_>>()?;
                    let mut out = vec![BTreeMap::new()];
                    for (k, c) in b {
                        let mut next = vec![];
                        for m in &out {
                            for n in 0..=c {
                                let mut m2: BTreeMap<Value, Value> = m.clone();
                                if n > 0 {
                                    m2.insert(k.clone(), Value::Int(n));
                                }
                                next.push(m2);
                            }
                        }
                        out = next;
                        if out.len() > ENUM_LIMIT {
                            return Err("SubBag too large to enumerate".into());
                        }
                    }
                    Value::Set(out.into_iter().map(fun_value).collect())
                }
                ("BagOfAll", [Lambda(ps, body), b]) if ps.len() == 1 => {
                    if let Some(msg) = bag_of_all_literal(self.atoms, body) {
                        return Err(msg);
                    }
                    let mut m: BTreeMap<Value, Value> = BTreeMap::new();
                    for (k, c) in self.bag(b, env)? {
                        let mut env2 = env.clone();
                        env2.insert(ps[0].clone(), k);
                        let y = self.eval(body, &env2)?;
                        let n = m.get(&y).map_or(Ok(0), |v| v.as_int())? + c.as_int()?;
                        m.insert(y, Value::Int(n));
                    }
                    fun_value(m)
                }
                ("BagCardinality", [b]) => Value::Int(self.bag(b, env)?.values().map(|c| c.as_int()).sum::<R<i64>>()?),
                // A stable insertion sort with Op as "comes before"
                ("SortSeq", [q, Lambda(ps, body)]) if ps.len() == 2 => {
                    let mut t = self.seq(q, env, "SortSeq")?;
                    for i in 1..t.len() {
                        let mut j = i;
                        while j > 0 {
                            let mut env2 = env.clone();
                            env2.insert(ps[0].clone(), t[j].clone());
                            env2.insert(ps[1].clone(), t[j - 1].clone());
                            if !self.eval(body, &env2)?.as_bool()? {
                                break;
                            }
                            t.swap(j, j - 1);
                            j -= 1;
                        }
                    }
                    Value::Tuple(t)
                }
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
                    let x = self.eval(x, env)?;
                    record_print(vec![x]);
                    Value::Bool(true)
                }
                ("Print", [x, v]) => {
                    let x = self.eval(x, env)?;
                    let v = self.eval(v, env)?;
                    record_print(vec![x, v.clone()]);
                    v
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
                        out.insert(fun_value(elems.iter().cloned().zip(idx.iter().map(|&i| elems[i].clone())).collect()));
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
                        Value::Rec(m) => Value::Set(m.keys().map(|k| Value::Atom(self.atoms.intern(false, k))).collect()),
                        _ => return Err("DOMAIN of a non-function".into()),
                    },
                    _ => return Err(format!("{op:?} is not a constant operator")),
                }
            }
            // `x \in Nat` / `x \in Int` (common in assumptions). The set itself can't be built, so
            // only test membership
            Bin(op @ (BOp::In | BOp::NotIn), x, set)
                if matches!(set.strip(), Ident(n) if (n == "Nat" || n == "Int" || n == "Any" || n == "STRING")
                    && !env.contains_key(n) && !self.constants.contains_key(n)) =>
            {
                let Ident(n) = set.strip() else { unreachable!() };
                let inside = self.in_builtin_set(n, self.eval(x, env)?)?;
                Value::Bool(inside == matches!(op, BOp::In))
            }
            // x \in [D -> R]: decided without enumerating the set of functions
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if matches!(set.strip(), FunSet(..)) => {
                let v = self.eval(x, env)?;
                Value::Bool(self.member(&v, set, env)? == matches!(op, BOp::In))
            }
            Bin(BOp::Subseteq, x, set)
                if matches!(set.strip(), Ident(n) if (n == "Nat" || n == "Int" || n == "STRING")
                    && !env.contains_key(n) && !self.constants.contains_key(n)) =>
            {
                let Ident(n) = set.strip() else { unreachable!() };
                let mut all = true;
                for v in self.eval(x, env)?.as_set()? {
                    all &= self.in_builtin_set(n, v.clone())?;
                }
                Value::Bool(all)
            }
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if matches!(set.strip(), Call(f, a) if f == "Seq" && a.len() == 1) => {
                let Call(_, a) = set.strip() else { unreachable!() };
                let inside = match self.eval(x, env)? {
                    Value::Tuple(t) => {
                        let s = self.eval(&a[0], env)?;
                        let s = s.as_set()?;
                        t.iter().all(|e| s.contains(e))
                    }
                    // A string is a sequence of one-character strings
                    Value::Atom(c) if !self.atoms.is_model(c) => {
                        let s = self.eval(&a[0], env)?;
                        let s = s.as_set()?;
                        self.atoms.name(c).chars().all(|ch| self.atoms.get(false, &ch.to_string()).is_some_and(|i| s.contains(&Value::Atom(i))))
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
            SetLit(xs) => {
                let vs: Vec<Value> = xs.iter().map(|x| self.eval(x, env)).collect::<R<_>>()?;
                // TLC sorts a set's elements, and stops when that compares a string with an integer
                if vs.iter().any(|a| vs.iter().any(|b| self.str_int(a, b))) {
                    return Err("Attempted to compare a string with an integer in a set".into());
                }
                Value::Set(vs.into_iter().collect())
            }
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
            // [y \in S |-> e][x] is e at x, without the rest of the function (as TLC evaluates it,
            // so S may be Nat)
            App(f, x) if matches!(f.strip(), FunCons(..)) => {
                let FunCons(y, s, body) = f.strip() else { unreachable!() };
                let x = self.eval(x, env)?;
                if !self.member(&x, s, env)? {
                    return Err("function applied outside its domain".into());
                }
                let mut env2 = env.clone();
                env2.insert(y.clone(), x);
                self.eval(body, &env2)?
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

    /// Whether a and b are a string and an integer, which TLC does not compare
    fn str_int(&self, a: &Value, b: &Value) -> bool {
        let s = |v: &Value| matches!(v, Value::Atom(x) if !self.atoms.is_model(*x));
        let i = |v: &Value| matches!(v, Value::Int(_));
        (s(a) && i(b)) || (i(a) && s(b))
    }

    /// Equality as TLC evaluates it: comparing a string with an integer is an error
    /// a = b as TLC evaluates it, with a on the left: TLC asks a whether it equals b. A string
    /// asked about a value that is not a string (nor a model value) stops with an error; a tuple
    /// asked about a string compares it with the string's characters; values that hold strings
    /// and tuples compare part by part in the same way.
    pub fn tlc_eq(&self, a: &Value, b: &Value) -> R<bool> {
        use Value::*;
        let s = |v: &Value| matches!(v, Atom(x) if !self.atoms.is_model(*x));
        if self.str_int(a, b) {
            return Err(format!("Attempted to check equality of {a:?} with {b:?} (a string and an integer)"));
        }
        if s(a) && matches!(b, Tuple(_) | Fun(_) | Rec(_) | Set(_)) {
            return Err(format!(
                "Attempted to check equality of string {} with non-string:\n{}",
                crate::compile::show_value(self.atoms, a),
                crate::compile::show_value(self.atoms, b)
            ));
        }
        let all = |xs: Vec<(&Value, &Value)>| -> R<bool> {
            for (x, y) in xs {
                if !self.tlc_eq(x, y)? {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        Ok(match (a, b) {
            (Tuple(t), Atom(x)) if s(b) => {
                let chars: Vec<Value> = self.atoms.name(*x).chars().map(|c| Atom(self.atoms.intern(false, &c.to_string()))).collect();
                t.len() == chars.len() && all(t.iter().zip(&chars).collect())?
            }
            (Tuple(x), Tuple(y)) => x.len() == y.len() && all(x.iter().zip(y).collect())?,
            (Set(x), Set(y)) => x.len() == y.len() && all(x.iter().zip(y).collect())?,
            (Fun(x), Fun(y)) => x.len() == y.len() && x.keys().eq(y.keys()) && all(x.values().zip(y.values()).collect())?,
            (Rec(x), Rec(y)) => x.len() == y.len() && x.keys().eq(y.keys()) && all(x.values().zip(y.values()).collect())?,
            // A record is the function over its field names
            (Rec(r), Fun(_)) | (Fun(_), Rec(r)) => {
                let as_fun = Fun(r.iter().map(|(k, x)| (Atom(self.atoms.intern(false, k)), x.clone())).collect());
                if matches!(a, Rec(_)) { self.tlc_eq(&as_fun, b)? } else { self.tlc_eq(a, &as_fun)? }
            }
            _ => a == b,
        })
    }

    /// The entries of a bag
    /// Whether `v` is in `set`. A set of functions [D -> R] is not enumerated: a function (records
    /// and tuples included) is in it when its domain is D and its values are in R. TLC answers FALSE
    /// for a model value and stops with an error for any other value that is not a function.
    fn member(&self, v: &Value, set: &Expr, env: &HashMap<String, Value>) -> R<bool> {
        match set.strip() {
            Expr::FunSet(d, r) => {
                let m: BTreeMap<Value, Value> = match v {
                    Value::Rec(m) => m.iter().map(|(k, x)| (Value::Atom(self.atoms.intern(false, k)), x.clone())).collect(),
                    Value::Atom(a) if self.atoms.is_model(*a) => return Ok(false),
                    v => as_fun(v).ok_or_else(|| {
                        format!(
                            "Attempted to check if \n{}\nwhich is not a TLC function value, is in the set of functions:\n{}",
                            crate::compile::show_value(self.atoms, v),
                            crate::codegen::short(set)
                        )
                    })?,
                };
                let dom = self.eval(d, env)?;
                if !m.keys().eq(dom.as_set()?.iter()) {
                    return Ok(false);
                }
                for x in m.values() {
                    if !self.member(x, r, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Expr::Ident(n) if ["Nat", "Int", "STRING", "Any"].contains(&n.as_str()) && !env.contains_key(n) && !self.constants.contains_key(n) => {
                self.in_builtin_set(n, v.clone())
            }
            _ => {
                let s = self.eval(set, env)?;
                let s = s.as_set()?;
                if let Some(e) = s.iter().find(|e| self.str_int(v, e)) {
                    return Err(format!("Attempted to check equality of {v:?} with {e:?} (a string and an integer)"));
                }
                Ok(s.contains(v))
            }
        }
    }

    /// Whether `v` is in the set `n`, which is Nat, Int, STRING, or TLC's Any
    fn in_builtin_set(&self, n: &str, v: Value) -> R<bool> {
        Ok(match v {
            // TLC's Any contains every value
            _ if n == "Any" => true,
            // TRUE for a string, FALSE for a model value, and an error for anything else
            Value::Atom(a) if n == "STRING" => !self.atoms.is_model(a),
            v if n == "STRING" => {
                return Err(format!("Attempted to check if the value:\n{}\nis an element of STRING.", crate::compile::show_value(self.atoms, &v)))
            }
            Value::Int(v) => n == "Int" || v >= 0,
            _ => false,
        })
    }

    fn bag(&self, e: &Expr, env: &HashMap<String, Value>) -> R<BTreeMap<Value, Value>> {
        let v = self.eval(e, env)?;
        as_fun(&v).ok_or(format!("{v:?} is not a bag"))
    }

    /// Whether `e` evaluates to a string
    fn is_str(&self, e: &Expr, env: &HashMap<String, Value>) -> bool {
        matches!(self.eval(e, env), Ok(Value::Atom(a)) if !self.atoms.is_model(a))
    }

    /// The text of a string-valued expression
    fn str_arg(&self, e: &Expr, env: &HashMap<String, Value>) -> R<String> {
        match self.eval(e, env)? {
            Value::Atom(a) if !self.atoms.is_model(a) => Ok(self.atoms.name(a)),
            v => Err(format!("expected a string, got {v:?}")),
        }
    }

    /// The elements of a sequence value (a tuple)
    fn seq(&self, q: &Expr, env: &HashMap<String, Value>, op: &str) -> R<Vec<Value>> {
        match self.eval(q, env)? {
            Value::Tuple(t) => Ok(t),
            Value::Atom(a) if !self.atoms.is_model(a) => {
                Err(format!("`{op}` on strings is not supported (\\o, Len, Head, Tail, Append, and SubSeq are)"))
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
            Eq => Value::Bool(self.tlc_eq(&a, &b)?),
            Neq => Value::Bool(!self.tlc_eq(&a, &b)?),
            Lt => Value::Bool(a.as_int()? < b.as_int()?),
            Le => Value::Bool(a.as_int()? <= b.as_int()?),
            Gt => Value::Bool(a.as_int()? > b.as_int()?),
            Ge => Value::Bool(a.as_int()? >= b.as_int()?),
            In | NotIn => {
                let set = b.as_set()?;
                if let Some(e) = set.iter().find(|e| self.str_int(&a, e)) {
                    return Err(format!("Attempted to check equality of {a:?} with {e:?} (a string and an integer)"));
                }
                // TLC asks each element whether it equals a, which matters when strings meet
                // tuples or records meet functions
                let mixed = |v: &Value| matches!(v, Value::Atom(x) if !self.atoms.is_model(*x)) || matches!(v, Value::Tuple(_) | Value::Rec(_) | Value::Fun(_));
                let inside = if mixed(&a) && set.iter().any(|e| mixed(e) && std::mem::discriminant(e) != std::mem::discriminant(&a)) {
                    let mut found = false;
                    for e in set {
                        if self.tlc_eq(e, &a)? {
                            found = true;
                            break;
                        }
                    }
                    found
                } else {
                    set.contains(&a)
                };
                Value::Bool(inside == (op == In))
            }
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

/// A pair of fields of a record inside v that the spec writes in the order opposite to TLC's
pub fn disordered_in(v: &Value) -> Option<(String, String)> {
    match v {
        Value::Rec(m) => {
            let names: Vec<&str> = m.keys().map(|k| k.as_str()).collect();
            crate::types::disordered_fields(&names).or_else(|| m.values().find_map(disordered_in))
        }
        Value::Set(s) => s.iter().find_map(disordered_in),
        Value::Fun(m) => m.iter().find_map(|(k, x)| disordered_in(k).or_else(|| disordered_in(x))),
        Value::Tuple(t) => t.iter().find_map(disordered_in),
        _ => None,
    }
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
