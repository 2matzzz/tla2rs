//! Compile-time values and an evaluator for constant expressions (used to fold state-free
//! expressions).

use crate::ast::*;
use crate::lexer::R;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

/// Strings and model values. At runtime they are u16 ids. Interning goes through a shared
/// reference, since evaluating a constant expression can build a new string (`"ab" \o "c"`).
#[derive(Default, Debug)]
pub struct Atoms {
    list: std::cell::RefCell<Vec<(bool, String)>>, // (is model value, name)
    map: std::cell::RefCell<HashMap<(bool, String), u32>>,
    /// While Some, the strings that operations (`\o`, ToString, ...) make, in order (see `made`)
    log: std::cell::RefCell<Option<Vec<u32>>>,
}

impl Atoms {
    /// A string made by an operation (TLC creates its string then, which decides where it comes in
    /// TLC's order of strings), noted while a log is kept
    pub fn made(&self, a: u32) -> u32 {
        if let Some(l) = self.log.borrow_mut().as_mut() {
            l.push(a);
        }
        a
    }
    /// Starts noting the strings made, until `log_end`
    pub fn log_start(&self) {
        *self.log.borrow_mut() = Some(vec![]);
    }
    /// The strings made since `log_start`, each once, in the order first made
    pub fn log_end(&self) -> Vec<u32> {
        let mut out: Vec<u32> = vec![];
        for a in self.log.borrow_mut().take().unwrap_or_default() {
            if !out.contains(&a) {
                out.push(a);
            }
        }
        out
    }
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
            (Rec(a), Rec(b)) => a.len().cmp(&b.len()).then_with(|| crate::types::rec_cmp(a, b)),
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
    /// While set, what Print and PrintT print: one line each, as the values printed on it, each
    /// as TLC prints it before pretty-printing (TLC prints those of the constant definitions and
    /// ASSUMEs when it starts)
    pub static PRINTED: std::cell::RefCell<Option<Vec<Vec<String>>>> = const { std::cell::RefCell::new(None) };
}

/// What starts a line recorded in PRINTED that is one of TLC's warnings, as it prints it (not a
/// value)
pub const WARNING_MARK: char = '\u{2}';

/// TLC's warning for an EXCEPT that names an argument or field the value at `at` does not have,
/// recorded with the lines printed (TLC prints it then, unless it printed it before)
fn except_warning(at: &str) {
    record_print(vec![format!("{WARNING_MARK}Warning: The EXCEPT was applied to non-existing fields of the value at\n{at}")]);
}

fn record_print(line: Vec<String>) {
    PRINTS.with(|n| n.set(n.get() + 1));
    PRINTED.with(|p| {
        if let Some(v) = p.borrow_mut().as_mut() {
            v.push(line);
        }
    });
}

thread_local! {
    /// How many times Print and PrintT have printed (a value printed while it was computed is not
    /// kept, see `eval_bound`)
    static PRINTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The expression of each name a BIND label binds (`ast::BIND`, `register_bound`)
    static BOUND: std::cell::RefCell<HashMap<String, Rc<Expr>>> = std::cell::RefCell::new(HashMap::new());
    /// The recursive definitions whose bodies `register_bound` has read
    static BOUND_RECS: std::cell::RefCell<HashSet<usize>> = std::cell::RefCell::new(HashSet::new());
    /// For each bound name, the names its value can depend on (see `free_names`)
    static BOUND_FREE: std::cell::RefCell<HashMap<String, Rc<Vec<String>>>> = std::cell::RefCell::new(HashMap::new());
    /// The values of bound names, by name and the values of the names each depends on, with the
    /// strings made while computing each (noted again where the value is used again, see
    /// `eval_bound`)
    static BOUND_VALUES: std::cell::RefCell<HashMap<(String, Vec<Option<Value>>), (Value, Vec<u32>)>> = std::cell::RefCell::new(HashMap::new());
}

/// Forgets the bound names and their values (the names are fresh for each expansion; the values
/// hold atoms, which are numbered again in each compilation)
pub fn clear_bound() {
    BOUND.with(|b| b.borrow_mut().clear());
    BOUND_RECS.with(|b| b.borrow_mut().clear());
    BOUND_FREE.with(|b| b.borrow_mut().clear());
    BOUND_VALUES.with(|b| b.borrow_mut().clear());
}

/// Notes the names the BIND labels in e bind (also in the recursive definitions e calls), before
/// the constant evaluator evaluates e
pub fn register_bound(e: &Expr) {
    match e {
        Expr::Label(n, args, body) if is_bind(n) => {
            for pair in args.chunks(2) {
                if let [Expr::Ident(x, _), a] = pair {
                    BOUND.with(|b| b.borrow_mut().insert(x.clone(), Rc::new(a.clone())));
                    register_bound(a);
                }
            }
            register_bound(body);
        }
        Expr::RecCall(i, args) => {
            if BOUND_RECS.with(|r| r.borrow_mut().insert(*i)) {
                register_bound(&crate::expand::rec_def(*i).body);
            }
            for a in args {
                register_bound(a);
            }
        }
        e => {
            for c in e.children() {
                register_bound(c);
            }
        }
    }
}

pub fn bound_expr(n: &str) -> Option<Rc<Expr>> {
    BOUND.with(|b| b.borrow().get(n).cloned())
}

/// e without labels, with the expression bound to a name in place of the name
enum Shape<'a> {
    Ref(&'a Expr),
    Bound(Rc<Expr>),
}

impl std::ops::Deref for Shape<'_> {
    type Target = Expr;
    fn deref(&self) -> &Expr {
        match self {
            Shape::Ref(e) => e,
            Shape::Bound(e) => e.strip(),
        }
    }
}

fn shape(e: &Expr) -> Shape<'_> {
    let Expr::Ident(n, _) = e.strip() else { return Shape::Ref(e.strip()) };
    let Some(mut x) = bound_expr(n) else { return Shape::Ref(e.strip()) };
    while let Some(y) = match x.strip() {
        Expr::Ident(m, _) => bound_expr(m),
        _ => None,
    } {
        x = y;
    }
    Shape::Bound(x)
}

/// e with the names bound along its labels and EXCEPTs replaced by their expressions, for
/// `codegen::lazy_fun_string`, which reads how a function constructor is written
fn unbind_spine(e: &Expr) -> Expr {
    match e {
        Expr::Label(n, a, b) => Expr::Label(n.clone(), a.clone(), unbind_spine(b).b()),
        Expr::Except(b, ups) => Expr::Except(unbind_spine(b).b(), ups.clone()),
        Expr::Ident(n, _) => match bound_expr(n) {
            Some(x) => unbind_spine(&x),
            None => e.clone(),
        },
        e => e.clone(),
    }
}

/// The names whose values the value of the bound name n can depend on: the free names of its
/// expression, of the expressions of the names it uses, and of the bodies of the recursive
/// definitions these call (but their parameters). The names are unique (expansion renames bound
/// variables), so a name the evaluator has bound when n is used has the value it had where n was
/// bound
fn bound_free(n: &str, x: &Expr) -> Rc<Vec<String>> {
    if let Some(f) = BOUND_FREE.with(|b| b.borrow().get(n).cloned()) {
        return f;
    }
    let mut fv = FreeNames::default();
    fv.slots.insert(n.to_string());
    fv.walk(x, &mut vec![]);
    let f = Rc::new(fv.out.into_iter().collect::<Vec<_>>());
    BOUND_FREE.with(|b| b.borrow_mut().insert(n.to_string(), f.clone()));
    f
}

#[derive(Default)]
struct FreeNames {
    out: BTreeSet<String>,
    slots: HashSet<String>,
    recs: HashSet<usize>,
}

impl FreeNames {
    fn walk(&mut self, e: &Expr, bound: &mut Vec<String>) {
        use Expr::*;
        let k = bound.len();
        match e {
            Ident(n, _) if bound.contains(n) => {}
            Ident(n, _) => match bound_expr(n) {
                Some(x) => {
                    if self.slots.insert(n.clone()) {
                        self.walk(&x, &mut vec![]);
                    }
                }
                None => {
                    self.out.insert(n.clone());
                }
            },
            Quant(_, bs, body) | SetMap(body, bs) => {
                for (_, s) in bs {
                    self.walk(s, bound);
                }
                bound.extend(bs.iter().map(|(x, _)| x.clone()));
                self.walk(body, bound);
            }
            Choose(x, s, p) | SetFilter(x, s, p) | FunCons(x, s, p) => {
                self.walk(s, bound);
                bound.push(x.clone());
                self.walk(p, bound);
            }
            Lambda(xs, body) => {
                bound.extend(xs.iter().cloned());
                self.walk(body, bound);
            }
            Except(f, ups) => {
                self.walk(f, bound);
                for (path, v) in ups {
                    for p in path {
                        match p {
                            Path::Idx(i) => self.walk(i, bound),
                            Path::Field(at) if at.starts_with('@') => bound.push(at.clone()),
                            Path::Field(_) => {}
                        }
                    }
                    self.walk(v, bound);
                    bound.truncate(k);
                }
            }
            RecCall(i, args) => {
                for a in args {
                    self.walk(a, bound);
                }
                if self.recs.insert(*i) {
                    let rd = crate::expand::rec_def(*i);
                    self.walk(&rd.body, &mut rd.params.clone());
                }
            }
            // The expressions bound are read where their names are used
            Label(n, _, body) if is_bind(n) => self.walk(body, bound),
            e => {
                for c in e.children() {
                    self.walk(c, bound);
                }
            }
        }
        bound.truncate(k);
    }
}

/// TLC's messages for failures that tla2rs evaluates at compile time
pub const DIV_ZERO: &str = "The second argument of \\div is 0.";

thread_local! {
    /// Whether `\div` is that of Naturals (the spec does not load Integers): see `nat_div`
    pub static NAT_DIV: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `a \div b` as TLC's Naturals computes it, measured on TLC 2.19: rounded toward zero, then one
/// less when that is negative and the division is not exact, so `(0 - 1) \div 3` is 0 where
/// Integers (and the floor of the quotient) gives -1
pub fn nat_div(a: i64, b: i64) -> i64 {
    let q = a / b;
    if a % b != 0 && q < 0 { q - 1 } else { q }
}
pub const MOD_NONPOS: &str = "The second argument of % should be a positive number, but instead it is:";
pub const CASE_NONE: &str = "Attempted to evaluate a CASE with no conditions true.";
pub const CHOOSE_NONE: &str = "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.";

/// The starts of the error messages for failures that TLC raises too when it evaluates the same
/// expression (as opposed to expressions tla2rs cannot evaluate here).
const EVAL_FAILURES: [&str; 11] = [
    "Attempted to check equality of string ",
    "The first argument of BagOfAll should be an operator",
    "Attempted to check if ",
    DIV_ZERO,
    MOD_NONPOS,
    CASE_NONE,
    CHOOSE_NONE,
    "function applied outside its domain",
    "tuple index out of range",
    "no field ",
    "TLC attempted to evaluate an unbounded ",
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
    /// The entries of a function value, also of a tuple or a record (the function over strings it
    /// is, its names numbered in TLC's order of names as for DOMAIN)
    fn entries(&self, v: &Value) -> Option<BTreeMap<Value, Value>> {
        let Value::Rec(m) = v else { return as_fun(v) };
        let mut ks: Vec<&String> = m.keys().collect();
        ks.sort_by(|a, b| crate::types::field_cmp(a, b));
        Some(ks.into_iter().map(|k| (Value::Atom(self.atoms.intern(false, k)), m[k].clone())).collect())
    }

    /// How TLC prints `f` when it is a function over a set TLC cannot enumerate (see
    /// `codegen::lazy_fun_string`), else None
    fn lazy_fun_shown(&self, f: &Expr, env: &HashMap<String, Value>) -> Option<String> {
        fn dom(e: &Expr) -> Option<Shape<'_>> {
            match e {
                Expr::Label(_, _, b) | Expr::Except(b, _) => dom(b),
                Expr::FunCons(_, d, _) => Some(Shape::Ref(d)),
                Expr::Ident(n, _) => {
                    let x = bound_expr(n)?;
                    let d = dom(&x)?;
                    Some(Shape::Bound(Rc::new(Expr::clone(&d))))
                }
                _ => None,
            }
        }
        if self.eval(&*dom(f)?, env).is_ok() {
            return None;
        }
        crate::codegen::lazy_fun_string(&unbind_spine(f), &mut |p| self.lazy_set_shown(p, env))
    }

    fn lazy_set_shown(&self, s: &Expr, env: &HashMap<String, Value>) -> Option<String> {
        match &*shape(s) {
            Expr::Ident(n, _) if ["Nat", "Int", "STRING"].contains(&n.as_str()) && !env.contains_key(n) && !self.constants.contains_key(n) => {
                Some(n.clone())
            }
            Expr::Call(f, a) if f == "Seq" && a.len() == 1 => Some(format!("Seq({})", self.lazy_set_shown(&a[0], env)?)),
            Expr::Call(f, parts) if f == "\\X" => {
                let ps: Vec<String> = parts.iter().map(|p| self.lazy_set_shown(p, env)).collect::<Option<_>>()?;
                Some(format!("({})", ps.join(" \\X ")))
            }
            Expr::Bin(BOp::Range, a, b) => match (self.eval(a, env).ok()?, self.eval(b, env).ok()?) {
                (Value::Int(a), Value::Int(b)) => Some(format!("{a}..{b}")),
                _ => None,
            },
            s => Some(crate::compile::show_value(self.atoms, &self.eval(s, env).ok()?)),
        }
    }

    /// The value of the bound name n, whose expression is x: evaluated where n is first used, as
    /// the expression written out there would be, and kept for the values of the names it depends
    /// on. A value whose computation printed is not kept, so it prints again at each use, as before.
    /// The strings made computing it are noted again at each use: code generation notes the
    /// strings a constant part makes where it folds the part (`Gen::note_folded`)
    fn eval_bound(&self, n: &str, x: &Expr, env: &HashMap<String, Value>) -> R<Value> {
        let key = (n.to_string(), bound_free(n, x).iter().map(|k| env.get(k).cloned()).collect::<Vec<_>>());
        if let Some((v, made)) = BOUND_VALUES.with(|b| b.borrow().get(&key).cloned()) {
            for a in made {
                self.atoms.made(a);
            }
            return Ok(v);
        }
        let prints = PRINTS.with(|p| p.get());
        let outer = self.atoms.log.replace(Some(vec![]));
        let v = self.eval(x, env);
        let mut seen = HashSet::new();
        let made: Vec<u32> = self.atoms.log.replace(outer).unwrap_or_default().into_iter().filter(|a| seen.insert(*a)).collect();
        for &a in &made {
            self.atoms.made(a);
        }
        let v = v?;
        if PRINTS.with(|p| p.get()) == prints {
            BOUND_VALUES.with(|b| b.borrow_mut().insert(key, (v.clone(), made)));
        }
        Ok(v)
    }

    /// Whether `eval` computes the value of `[D -> R]` or `[f1 : S1, ...]` (e), without
    /// enumerating it: its parts evaluate to sets, and it has at most ENUM_LIMIT elements
    pub fn enumerable(&self, e: &Expr, env: &HashMap<String, Value>) -> bool {
        match e {
            Expr::FunSet(d, r) => match (self.eval(d, env), self.eval(r, env)) {
                (Ok(Value::Set(d)), Ok(Value::Set(r))) => (r.len() as f64).powi(d.len() as i32) <= ENUM_LIMIT as f64,
                _ => false,
            },
            Expr::RecSet(fs) => {
                let mut n = 1f64;
                for (_, s) in fs {
                    match self.eval(s, env) {
                        Ok(Value::Set(s)) => n *= s.len() as f64,
                        Ok(_) if n == 0.0 => {}
                        _ => return false,
                    }
                    if n > ENUM_LIMIT as f64 {
                        return false;
                    }
                }
                true
            }
            e => self.eval(e, env).is_ok(),
        }
    }

    pub fn eval(&self, e: &Expr, env: &HashMap<String, Value>) -> R<Value> {
        use Expr::*;
        Ok(match e {
            Num(n) => Value::Int(*n),
            Bool(b) => Value::Bool(*b),
            Str(s) => Value::Atom(self.atoms.get(false, s).ok_or("unknown string")?),
            Ident(n, _) => {
                if let Some(v) = env.get(n) {
                    v.clone()
                } else if let Some(x) = bound_expr(n) {
                    self.eval_bound(n, &x, env)?
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
            // TLC gives the position of a CASE or CHOOSE that fails (see ast::AT)
            Label(n, _, b) => match (crate::ast::err_pos_of(n), self.eval(b, env)) {
                (Some(p), Err(m)) if m == CASE_NONE || m == CHOOSE_NONE => return Err(format!("{m}\n{p}")),
                (_, r) => r?,
            },
            Call(f, args) => match (f.as_str(), args.as_slice()) {
                (f, []) if crate::parser::unbounded_error(f).is_some() => return Err(crate::parser::unbounded_error(f).unwrap()),
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
                ("IsFiniteSet", [s]) if matches!(&*shape(s), Ident(n, _) if ["Nat", "Int", "STRING"].contains(&n.as_str()) && !env.contains_key(n) && !self.constants.contains_key(n)) => {
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
                        let v = self.eval(m, env)?;
                        return Err(format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{}", crate::compile::show_value(self.atoms, &v)));
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
                    (a, b) if self.entries(&a).is_some() && self.entries(&b).is_some() => {
                        let mut a = self.entries(&a).unwrap();
                        for (k, v) in self.entries(&b).unwrap() {
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
                    Value::Atom(self.atoms.made(self.atoms.intern(false, &out)))
                }
                ("ToString", [x]) if self.lazy_fun_shown(x, env).is_some() => {
                    let s = self.lazy_fun_shown(x, env).unwrap();
                    Value::Atom(self.atoms.made(self.atoms.intern(false, &s)))
                }
                ("ToString", [x]) => {
                    let v = self.eval(x, env)?;
                    if let Some((a, b)) = disordered_in(&v) {
                        return Err(crate::types::disordered_error(&a, &b));
                    }
                    Value::Atom(self.atoms.made(self.atoms.intern(false, &crate::compile::show_value(self.atoms, &v))))
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
                    let mut env2 = env.clone();
                    for (k, c) in self.bag(b, env)? {
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
                    let mut env2 = env.clone();
                    for x in t {
                        env2.insert(ps[0].clone(), x.clone());
                        if self.eval(body, &env2)?.as_bool()? {
                            out.push(x);
                        }
                    }
                    Value::Tuple(out)
                }
                ("PrintT", [x]) => {
                    let x = match self.lazy_fun_shown(x, env) {
                        Some(s) => s,
                        None => crate::compile::show_value(self.atoms, &self.eval(x, env)?),
                    };
                    record_print(vec![x]);
                    Value::Bool(true)
                }
                ("Print", [x, v]) => {
                    let x = match self.lazy_fun_shown(x, env) {
                        Some(s) => s,
                        None => crate::compile::show_value(self.atoms, &self.eval(x, env)?),
                    };
                    let v = self.eval(v, env)?;
                    record_print(vec![x, crate::compile::show_value(self.atoms, &v)]);
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
                        // The names in TLC's order of names (`types::field_cmp`), so that names not
                        // numbered yet are numbered in that order
                        Value::Rec(m) => {
                            let mut ks: Vec<&String> = m.keys().collect();
                            ks.sort_by(|a, b| crate::types::field_cmp(a, b));
                            Value::Set(ks.into_iter().map(|k| Value::Atom(self.atoms.intern(false, k))).collect())
                        }
                        _ => return Err("DOMAIN of a non-function".into()),
                    },
                    _ => return Err(format!("{op:?} is not a constant operator")),
                }
            }
            // `x \in Nat` / `x \in Int` (common in assumptions), also inside `\`, `\cup`, `\cap` and
            // `{y \in S : P}` (`N \in Nat \ {0}`). The set itself can't be built, so only test membership
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if self.lazy_set(set, env) => {
                let inside = self.member(&self.eval(x, env)?, set, env)?;
                Value::Bool(inside == matches!(op, BOp::In))
            }
            // x \in [D -> R]: decided without enumerating the set of functions
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if matches!(&*shape(set), FunSet(..)) => {
                let v = self.eval(x, env)?;
                Value::Bool(self.member(&v, set, env)? == matches!(op, BOp::In))
            }
            // S \subseteq T with T such a set (`R \subseteq Nat \ {0}`): each element of S in T
            Bin(BOp::Subseteq, x, set) if self.lazy_set(set, env) => {
                let mut all = true;
                for v in self.eval(x, env)?.as_set()? {
                    all &= self.member(v, set, env)?;
                }
                Value::Bool(all)
            }
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if matches!(&*shape(set), Call(f, a) if f == "Seq" && a.len() == 1) => {
                let set = shape(set);
                let Call(_, a) = &*set else { unreachable!() };
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
            // An integer in lo..hi: compared with the bounds, without building the interval
            Bin(op @ (BOp::In | BOp::NotIn), x, set) if matches!(&*shape(set), Bin(BOp::Range, ..)) => {
                let v = self.eval(x, env)?;
                let set = shape(set);
                let Bin(_, lo, hi) = &*set else { unreachable!() };
                let (lo, hi) = (self.eval(lo, env)?, self.eval(hi, env)?);
                match (&v, &lo, &hi) {
                    (Value::Int(i), Value::Int(l), Value::Int(h)) if (*h as i128 - *l as i128) <= ENUM_LIMIT as i128 => {
                        Value::Bool((l <= i && i <= h) == matches!(op, BOp::In))
                    }
                    _ => {
                        let s = self.bin(BOp::Range, lo, hi)?;
                        self.bin(*op, v, s)?
                    }
                }
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
                    None => return Err(CASE_NONE.into()),
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
                let mut env2 = env.clone();
                for v in s.as_set()? {
                    env2.insert(x.clone(), v.clone());
                    if self.eval(p, &env2)?.as_bool()? {
                        return Ok(v.clone());
                    }
                }
                return Err(CHOOSE_NONE.into());
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
                s.as_set()?;
                let Value::Set(s) = s else { unreachable!() };
                // The elements kept are in order, so the set is built from them without searching
                let mut out = vec![];
                let mut env2 = env.clone();
                for v in s {
                    env2.insert(x.clone(), v.clone());
                    if self.eval(p, &env2)?.as_bool()? {
                        out.push(v);
                    }
                }
                Value::Set(out.into_iter().collect())
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
                let mut env2 = env.clone();
                for v in s.as_set()? {
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
                // Over 1..n (the elements of d in order) the functions are tuples (see fun_value)
                let tuples = d.iter().enumerate().all(|(i, k)| *k == Value::Int(i as i64 + 1));
                loop {
                    if tuples {
                        out.insert(Value::Tuple(idx.iter().map(|&i| r[i].clone()).collect()));
                    } else {
                        out.insert(fun_value(d.iter().cloned().zip(idx.iter().map(|&i| r[i].clone())).collect()));
                    }
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
            App(f, x) if matches!(&*shape(f), FunCons(..)) => {
                let f = shape(f);
                let FunCons(y, s, body) = &*f else { unreachable!() };
                let x = self.eval(x, env)?;
                if !self.member(&x, s, env)? {
                    return Err("function applied outside its domain".into());
                }
                let mut env2 = env.clone();
                env2.insert(y.clone(), x);
                self.eval(body, &env2)?
            }
            // [[y \in S |-> e] EXCEPT ![k] = v][x] with S not enumerable: as above, with TLC's
            // warning for a key outside S
            App(f, x) if self.lazy_except(f, env) => {
                let x = self.eval(x, env)?;
                self.lazy_except_apply(f, &x, env, true)?
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
                    // r[d] with d a string, as for a function over the field names
                    Value::Rec(m) => match x {
                        Value::Atom(a) => m.iter().find(|(k, _)| self.atoms.intern(false, k) == a).map(|(_, v)| v.clone()).ok_or("function applied outside its domain")?,
                        _ => return Err("function applied outside its domain".into()),
                    },
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
                let warn = except_pos(f);
                for (path, val) in ups {
                    // The expander appends the name of this update's @ as a field step starting with @
                    let at = path.iter().find_map(|p| match p {
                        Path::Field(k) if k.starts_with('@') => Some(k.clone()),
                        _ => None,
                    });
                    let steps: Vec<&Path> = path.iter().filter(|p| !matches!(p, Path::Field(k) if k.starts_with('@'))).collect();
                    v = self.except_at(v, &steps, val, at.as_deref(), env, warn.as_deref())?;
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

    /// Whether f is `[[y \in S |-> e] EXCEPT ![k] = v, ...]` (EXCEPT one or more times, one key
    /// per update) with S a set TLC does not enumerate
    fn lazy_except(&self, f: &Expr, env: &HashMap<String, Value>) -> bool {
        let f = shape(f);
        let Expr::Except(base, ups) = &*f else { return false };
        let one_key = ups.iter().all(|(p, _)| p.iter().filter(|s| !matches!(s, Path::Field(k) if k.starts_with('@'))).count() == 1 && matches!(p.first(), Some(Path::Idx(_))));
        one_key && (self.lazy_except(base, env) || matches!(&*shape(base), Expr::FunCons(_, s, _) if self.lazy_set(s, env)))
    }

    /// `f[x]` for f as `lazy_except` accepts: TLC evaluates each update's key (and warns when it
    /// is outside the domain), then applies the function
    /// (with `warn` false, as the value before an update, whose keys were evaluated already)
    fn lazy_except_apply(&self, f: &Expr, x: &Value, env: &HashMap<String, Value>, warn: bool) -> R<Value> {
        let f = shape(f);
        match &*f {
            Expr::FunCons(y, s, body) => {
                if !self.member(x, s, env)? {
                    // Not folded: the checker reports it with TLC's message (`Gen::lazy_apply`)
                    return Err("a function over a set TLC does not enumerate applied outside its domain".into());
                }
                let mut env2 = env.clone();
                env2.insert(y.clone(), x.clone());
                self.eval(body, &env2)
            }
            Expr::Except(base, ups) => {
                let mut dom = base.as_ref().clone();
                while let Expr::Except(b, _) = &*shape(&dom) {
                    dom = b.as_ref().clone();
                }
                let Expr::FunCons(_, s, _) = &*shape(&dom) else { return Err("not a function".into()) };
                let s = s.as_ref().clone();
                let at = except_pos(base).filter(|_| warn);
                let mut hit = None;
                for (i, (path, _)) in ups.iter().enumerate() {
                    let Some(Path::Idx(k)) = path.first() else { unreachable!() };
                    let k = self.eval(k, env)?;
                    if !self.member(&k, &s, env)? {
                        if let Some(w) = &at {
                            except_warning(w);
                        }
                    } else if k == *x {
                        hit = Some(i);
                    }
                }
                match hit {
                    None => self.lazy_except_apply(base, x, env, warn),
                    Some(i) => {
                        let (path, val) = &ups[i];
                        let prev = if i == 0 { base.as_ref().clone() } else { Expr::Except(base.clone(), ups[..i].to_vec()) };
                        let mut env2 = env.clone();
                        if let Some(Path::Field(a)) = path.iter().find(|p| matches!(p, Path::Field(k) if k.starts_with('@'))) {
                            if val.any(&|e| matches!(e, Expr::Ident(n, _) if n == a)) {
                                env2.insert(a.clone(), self.lazy_except_apply(&prev, x, env, false)?);
                            }
                        }
                        self.eval(val, &env2)
                    }
                }
            }
            _ => Err("not a function".into()),
        }
    }

    /// `[v EXCEPT !<steps> = val]` for one update. As in TLC, an index outside the domain leaves the
    /// value unchanged
    fn except_at(&self, v: Value, steps: &[&Path], val: &Expr, at: Option<&str>, env: &HashMap<String, Value>, warn: Option<&str>) -> R<Value> {
        let missing = || {
            if let Some(w) = warn {
                except_warning(w);
            }
        };
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
                match m.remove(&k) {
                    Some(old) => {
                        m.insert(k, self.except_at(old, rest, val, at, env, warn)?);
                    }
                    None => missing(),
                }
                Value::Fun(m)
            }
            (Path::Idx(i), Value::Tuple(mut t)) => {
                let k = self.eval(i, env)?.as_int()?;
                if k >= 1 && (k as usize) <= t.len() {
                    let old = t[k as usize - 1].clone();
                    t[k as usize - 1] = self.except_at(old, rest, val, at, env, warn)?;
                } else {
                    missing();
                }
                Value::Tuple(t)
            }
            (Path::Field(n), Value::Rec(mut m)) => {
                match m.remove(n) {
                    Some(old) => {
                        m.insert(n.clone(), self.except_at(old, rest, val, at, env, warn)?);
                    }
                    None => missing(),
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
        let shaped = shape(set);
        match &*shaped {
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
            Expr::Ident(n, _) if ["Nat", "Int", "STRING", "Any"].contains(&n.as_str()) && !env.contains_key(n) && !self.constants.contains_key(n) => {
                self.in_builtin_set(n, v.clone())
            }
            // TLC tests membership in these without building the set: the right operand of `\` only
            // when v is in the left one, the right one of `\cup` only when v is not in the left one
            Expr::Bin(op @ (BOp::Cup | BOp::Cap | BOp::SetMinus), a, b) if self.lazy_set(set, env) => {
                let in_a = self.member(v, a, env)?;
                Ok(match op {
                    BOp::Cup => in_a || self.member(v, b, env)?,
                    BOp::Cap => in_a && self.member(v, b, env)?,
                    _ => in_a && !self.member(v, b, env)?,
                })
            }
            // A product with such a set (the domain of `f[n \in Nat, x \in S]`): component by
            // component. TLC answers FALSE for a string or model value and fails on any other value
            // that is not a tuple
            Expr::Call(f, parts) if f == "\\X" && self.lazy_set(set, env) => match v {
                Value::Tuple(t) if t.len() == parts.len() => {
                    for (x, p) in t.iter().zip(parts) {
                        if !self.member(x, p, env)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                Value::Tuple(_) | Value::Atom(_) => Ok(false),
                v => Err(format!("Attempted to check if the value:\n{}\nis an element of a cartesian product.", crate::compile::show_value(self.atoms, v))),
            },
            Expr::SetFilter(x, s, p) if self.lazy_set(set, env) => {
                if !self.member(v, s, env)? {
                    return Ok(false);
                }
                let mut env = env.clone();
                env.insert(x.clone(), v.clone());
                self.eval(p, &env)?.as_bool()
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

    /// Whether `set` cannot be built because it is, or is made with `\`, `\cup`, `\cap` or a filter
    /// from, Nat, Int, STRING or TLC's Any
    fn lazy_set(&self, set: &Expr, env: &HashMap<String, Value>) -> bool {
        match &*shape(set) {
            Expr::Ident(n, _) => ["Nat", "Int", "STRING", "Any"].contains(&n.as_str()) && !env.contains_key(n) && !self.constants.contains_key(n),
            Expr::Bin(BOp::Cup | BOp::Cap | BOp::SetMinus, a, b) => self.lazy_set(a, env) || self.lazy_set(b, env),
            Expr::SetFilter(_, s, _) => self.lazy_set(s, env),
            Expr::Call(f, parts) if f == "\\X" => parts.iter().any(|p| self.lazy_set(p, env)),
            _ => false,
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
        let mut env2 = env.clone();
        for v in s.as_set()? {
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
                    return Err(DIV_ZERO.into());
                }
                Value::Int(if NAT_DIV.with(|n| n.get()) { nat_div(a, b) } else { floor_div(a, b) })
            }
            Mod => {
                let (a, b) = (a.as_int()?, b.as_int()?);
                if b <= 0 {
                    return Err(format!("{MOD_NONPOS}\n{b}"));
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
