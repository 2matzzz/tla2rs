//! A bound on the length of every sequence the spec builds, found by running Init and Next over
//! lengths instead of values until the lengths of the variables stop growing. A length test such
//! as `Len(q) < 3` in a conjunction bounds `q` in the rest of that conjunction. The bound is
//! only used when it settles and every sequence-building expression has a known length;
//! otherwise the caller falls back to its heuristics.

use crate::ast::*;
use crate::value::Value;
use std::collections::HashMap;

/// Lengths of a value: `top` bounds the value itself when it is a sequence, `inner` bounds every
/// sequence nested inside it
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
struct Len {
    top: usize,
    inner: usize,
}

impl Len {
    fn deep(self) -> usize {
        self.top.max(self.inner)
    }
    fn flat(n: usize) -> Len {
        Len { top: n, inner: n }
    }
    fn max(self, o: Len) -> Len {
        Len { top: self.top.max(o.top), inner: self.inner.max(o.inner) }
    }
    /// A value that is not a sequence, holding values of these lengths
    fn holding(x: Len) -> Len {
        Len { top: 0, inner: x.deep() }
    }
    /// An element of a sequence, function, or set of these lengths
    fn element(self) -> Len {
        Len::flat(self.inner)
    }
}

/// Longest sequence length tracked; beyond it the lengths are taken not to settle
const LIMIT: usize = 1024;

struct Walk<'a> {
    vars: &'a [String],
    constants: &'a HashMap<String, Value>,
    /// Lengths of the variables so far
    bound: HashMap<String, Len>,
    /// Lengths assigned to the variables in this round
    assigned: HashMap<String, Len>,
    /// The longest sequence built anywhere
    longest: usize,
}

type Env = HashMap<String, Len>;
/// Bounds from length tests: (expression, its longest length)
type Facts = Vec<(Expr, usize)>;

fn norm(e: &Expr) -> Expr {
    match e {
        Expr::Label(_, _, b) => norm(b),
        _ => crate::codegen::map_children(e, &norm),
    }
}

fn value_len(v: &Value) -> Len {
    match v {
        Value::Tuple(t) => Len { top: t.len(), inner: t.iter().map(|x| value_len(x).deep()).max().unwrap_or(0) },
        Value::Set(s) => Len::holding(s.iter().map(value_len).fold(Len::default(), Len::max)),
        Value::Fun(m) => Len::holding(m.iter().map(|(k, x)| value_len(k).max(value_len(x))).fold(Len::default(), Len::max)),
        Value::Rec(m) => Len::holding(m.values().map(value_len).fold(Len::default(), Len::max)),
        _ => Len::default(),
    }
}

/// The bounds `Len(e) <= k` stated by a conjunct (with k a number)
fn facts_of(c: &Expr, out: &mut Facts) {
    let len_of = |x: &Expr| match x.strip() {
        Expr::Call(f, a) if f == "Len" && a.len() == 1 => Some(norm(&a[0])),
        _ => None,
    };
    let num = |x: &Expr| match x.strip() {
        Expr::Num(n) => Some(*n),
        _ => None,
    };
    let (e, k) = match c.strip() {
        Expr::And(xs) => return xs.iter().for_each(|x| facts_of(x, out)),
        Expr::Bin(BOp::Lt, a, b) => match (len_of(a), num(b)) {
            (Some(e), Some(k)) => (e, k - 1),
            _ => return,
        },
        Expr::Bin(BOp::Le | BOp::Eq, a, b) => match (len_of(a), num(b)) {
            (Some(e), Some(k)) => (e, k),
            _ => return,
        },
        Expr::Bin(BOp::Gt, a, b) => match (num(a), len_of(b)) {
            (Some(k), Some(e)) => (e, k - 1),
            _ => return,
        },
        Expr::Bin(BOp::Ge, a, b) => match (num(a), len_of(b)) {
            (Some(k), Some(e)) => (e, k),
            _ => return,
        },
        _ => return,
    };
    out.push((e, k.max(0) as usize));
}

impl Walk<'_> {
    fn note(&mut self, l: Len) -> Len {
        self.longest = self.longest.max(l.deep());
        l
    }

    fn assign(&mut self, v: &str, l: Len) {
        let e = self.assigned.entry(v.to_string()).or_default();
        *e = e.max(l);
    }

    /// The lengths of e's value; None when they are unknown
    fn len(&mut self, e: &Expr, env: &Env, facts: &Facts, init: bool) -> Option<Len> {
        let l = self.len_inner(e, env, facts, init)?;
        // A length test on this very expression bounds it
        let l = if facts.is_empty() || matches!(e, Expr::Label(..)) {
            l
        } else {
            let n = norm(e);
            match facts.iter().filter(|(f, _)| *f == n).map(|(_, k)| *k).min() {
                Some(k) => Len { top: l.top.min(k), inner: l.inner },
                None => l,
            }
        };
        if l.deep() > LIMIT {
            return None;
        }
        Some(self.note(l))
    }

    fn all(&mut self, xs: &[Expr], env: &Env, facts: &Facts, init: bool) -> Option<Len> {
        let mut out = Len::default();
        for x in xs {
            out = out.max(self.len(x, env, facts, init)?);
        }
        Some(out)
    }

    fn len_inner(&mut self, e: &Expr, env: &Env, facts: &Facts, init: bool) -> Option<Len> {
        use Expr::*;
        let mut env2 = env.clone();
        Some(match e {
            Num(_) | Bool(_) => Len::default(),
            // A string becomes a sequence of characters under SelectSeq, SortSeq and \o with a tuple
            Str(x) => Len::flat(x.chars().count()),
            Ident(n, _) => match env.get(n) {
                Some(l) => *l,
                None if self.vars.contains(n) => self.bound.get(n).copied().unwrap_or_default(),
                None => match self.constants.get(n) {
                    Some(v) => value_len(v),
                    None if ["Nat", "Int", "BOOLEAN", "STRING", "EmptyBag"].contains(&n.as_str()) || n.starts_with("@model:") => Len::default(),
                    None => return None,
                },
            },
            At => *env.get("@")?,
            Label(_, _, b) => self.len(b, env, facts, init)?,
            Prime(x) => self.len(x, env, facts, init)?,
            Tuple(xs) => {
                let inner = self.all(xs, env, facts, init)?.deep();
                Len { top: xs.len(), inner }
            }
            // Conjuncts bound each other's lengths; assignments record the lengths of variables
            And(xs) => {
                let mut f2 = facts.clone();
                for x in xs {
                    facts_of(x, &mut f2);
                }
                for x in xs {
                    self.len(x, env, &f2, init)?;
                }
                Len::default()
            }
            Bin(op @ (BOp::Eq | BOp::In), a, b) => {
                let target = match (a.strip(), init) {
                    (Prime(v), false) => match v.strip() {
                        Ident(n, _) if self.vars.contains(n) => Some(n.clone()),
                        _ => None,
                    },
                    (Ident(n, _), true) if self.vars.contains(n) => Some(n.clone()),
                    _ => None,
                };
                let lb = self.len(b, env, facts, init)?;
                self.len(a, env, facts, init)?;
                if let Some(v) = target {
                    self.assign(&v, if *op == BOp::Eq { lb } else { lb.element() });
                }
                Len::default()
            }
            If(c, a, b) => {
                let mut f2 = facts.clone();
                facts_of(c, &mut f2);
                self.len(c, env, facts, init)?;
                self.len(a, env, &f2, init)?.max(self.len(b, env, facts, init)?)
            }
            Case(arms, o) => {
                let mut out = Len::default();
                for (p, v) in arms {
                    let mut f2 = facts.clone();
                    facts_of(p, &mut f2);
                    self.len(p, env, facts, init)?;
                    out = out.max(self.len(v, env, &f2, init)?);
                }
                if let Some(o) = o {
                    out = out.max(self.len(o, env, facts, init)?);
                }
                out
            }
            Quant(_, bs, body) => {
                for (x, s) in bs {
                    let l = self.len(s, &env2, facts, init)?;
                    env2.insert(x.clone(), l.element());
                }
                self.len(body, &env2, facts, init)?;
                Len::default()
            }
            SetMap(f, bs) => {
                for (x, s) in bs {
                    let l = self.len(s, &env2, facts, init)?;
                    env2.insert(x.clone(), l.element());
                }
                Len::holding(self.len(f, &env2, facts, init)?)
            }
            Choose(x, s, p) | SetFilter(x, s, p) => {
                let l = self.len(s, env, facts, init)?;
                env2.insert(x.clone(), l.element());
                self.len(p, &env2, facts, init)?;
                if matches!(e, Choose(..)) { l.element() } else { l }
            }
            FunCons(x, d, b) => {
                let ld = self.len(d, env, facts, init)?;
                env2.insert(x.clone(), ld.element());
                let lb = self.len(b, &env2, facts, init)?;
                Len { top: self.domain_len(d, env, facts, init)?, inner: lb.deep().max(ld.inner) }
            }
            FunSet(d, r) => {
                let ld = self.len(d, env, facts, init)?;
                let lr = self.len(r, env, facts, init)?;
                let top = self.domain_len(d, env, facts, init)?;
                Len::holding(Len { top, inner: lr.inner.max(ld.inner) })
            }
            App(f, x) => {
                self.len(x, env, facts, init)?;
                self.len(f, env, facts, init)?.element()
            }
            Field(r, _) => self.len(r, env, facts, init)?.element(),
            RecLit(fs) => Len::holding(fs.iter().try_fold(Len::default(), |acc, (_, x)| Some(acc.max(self.len(x, env, facts, init)?)))?),
            RecSet(fs) => {
                let mut inner = 0;
                for (_, s) in fs {
                    inner = inner.max(self.len(s, env, facts, init)?.inner);
                }
                Len { top: 0, inner }
            }
            Except(f, ups) => {
                let lf = self.len(f, env, facts, init)?;
                let mut inner = lf.inner;
                for (path, v) in ups {
                    for p in path {
                        if let Path::Idx(i) = p {
                            self.len(i, env, facts, init)?;
                        }
                    }
                    // @ is the value at the path, bounded by a length test on f[i]
                    let mut at = lf.element();
                    if let [Path::Idx(i)] = path.as_slice() {
                        let n = norm(&App(f.clone(), Box::new(i.clone())));
                        if let Some(k) = facts.iter().filter(|(x, _)| *x == n).map(|(_, k)| *k).min() {
                            at.top = at.top.min(k);
                        }
                    }
                    env2.insert("@".into(), at);
                    inner = inner.max(self.len(v, &env2, facts, init)?.deep());
                }
                Len { top: lf.top, inner }
            }
            Call(f, a) => match (f.as_str(), a.as_slice()) {
                ("Append", [s, x]) => {
                    let ls = self.len(s, env, facts, init)?;
                    let lx = self.len(x, env, facts, init)?;
                    Len { top: ls.top + 1, inner: ls.inner.max(lx.deep()) }
                }
                ("\\o", [x, y]) => {
                    let (lx, ly) = (self.len(x, env, facts, init)?, self.len(y, env, facts, init)?);
                    Len { top: lx.top + ly.top, inner: lx.inner.max(ly.inner) }
                }
                ("Tail" | "SubSeq" | "SortSeq" | "SelectSeq", [s, rest @ ..]) => {
                    let mut ls = self.len(s, env, facts, init)?;
                    // Tail of the empty sequence is an error, so a value is one shorter
                    if f == "Tail" {
                        ls.top = ls.top.saturating_sub(1);
                    }
                    for r in rest {
                        if let Lambda(ps, body) = r {
                            for p in ps {
                                env2.insert(p.clone(), ls.element());
                            }
                            self.len(body, &env2, facts, init)?;
                        } else {
                            self.len(r, env, facts, init)?;
                        }
                    }
                    ls
                }
                ("Head", [s]) => self.len(s, env, facts, init)?.element(),
                ("\\X", parts) => {
                    let inner = self.all(parts, env, facts, init)?.inner;
                    Len::holding(Len { top: parts.len(), inner })
                }
                // The set of all sequences over S: its elements have no bound
                ("Seq", _) => return None,
                _ => {
                    // Other operators build no sequence: their value holds at most what their
                    // arguments hold. An operator argument's parameters range over those values.
                    let mut out = Len::default();
                    for x in a.iter().filter(|x| !matches!(x, Lambda(..))) {
                        out = out.max(self.len(x, env, facts, init)?);
                    }
                    for x in a {
                        if let Lambda(ps, body) = x {
                            for p in ps {
                                env2.insert(p.clone(), Len::flat(out.deep()));
                            }
                            out = out.max(self.len(body, &env2, facts, init)?);
                        }
                    }
                    Len::flat(out.deep())
                }
            },
            // A recursive operator may build sequences of any length
            RecCall(..) => return None,
            Let(..) | Lambda(..) => return None,
            Un(UOp::Union | UOp::Subset, x) => Len::holding(self.len(x, env, facts, init)?.element()),
            Bin(BOp::Cup | BOp::Cap | BOp::SetMinus, a, b) => {
                Len::holding(self.len(a, env, facts, init)?.element().max(self.len(b, env, facts, init)?.element()))
            }
            // Everything else yields a Boolean, a number, or a set of numbers (a..b), or is
            // temporal: only its parts are walked
            _ => {
                for c in e.children() {
                    self.len(c, env, facts, init)?;
                }
                Len::default()
            }
        })
    }

    /// The length of a function over `d` taken as a sequence: n for a constant 1..n, Len(e) for
    /// 1..Len(e), and 0 for a domain that is not a range of integers
    fn domain_len(&mut self, d: &Expr, env: &Env, facts: &Facts, init: bool) -> Option<usize> {
        match d.strip() {
            Expr::Bin(BOp::Range, lo, hi) => match (lo.strip(), hi.strip()) {
                (_, Expr::Num(n)) => Some((*n).max(0) as usize),
                (Expr::Num(1), Expr::Call(f, a)) if f == "Len" && a.len() == 1 => Some(self.len(&a[0], env, facts, init)?.top),
                (_, Expr::Ident(n, _)) => match self.constants.get(n) {
                    Some(Value::Int(n)) => Some((*n).max(0) as usize),
                    _ => None,
                },
                _ => None,
            },
            Expr::Un(UOp::Domain, x) => Some(self.len(x, env, facts, init)?.top),
            _ => Some(0),
        }
    }
}

/// The longest sequence the spec builds, if the lengths settle: `init` and `next` are run over
/// lengths until the variables' lengths stop growing, and `others` (invariants, properties,
/// constraints) are walked with those lengths
pub fn settled_bound(vars: &[String], constants: &HashMap<String, Value>, init: &Expr, next: &Expr, others: &[Expr]) -> Option<usize> {
    let mut w = Walk { vars, constants, bound: HashMap::new(), assigned: HashMap::new(), longest: 0 };
    let none = Env::new();
    w.len(init, &none, &vec![], true)?;
    w.bound = std::mem::take(&mut w.assigned);
    // A variable Init gives a value in some other way
    if vars.iter().any(|v| !w.bound.contains_key(v)) {
        return None;
    }
    for _ in 0..=LIMIT {
        w.len(next, &none, &vec![], false)?;
        let mut grew = false;
        for (v, l) in std::mem::take(&mut w.assigned) {
            let b = w.bound.entry(v).or_default();
            let n = b.max(l);
            if n != *b {
                *b = n;
                grew = true;
            }
        }
        if !grew {
            for o in others {
                w.len(o, &none, &vec![], false)?;
            }
            let vars_longest = w.bound.values().map(|l| l.deep()).max().unwrap_or(0);
            return Some(w.longest.max(vars_longest));
        }
    }
    None
}
