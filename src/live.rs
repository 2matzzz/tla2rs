//! Liveness: compiles fairness and temporal properties for the product search in the runtime.
//!
//! A property is turned into a formula over atoms (state predicates, `ENABLED A`, and action
//! predicates on the step taken from a state), negated, and translated into a Büchi automaton
//! (`ltl.rs`). Fairness stays outside the automaton, as conditions on the cycles the runtime
//! accepts: WF_v(A) holds on a cycle that has a <<A>>_v step or a state where <<A>>_v is not
//! enabled, SF_v(A) on one that has a <<A>>_v step or none where it is enabled.

use crate::ast::*;
use crate::codegen::{short, Env, Gen};
use crate::lexer::R;
use crate::ltl::{automaton, Ltl};
use crate::types::*;
use crate::value::*;
use std::collections::HashMap;
use std::fmt::Write;

/// A fairness condition: WF (weak) or SF, its action and subscript, and the values of the
/// constant-bound variables they mention
pub struct FairDef {
    pub weak: bool,
    pub action: Expr,
    pub sub: Expr,
    pub env: HashMap<String, Value>,
}

/// Collects the fairness conditions of a spec's fairness conjuncts (also quantified with \A over
/// constant sets, and on actions written inline)
pub fn collect_fair(e: &Expr, env: &HashMap<String, Value>, g: &Gen, out: &mut Vec<FairDef>) -> R<()> {
    match e {
        // TLC does not look into a label written in the spec
        Expr::Label(_, _, b) if !e.is_user_label() => collect_fair(b, env, g, out),
        Expr::And(xs) => xs.iter().try_for_each(|x| collect_fair(x, env, g, out)),
        Expr::Quant(false, bs, body) => {
            let mut err = Ok(());
            g.ce.each_binding(bs, env, &mut |env2| {
                if let Err(m) = collect_fair(body, env2, g, out) {
                    err = Err(m);
                    return Ok(false);
                }
                Ok(true)
            })?;
            err
        }
        // `c => F` with c constant, as in `\A x, y \in S : x # y => WF_v(A(x, y))`: TLC evaluates c
        // to TRUE or FALSE, so the conjunct is F or nothing. Kept out of the property's automaton,
        // which grows exponentially with the fairness conditions in it
        Expr::Bin(BOp::Implies, c, f) => match g.ce.eval(c, env)? {
            Value::Bool(true) => collect_fair(f, env, g, out),
            Value::Bool(false) => Ok(()),
            _ => Err(format!("unsupported fairness formula: {}", short(e))),
        },
        Expr::Fair(weak, sub, a) => {
            out.push(FairDef { weak: *weak, action: a.as_ref().clone(), sub: sub.as_ref().clone(), env: env.clone() });
            Ok(())
        }
        _ => Err(format!("unsupported fairness formula: {}", short(e))),
    }
}

/// A code-generation environment in which the constant-bound variables of `env` are literals
pub fn bind_env(g: &mut Gen, env: &HashMap<String, Value>) -> R<Env> {
    let mut e = Gen::env_next();
    let mut keys: Vec<&String> = env.keys().collect();
    keys.sort();
    for k in keys {
        let v = &env[k];
        let t = ty_of_value(v)?;
        let code = g.lit(v, &t)?;
        e.bind(k, code, t);
    }
    Ok(e)
}

/// Atoms of the temporal properties. State atoms (including ENABLED) are numbered from 0, action
/// atoms from ACTION_BASE.
#[derive(Default)]
struct Atoms {
    state: Vec<(String, String)>,
    action: Vec<(String, String)>,
}

const ACTION_BASE: usize = 64;

fn key(e: &Expr, env: &HashMap<String, Value>) -> String {
    let mut kv: Vec<String> = env.iter().map(|(k, v)| format!("{k}={v:?}")).collect();
    kv.sort();
    format!("{e:?}|{}", kv.join(","))
}

/// `(e)' # e`
fn changed(v: &Expr) -> Expr {
    Expr::Un(UOp::Not, Expr::Bin(BOp::Eq, Expr::Prime(v.clone().b()).b(), v.clone().b()).b())
}

impl Atoms {
    fn state(&mut self, g: &mut Gen, e: &Expr, env: &HashMap<String, Value>) -> R<usize> {
        let k = key(e, env);
        if let Some(i) = self.state.iter().position(|(x, _)| *x == k) {
            return Ok(i);
        }
        let genv = bind_env(g, env)?;
        let c = g.gen_as(e, &genv, &Ty::Bool).map_err(|m| format!("{m}\n  in: {}", short(e)))?;
        self.state.push((k, format!("{{ {c} }}")));
        Ok(self.state.len() - 1)
    }

    fn action(&mut self, g: &mut Gen, e: &Expr, env: &HashMap<String, Value>) -> R<usize> {
        let k = key(e, env);
        if let Some(i) = self.action.iter().position(|(x, _)| *x == k) {
            return Ok(ACTION_BASE + i);
        }
        let genv = bind_env(g, env)?;
        let genv = g.env_step(genv);
        let c = g.gen_as(e, &genv, &Ty::Bool).map_err(|m| format!("{m}\n  in: {}", short(e)))?;
        self.action.push((k, format!("{{ {c} }}")));
        Ok(ACTION_BASE + self.action.len() - 1)
    }
}

/// Whether e has temporal structure (as opposed to being one state or action predicate)
fn temporal(e: &Expr) -> bool {
    e.any(&|x| matches!(x, Expr::Un(UOp::Always | UOp::Eventually, _) | Expr::Bin(BOp::LeadsTo, ..) | Expr::Fair(..)) || x.is_unchecked_temporal())
}

/// Whether e is an action (primes, UNCHANGED or [A]_v outside ENABLED)
fn action_level(e: &Expr) -> bool {
    match e {
        Expr::Prime(_) | Expr::Un(UOp::Unchanged, _) | Expr::BoxAction(..) => true,
        Expr::Un(UOp::Enabled, _) => false,
        _ => e.children().into_iter().any(action_level),
    }
}

/// The marker the parser puts around <<A>>_v
const ANGLE: &str = "<<>>_";

fn is_angle(e: &Expr) -> bool {
    match e {
        Expr::Label(n, _, b) => n == ANGLE || is_angle(b),
        _ => false,
    }
}

fn is_box(e: &Expr) -> bool {
    match e {
        Expr::Label(n, _, b) if n != ANGLE => is_box(b),
        Expr::BoxAction(..) => true,
        _ => false,
    }
}

/// The level of e (0 constant or state, 2 action, 3 temporal), checking the rules of TLA+ that SANY
/// enforces on temporal formulas
pub(crate) fn sany_level(e: &Expr) -> Result<u8, String> {
    use Expr::*;
    Ok(match e {
        Label(n, _, b) if n == ANGLE => {
            sany_level(b)?;
            2
        }
        // The innermost SPAN label around the formula SANY refuses gives its position (see
        // `parser::parse_module_spans`)
        Label(n, _, b) if n.starts_with(crate::ast::SPAN) => match sany_level(b) {
            Err(m) if !m.starts_with(crate::ast::SPAN) => {
                let list = matches!(b.as_ref(), Label(l, ..) if l == crate::parser::LIST);
                let m = match m.split_once(" has both") {
                    Some(("\\land", r)) if list => format!("Conjunction list has both{r}"),
                    Some(("\\lor", r)) if list => format!("Disjunction list has both{r}"),
                    _ => m,
                };
                return Err(format!("{n}\n{m}"));
            }
            r => r?,
        },
        Label(_, _, b) => sany_level(b)?,
        Un(UOp::Enabled, x) => {
            sany_level(x)?;
            1
        }
        Prime(_) | Un(UOp::Unchanged, _) | BoxAction(..) => {
            for c in e.children() {
                sany_level(c)?;
            }
            2
        }
        Fair(..) => 3,
        Un(UOp::Always, x) => {
            if sany_level(x)? == 2 && !is_box(x) {
                return Err("[] followed by action not of form [A]_v.".into());
            }
            3
        }
        Un(UOp::Eventually, x) => {
            if sany_level(x)? == 2 && !is_angle(x) {
                return Err("<> followed by action not of form <<A>>_v.".into());
            }
            3
        }
        Bin(BOp::LeadsTo, a, b) => {
            if sany_level(a)? == 2 || sany_level(b)? == 2 {
                return Err("Action used where only temporal formula or state predicate allowed.".into());
            }
            3
        }
        And(_) | Or(_) | Bin(BOp::Implies | BOp::Equiv, ..) => {
            let ls: Vec<u8> = e.children().into_iter().map(sany_level).collect::<Result<_, _>>()?;
            if ls.contains(&3) && ls.contains(&2) {
                let op = match e {
                    And(_) => "\\land",
                    Or(_) => "\\lor",
                    Bin(BOp::Implies, ..) => "=>",
                    _ => "\\equiv",
                };
                return Err(format!("{op} has both temporal formula and action as arguments."));
            }
            ls.into_iter().max().unwrap_or(0)
        }
        _ => e.children().into_iter().map(sany_level).collect::<Result<Vec<u8>, _>>()?.into_iter().max().unwrap_or(0),
    })
}

/// e with each [A]_v written as A \/ v' = v
fn box_to_or(e: &Expr) -> Expr {
    match e {
        Expr::BoxAction(a, v) => {
            let same = Expr::Bin(BOp::Eq, Expr::Prime(v.clone()).b(), v.clone());
            Expr::Or(vec![box_to_or(a), same])
        }
        _ => crate::codegen::map_children(e, &box_to_or),
    }
}

/// A formula TLC refuses: its message and exit code
pub struct Rejected(pub String, pub i32);

/// TLC's form of a temporal formula (tlc2.tool.liveness.LiveExprNode), used to decide what TLC
/// accepts and when it evaluates each predicate. Atoms are indices into `Atoms` (state from 0,
/// action from ACTION_BASE); FAIR is a fairness atom, which is only classified.
#[derive(Clone, Debug)]
enum TExpr {
    Bool(bool),
    State(usize),
    Action(usize),
    Neg(Box<TExpr>),
    Conj(Vec<TExpr>),
    Disj(Vec<TExpr>),
    All(Box<TExpr>),
    Even(Box<TExpr>),
}

const FAIR: usize = usize::MAX;

impl TExpr {
    fn level(&self) -> u8 {
        match self {
            TExpr::Bool(_) => 0,
            TExpr::State(_) => 1,
            TExpr::Action(_) => 2,
            TExpr::Neg(b) => b.level(),
            TExpr::Conj(xs) | TExpr::Disj(xs) => xs.iter().map(|x| x.level()).max().unwrap_or(0),
            TExpr::All(_) | TExpr::Even(_) => 3,
        }
    }

    fn has_action(&self) -> bool {
        match self {
            TExpr::Action(_) => true,
            TExpr::Bool(_) | TExpr::State(_) => false,
            TExpr::Neg(b) | TExpr::All(b) | TExpr::Even(b) => b.has_action(),
            TExpr::Conj(xs) | TExpr::Disj(xs) => xs.iter().any(|x| x.has_action()),
        }
    }

    /// LNConj.addConj / LNDisj.addDisj: a nested junction of the same kind is spliced in
    fn add(v: &mut Vec<TExpr>, e: TExpr, conj: bool) {
        match e {
            TExpr::Conj(xs) if conj => xs.into_iter().for_each(|x| TExpr::add(v, x, conj)),
            TExpr::Disj(xs) if !conj => xs.into_iter().for_each(|x| TExpr::add(v, x, conj)),
            e => v.push(e),
        }
    }

    fn junction(xs: impl IntoIterator<Item = TExpr>, conj: bool) -> TExpr {
        let mut v = vec![];
        for x in xs {
            TExpr::add(&mut v, x, conj);
        }
        if conj { TExpr::Conj(v) } else { TExpr::Disj(v) }
    }

    /// pushNeg(hasNeg)
    fn push_neg(self, neg: bool) -> TExpr {
        match self {
            TExpr::Bool(b) => TExpr::Bool(b != neg),
            a @ (TExpr::State(_) | TExpr::Action(_)) => {
                if neg { TExpr::Neg(a.into()) } else { a }
            }
            TExpr::Neg(b) => b.push_neg(!neg),
            TExpr::Conj(xs) => TExpr::junction(xs.into_iter().map(|x| x.push_neg(neg)), !neg),
            TExpr::Disj(xs) => TExpr::junction(xs.into_iter().map(|x| x.push_neg(neg)), neg),
            TExpr::All(b) => {
                if neg { TExpr::Even(b.push_neg(true).into()) } else { TExpr::All(b.push_neg(false).into()) }
            }
            TExpr::Even(b) => {
                if neg { TExpr::All(b.push_neg(true).into()) } else { TExpr::Even(b.push_neg(false).into()) }
            }
        }
    }

    /// pushNeg() without an argument
    fn negate(self) -> TExpr {
        match self {
            TExpr::Bool(b) => TExpr::Bool(!b),
            a @ (TExpr::State(_) | TExpr::Action(_)) => TExpr::Neg(a.into()),
            TExpr::Neg(b) => *b,
            TExpr::Conj(xs) => TExpr::junction(xs.into_iter().map(|x| x.negate()), false),
            TExpr::Disj(xs) => TExpr::junction(xs.into_iter().map(|x| x.negate()), true),
            TExpr::All(b) => TExpr::Even(b.negate().into()),
            TExpr::Even(b) => TExpr::All(b.negate().into()),
        }
    }

    fn simplify(self) -> TExpr {
        match self {
            TExpr::Conj(xs) | TExpr::Disj(xs) if false => TExpr::Conj(xs),
            TExpr::Conj(xs) => {
                let mut v = vec![];
                for x in xs {
                    match x.simplify() {
                        TExpr::Bool(false) => return TExpr::Bool(false),
                        TExpr::Bool(true) => {}
                        e => TExpr::add(&mut v, e, true),
                    }
                }
                match v.len() {
                    0 => TExpr::Bool(true),
                    1 => v.pop().unwrap(),
                    _ => TExpr::Conj(v),
                }
            }
            TExpr::Disj(xs) => {
                let mut v = vec![];
                for x in xs {
                    match x.simplify() {
                        TExpr::Bool(true) => return TExpr::Bool(true),
                        TExpr::Bool(false) => {}
                        e => TExpr::add(&mut v, e, false),
                    }
                }
                match v.len() {
                    0 => TExpr::Bool(false),
                    1 => v.pop().unwrap(),
                    _ => TExpr::Disj(v),
                }
            }
            TExpr::Neg(b) => match b.simplify() {
                TExpr::Bool(x) => TExpr::Bool(!x),
                b => TExpr::Neg(b.into()),
            },
            TExpr::All(b) => match b.simplify() {
                TExpr::All(c) => TExpr::All(c),
                b => TExpr::All(b.into()),
            },
            TExpr::Even(b) => match b.simplify() {
                TExpr::Even(c) => TExpr::Even(c),
                b => TExpr::Even(b.into()),
            },
            e => e,
        }
    }

    fn ae_body(&self) -> Option<&TExpr> {
        match self {
            TExpr::All(b) => match b.as_ref() {
                TExpr::Even(c) => Some(c),
                _ => None,
            },
            _ => None,
        }
    }

    fn to_dnf(self) -> TExpr {
        match self {
            TExpr::Conj(xs) => {
                let mut nes = vec![];
                let mut total = 1usize;
                for x in xs {
                    match x.to_dnf() {
                        TExpr::Disj(d) => {
                            total = total.saturating_mul(d.len());
                            nes.push(TExpr::Disj(d));
                        }
                        TExpr::Conj(c) => nes.extend(c),
                        e => nes.push(e),
                    }
                }
                if total == 1 {
                    return TExpr::Conj(nes);
                }
                let mut res: Vec<Vec<TExpr>> = vec![vec![]; total];
                let mut num = 1;
                let mut rcount = total;
                for ln in nes {
                    match ln {
                        TExpr::Disj(d) => {
                            rcount /= d.len();
                            let mut idx = 0;
                            for _ in 0..num {
                                for e in &d {
                                    for _ in 0..rcount {
                                        TExpr::add(&mut res[idx], e.clone(), true);
                                        idx += 1;
                                    }
                                }
                            }
                            num *= d.len();
                        }
                        e => {
                            for r in res.iter_mut() {
                                TExpr::add(r, e.clone(), true);
                            }
                        }
                    }
                }
                TExpr::Disj(res.into_iter().map(TExpr::Conj).collect())
            }
            TExpr::Disj(xs) => {
                let mut ae = vec![];
                let mut res = vec![];
                for x in xs {
                    let items = match x.to_dnf() {
                        TExpr::Disj(d) => d,
                        e => vec![e],
                    };
                    for e in items {
                        match e.ae_body() {
                            Some(b) => TExpr::add(&mut ae, b.clone(), false),
                            None => TExpr::add(&mut res, e, false),
                        }
                    }
                }
                if ae.len() == 1 {
                    let b = ae.pop().unwrap();
                    TExpr::add(&mut res, TExpr::All(TExpr::Even(b.into()).into()), false);
                } else if ae.len() > 1 {
                    TExpr::add(&mut res, TExpr::All(TExpr::Even(TExpr::Disj(ae).into()).into()), false);
                }
                TExpr::Disj(res)
            }
            TExpr::Neg(b) => match *b {
                a @ (TExpr::State(_) | TExpr::Action(_)) => TExpr::Neg(a.into()),
                b => b.negate().to_dnf(),
            },
            e => e,
        }
    }

    fn flatten(self) -> TExpr {
        match self {
            TExpr::Conj(mut xs) if xs.len() == 1 => xs.pop().unwrap().flatten(),
            TExpr::Disj(mut xs) if xs.len() == 1 => xs.pop().unwrap().flatten(),
            TExpr::Conj(xs) => TExpr::junction(xs.into_iter().map(|x| x.flatten()), true),
            TExpr::Disj(xs) => TExpr::junction(xs.into_iter().map(|x| x.flatten()), false),
            TExpr::Neg(b) => match *b {
                TExpr::Neg(c) => c.flatten(),
                b => TExpr::Neg(b.flatten().into()),
            },
            TExpr::All(b) => TExpr::All(b.flatten().into()),
            TExpr::Even(b) => TExpr::Even(b.flatten().into()),
            e => e,
        }
    }

    fn to_ltl(&self) -> Ltl {
        match self {
            TExpr::Bool(b) => Ltl::Bool(*b),
            TExpr::State(i) | TExpr::Action(i) => Ltl::Atom(*i, true),
            TExpr::Neg(b) => b.to_ltl().not(),
            TExpr::Conj(xs) => Ltl::And(xs.iter().map(|x| x.to_ltl()).collect()),
            TExpr::Disj(xs) => Ltl::Or(xs.iter().map(|x| x.to_ltl()).collect()),
            TExpr::All(b) => Ltl::Always(b.to_ltl().into()),
            TExpr::Even(b) => Ltl::Eventually(b.to_ltl().into()),
        }
    }

    fn state_atoms(&self, out: &mut u64) {
        match self {
            TExpr::State(i) if *i != FAIR => *out |= 1 << i,
            TExpr::Neg(b) | TExpr::All(b) | TExpr::Even(b) => b.state_atoms(out),
            TExpr::Conj(xs) | TExpr::Disj(xs) => xs.iter().for_each(|x| x.state_atoms(out)),
            _ => {}
        }
    }
}

/// Turns a property into TLC's form, as tlc2.tool.liveness.Liveness.astToLive does
/// TLC's refusal of the temporal formula e, which it names by position: that of a label or
/// RealTime operator around e (see ast::AT), of the definition e is the body of, or `at`
fn refused(g: &Gen, e: &Expr, at: Option<&str>) -> Rejected {
    let mut x = e;
    let mut pos = None;
    while let Expr::Label(n, args, b) = x {
        if pos.is_none() {
            pos = err_pos_of(n).or_else(|| if args.is_empty() { g.def_pos.get(n).map(|p| p.as_str()) } else { None });
        }
        x = b;
    }
    let what = pos.or(at).map(|p| p.to_string()).unwrap_or_else(|| short(e));
    Rejected(format!("TLC cannot handle the temporal formula {what}"), 255)
}

/// `at` is the position of e as written, if known (see `refused`)
fn to_texpr(g: &mut Gen, e: &Expr, env: &HashMap<String, Value>, atoms: &mut Atoms, at: Option<&str>) -> R<Result<TExpr, Rejected>> {
    use Expr::*;
    // TLC cannot handle a temporal formula under a label written in the spec
    let mut x = e;
    while let Label(_, _, b) = x {
        if x.is_user_label() && temporal(b) {
            return Ok(Err(refused(g, e, at)));
        }
        x = b;
    }
    let e0 = e;
    let e = e.strip();
    if !temporal(e) {
        if let Bool(b) = e {
            return Ok(Ok(TExpr::Bool(*b)));
        }
        return Ok(Ok(if action_level(e) {
            TExpr::Action(atoms.action(g, &box_to_or(e), env)?)
        } else {
            TExpr::State(atoms.state(g, e, env)?)
        }));
    }
    macro_rules! sub {
        ($x:expr) => {
            match to_texpr(g, $x, env, atoms, None)? {
                Ok(t) => t,
                Err(r) => return Ok(Err(r)),
            }
        };
    }
    Ok(Ok(match e {
        And(xs) => {
            let mut v = vec![];
            for x in xs {
                let t = sub!(x);
                TExpr::add(&mut v, t, true);
            }
            TExpr::Conj(v)
        }
        Or(xs) => {
            let mut v = vec![];
            for x in xs {
                let t = sub!(x);
                TExpr::add(&mut v, t, false);
            }
            TExpr::Disj(v)
        }
        Un(UOp::Not, x) => TExpr::Neg(sub!(x).into()),
        Bin(BOp::Implies, a, b) => TExpr::Disj(vec![TExpr::Neg(sub!(a).into()), sub!(b)]),
        Un(UOp::Always, x) => TExpr::All(sub!(x).into()),
        Un(UOp::Eventually, x) => TExpr::Even(sub!(x).into()),
        // P ~> Q is [](~P \/ <>Q)
        Bin(BOp::LeadsTo, a, b) => TExpr::All(TExpr::Disj(vec![TExpr::Neg(sub!(a).into()), TExpr::Even(sub!(b).into())]).into()),
        // WF_v(A) is []<>(~ENABLED <<A>>_v \/ <<A>>_v); SF_v(A) is <>[]~ENABLED <<A>>_v \/ []<><<A>>_v
        Fair(weak, v, a) => {
            let step = And(vec![a.as_ref().clone(), changed(v)]);
            // Written in an instantiated module (see ast::SUBVAR), subscript included
            let en_step = match a.as_ref() {
                Label(n, ..) if n == crate::ast::ENINST => Label(n.clone(), vec![], step.clone().b()),
                _ => step.clone(),
            };
            let en = TExpr::Neg(TExpr::State(atoms.state(g, &Un(UOp::Enabled, en_step.b()), env)?).into());
            let act = TExpr::Action(atoms.action(g, &step, env)?);
            if *weak {
                TExpr::All(TExpr::Even(TExpr::Disj(vec![en, act]).into()).into())
            } else {
                TExpr::Disj(vec![TExpr::Even(TExpr::All(en.into()).into()), TExpr::All(TExpr::Even(act.into()).into())])
            }
        }
        Quant(exists, bs, body) => {
            let mut parts = vec![];
            let mut err: R<Option<Rejected>> = Ok(None);
            let ce = g.ce.clone();
            let r = ce.each_binding(bs, env, &mut |env2| {
                match to_texpr(g, body, env2, atoms, None) {
                    Ok(Ok(t)) => parts.push(t),
                    Ok(Err(r)) => {
                        err = Ok(Some(r));
                        return Ok(false);
                    }
                    Err(m) => {
                        err = Err(m);
                        return Ok(false);
                    }
                }
                Ok(true)
            });
            if let Err(m) = r {
                // The bound is not a constant (it depends on the state, or is infinite)
                if m.contains("is not a constant") {
                    let mut r = refused(g, e0, at);
                    // A bound that reads a variable: TLC adds the error it got evaluating it
                    if let Some(v) = m.strip_prefix('`').and_then(|x| x.strip_suffix("` is not a constant")).filter(|v| g.vars.iter().any(|(n, _)| n == v)) {
                        r.0 += &format!(":\nIn evaluation, the identifier {v} is either undefined or not an operator.");
                        // With the position of the variable in the bounds, where TLC met it
                        let at = bs.iter().find_map(|(_, s)| first_named(s, v));
                        if let Some(at) = at {
                            r.0 += &format!("\n{}", at.text());
                        }
                    }
                    return Ok(Err(r));
                }
                return Err(m);
            }
            if let Some(r) = err? {
                return Ok(Err(r));
            }
            if parts.is_empty() {
                TExpr::Bool(!*exists)
            } else {
                TExpr::junction(parts, !*exists)
            }
        }
        If(c, a, b) if !temporal(c) => {
            let c = sub!(c);
            TExpr::Disj(vec![TExpr::Conj(vec![c.clone(), sub!(a)]), TExpr::Conj(vec![TExpr::Neg(c.into()), sub!(b)])])
        }
        _ => return Ok(Err(refused(g, e0, at))),
    }))
}

/// TLC's fairness conditions in its form; their atoms are only classified
fn fair_texpr(f: &FairDef) -> TExpr {
    let en = TExpr::Neg(TExpr::State(FAIR).into());
    let act = TExpr::Action(FAIR);
    if f.weak {
        TExpr::All(TExpr::Even(TExpr::Disj(vec![en, act]).into()).into())
    } else {
        TExpr::Disj(vec![TExpr::Even(TExpr::All(en.into()).into()), TExpr::All(TExpr::Even(act.into()).into())])
    }
}

/// What TLC does with fairness /\ ~(the properties), as tlc2.tool.liveness.Liveness.processLiveness:
/// an error if a part of a disjunct of its normal form has an action but is not <>[]A or []<>A;
/// otherwise the state atoms that end up in the tableau (TLC evaluates those on a state when it is
/// generated, and the others when the state is expanded)
fn tlc_plan(fair: &[FairDef], assumed: &[TExpr], props: &[TExpr]) -> Result<u64, Rejected> {
    if props.is_empty() {
        return Ok(0);
    }
    let mut conj = vec![];
    for f in fair {
        TExpr::add(&mut conj, fair_texpr(f), true);
    }
    for a in assumed {
        TExpr::add(&mut conj, a.clone(), true);
    }
    let neg = if props.len() == 1 {
        TExpr::Neg(props[0].clone().into())
    } else {
        TExpr::junction(props.iter().map(|p| TExpr::Neg(p.clone().into())), false)
    };
    let e = if conj.is_empty() {
        neg
    } else {
        TExpr::add(&mut conj, neg, true);
        TExpr::Conj(conj)
    };
    let dnf = match e.push_neg(false).simplify().to_dnf() {
        TExpr::Bool(false) => return Ok(0),
        TExpr::Disj(d) => d,
        e => vec![e],
    };
    let mut tableau = 0u64;
    for d in dnf {
        let items = match d.flatten() {
            TExpr::Conj(xs) => xs,
            e => vec![e],
        };
        for ln in items {
            let ea = matches!(&ln, TExpr::Even(b) if matches!(b.as_ref(), TExpr::All(c) if c.level() < 3));
            let ae = matches!(&ln, TExpr::All(b) if matches!(b.as_ref(), TExpr::Even(c) if c.level() <= 2));
            if ea || ae {
                continue;
            }
            if ln.has_action() {
                return Err(Rejected("Temporal formulas containing actions must be of forms <>[]A or []<>A.".into(), 255));
            }
            ln.state_atoms(&mut tableau);
        }
    }
    Ok(tableau)
}

/// Fairness atoms in TLC's form for `tlc_live`: whether fairness condition i's <<A>>_v is enabled
/// (a state atom) and whether a step is one (an action atom), numbered past every other atom
const FAIR_EN: usize = 1 << 40;
const FAIR_STEP: usize = 1 << 41;

/// A predicate of level 0 to 2 as the runtime's `LP`
fn lp_src(e: &TExpr) -> String {
    match e {
        TExpr::Bool(b) => format!("LP::B({b})"),
        TExpr::State(i) if *i >= FAIR_EN => format!("LP::FE({})", i - FAIR_EN),
        TExpr::State(i) => format!("LP::S({i})"),
        TExpr::Action(i) if *i >= FAIR_STEP => format!("LP::FS({})", i - FAIR_STEP),
        TExpr::Action(i) => format!("LP::A({})", i - ACTION_BASE),
        TExpr::Neg(b) => format!("LP::Not(&{})", lp_src(b)),
        TExpr::Conj(xs) => format!("LP::And(&[{}])", xs.iter().map(lp_src).collect::<Vec<_>>().join(", ")),
        TExpr::Disj(xs) => format!("LP::Or(&[{}])", xs.iter().map(lp_src).collect::<Vec<_>>().join(", ")),
        TExpr::All(_) | TExpr::Even(_) => unreachable!("a temporal predicate"),
    }
}

/// TLC's plan for finding a counterexample (tlc2.tool.liveness.Liveness.processLiveness), as the
/// runtime's `TLC_LIVE`, which follows TLC's search on the state graph to print the counterexample
/// TLC prints: the normal form of fairness /\ ~(the properties), each disjunct a possible error
/// model of <>[]A (EAAction), []<>S (AEState) and []<>A (AEAction) parts, with the predicates
/// numbered in TLC's order. A disjunct with another part needs TLC's tableau, which the runtime
/// does not follow; it then gets the reason.
fn tlc_live(fair: &[FairDef], assumed: &[TExpr], props: &[TExpr]) -> String {
    let none = |why: &str| format!("static TLC_LIVE: Result<TLive, &str> = Err({why:?});\n");
    if props.is_empty() {
        return none("no properties");
    }
    let mut conj = vec![];
    for (i, f) in fair.iter().enumerate() {
        let en = TExpr::Neg(TExpr::State(FAIR_EN + i).into());
        let act = TExpr::Action(FAIR_STEP + i);
        let t = if f.weak {
            TExpr::All(TExpr::Even(TExpr::Disj(vec![en, act]).into()).into())
        } else {
            TExpr::Disj(vec![TExpr::Even(TExpr::All(en.into()).into()), TExpr::All(TExpr::Even(act.into()).into())])
        };
        TExpr::add(&mut conj, t, true);
    }
    for a in assumed {
        TExpr::add(&mut conj, a.clone(), true);
    }
    let neg = if props.len() == 1 {
        TExpr::Neg(props[0].clone().into())
    } else {
        TExpr::junction(props.iter().map(|p| TExpr::Neg(p.clone().into())), false)
    };
    let e = if conj.is_empty() {
        neg
    } else {
        TExpr::add(&mut conj, neg, true);
        TExpr::Conj(conj)
    };
    let dnf = match e.push_neg(false).simplify().to_dnf() {
        TExpr::Bool(false) => return none("no possible error"),
        TExpr::Disj(d) => d,
        e => vec![e],
    };
    // The predicates, numbered as TLC's checkState and checkAction (equal ones once)
    let mut sbin: Vec<(String, TExpr)> = vec![];
    let mut abin: Vec<(String, TExpr)> = vec![];
    let bin = |b: &mut Vec<(String, TExpr)>, x: &TExpr| -> usize {
        let k = format!("{x:?}");
        match b.iter().position(|(y, _)| *y == k) {
            Some(i) => i,
            None => {
                b.push((k, x.clone()));
                b.len() - 1
            }
        }
    };
    let mut pems = vec![];
    for d in dnf {
        let items = match d.flatten() {
            TExpr::Conj(xs) => xs,
            e => vec![e],
        };
        let (mut ea, mut aes, mut aea) = (vec![], vec![], vec![]);
        for ln in items {
            match &ln {
                TExpr::Even(b) if matches!(b.as_ref(), TExpr::All(c) if c.level() < 3) => {
                    let TExpr::All(c) = b.as_ref() else { unreachable!() };
                    ea.push(c.as_ref().clone());
                }
                TExpr::All(b) if matches!(b.as_ref(), TExpr::Even(c) if c.level() <= 2) => {
                    let TExpr::Even(c) = b.as_ref() else { unreachable!() };
                    if c.level() <= 1 { aes.push(c.as_ref().clone()) } else { aea.push(c.as_ref().clone()) }
                }
                _ => return none("a property TLC checks with its tableau"),
            }
        }
        // PossibleErrorModel(AEAction, AEState, EAAction): the bins are filled in that order
        let aea: Vec<usize> = aea.iter().map(|x| bin(&mut abin, x)).collect();
        let aes: Vec<usize> = aes.iter().map(|x| bin(&mut sbin, x)).collect();
        let ea: Vec<usize> = ea.iter().map(|x| bin(&mut abin, x)).collect();
        pems.push(format!("TPem {{ ae_state: &{aes:?}, ae_action: &{aea:?}, ea_action: &{ea:?} }}"));
    }
    if sbin.len() > 64 || abin.len() > 64 {
        return none("more than 64 predicates");
    }
    let cs: Vec<String> = sbin.iter().map(|(_, x)| lp_src(x)).collect();
    let ca: Vec<String> = abin.iter().map(|(_, x)| lp_src(x)).collect();
    format!(
        "static TLC_LIVE: Result<TLive, &str> = Ok(TLive {{ check_state: &[{}], check_action: &[{}], pems: &[{}] }});\n",
        cs.join(", "),
        ca.join(", "),
        pems.join(", ")
    )
}

/// Generated code for the liveness checks: the atoms, the fairness conditions, and an automaton per
/// property part. `assumed` are the spec's temporal conjuncts other than fairness (with their
/// constant bindings), under which each part is checked; `parts` are (name, formula, constant
/// bindings). A formula TLC rejects comes back as Ok(Err(..)).
pub fn compile(
    g: &mut Gen,
    fair: &[FairDef],
    assumed: &[(Expr, HashMap<String, Value>)],
    parts: &[(String, Expr, HashMap<String, Value>)],
) -> R<Result<String, Rejected>> {
    // The spec's temporal conjuncts matter only when there are properties to check
    let assumed = if parts.is_empty() { &[][..] } else { assumed };
    let mut atoms = Atoms::default();
    let mut src = String::new();
    let mut props = vec![];
    // SANY's rules on temporal formulas (TLC stops with exit code 150 before checking anything)
    for e in parts.iter().map(|p| &p.1).chain(assumed.iter().map(|a| &a.0)) {
        if let Err(m) = sany_level(e) {
            return Ok(Err(Rejected(m, 150)));
        }
    }
    let mut texprs = vec![];
    for (name, e, env) in parts {
        let at = g.def_pos.get(name).cloned();
        match to_texpr(g, e, env, &mut atoms, at.as_deref()).map_err(|m| format!("property {name}: {m}"))? {
            Ok(t) => texprs.push(t),
            Err(r) => return Ok(Err(r)),
        }
    }
    let mut atexprs = vec![];
    for (e, env) in assumed {
        match to_texpr(g, e, env, &mut atoms, None).map_err(|m| format!("spec: {m}"))? {
            Ok(t) => atexprs.push(t),
            Err(r) => return Ok(Err(r)),
        }
    }
    let tableau = match tlc_plan(fair, &atexprs, &texprs) {
        Ok(t) => t,
        Err(r) => return Ok(Err(r)),
    };
    src += &tlc_live(fair, &atexprs, &texprs);
    for ((name, _, _), t) in parts.iter().zip(&texprs) {
        let f = t.to_ltl();
        let neg = if atexprs.is_empty() {
            f.not()
        } else {
            Ltl::And(atexprs.iter().map(|a| a.to_ltl()).chain([f.not()]).collect())
        };
        let (nodes, nacc) = automaton(&neg, 4096).map_err(|m| format!("property {name}: {m}"))?;
        let mut ns = vec![];
        for n in &nodes {
            let (mut sp, mut sn, mut ap, mut an) = (0u64, 0u64, 0u64, 0u64);
            for &(a, p) in &n.lits {
                let (pos, neg, b) = if a >= ACTION_BASE { (&mut ap, &mut an, a - ACTION_BASE) } else { (&mut sp, &mut sn, a) };
                if p {
                    *pos |= 1 << b;
                } else {
                    *neg |= 1 << b;
                }
            }
            let succ: Vec<String> = n.succ.iter().map(|x| x.to_string()).collect();
            ns.push(format!(
                "LNode {{ s_pos: {sp}, s_neg: {sn}, a_pos: {ap}, a_neg: {an}, succ: &[{}], init: {}, acc: {} }}",
                succ.join(", "),
                n.init,
                n.acc
            ));
        }
        props.push(format!("LProp {{ name: {name:?}, nodes: &[{}], nacc: {nacc} }}", ns.join(", ")));
    }
    // Fairness matters only when there are properties to check
    let mut fairs = vec![];
    if !parts.is_empty() {
        for (i, f) in fair.iter().enumerate() {
            let genv = bind_env(g, &f.env)?;
            let step_env = g.env_step(genv.clone());
            let what = if f.weak { "WF" } else { "SF" };
            let chg = g.gen_as(&changed(&f.sub), &step_env, &Ty::Bool).map_err(|m| format!("{what} subscript: {m}"))?;
            let act = g.gen_as(&f.action, &step_env, &Ty::Bool).map_err(|m| format!("{what}: {m}\n  in: {}", short(&f.action)))?;
            // Whether <<A>>_v is enabled, as for WF in a property: v changes in a successor of A
            let mut succ = String::new();
            let step = Expr::And(vec![f.action.clone(), changed(&f.sub)]);
            let fenv = g.env_fair(genv.clone(), &f.action);
            let exit = fenv.en_exit.clone().unwrap();
            g.gen_action(&[step], &fenv, &mut succ).map_err(|m| format!("{what}: {m}\n  in: {}", short(&f.action)))?;
            writeln!(src, "#[allow(unused_variables)]\nfn fchg_{i}(s: &State, t: &State) -> bool {{ {chg} }}").unwrap();
            writeln!(src, "#[allow(unused_variables)]\nfn fstep_{i}(s: &State, t: &State) -> bool {{ ({act}) && fchg_{i}(s, t) }}").unwrap();
            writeln!(
                src,
                "#[allow(unreachable_code)]\nfn fen_{i}(s: &State) -> bool {{ '{exit}: {{ {succ} false }} }}"
            )
            .unwrap();
            fairs.push(format!("({}, fen_{i} as fn(&State) -> bool, fstep_{i} as fn(&State, &State) -> bool)", f.weak));
        }
    }
    if atoms.state.len() > 64 || atoms.action.len() > 64 || fairs.len() > 128 {
        return Err(format!(
            "liveness checking supports up to 64 state predicates, 64 action predicates and 128 fairness conditions (here {}, {} and {})",
            atoms.state.len(),
            atoms.action.len(),
            fairs.len()
        ));
    }
    let mut sl = vec![];
    for (i, (_, c)) in atoms.state.iter().enumerate() {
        writeln!(src, "#[allow(unused_variables)]\nfn sa_{i}(s: &State) -> bool {c}").unwrap();
        sl.push(format!("sa_{i} as fn(&State) -> bool"));
    }
    let mut al = vec![];
    for (i, (_, c)) in atoms.action.iter().enumerate() {
        writeln!(src, "#[allow(unused_variables)]\nfn aa_{i}(s: &State, t: &State) -> bool {c}").unwrap();
        al.push(format!("aa_{i} as fn(&State, &State) -> bool"));
    }
    writeln!(src, "static SATOMS: &[fn(&State) -> bool] = &[{}];", sl.join(", ")).unwrap();
    writeln!(src, "static AATOMS: &[fn(&State, &State) -> bool] = &[{}];", al.join(", ")).unwrap();
    writeln!(src, "static FAIRS: &[(bool, fn(&State) -> bool, fn(&State, &State) -> bool)] = &[{}];", fairs.join(", ")).unwrap();
    // The fairness conditions of a state or step, as a bit mask (wider only when needed: the
    // liveness graph keeps one per state and per edge)
    writeln!(src, "type FMask = {};", if fairs.len() > 64 { "u128" } else { "u64" }).unwrap();
    writeln!(src, "static LPROPS: &[LProp] = &[{}];", props.join(", ")).unwrap();
    writeln!(src, "const LIVENESS: bool = {};", !parts.is_empty()).unwrap();
    // The state atoms TLC evaluates when a state is generated (those of the tableau); it evaluates
    // the others when the state is expanded
    writeln!(src, "const SATOMS_TABLEAU: u64 = {tableau};").unwrap();
    Ok(Ok(src))
}

/// The position of the first identifier named v written in e
fn first_named(e: &Expr, v: &str) -> Option<Pos> {
    match e {
        Expr::Ident(n, at) if n == v && at.known() => Some(*at),
        e => e.children().into_iter().find_map(|c| first_named(c, v)),
    }
}
