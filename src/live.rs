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
/// action from ACTION_BASE); FAIR is a fairness atom, which is only classified. The second field
/// tells the occurrences apart: TLC numbers each predicate it makes from the formula
/// (LiveExprNode.tagExpr) and two predicates are equal only when their numbers are, also when they
/// are written alike.
#[derive(Clone, Debug, PartialEq)]
enum TExpr {
    Bool(bool),
    State(usize, u32),
    Action(usize, u32),
    Neg(Box<TExpr>),
    Conj(Vec<TExpr>),
    Disj(Vec<TExpr>),
    All(Box<TExpr>),
    Even(Box<TExpr>),
}

const FAIR: usize = usize::MAX;

/// A new number for a predicate made from the formula (see TExpr)
fn tag() -> u32 {
    static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

impl TExpr {
    fn level(&self) -> u8 {
        match self {
            TExpr::Bool(_) => 0,
            TExpr::State(..) => 1,
            TExpr::Action(..) => 2,
            TExpr::Neg(b) => b.level(),
            TExpr::Conj(xs) | TExpr::Disj(xs) => xs.iter().map(|x| x.level()).max().unwrap_or(0),
            TExpr::All(_) | TExpr::Even(_) => 3,
        }
    }

    fn has_action(&self) -> bool {
        match self {
            TExpr::Action(..) => true,
            TExpr::Bool(_) | TExpr::State(..) => false,
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
            a @ (TExpr::State(..) | TExpr::Action(..)) => {
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
            a @ (TExpr::State(..) | TExpr::Action(..)) => TExpr::Neg(a.into()),
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
                a @ (TExpr::State(..) | TExpr::Action(..)) => TExpr::Neg(a.into()),
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

    /// TLC's tableau ignores boolean constants: a particle's consistency (TBPar.isLocallyConsistent)
    /// and a state's (TBGraphNode.isConsistent) look at state predicates only. So a constant that
    /// simplify leaves under [] or <> (`<>TRUE` negated is `[]FALSE`) holds in every state, outside
    /// the forms <>[]A and []<>A, which TLC checks without the tableau. Called on the simplified
    /// negation, whose top-level junctions are those TLC's DNF splits
    fn tableau_bools(self) -> TExpr {
        match self {
            TExpr::Conj(xs) => TExpr::Conj(xs.into_iter().map(|x| x.tableau_bools()).collect()),
            TExpr::Disj(xs) => TExpr::Disj(xs.into_iter().map(|x| x.tableau_bools()).collect()),
            e if matches!(&e, TExpr::Even(b) if matches!(b.as_ref(), TExpr::All(c) if c.level() < 3)) => e,
            e if matches!(&e, TExpr::All(b) if matches!(b.as_ref(), TExpr::Even(c) if c.level() <= 2)) => e,
            TExpr::All(b) => TExpr::All(b.bools_true().into()),
            TExpr::Even(b) => TExpr::Even(b.bools_true().into()),
            e => e,
        }
    }
    fn bools_true(self) -> TExpr {
        match self {
            TExpr::Bool(_) => TExpr::Bool(true),
            TExpr::Neg(b) => TExpr::Neg(b.bools_true().into()),
            TExpr::Conj(xs) => TExpr::Conj(xs.into_iter().map(|x| x.bools_true()).collect()),
            TExpr::Disj(xs) => TExpr::Disj(xs.into_iter().map(|x| x.bools_true()).collect()),
            TExpr::All(b) => TExpr::All(b.bools_true().into()),
            TExpr::Even(b) => TExpr::Even(b.bools_true().into()),
            e => e,
        }
    }
    fn to_ltl(&self) -> Ltl {
        match self {
            TExpr::Bool(b) => Ltl::Bool(*b),
            TExpr::State(i, _) | TExpr::Action(i, _) => Ltl::Atom(*i, true),
            TExpr::Neg(b) => b.to_ltl().not(),
            TExpr::Conj(xs) => Ltl::And(xs.iter().map(|x| x.to_ltl()).collect()),
            TExpr::Disj(xs) => Ltl::Or(xs.iter().map(|x| x.to_ltl()).collect()),
            TExpr::All(b) => Ltl::Always(b.to_ltl().into()),
            TExpr::Even(b) => Ltl::Eventually(b.to_ltl().into()),
        }
    }

    fn state_atoms(&self, out: &mut u64) {
        match self {
            TExpr::State(i, _) if *i != FAIR => *out |= 1 << i,
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
        if let Some(m) = live_const_error(g, e0, env) {
            let m = format!("TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\n{m}");
            return Ok(Err(Rejected(m, 255)));
        }
        if let Bool(b) = e {
            return Ok(Ok(TExpr::Bool(*b)));
        }
        // A predicate of constant level is a boolean constant to TLC, which evaluates it here
        // (Liveness.astToLive); see TExpr::tableau_bools for what that changes
        let reads_state = e.any(&|x| match x {
            Ident(n, _) => g.vars.iter().any(|(v, _)| v == n),
            Prime(_) | Un(UOp::Enabled | UOp::Unchanged, _) => true,
            _ => false,
        });
        if !reads_state {
            if let Ok(Value::Bool(b)) = g.ce.eval(e, env) {
                return Ok(Ok(TExpr::Bool(b)));
            }
        }
        return Ok(Ok(if action_level(e) {
            TExpr::Action(atoms.action(g, &box_to_or(e), env)?, tag())
        } else {
            TExpr::State(atoms.state(g, e, env)?, tag())
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
            let en = TExpr::Neg(TExpr::State(atoms.state(g, &Un(UOp::Enabled, en_step.b()), env)?, tag()).into());
            let act = TExpr::Action(atoms.action(g, &step, env)?, tag());
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

/// The error TLC stops with when it starts, converting a temporal formula: it goes through /\, \/,
/// ~, =>, IF and LET (Liveness.astToLive) and evaluates each part of constant level, also a branch
/// of an IF that the condition does not take (`tests/tlc/LiveConstErr`)
fn live_const_error(g: &Gen, e: &Expr, env: &HashMap<String, Value>) -> Option<String> {
    use Expr::*;
    match e {
        // <<A>>_v is an action of the formula, not taken apart (`tests/tlc/LiveConstErr-Angle`)
        Label(n, ..) if n == ANGLE => return None,
        Label(n, pairs, b) if crate::ast::is_bind(n) => {
            let mut body = b.as_ref().clone();
            for p in pairs.chunks(2).rev() {
                if let [Ident(name, _), x] = p {
                    body = crate::expand::subst_ident(&body, name, x);
                }
            }
            return live_const_error(g, &body, env);
        }
        Label(_, _, b) if matches!(b.as_ref(), Label(..) | And(_) | Or(_) | Un(UOp::Not, _) | Bin(BOp::Implies, ..) | If(..)) => {
            return live_const_error(g, b, env);
        }
        And(xs) | Or(xs) => return xs.iter().find_map(|x| live_const_error(g, x, env)),
        Un(UOp::Not, x) => return live_const_error(g, x, env),
        Bin(BOp::Implies, a, b) => return [a, b].into_iter().find_map(|x| live_const_error(g, x, env)),
        If(c, a, b) => return [c, a, b].into_iter().find_map(|x| live_const_error(g, x, env)),
        _ => {}
    }
    let reads_state = e.any(&|x| match x {
        Ident(n, _) => g.vars.iter().any(|(v, _)| v == n),
        Prime(_) | Un(UOp::Enabled | UOp::Unchanged, _) => true,
        _ => false,
    });
    if reads_state {
        return None;
    }
    // Only TLC's own evaluation errors (the constant evaluator also fails on what it cannot do)
    match g.ce.eval(e, env) {
        Err(m) if m.starts_with("Attempted to") || m.starts_with("0^0") || m.starts_with("The second argument of ^") => Some(m),
        _ => None,
    }
}
/// TLC's fairness conditions in its form; their atoms are only classified
fn fair_texpr(f: &FairDef) -> TExpr {
    let en = TExpr::Neg(TExpr::State(FAIR, tag()).into());
    let act = TExpr::Action(FAIR, tag());
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
        TExpr::State(i, _) if *i >= FAIR_EN => format!("LP::FE({})", i - FAIR_EN),
        TExpr::State(i, _) => format!("LP::S({i})"),
        TExpr::Action(i, _) if *i >= FAIR_STEP => format!("LP::FS({})", i - FAIR_STEP),
        TExpr::Action(i, _) => format!("LP::A({})", i - ACTION_BASE),
        TExpr::Neg(b) => format!("LP::Not(&{})", lp_src(b)),
        TExpr::Conj(xs) => format!("LP::And(&[{}])", xs.iter().map(lp_src).collect::<Vec<_>>().join(", ")),
        TExpr::Disj(xs) => format!("LP::Or(&[{}])", xs.iter().map(lp_src).collect::<Vec<_>>().join(", ")),
        TExpr::All(_) | TExpr::Even(_) => unreachable!("a temporal predicate"),
    }
}

/// A formula in TLC's tableau (tlc2.tool.liveness: LiveExprNode with LNNext), its state predicates
/// equal when they come from the same occurrence (see TExpr)
#[derive(Clone, Debug, PartialEq)]
enum LN {
    Bool(bool),
    State(usize, u32),
    Neg(Box<LN>),
    Conj(Vec<LN>),
    Disj(Vec<LN>),
    Even(Box<LN>),
    All(Box<LN>),
    Next(Box<LN>),
}

impl LN {
    /// None for a formula with an action, which TLC refuses in its tableau
    fn of(t: &TExpr) -> Option<LN> {
        Some(match t {
            TExpr::Bool(b) => LN::Bool(*b),
            TExpr::State(i, k) => LN::State(*i, *k),
            TExpr::Action(..) => return None,
            TExpr::Neg(b) => LN::Neg(LN::of(b)?.into()),
            TExpr::Conj(xs) => LN::Conj(xs.iter().map(LN::of).collect::<Option<_>>()?),
            TExpr::Disj(xs) => LN::Disj(xs.iter().map(LN::of).collect::<Option<_>>()?),
            TExpr::All(b) => LN::All(LN::of(b)?.into()),
            TExpr::Even(b) => LN::Even(LN::of(b)?.into()),
        })
    }

    /// makeBinary: a junction split into halves until each has two parts
    fn binary(self) -> LN {
        fn junction(xs: Vec<LN>, conj: bool) -> LN {
            if xs.len() == 1 {
                return xs.into_iter().next().unwrap().binary();
            }
            let h = xs.len() / 2;
            let (mut a, mut b) = (vec![], vec![]);
            for (i, x) in xs.into_iter().enumerate() {
                let v = if i < h { &mut a } else { &mut b };
                // addConj / addDisj splice a junction of the same kind
                match x {
                    LN::Conj(ys) if conj => v.extend(ys),
                    LN::Disj(ys) if !conj => v.extend(ys),
                    x => v.push(x),
                }
            }
            let two = vec![junction(a, conj), junction(b, conj)];
            if conj { LN::Conj(two) } else { LN::Disj(two) }
        }
        match self {
            LN::Conj(xs) => junction(xs, true),
            LN::Disj(xs) => junction(xs, false),
            LN::Neg(b) => LN::Neg(b.binary().into()),
            LN::Even(b) => LN::Even(b.binary().into()),
            LN::All(b) => LN::All(b.binary().into()),
            e => e,
        }
    }

    /// extractPromises: the <> subformulas, each once, in the order met
    fn promises(&self, out: &mut Vec<LN>) {
        match self {
            LN::Even(b) => {
                if !out.contains(self) {
                    out.push(self.clone());
                }
                b.promises(out);
            }
            LN::Conj(xs) | LN::Disj(xs) => xs.iter().take(2).for_each(|x| x.promises(out)),
            LN::Neg(b) | LN::All(b) => b.promises(out),
            _ => {}
        }
    }

    /// The two parts an alpha (/\, []) or beta (\/, <>) rule splits a formula into
    fn split(&self, alpha: bool) -> Option<(LN, LN)> {
        match self {
            LN::All(b) if alpha => Some(((**b).clone(), LN::Next(self.clone().into()))),
            LN::Conj(xs) if alpha => Some((xs[0].clone(), xs[1].clone())),
            LN::Even(b) if !alpha => Some(((**b).clone(), LN::Next(self.clone().into()))),
            LN::Disj(xs) if !alpha => Some((xs[0].clone(), xs[1].clone())),
            _ => None,
        }
    }
}

/// TLC's tableau of a formula (TBPar, TBGraph): its particles in TLC's order, the first `init` of
/// them those of the formula, each with the particles that can follow it
struct Tableau {
    pars: Vec<Vec<LN>>,
    nexts: Vec<Vec<usize>>,
    init: usize,
}

/// TBPar.isLocallyConsistent: no state predicate both in a particle and negated in it
fn tb_consistent(p: &[LN]) -> bool {
    let neg: Vec<&LN> = p
        .iter()
        .filter_map(|x| match x {
            LN::Neg(b) if matches!(b.as_ref(), LN::State(..)) => Some(b.as_ref()),
            _ => None,
        })
        .collect();
    !p.iter().any(|x| matches!(x, LN::State(..)) && neg.contains(&x))
}

/// TBPar.equals: the same formulas
fn tb_equal(p: &[LN], q: &[LN]) -> bool {
    p.iter().all(|x| q.contains(x)) && q.iter().all(|x| p.contains(x))
}

/// A formula and the two parts of its alpha or beta rule (TBTriple)
type Triple = (LN, LN, LN);

/// TBPar.particleClosure: the particles of a set of formulas, in TLC's order
fn tb_particles(terms: Vec<LN>) -> Vec<Vec<LN>> {
    // positiveClosure (a worklist taken from its end), then the rules of its formulas
    let mut list = terms.clone();
    let mut pc = vec![];
    while let Some(ln) = list.pop() {
        match &ln {
            LN::Neg(b) => list.push((**b).clone()),
            LN::Next(b) => {
                list.push((**b).clone());
                pc.push(ln);
            }
            LN::Even(b) | LN::All(b) => {
                list.push((**b).clone());
                pc.push(ln.clone());
                pc.push(LN::Next(ln.into()));
            }
            LN::Conj(xs) | LN::Disj(xs) => {
                list.extend(xs.iter().cloned());
                pc.push(ln);
            }
            LN::State(..) | LN::Bool(_) => pc.push(ln),
        }
    }
    let rules = |alpha: bool| -> Vec<Triple> {
        pc.iter().filter_map(|x| x.split(alpha).map(|(b, c)| (x.clone(), b, c))).collect()
    };
    let (alphas, betas) = (rules(true), rules(false));
    tb_closure(terms, &alphas, &betas)
}

fn tb_closure(terms: Vec<LN>, alphas: &[Triple], betas: &[Triple]) -> Vec<Vec<LN>> {
    if !tb_consistent(&terms) {
        return vec![];
    }
    let mut t1 = terms.clone();
    let mut i = 0;
    while i < t1.len() {
        if let Some((k1, k2)) = t1[i].split(true) {
            match (t1.contains(&k1), t1.contains(&k2)) {
                (true, true) => {}
                (true, false) => t1.push(k2),
                (false, true) => t1.push(k1),
                (false, false) => {
                    t1.push(k1);
                    t1.push(k2);
                }
            }
        }
        i += 1;
    }
    loop {
        let mut done = true;
        for (a, b, c) in alphas {
            if t1.contains(b) && t1.contains(c) && !t1.contains(a) {
                t1.push(a.clone());
                done = false;
            }
        }
        if done {
            break;
        }
    }
    if t1.len() > terms.len() && !tb_consistent(&t1) {
        return vec![];
    }
    // particleClosureBeta
    for x in &t1 {
        if let Some((k1, k2)) = x.split(false) {
            if !t1.contains(&k1) && !t1.contains(&k2) {
                let mut a = t1.clone();
                a.push(k1);
                let mut b = t1.clone();
                b.push(k2);
                let r1 = tb_closure(a, alphas, betas);
                let r2 = tb_closure(b, alphas, betas);
                // TBParVec.union: those of the first not in the second, then the second
                let mut r: Vec<Vec<LN>> = r1.into_iter().filter(|p| !r2.iter().any(|q| tb_equal(q, p))).collect();
                r.extend(r2);
                return r;
            }
        }
    }
    for (a, b, c) in betas {
        if (t1.contains(b) || t1.contains(c)) && !t1.contains(a) {
            let mut t2 = t1.clone();
            t2.push(a.clone());
            return tb_closure(t2, alphas, betas);
        }
    }
    vec![t1]
}

/// The most particles a tableau may have
const MAX_TABLEAU: usize = 4096;

/// TBGraph's constructor: the particles of the formula, then those that follow each particle
/// (of its implied successors, the bodies of its ()-formulas), each new one appended
fn tableau(tf: &LN) -> Option<Tableau> {
    let mut pars = tb_particles(vec![tf.clone()]);
    let init = pars.len();
    let mut nexts = vec![];
    let mut i = 0;
    while i < pars.len() {
        let imp: Vec<LN> = pars[i].iter().filter_map(|x| if let LN::Next(b) = x { Some((**b).clone()) } else { None }).collect();
        let mut ns = vec![];
        for p in tb_particles(imp) {
            let j = match pars.iter().position(|q| tb_equal(&p, q)) {
                Some(j) => j,
                None => {
                    pars.push(p);
                    pars.len() - 1
                }
            };
            ns.push(j);
        }
        nexts.push(ns);
        if pars.len() > MAX_TABLEAU {
            return None;
        }
        i += 1;
    }
    Some(Tableau { pars, nexts, init })
}

/// The tableau of an order of solution as the runtime's `TTab` fields: each particle's state
/// predicates (TBGraphNode.statePreds: the state atom and whether it holds), the particles that can
/// follow it, and the promises it fulfils (TBPar.isFulfilling: <>P not in it, or P in it)
fn tableau_src(tf: &TExpr) -> Result<String, &'static str> {
    let tf = LN::of(tf).ok_or("an action in the tableau")?.binary();
    let mut proms = vec![];
    tf.promises(&mut proms);
    if proms.len() > 64 {
        return Err("more than 64 promises");
    }
    let t = tableau(&tf).ok_or("a tableau of more than 4096 particles")?;
    let mut nodes = vec![];
    for (p, ns) in t.pars.iter().zip(&t.nexts) {
        let preds: Vec<String> = p
            .iter()
            .filter_map(|x| match x {
                LN::State(i, _) => Some(format!("({i}, true)")),
                LN::Neg(b) => match b.as_ref() {
                    LN::State(i, _) => Some(format!("({i}, false)")),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let mut ful = 0u64;
        for (k, pr) in proms.iter().enumerate() {
            let LN::Even(body) = pr else { unreachable!() };
            if !p.contains(pr) || p.contains(body) {
                ful |= 1 << k;
            }
        }
        nodes.push(format!("TNode {{ preds: &[{}], nexts: &{ns:?}, fulfils: {ful} }}", preds.join(", ")));
    }
    Ok(format!("tableau: Some(&[{}]), init_cnt: {}, promises: {}", nodes.join(", "), t.init, proms.len()))
}

/// TLC's plan for finding a counterexample (tlc2.tool.liveness.Liveness.processLiveness), as the
/// runtime's `TLC_LIVE`, which follows TLC's search on the state graph to print the counterexample
/// TLC prints: the normal form of fairness /\ ~(the properties), each disjunct a possible error
/// model of <>[]A (EAAction), []<>S (AEState) and []<>A (AEAction) parts, and the rest of it a
/// formula for a tableau. The disjuncts with the same rest make an order of solution, in the order
/// first met, with its tableau and the predicates of its models numbered in TLC's order.
fn tlc_live(fair: &[FairDef], assumed: &[TExpr], props: &[TExpr]) -> String {
    let none = |why: &str| format!("type TBits = u64;\nstatic TLC_LIVE: Result<TLive, &str> = Err({why:?});\n");
    if props.is_empty() {
        return none("no properties");
    }
    let mut conj = vec![];
    for (i, f) in fair.iter().enumerate() {
        let en = TExpr::Neg(TExpr::State(FAIR_EN + i, tag()).into());
        let act = TExpr::Action(FAIR_STEP + i, tag());
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
    // Each disjunct's tableau formula and model (AEAction, AEState, EAAction parts)
    #[allow(clippy::type_complexity)]
    let mut tfbin: Vec<(Option<TExpr>, Vec<(Vec<TExpr>, Vec<TExpr>, Vec<TExpr>)>)> = vec![];
    for d in dnf {
        let items = match d.flatten() {
            TExpr::Conj(xs) => xs,
            e => vec![e],
        };
        let (mut ea, mut aes, mut aea, mut tfs) = (vec![], vec![], vec![], vec![]);
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
                _ => tfs.push(ln),
            }
        }
        let tf = match tfs.len() {
            0 => None,
            1 => tfs.pop(),
            _ => Some(TExpr::junction(tfs, true)),
        };
        match tfbin.iter_mut().find(|x| x.0 == tf) {
            Some(x) => x.1.push((aea, aes, ea)),
            None => tfbin.push((tf, vec![(aea, aes, ea)])),
        }
    }
    // The predicates of an order of solution, numbered as TLC's checkState and checkAction (equal
    // ones once)
    let bin = |b: &mut Vec<TExpr>, x: &TExpr| -> usize {
        match b.iter().position(|y| y == x) {
            Some(i) => i,
            None => {
                b.push(x.clone());
                b.len() - 1
            }
        }
    };
    let mut wide = false;
    let mut oss = vec![];
    for (tf, models) in &tfbin {
        let tab = match tf {
            None => "tableau: None, init_cnt: 0, promises: 0".to_string(),
            Some(tf) => match tableau_src(tf) {
                Ok(s) => s,
                Err(m) => return none(m),
            },
        };
        let (mut sbin, mut abin) = (vec![], vec![]);
        let mut pems = vec![];
        for (aea, aes, ea) in models {
            // PossibleErrorModel(AEAction, AEState, EAAction): the bins are filled in that order
            let aea: Vec<usize> = aea.iter().map(|x| bin(&mut abin, x)).collect();
            let aes: Vec<usize> = aes.iter().map(|x| bin(&mut sbin, x)).collect();
            let ea: Vec<usize> = ea.iter().map(|x| bin(&mut abin, x)).collect();
            pems.push(format!("TPem {{ ae_state: &{aes:?}, ae_action: &{aea:?}, ea_action: &{ea:?} }}"));
        }
        if sbin.len() > 128 || abin.len() > 128 {
            return none("more than 128 predicates");
        }
        wide |= sbin.len() > 64 || abin.len() > 64;
        let cs: Vec<String> = sbin.iter().map(lp_src).collect();
        let ca: Vec<String> = abin.iter().map(lp_src).collect();
        oss.push(format!(
            "TOos {{ {tab}, check_state: &[{}], check_action: &[{}], pems: &[{}] }}",
            cs.join(", "),
            ca.join(", "),
            pems.join(", ")
        ));
    }
    // The predicates of a state or step as a bit mask (wider only when needed)
    let bits = if wide { "u128" } else { "u64" };
    format!("type TBits = {bits};\nstatic TLC_LIVE: Result<TLive, &str> = Ok(TLive {{ oos: &[{}] }});\n", oss.join(", "))
}

/// The most states an automaton may have
const MAX_AUTOMATON: usize = 4096;

/// The nodes of an automaton as the runtime's `LNode`s
fn lnodes(nodes: &[crate::ltl::Node]) -> String {
    let mut ns = vec![];
    for n in nodes {
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
    ns.join(", ")
}

/// The disjuncts of the normal form of a simplified negation, each as the formula left for an
/// automaton and its []<>S, []<>A and <>[]A parts. None if there is a single disjunct with nothing
/// to take out, which splitting does not make smaller.
#[allow(clippy::type_complexity)]
fn split_disjuncts(neg: TExpr) -> Option<Vec<(Ltl, Vec<TExpr>, Vec<TExpr>, Vec<TExpr>)>> {
    let dnf = match neg.to_dnf() {
        TExpr::Bool(false) => vec![],
        TExpr::Disj(d) => d,
        e => vec![e],
    };
    let mut out = vec![];
    let mut taken = false;
    for d in dnf {
        let items = match d.flatten() {
            TExpr::Conj(xs) => xs,
            e => vec![e],
        };
        let (mut rest, mut aes, mut aea, mut ea) = (vec![], vec![], vec![], vec![]);
        for ln in items {
            match ln {
                TExpr::Even(b) if matches!(b.as_ref(), TExpr::All(c) if c.level() < 3) => {
                    let TExpr::All(c) = *b else { unreachable!() };
                    ea.push(*c);
                }
                TExpr::All(b) if matches!(b.as_ref(), TExpr::Even(c) if c.level() <= 2) => {
                    let TExpr::Even(c) = *b else { unreachable!() };
                    if c.level() <= 1 { aes.push(*c) } else { aea.push(*c) }
                }
                ln => rest.push(ln.tableau_bools().to_ltl()),
            }
        }
        taken |= !(aes.is_empty() && aea.is_empty() && ea.is_empty());
        out.push((Ltl::And(rest), aes, aea, ea));
    }
    (taken || out.len() > 1).then_some(out)
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
        let neg = TExpr::junction(atexprs.iter().cloned().chain([TExpr::Neg(t.clone().into())]), true).push_neg(false).simplify();
        let lp_list = |xs: &[TExpr]| format!("&[{}]", xs.iter().map(lp_src).collect::<Vec<_>>().join(", "));
        match automaton(&neg.clone().tableau_bools().to_ltl(), MAX_AUTOMATON) {
            Ok((nodes, nacc)) => props.push(format!("LProp {{ name: {name:?}, nodes: &[{}], nacc: {nacc}, ae_state: &[], ae_action: &[], ea: &[] }}", lnodes(&nodes))),
            Err(m) => {
                // Too large for one automaton: as TLC does, each disjunct of the normal form on
                // its own, its <>[]A, []<>S and []<>A parts as conditions on components and only
                // the rest in an automaton. Each disjunct is checked as a property of its own.
                let alts = split_disjuncts(neg).ok_or_else(|| format!("property {name}: {m}"))?;
                for (rest, aes, aea, ea) in alts {
                    let (nodes, nacc) = automaton(&rest, MAX_AUTOMATON).map_err(|m| format!("property {name}: {m}"))?;
                    props.push(format!(
                        "LProp {{ name: {name:?}, nodes: &[{}], nacc: {nacc}, ae_state: {}, ae_action: {}, ea: {} }}",
                        lnodes(&nodes),
                        lp_list(&aes),
                        lp_list(&aea),
                        lp_list(&ea)
                    ));
                }
            }
        }
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
    writeln!(src, "const NPROPS: usize = {};", parts.len()).unwrap();
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
