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
        Expr::Label(_, _, b) => collect_fair(b, env, g, out),
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

    /// ENABLED x: whether x has a successor from the state
    fn enabled(&mut self, g: &mut Gen, x: &Expr, env: &HashMap<String, Value>) -> R<usize> {
        let k = format!("ENABLED {}", key(x, env));
        if let Some(i) = self.state.iter().position(|(y, _)| *y == k) {
            return Ok(i);
        }
        let genv = bind_env(g, env)?;
        let mut code = String::new();
        g.gen_action(&[x.clone()], &genv, &mut code).map_err(|m| format!("ENABLED: {m}\n  in: {}", short(x)))?;
        self.state.push((k, format!("{{ let mut buf: Vec<(State, u32)> = Vec::new(); {{ let out = &mut buf; {code} }} !buf.is_empty() }}")));
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
    e.any(&|x| {
        matches!(
            x,
            Expr::Un(UOp::Always | UOp::Eventually | UOp::Enabled, _) | Expr::Bin(BOp::LeadsTo, ..) | Expr::BoxAction(..) | Expr::Fair(..)
        )
    })
}

fn to_ltl(g: &mut Gen, e: &Expr, env: &HashMap<String, Value>, atoms: &mut Atoms) -> R<Ltl> {
    use Expr::*;
    let e = e.strip();
    if !temporal(e) {
        if let Bool(b) = e {
            return Ok(Ltl::Bool(*b));
        }
        let i = if e.is_action() { atoms.action(g, e, env)? } else { atoms.state(g, e, env)? };
        return Ok(Ltl::Atom(i, true));
    }
    let mut sub = |x: &Expr| to_ltl(g, x, env, atoms);
    Ok(match e {
        And(xs) => Ltl::And(xs.iter().map(&mut sub).collect::<R<_>>()?),
        Or(xs) => Ltl::Or(xs.iter().map(&mut sub).collect::<R<_>>()?),
        Un(UOp::Not, x) => sub(x)?.not(),
        Bin(BOp::Implies, a, b) => Ltl::Or(vec![sub(a)?.not(), sub(b)?]),
        Bin(BOp::Equiv, a, b) => {
            let (a, b) = (sub(a)?, sub(b)?);
            Ltl::Or(vec![Ltl::And(vec![a.clone(), b.clone()]), Ltl::And(vec![a.not(), b.not()])])
        }
        Un(UOp::Always, x) => Ltl::Always(sub(x)?.into()),
        Un(UOp::Eventually, x) => Ltl::Eventually(sub(x)?.into()),
        // P ~> Q is [](P => <>Q)
        Bin(BOp::LeadsTo, a, b) => Ltl::Always(Ltl::Or(vec![sub(a)?.not(), Ltl::Eventually(sub(b)?.into())]).into()),
        // [A]_v is A \/ v' = v
        BoxAction(a, v) => {
            let same = Bin(BOp::Eq, Prime(v.clone()).b(), v.clone());
            Ltl::Atom(atoms.action(g, &Or(vec![a.as_ref().clone(), same]), env)?, true)
        }
        Un(UOp::Enabled, x) => Ltl::Atom(atoms.enabled(g, x, env)?, true),
        // WF_v(A) is []<>~ENABLED <<A>>_v \/ []<><<A>>_v; SF_v(A) is <>[]~ENABLED <<A>>_v \/ []<><<A>>_v
        Fair(weak, v, a) => {
            let step = And(vec![a.as_ref().clone(), changed(v)]);
            let en = Ltl::Atom(atoms.enabled(g, &step, env)?, false);
            let taken = Ltl::Always(Ltl::Eventually(Ltl::Atom(atoms.action(g, &step, env)?, true).into()).into());
            let off = if *weak { Ltl::Always(Ltl::Eventually(en.into()).into()) } else { Ltl::Eventually(Ltl::Always(en.into()).into()) };
            Ltl::Or(vec![off, taken])
        }
        Quant(exists, bs, body) => {
            let mut parts = vec![];
            let mut err = Ok(());
            let ce = g.ce.clone();
            ce.each_binding(bs, env, &mut |env2| {
                match to_ltl(g, body, env2, atoms) {
                    Ok(l) => parts.push(l),
                    Err(m) => {
                        err = Err(m);
                        return Ok(false);
                    }
                }
                Ok(true)
            })?;
            err?;
            if *exists { Ltl::Or(parts) } else { Ltl::And(parts) }
        }
        If(c, a, b) if !temporal(c) => {
            let c = sub(c)?;
            Ltl::Or(vec![Ltl::And(vec![c.clone(), sub(a)?]), Ltl::And(vec![c.not(), sub(b)?])])
        }
        _ => return Err(format!("unsupported temporal formula {}", short(e))),
    })
}

/// Generated code for the liveness checks: the atoms, the fairness conditions, and an automaton per
/// property part. `parts` are (name, formula, constant bindings).
pub fn compile(g: &mut Gen, fair: &[FairDef], parts: &[(String, Expr, HashMap<String, Value>)]) -> R<String> {
    let mut atoms = Atoms::default();
    let mut src = String::new();
    let mut props = vec![];
    for (name, e, env) in parts {
        let f = to_ltl(g, e, env, &mut atoms).map_err(|m| format!("property {name}: {m}"))?;
        let (nodes, nacc) = automaton(&f.not(), 4096).map_err(|m| format!("property {name}: {m}"))?;
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
            let mut succ = String::new();
            g.gen_action(&[f.action.clone()], &genv, &mut succ).map_err(|m| format!("{what}: {m}\n  in: {}", short(&f.action)))?;
            writeln!(src, "#[allow(unused_variables)]\nfn fchg_{i}(s: &State, t: &State) -> bool {{ {chg} }}").unwrap();
            writeln!(src, "#[allow(unused_variables)]\nfn fstep_{i}(s: &State, t: &State) -> bool {{ ({act}) && fchg_{i}(s, t) }}").unwrap();
            writeln!(
                src,
                "fn fen_{i}(s: &State) -> bool {{ let mut buf: Vec<(State, u32)> = Vec::new(); {{ let out = &mut buf; {succ} }} buf.iter().any(|(t, _)| fchg_{i}(s, t)) }}"
            )
            .unwrap();
            fairs.push(format!("({}, fen_{i} as fn(&State) -> bool, fstep_{i} as fn(&State, &State) -> bool)", f.weak));
        }
    }
    if atoms.state.len() > 64 || atoms.action.len() > 64 || fairs.len() > 64 {
        return Err("liveness checking supports up to 64 state predicates, 64 action predicates and 64 fairness conditions".into());
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
    writeln!(src, "static LPROPS: &[LProp] = &[{}];", props.join(", ")).unwrap();
    writeln!(src, "const LIVENESS: bool = {};", !parts.is_empty()).unwrap();
    Ok(src)
}
