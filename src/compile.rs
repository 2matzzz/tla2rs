//! .tla + .cfg → Rust source for the model checker

use crate::ast::*;
use crate::cfg::{parse_cfg, Cfg};
use crate::codegen::{short, Gen};
use crate::expand::Expander;
use crate::lexer::R;
use crate::parser::parse_module;
use crate::types::*;
use crate::value::*;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

pub struct Output {
    pub rust: String,
    pub warnings: Vec<String>,
    /// The ASSUME that evaluated to false (worded as TLC reports it). When set, no checker is
    /// generated.
    pub assume_failed: Option<String>,
}

const TYPE_OK_NAMES: &[&str] = &["TypeOK", "TypeOk", "TypeInvariant", "TypeInv", "TypeCorrect"];

const TYPE_DECL_NAMES: &[&str] = &["TypeDecl"];

/// Loads the EXTENDS'd modules whose .tla files sit in the same directory and merges them into one.
/// Definitions loaded later (from the extending module) take precedence.
fn load_module(src: &str, dir: &std::path::Path, warnings: &mut Vec<String>, depth: usize) -> R<Module> {
    if depth > 16 {
        return Err("EXTENDS nests too deeply".into());
    }
    let m = parse_module(src)?;
    let mut out = Module { name: m.name.clone(), ..Default::default() };
    for e in &m.extends {
        match e.as_str() {
            "Naturals" | "Integers" | "FiniteSets" | "TLC" => out.extends.push(e.clone()),
            // Apalache type annotations and Gen are not used
            "Apalache" => {}
            _ => {
                let path = dir.join(format!("{e}.tla"));
                let Ok(sub_src) = std::fs::read_to_string(&path) else {
                    warnings.push(format!("EXTENDS {e}: module not found next to the spec (only Naturals / Integers / FiniteSets are built in)"));
                    continue;
                };
                let sub = load_module(&sub_src, dir, warnings, depth + 1)?;
                out.extends.extend(sub.extends);
                out.constants.extend(sub.constants);
                out.variables.extend(sub.variables);
                out.defs.extend(sub.defs);
                out.assumes.extend(sub.assumes);
            }
        }
    }
    out.constants.extend(m.constants);
    out.variables.extend(m.variables);
    out.defs.extend(m.defs);
    out.assumes.extend(m.assumes);
    Ok(out)
}

pub fn compile(tla: &str, cfg_src: &str, dir: &std::path::Path, setcap: usize, fp128: bool, metal: bool) -> R<Output> {
    let mut warnings = vec![];
    let m = load_module(tla, dir, &mut warnings, 0)?;
    let cfg = parse_cfg(cfg_src)?;

    // Strings and model values
    let mut atoms = Atoms::default();
    for d in &m.defs {
        collect_strings(&d.body, &mut atoms);
    }
    for (_, v) in &cfg.constants {
        collect_strings(v, &mut atoms);
    }
    for a in &m.assumes {
        collect_strings(&a.expr, &mut atoms);
    }

    // Constants
    let empty = HashMap::new();
    let mut constants = HashMap::new();
    {
        let ce = ConstEval { atoms: &atoms, constants: &empty };
        for c in &m.constants {
            let (_, e) = cfg
                .constants
                .iter()
                .find(|(n, _)| n == c)
                .ok_or(format!("CONSTANT {c} has no value in the cfg"))?;
            constants.insert(c.clone(), ce.eval(e, &HashMap::new())?);
        }
    }

    let mut ex = Expander::new(&m);

    // ASSUMEs are constant-level expressions, so check them here and stop with TLC's message if one
    // is false. An expression that cannot be evaluated is an error rather than silently passing.
    {
        let ce = ConstEval { atoms: &atoms, constants: &constants };
        for a in &m.assumes {
            let (l1, c1, l2, c2) = a.span;
            let at = format!("line {l1}, col {c1} to line {l2}, col {c2} of module {}", a.module);
            let e = ex.expand_top(&a.expr).map_err(|e| format!("ASSUME at {at}: {e}"))?;
            match ce.eval(&e, &HashMap::new()) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    return Ok(Output {
                        rust: String::new(),
                        warnings,
                        assume_failed: Some(format!("Error: Assumption {at} is false.")),
                    })
                }
                Ok(v) => return Err(format!("ASSUME at {at} is not a boolean: {v:?}")),
                Err(e) => return Err(format!("cannot evaluate the ASSUME at {at}: {e}")),
            }
        }
    }

    let (init, next, fairness) = resolve_spec(&m, &cfg, &mut ex)?;

    let mut g = Gen::new(&atoms, &constants);
    if setcap > 0 {
        g.scap = setcap;
    }

    // Enumerate fairness instances (only relevant when checking properties)
    if !cfg.properties.is_empty() {
        for f in &fairness {
            let f = ex.expand_top(f)?;
            collect_fair(&f, &HashMap::new(), &mut g, &m.variables, &mut warnings)?;
        }
    }

    // Variable types come from TypeOK
    let tname = TYPE_DECL_NAMES
        .iter()
        .chain(TYPE_OK_NAMES)
        .find(|n| ex.has_def(n))
        .copied()
        .unwrap_or("TypeOK");
    // Without a TypeOK, every type is inferred
    let tok = if ex.has_def(tname) { ex.expand_def(tname)? } else { Expr::Bool(true) };
    let mut decl: HashMap<String, Ty> = HashMap::new();
    let mut conj = vec![];
    flatten_and(&tok, &mut conj);
    // Conjuncts that could not be read as type declarations. If there are none, pack enforces this
    // invariant in full.
    let mut leftover = 0;
    for c in conj {
        match c.strip() {
            Expr::Bin(BOp::In, v, s) => {
                let mut taken = false;
                if let Expr::Ident(v) = v.strip() {
                    if m.variables.contains(v) {
                        decl.insert(v.clone(), ty_of_set(&g, s).map_err(|e| format!("{tname}: type of `{v}`: {e}"))?);
                        taken = true;
                    }
                }
                if !taken {
                    leftover += 1;
                }
            }
            Expr::Bin(BOp::Le, c, k) if matches!(c.strip(), Expr::Call(f, _) if f == "Cardinality") => {
                if let Ok(Value::Int(k)) = g.ce.eval(k, &HashMap::new()) {
                    g.scap = g.scap.max(k as usize);
                }
            }
            Expr::Bin(BOp::Subseteq, v, s) => {
                let mut taken = false;
                if let Expr::Ident(v) = v.strip() {
                    if m.variables.contains(v) {
                        let t = ty_of_set(&g, s).map_err(|e| format!("{tname}: type of `{v}`: {e}"))?;
                        decl.insert(v.clone(), Ty::Set(t.into()));
                        taken = true;
                    }
                }
                if !taken {
                    leftover += 1;
                }
            }
            Expr::Bool(true) => {}
            _ => leftover += 1,
        }
    }
    // Variables whose type TypeOK leaves open are inferred from the assignments in Init and Next
    let undeclared: Vec<String> = m.variables.iter().filter(|v| !decl.contains_key(*v)).cloned().collect();
    if !undeclared.is_empty() {
        let inferred = infer_types(&atoms, &constants, &m.variables, &decl, &undeclared, &init, &next, g.scap)?;
        decl.extend(inferred);
    }
    for v in &m.variables {
        g.vars.push((v.clone(), decl.remove(v).unwrap()));
    }

    // Init / Next
    let mut init_code = String::new();
    g.gen_action(&[init], &Gen::env_init(), &mut init_code).map_err(|e| format!("Init: {e}"))?;
    let mut next_code = String::new();
    g.gen_action(&[next], &Gen::env_next(), &mut next_code).map_err(|e| format!("Next: {e}"))?;
    // Compile each fair action on its own, so that ENABLED and "this transition is an A step" are
    // decided by the action's actual semantics
    let mut fair_ops: Vec<String> = vec![];
    for f in &g.fair {
        if !fair_ops.contains(&f.name) {
            fair_ops.push(f.name.clone());
        }
    }
    let mut fair_code = String::new();
    for (k, name) in fair_ops.iter().enumerate() {
        let (params, body) = ex.expand_params(name)?;
        let code = g.gen_fair_fn(k, name, &params, &body).map_err(|e| format!("fairness on `{name}`: {e}"))?;
        fair_code += &code;
    }
    fair_code += &g.gen_fair_dispatch(&fair_ops)?;

    // Invariants. If this is the invariant the types came from and every conjunct was read as a
    // type declaration, there is no need to check it at runtime: pack performs the same check while
    // packing the state and reports a violation under the same name.
    let type_inv_subsumed = leftover == 0 && ex.has_def(tname) && cfg.invariants.iter().any(|n| n == tname);
    let mut inv_code = String::new();
    let mut inv_list = vec![];
    for (i, name) in cfg.invariants.iter().enumerate() {
        if type_inv_subsumed && name == tname {
            continue;
        }
        let e = ex.expand_def(name)?;
        let c = g.gen_as(&e, &Gen::env_next(), &Ty::Bool).map_err(|m| format!("invariant {name}: {m}"))?;
        writeln!(inv_code, "fn inv_{i}(s: &State) -> bool {{ {c} }}").unwrap();
        inv_list.push(format!("({name:?}, inv_{i} as fn(&State) -> bool)"));
    }

    // Temporal properties
    let mut props: Vec<(String, u8, String, String)> = vec![];
    let mut action_props: Vec<(String, String, String)> = vec![];
    for name in &cfg.properties {
        let e = ex.expand_def(name)?;
        let mut parts = vec![];
        split_property(&g, &e, &HashMap::new(), name, &mut parts)?;
        for (disp, kind, p, q, env) in parts {
            if kind == 5 {
                let env = g.env_step(env);
                let pc = g.gen_as(&p, &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?;
                let qc = g.gen_as(&q.unwrap(), &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?;
                action_props.push((disp, pc, qc));
                continue;
            }
            let pc = g.gen_as(&p, &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?;
            let qc = match q {
                Some(q) => g.gen_as(&q, &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?,
                None => "true".into(),
            };
            props.push((disp, kind, pc, qc));
        }
    }
    let mut prop_code = String::new();
    let mut prop_list = vec![];
    let mut aprop_list = vec![];
    for (i, (disp, pc, qc)) in action_props.iter().enumerate() {
        writeln!(prop_code, "fn aprop_{i}(s: &State, t: &State) -> bool {{ {pc} || {qc} }}").unwrap();
        aprop_list.push(format!("({disp:?}, aprop_{i} as fn(&State, &State) -> bool)"));
    }
    // CONSTRAINT: states that violate it are discarded (as in TLC, they are neither counted nor
    // checked against invariants)
    let mut cons = vec![];
    for name in &cfg.constraints {
        let e = ex.expand_def(name)?;
        cons.push(g.gen_as(&e, &Gen::env_next(), &Ty::Bool).map_err(|m| format!("constraint {name}: {m}"))?);
    }
    writeln!(prop_code, "fn constraint(s: &State) -> bool {{ {} }}", if cons.is_empty() { "true".into() } else { cons.join(" && ") }).unwrap();
    for (i, (disp, kind, pc, qc)) in props.iter().enumerate() {
        writeln!(prop_code, "fn prop_{i}_p(s: &State) -> bool {{ {pc} }}\nfn prop_{i}_q(s: &State) -> bool {{ {qc} }}").unwrap();
        prop_list.push(format!("({disp:?}, {kind}u8, prop_{i}_p as fn(&State) -> bool, prop_{i}_q as fn(&State) -> bool)"));
    }

    let pack = g.gen_pack()?;
    // VIEW and SYMMETRY
    let view_expr = match &cfg.view {
        Some(v) => Some(ex.expand_def(v)?),
        None => None,
    };
    let key_code = g.gen_key(view_expr.as_ref())?;
    let mut perms: Vec<Vec<u16>> = vec![];
    if let Some(sym) = &cfg.symmetry {
        let e = ex.expand_def(sym)?;
        let v = g.ce.eval(&e, &HashMap::new()).map_err(|m| format!("SYMMETRY {sym}: {m}"))?;
        for f in v.as_set()? {
            let Value::Fun(m) = f else { return Err(format!("SYMMETRY {sym} must be a set of permutations")) };
            let mut t: Vec<u16> = (0..atoms.list.len() as u16).collect();
            for (a, b) in m {
                let (Value::Atom(a), Value::Atom(b)) = (a, b) else {
                    return Err(format!("SYMMETRY {sym}: only permutations of model values / strings are supported"));
                };
                t[*a as usize] = *b as u16;
            }
            perms.push(t);
        }
    }
    let perm_code = if perms.is_empty() {
        "static PERMS: &[&[u16]] = &[];\nfn perm_state(s: &State, _: &[u16]) -> State { *s }\n".to_string()
    } else {
        g.gen_perms(&perms)?
    };
    let helpers = g.helpers()?;
    let mut src = String::new();
    writeln!(src, "// Generated by tla2rs from module {}. Do not edit.", m.name).unwrap();
    src += "#![allow(unused, non_snake_case, unused_parens, unused_braces, clippy::all)]\n";
    src += &g.atoms_table();
    let fields: Vec<String> = g.vars.iter().map(|(v, t)| format!("v_{v}: {}", t.repr())).collect();
    writeln!(src, "#[derive(Clone, Copy, PartialEq, Eq, Hash)]\nstruct State {{ {} }}", fields.join(", ")).unwrap();
    src += &helpers;
    src += &pack;
    src += &key_code;
    src += &perm_code;
    writeln!(src, "fn init(out: &mut Vec<State>) {{\n{init_code}}}").unwrap();
    writeln!(src, "fn next(s: &State, out: &mut Vec<(State, u32)>) {{\n{next_code}}}").unwrap();
    src += &inv_code;
    src += &prop_code;
    src += &fair_code;
    writeln!(src, "const TYPE_INVARIANT: &str = {tname:?};").unwrap();
    writeln!(src, "const TYPE_INV_SUBSUMED: bool = {type_inv_subsumed};").unwrap();
    writeln!(src, "static PROPS: &[(&str, u8, fn(&State) -> bool, fn(&State) -> bool)] = &[{}];", prop_list.join(", ")).unwrap();
    let fair_names: Vec<String> = g.fair.iter().map(|f| format!("{:?}", f.display)).collect();
    writeln!(src, "static FAIR: &[&str] = &[{}];", fair_names.join(", ")).unwrap();
    writeln!(src, "static ACTION_PROPS: &[(&str, fn(&State, &State) -> bool)] = &[{}];", aprop_list.join(", ")).unwrap();
    writeln!(src, "const LIVENESS: bool = {};", !props.is_empty()).unwrap();
    writeln!(src, "static INVARIANTS: &[(&str, fn(&State) -> bool)] = &[{}];", inv_list.join(", ")).unwrap();
    let labels: Vec<String> = g.labels.iter().map(|l| format!("{l:?}")).collect();
    writeln!(src, "static LABELS: &[&str] = &[{}];", labels.join(", ")).unwrap();
    let mut show = String::from("fn show(s: &State) -> String { let mut o = String::new(); ");
    for (i, (v, t)) in g.vars.clone().iter().enumerate() {
        let tid = g.ty_id_pub(t)?;
        let nl = if i + 1 < g.vars.len() { "\\n" } else { "" };
        write!(show, "o += &format!(\"/\\\\ {v} = {{}}{nl}\", fmt_{tid}(&s.v_{v})); ").unwrap();
    }
    show += "o }\n";
    src += &show;
    writeln!(src, "const CHECK_DEADLOCK: bool = {};", cfg.check_deadlock.unwrap_or(true)).unwrap();
    writeln!(src, "const SCAP: usize = {};", g.scap).unwrap();
    let fp_bits = if fp128 { 128 } else { 64 };
    writeln!(src, "const FP_BITS: usize = {fp_bits};\ntype Fp = u{fp_bits};").unwrap();
    src += if metal { crate::metal::GLUE } else { crate::metal::NO_GPU };
    src += crate::runtime::RUNTIME;
    src += crate::runtime::LIVENESS_RT;
    Ok(Output { rust: src, warnings, assume_failed: None })
}

fn collect_strings(e: &Expr, atoms: &mut Atoms) {
    match e {
        Expr::Str(s) => {
            atoms.intern(false, s);
        }
        Expr::Ident(n) => {
            if let Some(mv) = n.strip_prefix("@model:") {
                atoms.intern(true, mv);
            }
        }
        _ => {}
    }
    for c in e.children() {
        collect_strings(c, atoms);
    }
    if let Expr::Let(defs, _) = e {
        for d in defs {
            collect_strings(&d.body, atoms);
        }
    }
}

fn flatten_and(e: &Expr, out: &mut Vec<Expr>) {
    match e.strip() {
        Expr::And(xs) => {
            for x in xs {
                flatten_and(x, out);
            }
        }
        e => out.push(e.clone()),
    }
}

/// Builds the element type from a set expression used in type position.
fn ty_of_set(g: &Gen, s: &Expr) -> R<Ty> {
    let ce = &g.ce;
    let no = HashMap::new();
    Ok(match s.strip() {
        Expr::Un(UOp::Subset, x) => Ty::Set(ty_of_set(g, x)?.into()),
        Expr::FunSet(d, r) => {
            let dv = ce.eval(d, &no)?;
            Ty::Fun(elem_ty_of_domain(dv.as_set()?)?.into(), ty_of_set(g, r)?.into())
        }
        Expr::RecSet(fs) => {
            let mut fs: Vec<(String, Ty)> = fs.iter().map(|(k, x)| Ok((k.clone(), ty_of_set(g, x)?))).collect::<R<_>>()?;
            fs.sort_by(|a, b| a.0.cmp(&b.0));
            Ty::Rec(fs)
        }
        Expr::Ident(n) if n == "BOOLEAN" => Ty::Bool,
        // Unbounded integers are stored as 64-bit
        Expr::Ident(n) if n == "Nat" => Ty::Int(0, BIG),
        Expr::Ident(n) if n == "Int" => Ty::Int(-BIG, BIG),
        e => {
            let v = ce.eval(e, &no)?;
            let set = v.as_set()?;
            if set.is_empty() {
                return Err("empty set as a type".into());
            }
            match ty_of_value(&v)? {
                Ty::Set(t) => *t,
                _ => unreachable!(),
            }
        }
    })
}

fn is_temporal(e: &Expr, m: &Module, seen: &mut HashSet<String>) -> bool {
    e.any(&|x| matches!(x, Expr::Un(UOp::Always | UOp::Eventually, _) | Expr::BoxAction(..) | Expr::Fair(..)))
        || {
            let mut names = vec![];
            collect_refs(e, &mut names);
            names.into_iter().any(|n| {
                if !seen.insert(n.clone()) {
                    return false;
                }
                m.defs.iter().find(|d| d.name == n).is_some_and(|d| is_temporal(&d.body, m, seen))
            })
        }
}

fn collect_refs(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Ident(n) | Expr::Call(n, _) => out.push(n.clone()),
        _ => {}
    }
    for c in e.children() {
        collect_refs(c, out);
    }
}

fn resolve_spec(m: &Module, cfg: &Cfg, ex: &mut Expander) -> R<(Expr, Expr, Vec<Expr>)> {
    if let (Some(i), Some(n)) = (&cfg.init, &cfg.next) {
        return Ok((ex.expand_def(i)?, ex.expand_def(n)?, vec![]));
    }
    let spec = cfg.specification.as_ref().ok_or("cfg needs SPECIFICATION or INIT/NEXT")?;
    let mut init = vec![];
    let mut next = None;
    let mut fair = vec![];
    let body = ex.def(spec).ok_or(format!("no definition `{spec}`"))?.body.clone();
    walk_spec(&body, m, ex, &mut init, &mut next, &mut fair)?;
    let next = next.ok_or(format!("{spec}: no [][Next]_vars conjunct"))?;
    if init.is_empty() {
        return Err(format!("{spec}: no initial predicate"));
    }
    let init = if init.len() == 1 { init.pop().unwrap() } else { Expr::And(init) };
    Ok((ex.expand_top(&init)?, ex.expand_top(&next)?, fair))
}

fn walk_spec(
    e: &Expr,
    m: &Module,
    ex: &mut Expander,
    init: &mut Vec<Expr>,
    next: &mut Option<Expr>,
    fair: &mut Vec<Expr>,
) -> R<()> {
    match e {
        Expr::And(xs) => {
            for x in xs {
                walk_spec(x, m, ex, init, next, fair)?;
            }
        }
        Expr::Un(UOp::Always, x) => match x.as_ref() {
            Expr::BoxAction(a, _) => *next = Some(a.as_ref().clone()),
            _ => return Err(format!("unsupported temporal conjunct in the spec: {}", short(e))),
        },
        Expr::Ident(n) if ex.def(n).is_some_and(|d| d.params.is_empty()) && is_temporal(e, m, &mut HashSet::new()) => {
            let b = ex.def(n).unwrap().body.clone();
            walk_spec(&b, m, ex, init, next, fair)?;
        }
        e if is_temporal(e, m, &mut HashSet::new()) => fair.push(e.clone()),
        e => init.push(e.clone()),
    }
    Ok(())
}

/// Enumerates (is_weak, operator, arguments) triples from a fairness formula.
fn collect_fair(
    e: &Expr,
    env: &HashMap<String, Value>,
    g: &mut Gen,
    vars: &[String],
    warnings: &mut Vec<String>,
) -> R<()> {
    match e {
        Expr::Label(_, _, b) => collect_fair(b, env, g, vars, warnings),
        Expr::And(xs) => {
            for x in xs {
                collect_fair(x, env, g, vars, warnings)?;
            }
            Ok(())
        }
        Expr::Quant(false, bs, body) => {
            let mut err = Ok(());
            g.ce.clone().each_binding(bs, env, &mut |env2| {
                if let Err(m) = collect_fair(body, env2, g, vars, warnings) {
                    err = Err(m);
                    return Ok(false);
                }
                Ok(true)
            })?;
            err
        }
        Expr::Fair(weak, sub, a) => {
            if !weak {
                return Err("strong fairness (SF) is not supported yet".into());
            }
            let mut sv = vec![];
            sub_vars(sub, &mut sv)?;
            for v in &sv {
                if !vars.contains(v) {
                    return Err(format!("WF subscript `{v}` is not a variable"));
                }
            }
            let _ = &warnings;
            let Expr::Label(name, args, _) = a.as_ref() else {
                return Err(format!("fairness on an unnamed action is not supported yet; give it a definition ({})", short(a)));
            };
            let vals: Vec<Value> = args.iter().map(|x| g.ce.eval(x, env)).collect::<R<_>>()?;
            let shown: Vec<String> = vals.iter().map(|v| show_value(g.atoms, v)).collect();
            let disp = if shown.is_empty() { format!("WF({name})") } else { format!("WF({name}({}))", shown.join(", ")) };
            g.fair.push(crate::codegen::FairInst { name: name.clone(), args: vals, display: disp, sub: sv });
            Ok(())
        }
        _ => Err(format!("unsupported fairness formula: {}", short(e))),
    }
}

fn sub_vars(e: &Expr, out: &mut Vec<String>) -> R<()> {
    match e.strip() {
        Expr::Ident(n) => out.push(n.clone()),
        Expr::Tuple(xs) => {
            for x in xs {
                sub_vars(x, out)?;
            }
        }
        e => return Err(format!("unsupported WF subscript {}", short(e))),
    }
    Ok(())
}

pub fn show_value(atoms: &Atoms, v: &Value) -> String {
    match v {
        Value::Bool(b) => if *b { "TRUE".into() } else { "FALSE".into() },
        Value::Int(i) => i.to_string(),
        Value::Atom(a) => atoms.show(*a),
        Value::Set(s) => format!("{{{}}}", s.iter().map(|x| show_value(atoms, x)).collect::<Vec<_>>().join(", ")),
        Value::Rec(m) => format!("[{}]", m.iter().map(|(k, x)| format!("{k} |-> {}", show_value(atoms, x))).collect::<Vec<_>>().join(", ")),
        Value::Fun(m) => format!("({})", m.iter().map(|(k, x)| format!("{} :> {}", show_value(atoms, k), show_value(atoms, x))).collect::<Vec<_>>().join(" @@ ")),
        Value::Tuple(t) => format!("<<{}>>", t.iter().map(|x| show_value(atoms, x)).collect::<Vec<_>>().join(", ")),
    }
}

type PropPart = (String, u8, Expr, Option<Expr>, crate::codegen::Env);

/// Splits a property into checkable forms: 0: <>P, 1: []<>P, 2: <>[]P, 3: P ~> Q, 4: []P (state
/// predicate), 5: [][A]_v.
fn split_property(g: &Gen, e: &Expr, env: &HashMap<String, Value>, name: &str, out: &mut Vec<PropPart>) -> R<()> {
    use Expr::*;
    let temporal = |x: &Expr| x.any(&|y| matches!(y, Un(UOp::Always | UOp::Eventually, _) | Bin(BOp::LeadsTo, ..)));
    let mut cenv = Gen::env_next();
    let mut tag = String::new();
    for (k, v) in env {
        let lit = crate::codegen::lit_for(g, v)?;
        cenv.bind(k, lit.0, lit.1);
        tag += &format!("{}={}", k.split("__").next().unwrap_or(k), show_value(g.atoms, v));
    }
    let disp = if tag.is_empty() { name.to_string() } else { format!("{name} [{tag}]") };
    match e {
        Label(_, _, b) => split_property(g, b, env, name, out),
        And(xs) => xs.iter().try_for_each(|x| split_property(g, x, env, name, out)),
        Quant(false, bs, body) => {
            let mut err = Ok(());
            g.ce.each_binding(bs, env, &mut |env2| {
                if let Err(m) = split_property(g, body, env2, name, out) {
                    err = Err(m);
                    return Ok(false);
                }
                Ok(true)
            })?;
            err
        }
        Un(UOp::Eventually, p) => match p.strip() {
            Un(UOp::Always, q) if !temporal(q) => Ok(out.push((disp, 2, q.as_ref().clone(), None, cenv))),
            p if !temporal(p) => Ok(out.push((disp, 0, p.clone(), None, cenv))),
            _ => Err(format!("property {name}: unsupported form {}", short(e))),
        },
        Un(UOp::Always, p) => match p.strip() {
            Un(UOp::Eventually, q) if !temporal(q) => Ok(out.push((disp, 1, q.as_ref().clone(), None, cenv))),
            Bin(BOp::LeadsTo, a, b) if !temporal(a) && !temporal(b) => {
                Ok(out.push((disp, 3, a.as_ref().clone(), Some(b.as_ref().clone()), cenv)))
            }
            p if !temporal(p) && !p.is_action() => Ok(out.push((disp, 4, p.clone(), None, cenv))),
            // [][A]_v: every transition is an A step or leaves v unchanged
            BoxAction(a, v) if !temporal(a) => {
                Ok(out.push((disp, 5, a.as_ref().clone(), Some(Un(UOp::Unchanged, v.clone())), cenv)))
            }
            _ => Err(format!("property {name}: unsupported form {}", short(e))),
        },
        Bin(BOp::LeadsTo, a, b) if !temporal(a) && !temporal(b) => {
            Ok(out.push((disp, 3, a.as_ref().clone(), Some(b.as_ref().clone()), cenv)))
        }
        _ => Err(format!("property {name}: only <>P, []<>P, <>[]P, P ~> Q and []P are supported ({})", short(e))),
    }
}

/// Type inference. Taking the types fixed by TypeOK as given, walks Init and Next at the type level
/// only, collecting the types of assignments, and iterates to a fixpoint. Integers whose range
/// keeps changing are widened to unbounded (64-bit).
#[allow(clippy::too_many_arguments)]
fn infer_types(
    atoms: &Atoms,
    constants: &HashMap<String, Value>,
    vars: &[String],
    decl: &HashMap<String, Ty>,
    undeclared: &[String],
    init: &Expr,
    next: &Expr,
    scap: usize,
) -> R<HashMap<String, Ty>> {
    let bottom = Ty::Enum(vec![]);
    let mut cur: HashMap<String, Ty> = undeclared.iter().map(|v| (v.clone(), bottom.clone())).collect();
    for _ in 0..40 {
        let mut g = Gen::new(atoms, constants);
        g.scap = scap;
        for v in vars {
            g.vars.push((v.clone(), decl.get(v).or(cur.get(v)).unwrap().clone()));
        }
        g.infer = Some(HashMap::new());
        let mut sink = String::new();
        let _ = g.gen_action(&[init.clone()], &Gen::env_init(), &mut sink);
        let _ = g.gen_action(&[next.clone()], &Gen::env_next(), &mut sink);
        let got = g.infer.take().unwrap();
        let mut changed = false;
        for v in undeclared {
            let old = cur[v].clone();
            let Some(t) = got.get(v) else { continue };
            let j = join(&old, t).unwrap_or_else(|_| t.clone());
            let w = widen(&old, &j);
            if w != old {
                cur.insert(v.clone(), w);
                changed = true;
            }
        }
        if !changed {
            for v in undeclared {
                if cur[v] == bottom {
                    return Err(format!("cannot infer the type of `{v}`; add `{v} \\in S` to TypeOK (or TypeDecl)"));
                }
            }
            return Ok(cur);
        }
    }
    Err(format!("type inference did not settle for {}; add them to TypeOK (or TypeDecl)", undeclared.join(", ")))
}

/// Widens integers whose range changed from the previous type to unbounded.
fn widen(old: &Ty, new: &Ty) -> Ty {
    match (old, new) {
        (Ty::Enum(o), _) if o.is_empty() => new.clone(),
        (Ty::Int(a, b), Ty::Int(c, d)) if (a, b) != (c, d) => Ty::Int(if c < a { -BIG } else { *a }, if d > b { BIG } else { *b }),
        (Ty::Rec(a), Ty::Rec(b)) => Ty::Rec(
            b.iter()
                .map(|(n, t)| match a.iter().find(|(m, _)| m == n) {
                    Some((_, o)) => (n.clone(), widen(o, t)),
                    None => (n.clone(), t.clone()),
                })
                .collect(),
        ),
        (Ty::Opt(a), Ty::Opt(b)) => Ty::Opt(widen(a, b).into()),
        (a, Ty::Opt(b)) => Ty::Opt(widen(a, b).into()),
        (Ty::Fun(_, a), Ty::Fun(d, b)) => Ty::Fun(d.clone(), widen(a, b).into()),
        (Ty::Set(a), Ty::Set(b)) => Ty::Set(widen(a, b).into()),
        _ => new.clone(),
    }
}
