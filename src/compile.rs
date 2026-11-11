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
    /// Why TLC refuses the spec before checking anything, worded as TLC reports it, and its exit
    /// code: an ASSUME that is false or fails to evaluate (10), a temporal formula TLC cannot check
    /// (150 or 255). When set, no checker is generated.
    pub rejected: Option<(String, i32)>,
}

const TYPE_OK_NAMES: &[&str] = &["TypeOK", "TypeOk", "TypeInvariant", "TypeInv", "TypeCorrect"];

const TYPE_DECL_NAMES: &[&str] = &["TypeDecl"];

/// The bounded sequences `UNION {[1..n -> S] : n \in R}`: (R, S)
pub fn bounded_seq(e: &Expr) -> Option<(&Expr, &Expr)> {
    let Expr::Un(UOp::Union, x) = e.strip() else { return None };
    let Expr::SetMap(f, bs) = x.strip() else { return None };
    let [(n, r)] = bs.as_slice() else { return None };
    let Expr::FunSet(d, s) = f.strip() else { return None };
    match d.strip() {
        Expr::Bin(BOp::Range, lo, hi) if matches!(lo.strip(), Expr::Num(1)) && matches!(hi.strip(), Expr::Ident(m) if m == n) => Some((r, s)),
        _ => None,
    }
}

/// The maximum length of a sequence value. `-seqcap N` sets it. Otherwise it comes from bounds
/// `Len(e) <= N` (or `< N`) among the conjuncts of TypeOK and of the CONSTRAINTs: one more than
/// the largest, so that a state one element too long can still be built, counted, and reported
/// by TypeOK or discarded by the constraint as in TLC. Without either it is the length of the
/// longest tuple written in the spec, unless the spec makes sequences grow (Append, \o, Seq),
/// in which case it stays unknown (0) and using a sequence is an error that asks for a bound.
fn seq_cap(m: &Module, cfg: &Cfg, ex: &mut Expander, g: &Gen, seqcap: usize, init: &Expr, next: &Expr) -> R<usize> {
    fn longest(e: &Expr) -> usize {
        let here = if let Expr::Tuple(xs) = e { xs.len() } else { 0 };
        e.children().into_iter().map(longest).max().unwrap_or(0).max(here)
    }
    fn grows(e: &Expr) -> bool {
        e.any(&|x| matches!(x, Expr::Call(f, _) if f == "Append" || f == "\\o" || f == "Seq"))
    }
    let lit = m.defs.iter().map(|d| longest(&d.body)).chain(cfg.constants.iter().map(|(_, e)| longest(e))).max().unwrap_or(0);
    let cap = if seqcap > 0 {
        seqcap.max(lit)
    } else {
        let mut bound: Option<usize> = None;
        let mut sources: Vec<Expr> = vec![];
        for n in TYPE_DECL_NAMES.iter().chain(TYPE_OK_NAMES) {
            if ex.has_def(n) {
                sources.push(ex.expand_def(n)?);
            }
        }
        for c in &cfg.constraints {
            sources.push(ex.expand_def(c)?);
        }
        // Conjuncts, also under \A (as in `\A p \in P : Len(q[p]) <= N`)
        fn conjuncts(e: &Expr, out: &mut Vec<Expr>) {
            match e.strip() {
                Expr::And(xs) => xs.iter().for_each(|x| conjuncts(x, out)),
                Expr::Quant(false, _, b) => conjuncts(b, out),
                e => out.push(e.clone()),
            }
        }
        for src in &sources {
            let mut conj = vec![];
            conjuncts(src, &mut conj);
            for c in conj {
                // x \in UNION {[1..n -> S] : n \in R}
                if let Expr::Bin(BOp::In, _, set) = c.strip() {
                    if let Some((r, _)) = bounded_seq(set) {
                        if let Ok(Value::Set(r)) = g.ce.eval(r, &HashMap::new()) {
                            if let Some(Value::Int(k)) = r.iter().max() {
                                bound = Some(bound.unwrap_or(0).max(*k.max(&0) as usize + 1));
                            }
                        }
                    }
                }
                let (k, strict) = match c.strip() {
                    Expr::Bin(BOp::Le, l, k) if matches!(l.strip(), Expr::Call(f, _) if f == "Len") => (k, false),
                    Expr::Bin(BOp::Lt, l, k) if matches!(l.strip(), Expr::Call(f, _) if f == "Len") => (k, true),
                    _ => continue,
                };
                if let Ok(Value::Int(k)) = g.ce.eval(k, &HashMap::new()) {
                    let n = (k.max(0) as usize).saturating_sub(strict as usize);
                    bound = Some(bound.unwrap_or(0).max(n + 1));
                }
            }
        }
        // Otherwise a test of a length anywhere in the spec (a guard such as `Len(q) < 3` before
        // an Append) suggests the bound. It need not be proven: a sequence growing past the bound
        // is an evaluation error, never cut short
        let guard = || -> Option<usize> {
            let best = std::cell::Cell::new(None::<usize>);
            for d in &m.defs {
                d.body.any(&|e| {
                    let k = match e {
                        Expr::Bin(BOp::Le | BOp::Lt, l, k) if matches!(l.strip(), Expr::Call(f, _) if f == "Len") => k,
                        Expr::Bin(BOp::Ge | BOp::Gt, k, l) if matches!(l.strip(), Expr::Call(f, _) if f == "Len") => k,
                        _ => return false,
                    };
                    if let Ok(Value::Int(k)) = g.ce.eval(k, &HashMap::new()) {
                        best.set(Some(best.get().unwrap_or(0).max(k.max(0) as usize + 2)));
                    }
                    false
                });
            }
            best.get()
        };
        // Otherwise the lengths Init and Next can reach, when they settle
        let mut settled = || -> R<Option<usize>> {
            let mut others = vec![];
            for n in cfg.invariants.iter().chain(&cfg.properties).chain(&cfg.constraints).chain(&cfg.action_constraints).chain(&cfg.view) {
                others.push(ex.expand_def(n)?);
            }
            Ok(crate::seqlen::settled_bound(&m.variables, g.ce.constants, init, next, &others))
        };
        match bound {
            Some(b) => b.max(lit),
            None => match settled()? {
                Some(b) => b.max(lit),
                None if m.defs.iter().any(|d| grows(&d.body)) => guard().map_or(0, |b| b.max(lit)),
                None => lit,
            },
        }
    };
    if cap > 1024 {
        return Err(format!("sequences of up to {cap} elements are not supported (at most 1024)"));
    }
    Ok(cap)
}

/// Applies the cfg entries that replace a definition (`Name = value`, `Name <- Def`,
/// `Name <- [Module] Def` where Name is defined rather than declared) and returns the constants
/// substituted by a definition, (constant, definition), to be evaluated once the other constants
/// are known. As in TLC, `[Module]` applies to definitions only, and `Name = value` for a name that
/// is neither declared nor defined is ignored.
fn override_defs(m: &mut Module, cfg: &Cfg, warnings: &mut Vec<String>) -> R<Vec<(String, String)>> {
    let def_params = |m: &Module, n: &str| m.defs.iter().rev().find(|d| d.name == n).map(|d| d.params.clone());
    let mut extra = vec![];
    // A CONSTANT with parameters becomes a definition: `F <- Def` is F(p, ...) == Def(p, ...), and
    // `F = v` (which TLC accepts) is F(p, ...) == v
    let op_arity = |n: &str| m.op_constants.iter().find(|(c, _)| c == n).map(|(_, k)| *k);
    let fresh = |k: usize| (1..=k).map(|i| format!("#p{i}")).collect::<Vec<_>>();
    let mut op_done = vec![];
    for (n, e) in &cfg.constants {
        if let Some(k) = op_arity(n) {
            extra.push(Def { name: n.clone(), params: fresh(k), arity: vec![0; k], body: e.clone() });
            op_done.push(n.clone());
        }
    }
    for (n, module, def) in &cfg.substs {
        let Some(k) = op_arity(n) else { continue };
        if let Some(md) = module {
            return Err(format!("cfg: `{n} <- [{md}] {def}`: [Module] replaces a definition, but {n} is a CONSTANT (TLC leaves it without a value)"));
        }
        let Some(dp) = def_params(m, def) else {
            return Err(format!("cfg: `{n} <- {def}`: {def} is not defined"));
        };
        if dp.len() != k {
            return Err(format!("cfg: `{n} <- {def}`: {n} takes {k} arguments and {def} takes {}", dp.len()));
        }
        if op_done.contains(n) {
            return Err(format!("cfg: `{n}` is given a value more than once"));
        }
        let ps = fresh(k);
        let body = Expr::Call(def.clone(), ps.iter().map(|p| Expr::Ident(p.clone())).collect());
        extra.push(Def { name: n.clone(), params: ps, arity: vec![0; k], body });
        op_done.push(n.clone());
    }
    m.constants.retain(|c| !op_done.contains(c));
    for (n, e) in &cfg.constants {
        if m.constants.contains(n) || op_done.contains(n) {
            continue;
        }
        match def_params(m, n) {
            Some(p) if p.is_empty() => extra.push(Def { name: n.clone(), params: vec![], arity: vec![], body: e.clone() }),
            Some(_) => return Err(format!("cfg: `{n} = ...` replaces an operator that takes arguments")),
            None => warnings.push(format!("cfg: `{n}` is neither a CONSTANT nor a definition of the spec; ignored")),
        }
    }
    let mut const_substs = vec![];
    for (n, module, def) in &cfg.substs {
        if op_done.contains(n) {
            continue;
        }
        if const_substs.iter().any(|(c, _): &(String, String)| c == n) || cfg.constants.iter().any(|(c, _)| c == n) {
            return Err(format!("cfg: `{n}` is given a value more than once"));
        }
        let Some(dp) = def_params(m, def) else {
            return Err(format!("cfg: `{n} <- {def}`: {def} is not defined"));
        };
        if let Some(md) = module {
            if !m.modules.contains(md) {
                return Err(format!("cfg: `{n} <- [{md}] {def}`: {md} is not a module of the spec"));
            }
        }
        if m.constants.contains(n) {
            if let Some(md) = module {
                return Err(format!("cfg: `{n} <- [{md}] {def}`: [Module] replaces a definition, but {n} is a CONSTANT (TLC leaves it without a value)"));
            }
            if !dp.is_empty() {
                return Err(format!("cfg: `{n} <- {def}`: {n} takes no arguments and {def} takes {}", dp.len()));
            }
            const_substs.push((n.clone(), def.clone()));
            continue;
        }
        let Some(np) = def_params(m, n) else {
            return Err(format!("cfg: `{n} <- {def}`: {n} is neither a CONSTANT nor a definition of the spec"));
        };
        if np.len() != dp.len() {
            return Err(format!("cfg: `{n} <- {def}`: they take {} and {} arguments", np.len(), dp.len()));
        }
        // Name(p1, ...) == Def(p1, ...); defined last, so it takes precedence
        let args: Vec<Expr> = np.iter().map(|p| Expr::Ident(p.clone())).collect();
        let body = if args.is_empty() { Expr::Ident(def.clone()) } else { Expr::Call(def.clone(), args) };
        let arity = m.defs.iter().rev().find(|d| d.name == *n).map(|d| d.arity.clone()).unwrap_or_default();
        extra.push(Def { name: n.clone(), params: np, arity, body });
    }
    m.defs.extend(extra);
    Ok(const_substs)
}

/// Loads the EXTENDS'd modules whose .tla files sit in the same directory and merges them into one.
/// Definitions loaded later (from the extending module) take precedence.
fn load_module(src: &str, dir: &std::path::Path, warnings: &mut Vec<String>, depth: usize) -> R<Module> {
    load_parsed(parse_module(src)?, dir, warnings, depth)
}

thread_local! {
    /// Modules nested in the modules loaded so far, by name
    static NESTED: std::cell::RefCell<HashMap<String, Module>> = std::cell::RefCell::new(HashMap::new());
}

/// The module `name` for EXTENDS or INSTANCE: one nested in a loaded module, or else the file next
/// to the spec
fn find_module(name: &str, how: &str, dir: &std::path::Path, warnings: &mut Vec<String>, depth: usize) -> R<Module> {
    if let Some(m) = NESTED.with(|n| n.borrow().get(name).cloned()) {
        return load_parsed(m, dir, warnings, depth);
    }
    let path = dir.join(format!("{name}.tla"));
    let src = std::fs::read_to_string(&path).map_err(|_| format!("{how} {name}: module not found next to the spec"))?;
    load_module(&src, dir, warnings, depth)
}

fn load_parsed(m: Module, dir: &std::path::Path, warnings: &mut Vec<String>, depth: usize) -> R<Module> {
    if depth > 16 {
        return Err("EXTENDS nests too deeply".into());
    }
    NESTED.with(|n| {
        for inner in &m.nested {
            n.borrow_mut().insert(inner.name.clone(), inner.clone());
        }
    });
    let mut out = Module { name: m.name.clone(), modules: vec![m.name.clone()], ..Default::default() };
    for e in &m.extends {
        if e == "RealTime" {
            real_time(&mut out);
            continue;
        }
        if e == "Reals" {
            reals(&mut out);
            continue;
        }
        if standard_module(e, "EXTENDS")? {
            out.extends.push(e.clone());
            continue;
        }
        match e.as_str() {
            // Apalache type annotations and Gen are not used
            "Apalache" => {}
            _ => {
                let sub = find_module(e, "EXTENDS", dir, warnings, depth + 1)?;
                out.extends.extend(sub.extends);
                out.constants.extend(sub.constants);
                out.variables.extend(sub.variables);
                out.defs.extend(sub.defs);
                out.assumes.extend(sub.assumes);
                out.modules.extend(sub.modules);
                out.op_constants.extend(sub.op_constants);
                out.recursive.extend(sub.recursive);
            }
        }
    }
    out.op_constants.extend(m.op_constants);
    out.recursive.extend(m.recursive);
    out.constants.extend(m.constants);
    out.variables.extend(m.variables);
    out.defs.extend(m.defs);
    out.assumes.extend(m.assumes);
    out.local_defs.extend(m.local_defs);
    for inst in &m.instances {
        instantiate(&mut out, inst, dir, warnings, depth)?;
    }
    Ok(out)
}

/// Whether `name` is a standard module that tla2rs provides itself (an error for the standard
/// modules it does not support)
fn standard_module(name: &str, how: &str) -> R<bool> {
    match name {
        // Reals in TLC is Integers plus operators it cannot evaluate. Toolbox only has definitions
        // for the Toolbox's trace explorer.
        "Naturals" | "Integers" | "FiniteSets" | "TLC" | "Sequences" | "Reals" | "Toolbox" | "Bags" => Ok(true),
        // Handled by `real_time` (EXTENDS only)
        "RealTime" => Err(format!("{how} {name}: only EXTENDS RealTime is supported")),
        // TLC picks the subsets at random, so its results cannot be reproduced
        "Randomization" => Err(format!("{how} {name}: TLC chooses its values at random; not supported")),
        _ => Ok(false),
    }
}

/// The order in which TLC creates the strings it knows before it starts exploring: TLC orders
/// strings by when it first creates them. Measured on TLC 2.19: the strings and model values of
/// the cfg; SANY's built-in names; the identifiers and keywords of each module as it parses them,
/// root module first and then the modules it extends or instantiates, breadth first; a few more
/// built-in names; then the string literals of each module, dependencies before the modules that
/// use them. Strings created later (by \o, ToString, ...) follow, in the order TLC happens to
/// create them, which tla2rs does not reproduce (see CLAUDE.md).
fn tlc_string_ranks(root: &str, cfg: &Cfg, dir: &std::path::Path) -> HashMap<String, usize> {
    let mut order: Vec<String> = vec![];
    fn cfg_values(e: &Expr, order: &mut Vec<String>) {
        match e {
            Expr::Str(x) => order.push(x.clone()),
            Expr::Ident(n) => {
                if let Some(mv) = n.strip_prefix("@model:") {
                    order.push(mv.to_string());
                }
            }
            _ => {}
        }
        for c in e.children() {
            cfg_values(c, order);
        }
    }
    for (_, v) in &cfg.constants {
        cfg_values(v, &mut order);
    }
    for b in ["ENABLED", "UNCHANGED", "SUBSET", "UNION", "DOMAIN", "STRING", "FALSE", "TRUE", "BOOLEAN"] {
        order.push(b.into());
    }
    // (identifiers, dependencies, strings) of a module, from its file next to the spec or from
    // TLC's standard modules
    let module = |src: Option<&str>, name: &str| -> (Vec<String>, Vec<String>, Vec<String>) {
        let src = match src {
            Some(x) => Some(x.to_string()),
            None => std::fs::read_to_string(dir.join(format!("{name}.tla"))).ok(),
        };
        let Some(src) = src else {
            return match crate::std_modules::STD_MODULES.iter().find(|m| m.0 == name) {
                Some((_, deps, ids, strs)) => (
                    ids.iter().map(|x| x.to_string()).collect(),
                    deps.iter().map(|x| x.to_string()).collect(),
                    strs.iter().map(|x| x.to_string()).collect(),
                ),
                None => (vec![], vec![], vec![]),
            };
        };
        let toks = crate::lexer::lex_module(&src).unwrap_or_default();
        let (mut ids, mut deps, mut strs) = (vec![], vec![], vec![]);
        for (i, t) in toks.iter().enumerate() {
            match &t.tok {
                crate::lexer::Tok::Ident(w) if w == "MODULE" => {}
                crate::lexer::Tok::Ident(w) => {
                    // SANY reads WF_v as WF_ and v
                    let w = if (w.starts_with("WF_") || w.starts_with("SF_")) && w.len() > 3 { &w[3..] } else { w.as_str() };
                    ids.push(w.to_string());
                    let prev = |k: usize| i.checked_sub(k).and_then(|j| toks.get(j)).map(|t| &t.tok);
                    let after_extends = {
                        let mut j = i;
                        loop {
                            match j.checked_sub(1).and_then(|k| toks.get(k)).map(|t| &t.tok) {
                                Some(crate::lexer::Tok::Sym(c)) if c == "," => j = j.saturating_sub(2),
                                Some(crate::lexer::Tok::Ident(k)) if k == "EXTENDS" => break true,
                                _ => break false,
                            }
                        }
                    };
                    if (after_extends || matches!(prev(1), Some(crate::lexer::Tok::Ident(k)) if k == "INSTANCE")) && !deps.contains(&w.to_string()) {
                        deps.push(w.to_string());
                    }
                }
                crate::lexer::Tok::Str(x) => strs.push(x.clone()),
                _ => {}
            }
        }
        (ids, deps, strs)
    };
    let root_name = crate::lexer::lex_module(root)
        .ok()
        .and_then(|t| t.iter().position(|x| x.tok == crate::lexer::Tok::Ident("MODULE".into())).and_then(|i| t.get(i + 1)).map(|x| x.tok.clone()));
    let root_name = match root_name {
        Some(crate::lexer::Tok::Ident(n)) => n,
        _ => String::new(),
    };
    let mut mods: HashMap<String, (Vec<String>, Vec<String>, Vec<String>)> = HashMap::new();
    mods.insert(root_name.clone(), module(Some(root), &root_name));
    // Identifiers, modules breadth first
    let mut queue = vec![root_name.clone()];
    let mut h = 0;
    while h < queue.len() {
        let name = queue[h].clone();
        h += 1;
        if !mods.contains_key(&name) {
            let m = module(None, &name);
            mods.insert(name.clone(), m);
        }
        let (ids, deps, _) = mods[&name].clone();
        order.extend(ids);
        for d in deps {
            if !queue.contains(&d) {
                queue.push(d);
            }
        }
    }
    for b in ["SF_", "WF_", "LAMBDA"] {
        order.push(b.into());
    }
    // String literals, dependencies first
    fn literals(name: &str, mods: &HashMap<String, (Vec<String>, Vec<String>, Vec<String>)>, done: &mut Vec<String>, order: &mut Vec<String>) {
        done.push(name.to_string());
        let Some((_, deps, strs)) = mods.get(name) else { return };
        for d in deps {
            if !done.contains(d) {
                literals(d, mods, done, order);
            }
        }
        order.extend(strs.iter().cloned());
    }
    literals(&root_name, &mods, &mut vec![], &mut order);
    let mut ranks = HashMap::new();
    for (i, x) in order.into_iter().enumerate() {
        ranks.entry(x).or_insert(i);
    }
    ranks
}

/// RealTime: Reals (for TLC, Integers) and the variable `now`. TLC cannot check RTBound and RTnow
/// (they quantify over Real, and RTBound uses \EE), so their bodies are left undefined: using them
/// is refused (see `uses_real_time`)
fn real_time(out: &mut Module) {
    reals(out);
    out.modules.push("RealTime".into());
    if !out.variables.iter().any(|v| v == "now") {
        out.variables.push("now".into());
    }
    for (name, params) in [("RTBound", vec!["A", "v", "D", "E"]), ("RTnow", vec!["v"])] {
        out.defs.push(Def {
            name: name.into(),
            params: params.iter().map(|p| p.to_string()).collect(),
            arity: vec![0; params.len()],
            body: Expr::Call(format!("#{name}"), vec![]),
        });
    }
}

/// Reals: for TLC, Integers, with the dummy Real == "Reals" of its Reals module (so using Real as
/// a set is an error, as in TLC)
fn reals(out: &mut Module) {
    out.extends.push("Reals".into());
    if !out.defs.iter().any(|d| d.name == "Real") {
        out.defs.push(Def { name: "Real".into(), params: vec![], arity: vec![], body: Expr::Str("Reals".into()) });
    }
}

/// Whether e uses RealTime's RTBound or RTnow
fn uses_real_time(e: &Expr) -> bool {
    e.any(&|x| matches!(x, Expr::Label(n, ..) if n == "RTBound" || n == "RTnow"))
}

/// The operators of the standard modules and their numbers of arguments, for a named instance
/// (`S == INSTANCE Sequences` used as `S!Len(s)`)
fn std_ops(m: &str) -> &'static [(&'static str, usize)] {
    const NAT: &[(&str, usize)] = &[
        ("Nat", 0), ("+", 2), ("-", 2), ("*", 2), ("^", 2), ("<", 2), (">", 2), ("<=", 2), (">=", 2), ("%", 2),
        ("\\div", 2), ("..", 2),
    ];
    const INT: &[(&str, usize)] = &[
        ("Nat", 0), ("Int", 0), ("+", 2), ("-", 2), ("*", 2), ("^", 2), ("<", 2), (">", 2), ("<=", 2), (">=", 2),
        ("%", 2), ("\\div", 2), ("..", 2),
    ];
    match m {
        "Naturals" => NAT,
        "Integers" | "Reals" => INT,
        "Sequences" => &[
            ("Seq", 1), ("Len", 1), ("\\o", 2), ("Append", 2), ("Head", 1), ("Tail", 1), ("SubSeq", 3), ("SelectSeq", 2),
        ],
        "FiniteSets" => &[("IsFiniteSet", 1), ("Cardinality", 1)],
        "TLC" => &[
            ("Print", 2), ("PrintT", 1), ("Assert", 2), ("JavaTime", 0), ("TLCGet", 1), ("TLCSet", 2), (":>", 2), ("@@", 2),
            ("Permutations", 1), ("SortSeq", 2), ("RandomElement", 1), ("Any", 0), ("ToString", 1), ("TLCEval", 1),
        ],
        "Bags" => &[
            ("IsABag", 1), ("BagToSet", 1), ("SetToBag", 1), ("BagIn", 2), ("EmptyBag", 0), ("\\oplus", 2), ("\\ominus", 2),
            ("BagUnion", 1), ("\\sqsubseteq", 2), ("SubBag", 1), ("BagCardinality", 1), ("CopiesIn", 2),
        ],
        _ => &[],
    }
}

/// Counts instances, to give the definitions of each one unique names
static INSTANCES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Adds the definitions of an instance of a module. Each definition D of the instantiated module
/// becomes a hidden definition that takes the module's constants and variables as leading
/// parameters, so that expanding a call substitutes them without capturing bound variables. The
/// visible definition (D for an unnamed instance, N!D for `N(p) == INSTANCE ...`) calls it with
/// the WITH substitutions (a constant or variable without one stands for the same name here). As
/// in TLC, the ASSUMEs of the instantiated module are not checked.
fn instantiate(out: &mut Module, inst: &Instance, dir: &std::path::Path, warnings: &mut Vec<String>, depth: usize) -> R<()> {
    let mname = &inst.module;
    if standard_module(mname, "INSTANCE")? {
        out.extends.push(mname.clone());
        // A named instance: N!Op stands for the module's Op
        if let Some(n) = &inst.name {
            for &(op, k) in std_ops(mname) {
                let ps: Vec<String> = (1..=k).map(|i| format!("#a{i}")).collect();
                let args: Vec<Expr> = ps.iter().map(|p| Expr::Ident(p.clone())).collect();
                let body = if op.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) {
                    if k == 0 { Expr::Ident(op.into()) } else { Expr::Call(op.into(), args) }
                } else {
                    let mut it = args.into_iter();
                    crate::parser::bin(op, it.next().unwrap(), it.next().unwrap())
                };
                let mut params = inst.params.clone();
                params.extend(ps);
                let mut arity = inst.arity.clone();
                arity.extend(vec![0; k]);
                out.defs.push(Def { name: format!("{n}!{op}"), params, arity, body });
            }
        }
        return Ok(());
    }
    let mm = find_module(mname, "INSTANCE", dir, warnings, depth + 1)?;
    out.extends.extend(mm.extends.iter().cloned());
    let k = INSTANCES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let arity_of = |c: &str| mm.op_constants.iter().find(|(n, _)| n == c).map_or(0, |(_, a)| *a);
    let params: Vec<(String, usize)> =
        mm.constants.iter().map(|c| (c.clone(), arity_of(c))).chain(mm.variables.iter().map(|v| (v.clone(), 0))).collect();
    for (x, _) in &inst.subs {
        if !params.iter().any(|(p, _)| p == x) {
            return Err(format!("INSTANCE {mname} WITH {x} <- ...: {x} is not a CONSTANT or VARIABLE of {mname}"));
        }
    }
    let raw = |d: &str| format!("{mname}#i{k}#{d}");
    let names: HashSet<&str> = mm.defs.iter().map(|d| d.name.as_str()).collect();
    let pargs: Vec<Expr> = params.iter().map(|(p, _)| Expr::Ident(p.clone())).collect();
    fn rename(e: &Expr, names: &HashSet<&str>, raw: &dyn Fn(&str) -> String, pargs: &[Expr]) -> Expr {
        match e {
            Expr::Ident(n) if names.contains(n.as_str()) => {
                if pargs.is_empty() { Expr::Ident(raw(n)) } else { Expr::Call(raw(n), pargs.to_vec()) }
            }
            Expr::Call(n, args) if names.contains(n.as_str()) => {
                let mut a = pargs.to_vec();
                a.extend(args.iter().map(|x| rename(x, names, raw, pargs)));
                Expr::Call(raw(n), a)
            }
            _ => crate::codegen::map_children(e, &|c| rename(c, names, raw, pargs)),
        }
    }
    for d in &mm.defs {
        let mut ps: Vec<String> = params.iter().map(|(p, _)| p.clone()).collect();
        ps.extend(d.params.iter().cloned());
        let mut arity: Vec<usize> = params.iter().map(|(_, a)| *a).collect();
        arity.extend(d.arity.iter().copied());
        out.defs.push(Def { name: raw(&d.name), params: ps, arity, body: rename(&d.body, &names, &raw, &pargs) });
    }
    for r in &mm.recursive {
        if names.contains(r.as_str()) {
            out.recursive.push(raw(r));
        } else {
            out.recursive.push(r.clone());
        }
    }
    // What each constant and variable of the instantiated module stands for here
    let known = |n: &str| {
        out.constants.iter().any(|c| c == n) || out.variables.iter().any(|v| v == n) || out.defs.iter().any(|d| d.name == n)
    };
    let mut args = vec![];
    for (p, _) in &params {
        match inst.subs.iter().find(|(x, _)| x == p) {
            Some((_, e)) => args.push(e.clone()),
            None if known(p) || inst.params.contains(p) => args.push(Expr::Ident(p.clone())),
            None => return Err(format!("INSTANCE {mname}: {p} has no WITH substitution and is not declared or defined here")),
        }
    }
    for d in &mm.defs {
        if mm.local_defs.contains(&d.name) || d.name.contains('#') {
            continue;
        }
        let mut call_args = args.clone();
        call_args.extend(d.params.iter().map(|p| Expr::Ident(p.clone())));
        let body = if call_args.is_empty() { Expr::Ident(raw(&d.name)) } else { Expr::Call(raw(&d.name), call_args) };
        let (name, params, arity) = match &inst.name {
            None => (d.name.clone(), d.params.clone(), d.arity.clone()),
            Some(n) => {
                let mut ps = inst.params.clone();
                ps.extend(d.params.iter().cloned());
                let mut ar = inst.arity.clone();
                // An instance hoisted out of a LET takes the names its substitutions mention; one
                // that names an operator with arguments is passed as that operator
                if n.contains("#let") {
                    for (i, p) in inst.params.iter().enumerate() {
                        if let Some(def) = out.defs.iter().rev().find(|x| x.name == *p) {
                            ar[i] = def.params.len();
                        }
                    }
                }
                ar.extend(d.arity.iter().copied());
                (format!("{n}!{}", d.name), ps, ar)
            }
        };
        if out.defs.iter().any(|x| x.name == name) {
            return Err(format!("INSTANCE {mname}: `{name}` is defined both here and in {mname}"));
        }
        out.defs.push(Def { name, params, arity, body });
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn compile(tla: &str, cfg_src: &str, dir: &std::path::Path, setcap: usize, seqcap: usize, fp128: bool, metal: bool) -> R<Output> {
    let mut warnings = vec![];
    let mut m = load_module(tla, dir, &mut warnings, 0)?;
    let cfg = parse_cfg(cfg_src)?;
    let const_substs = override_defs(&mut m, &cfg, &mut warnings)?;

    // Strings and model values. Strings are numbered in the order TLC creates them (TLC orders
    // strings that way), as far as that order is known before exploring
    let mut seen = Atoms::default();
    for d in &m.defs {
        collect_strings(&d.body, &mut seen);
    }
    for (_, v) in &cfg.constants {
        collect_strings(v, &mut seen);
    }
    for a in &m.assumes {
        collect_strings(&a.expr, &mut seen);
    }
    let ranks = tlc_string_ranks(tla, &cfg, dir);
    crate::types::set_field_ranks(ranks.clone());
    crate::types::clear_written_fields();
    for d in &m.defs {
        crate::types::note_written_fields(&d.body);
    }
    for a in &m.assumes {
        crate::types::note_written_fields(&a.expr);
    }
    let mut strings: Vec<String> = (0..seen.len() as u32).filter(|&a| !seen.is_model(a)).map(|a| seen.name(a)).collect();
    strings.sort_by_key(|x| ranks.get(x).copied().unwrap_or(usize::MAX));
    let atoms = Atoms::default();
    for x in &strings {
        atoms.intern(false, x);
    }
    for a in 0..seen.len() as u32 {
        if seen.is_model(a) {
            atoms.intern(true, &seen.name(a));
        }
    }

    // Constants
    let empty = HashMap::new();
    let mut constants = HashMap::new();
    {
        let ce = ConstEval { atoms: &atoms, constants: &empty };
        for c in &m.constants {
            if const_substs.iter().any(|(n, _)| n == c) {
                continue;
            }
            let (_, e) = cfg
                .constants
                .iter()
                .find(|(n, _)| n == c)
                .ok_or(format!("CONSTANT {c} has no value in the cfg"))?;
            constants.insert(c.clone(), ce.eval(e, &HashMap::new())?);
        }
    }

    let mut ex = Expander::new(&m);

    // CONSTANT c <- Def: c takes the value of Def, which may refer to other constants (including
    // other substituted ones, so evaluate until nothing changes)
    let mut pending = const_substs;
    while !pending.is_empty() {
        let mut left = vec![];
        let mut last_err = String::new();
        for (c, def) in pending.iter() {
            let e = ex.expand_def(def).map_err(|e| format!("cfg: {c} <- {def}: {e}"))?;
            let ce = ConstEval { atoms: &atoms, constants: &constants };
            match ce.eval(&e, &HashMap::new()) {
                Ok(v) => {
                    constants.insert(c.clone(), v);
                }
                Err(e) => {
                    last_err = format!("cfg: {c} <- {def}: {def} must be a constant expression ({e})");
                    left.push((c.clone(), def.clone()));
                }
            }
        }
        if left.len() == pending.len() {
            return Err(last_err);
        }
        pending = left;
    }

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
                        rejected: Some((format!("Error: Assumption {at} is false."), 10)),
                    })
                }
                Ok(v) => return Err(format!("ASSUME at {at} is not a boolean: {v:?}")),
                Err(e) if crate::value::is_eval_failure(&e) => {
                    let msg = format!("Error: Evaluating assumption {at} failed.\n{e}");
                    return Ok(Output { rust: String::new(), warnings, rejected: Some((msg, 10)) });
                }
                Err(e) => return Err(format!("cannot evaluate the ASSUME at {at}: {e}")),
            }
        }
    }

    let (init, next, fairness) = resolve_spec(&m, &cfg, &mut ex)?;
    if uses_real_time(&init) || uses_real_time(&next) || fairness.iter().any(uses_real_time) {
        return Err("RTnow and RTBound of RealTime are not supported in the spec (TLC cannot check them either)".into());
    }

    let mut g = Gen::new(&atoms, &constants);
    if setcap > 0 {
        g.scap = setcap;
    }
    g.qcap = seq_cap(&m, &cfg, &mut ex, &g, seqcap, &init, &next)?;

    // Fairness conditions (only relevant when checking properties)
    let mut fair_defs = vec![];
    if !cfg.properties.is_empty() {
        for f in &fairness {
            let f = ex.expand_top(f)?;
            crate::live::collect_fair(&f, &HashMap::new(), &g, &mut fair_defs)?;
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
            // STRING is not a set of values here: the variable's type is inferred, and the conjunct
            // is checked as an invariant
            Expr::Bin(BOp::In | BOp::Subseteq, _, s) if matches!(s.strip(), Expr::Ident(n) if n == "STRING") => leftover += 1,
            Expr::Bin(BOp::In, v, s) => {
                let mut taken = false;
                if let Expr::Ident(v) = v.strip() {
                    if m.variables.contains(v) {
                        decl.insert(v.clone(), ty_of_set(&g, s).map_err(|e| format!("{tname}: type of `{v}`: {e}"))?);
                        // Packing checks the element type of a bounded sequence, not its length
                        taken = bounded_seq(s).is_none();
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
        let inferred = infer_types(&atoms, &constants, &m.variables, &decl, &undeclared, &init, &next, g.scap, g.qcap)?;
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
    let mut live_parts: Vec<(String, Expr, HashMap<String, Value>)> = vec![];
    let mut action_props: Vec<(String, String, String)> = vec![];
    let mut init_props: Vec<(String, String)> = vec![];
    for name in &cfg.properties {
        let e = ex.expand_def(name)?;
        if uses_real_time(&e) {
            let msg = format!("Error: TLC cannot handle the temporal formula {name} (RTBound / RTnow of RealTime)");
            return Ok(Output { rust: String::new(), warnings, rejected: Some((msg, 255)) });
        }
        let mut parts = vec![];
        split_property(&g, &e, &HashMap::new(), name, &mut parts)?;
        let whole = parts.len() == 1;
        for (disp, kind, p, q, venv) in parts {
            if kind == 7 {
                live_parts.push((disp, p, venv));
                continue;
            }
            let env = crate::live::bind_env(&mut g, &venv).map_err(|m| format!("property {name}: {m}"))?;
            // As TLC does, []P for a state predicate P is checked as an invariant while exploring,
            // and a state predicate on its own only on the initial states. TLC names a part of a
            // property by its position in the source, which tla2rs does not keep.
            let part_name = if whole && disp == *name { disp.clone() } else { format!("{disp} (a part)") };
            if kind == 4 || kind == 6 {
                let pc = g.gen_as(&p, &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?;
                if kind == 4 {
                    let i = inv_list.len() + 1000;
                    writeln!(inv_code, "fn inv_{i}(s: &State) -> bool {{ {pc} }}").unwrap();
                    inv_list.push(format!("({part_name:?}, inv_{i} as fn(&State) -> bool)"));
                } else {
                    init_props.push((part_name, pc));
                }
                continue;
            }
            if kind == 5 {
                let env = g.env_step(env);
                let pc = g.gen_as(&p, &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?;
                let qc = g.gen_as(&q.unwrap(), &env, &Ty::Bool).map_err(|m| format!("property {name}: {m}"))?;
                action_props.push((part_name, pc, qc));
                continue;
            }
            unreachable!();
        }
    }
    let live_code = match crate::live::compile(&mut g, &fair_defs, &live_parts)? {
        Ok(c) => c,
        Err(crate::live::Rejected(m, code)) => {
            return Ok(Output { rust: String::new(), warnings, rejected: Some((format!("Error: {m}"), code)) })
        }
    };
    let mut prop_code = String::new();
    let mut aprop_list = vec![];
    for (i, (disp, pc, qc)) in action_props.iter().enumerate() {
        writeln!(prop_code, "fn aprop_{i}(s: &State, t: &State) -> bool {{ {pc} || {qc} }}").unwrap();
        aprop_list.push(format!("({disp:?}, aprop_{i} as fn(&State, &State) -> bool)"));
    }
    let mut iprop_list = vec![];
    for (i, (disp, pc)) in init_props.iter().enumerate() {
        writeln!(prop_code, "fn iprop_{i}(s: &State) -> bool {{ {pc} }}").unwrap();
        iprop_list.push(format!("({disp:?}, iprop_{i} as fn(&State) -> bool)"));
    }
    // ACTION_CONSTRAINT: like CONSTRAINT, but on the step from a state to its successor
    let mut acons = vec![];
    for name in &cfg.action_constraints {
        let e = ex.expand_def(name)?;
        let env = g.env_step(Gen::env_next());
        acons.push(g.gen_as(&e, &env, &Ty::Bool).map_err(|m| format!("action constraint {name}: {m}"))?);
    }
    writeln!(
        prop_code,
        "#[allow(unused_variables)]\nfn action_constraint(s: &State, t: &State) -> bool {{ {} }}",
        if acons.is_empty() { "true".into() } else { acons.join(" && ") }
    )
    .unwrap();
    // CONSTRAINT: states that violate it are discarded (as in TLC, they are neither counted nor
    // checked against invariants)
    let mut cons = vec![];
    for name in &cfg.constraints {
        let e = ex.expand_def(name)?;
        cons.push(g.gen_as(&e, &Gen::env_next(), &Ty::Bool).map_err(|m| format!("constraint {name}: {m}"))?);
    }
    writeln!(prop_code, "fn constraint(s: &State) -> bool {{ {} }}", if cons.is_empty() { "true".into() } else { cons.join(" && ") }).unwrap();

    let pack = g.gen_pack()?;
    // VIEW and SYMMETRY
    let view_expr = match &cfg.view {
        Some(v) => Some(ex.expand_def(v)?),
        None => None,
    };
    let mut listed: Vec<Vec<u16>> = vec![];
    if let Some(sym) = &cfg.symmetry {
        let e = ex.expand_def(sym)?;
        let v = g.ce.eval(&e, &HashMap::new()).map_err(|m| format!("SYMMETRY {sym}: {m}"))?;
        for f in v.as_set()? {
            let m = match f {
                Value::Fun(m) => m.clone(),
                // The permutation of the empty set is the empty function, <<>>
                Value::Tuple(t) if t.is_empty() => Default::default(),
                _ => return Err(format!("SYMMETRY {sym} must be a set of permutations of model values or strings")),
            };
            let m = &m;
            let mut t: Vec<u16> = (0..atoms.len() as u16).collect();
            for (a, b) in m {
                let (Value::Atom(a), Value::Atom(b)) = (a, b) else {
                    return Err(format!("SYMMETRY {sym}: only permutations of model values / strings are supported"));
                };
                t[*a as usize] = *b as u16;
            }
            // Identities over different domains (e.g. Permutations(A) \cup Permutations(B)) become the same table.
            if !listed.contains(&t) {
                listed.push(t);
            }
        }
    }
    let mut perms = generated_group(listed);
    // The identity goes first so that the canonicalization can skip permuting for it.
    if let Some(i) = perms.iter().position(|t| t.iter().enumerate().all(|(i, &x)| i as u16 == x)) {
        let id = perms.remove(i);
        perms.insert(0, id);
    }
    let view_equiv = match &view_expr {
        Some(v) if !perms.is_empty() => view_is_equivariant(v, &perms, &constants, &atoms),
        _ => false,
    };
    let key_code = g.gen_key(view_expr.as_ref(), view_equiv)?;
    let perm0_is_id = perms.first().is_some_and(|t| t.iter().enumerate().all(|(i, &x)| i as u16 == x));
    let mut perm_code = if perms.is_empty() {
        "static PERMS: &[&[u16]] = &[];\nfn perm_state(s: &State, _: &[u16]) -> State { *s }\n".to_string()
    } else {
        g.gen_perms(&perms)?
    };
    writeln!(perm_code, "const PERM0_IS_ID: bool = {perm0_is_id};").unwrap();
    let inv: Vec<String> = perms
        .iter()
        .map(|t| {
            let mut v = vec![0u16; t.len()];
            for (i, &x) in t.iter().enumerate() {
                v[x as usize] = i as u16;
            }
            format!("&{v:?}")
        })
        .collect();
    writeln!(perm_code, "static PERMS_INV: &[&[u16]] = &[{}];", inv.join(", ")).unwrap();
    let rec_fns = g.rec_functions();
    let helpers = g.helpers()?;
    let mut src = String::new();
    writeln!(src, "// Generated by tla2rs from module {}. Do not edit.", m.name).unwrap();
    src += "#![allow(unused, non_snake_case, unused_parens, unused_braces, clippy::all)]\n";
    // Strings and model values are 16-bit ids at run time
    if atoms.len() > 1 << 16 {
        return Err(format!("the spec uses {} strings and model values (with those built at compile time by ToString and string operators); at most 65536 are supported", atoms.len()));
    }
    src += &g.atoms_table();
    let fields: Vec<String> = g.vars.iter().map(|(v, t)| format!("v_{v}: {}", t.repr())).collect();
    writeln!(src, "#[derive(Clone, Copy, PartialEq, Eq, Hash)]\nstruct State {{ {} }}", fields.join(", ")).unwrap();
    src += &helpers;
    src += &rec_fns;
    src += &pack;
    src += &key_code;
    src += &perm_code;
    writeln!(src, "fn init(out: &mut Vec<State>) {{\n{init_code}}}").unwrap();
    writeln!(src, "fn next(s: &State, out: &mut Vec<(State, u32)>) {{\n{next_code}}}").unwrap();
    src += &inv_code;
    src += &prop_code;
    src += &live_code;
    writeln!(src, "const TYPE_INVARIANT: &str = {tname:?};").unwrap();
    writeln!(src, "const TYPE_INV_SUBSUMED: bool = {type_inv_subsumed};").unwrap();
    writeln!(src, "static ACTION_PROPS: &[(&str, fn(&State, &State) -> bool)] = &[{}];", aprop_list.join(", ")).unwrap();
    writeln!(src, "static INIT_PROPS: &[(&str, fn(&State) -> bool)] = &[{}];", iprop_list.join(", ")).unwrap();
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
    writeln!(src, "const QCAP: usize = {};", g.qcap).unwrap();
    src += crate::codegen::SQ_RUNTIME;
    let fp_bits = if fp128 { 128 } else { 64 };
    writeln!(src, "const FP_BITS: usize = {fp_bits};\ntype Fp = u{fp_bits};").unwrap();
    src += if metal { crate::metal::GLUE } else { crate::metal::NO_GPU };
    src += crate::runtime::RUNTIME;
    src += crate::runtime::LIVENESS_RT;
    Ok(Output { rust: src, warnings, rejected: None })
}

/// Whether VIEW(perm(s)) = perm(VIEW(s)) for every permutation, so the view can be computed once
/// and permuted instead of being recomputed per permuted state. Conservative: the expression may
/// name a constant, string, or model value only if every permutation leaves its value unchanged,
/// and may not use CHOOSE (its pick depends on the order of model values).
/// The group generated by `listed`: the listed permutations in their order, then the products
/// missing from the list. TLC reduces by this group, so `Permutations(A) \cup Permutations(B)`
/// also identifies states that differ by permuting both A and B.
fn generated_group(mut listed: Vec<Vec<u16>>) -> Vec<Vec<u16>> {
    let mut group: Vec<Vec<u16>> = vec![];
    let mut seen: HashSet<Vec<u16>> = HashSet::new();
    let mut generators: Vec<&Vec<u16>> = vec![];
    for g in &listed {
        if !seen.insert(g.clone()) {
            continue;
        }
        group.push(g.clone());
        generators.push(g);
        // Earlier elements have not been multiplied by the new generator, so start over.
        let mut i = 0;
        while i < group.len() {
            for h in &generators {
                let product: Vec<u16> = group[i].iter().map(|&x| h[x as usize]).collect();
                if seen.insert(product.clone()) {
                    group.push(product);
                }
            }
            i += 1;
        }
    }
    let in_list: HashSet<&Vec<u16>> = listed.iter().collect();
    group.retain(|p| !in_list.contains(p));
    listed.append(&mut group);
    listed
}

fn view_is_equivariant(e: &Expr, perms: &[Vec<u16>], constants: &HashMap<String, Value>, atoms: &Atoms) -> bool {
    fn permute(v: &Value, t: &[u16]) -> Value {
        match v {
            Value::Bool(_) | Value::Int(_) => v.clone(),
            Value::Atom(a) => Value::Atom(t[*a as usize] as u32),
            Value::Set(s) => Value::Set(s.iter().map(|x| permute(x, t)).collect()),
            Value::Fun(m) => Value::Fun(m.iter().map(|(k, x)| (permute(k, t), permute(x, t))).collect()),
            Value::Rec(m) => Value::Rec(m.iter().map(|(k, x)| (k.clone(), permute(x, t))).collect()),
            Value::Tuple(xs) => Value::Tuple(xs.iter().map(|x| permute(x, t)).collect()),
        }
    }
    let fixed = |v: &Value| perms.iter().all(|t| permute(v, t) == *v);
    let atom_fixed = |a: Option<u32>| a.is_some_and(|a| fixed(&Value::Atom(a)));
    let ok = match e {
        Expr::Choose(..) => false,
        Expr::Str(s) => atom_fixed(atoms.get(false, s)),
        Expr::Ident(n) => match n.strip_prefix("@model:") {
            Some(mv) => atom_fixed(atoms.get(true, mv)),
            None => constants.get(n).is_none_or(fixed),
        },
        _ => true,
    };
    ok && e.children().into_iter().all(|c| view_is_equivariant(c, perms, constants, atoms))
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
            fs.sort_by(|a, b| crate::types::field_cmp(&a.0, &b.0));
            Ty::Rec(fs)
        }
        Expr::Call(f, parts) if f == "\\X" => tuple_ty(parts.iter().map(|x| ty_of_set(g, x)).collect::<R<_>>()?)?,
        Expr::Call(f, a) if f == "Seq" && a.len() == 1 => Ty::Seq(ty_of_set(g, &a[0])?.into()),
        e if bounded_seq(e).is_some() => Ty::Seq(ty_of_set(g, bounded_seq(e).unwrap().1)?.into()),
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

pub fn show_value(atoms: &Atoms, v: &Value) -> String {
    match v {
        Value::Bool(b) => if *b { "TRUE".into() } else { "FALSE".into() },
        Value::Int(i) => i.to_string(),
        Value::Atom(a) => atoms.show(*a),
        Value::Set(s) => format!("{{{}}}", s.iter().map(|x| show_value(atoms, x)).collect::<Vec<_>>().join(", ")),
        // In TLC's normal form: fields in TLC's order of names
        Value::Rec(m) => {
            let fs = crate::types::sorted_fields(m.iter().map(|(k, x)| (k.clone(), x)).collect());
            format!("[{}]", fs.iter().map(|(k, x)| format!("{k} |-> {}", show_value(atoms, x))).collect::<Vec<_>>().join(", "))
        }
        // A function over strings prints as a record
        Value::Fun(m) if m.keys().all(|k| matches!(k, Value::Atom(a) if !atoms.is_model(*a))) => format!(
            "[{}]",
            m.iter()
                .map(|(k, x)| format!("{} |-> {}", match k { Value::Atom(a) => atoms.name(*a), _ => unreachable!() }, show_value(atoms, x)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Value::Fun(m) => format!("({})", m.iter().map(|(k, x)| format!("{} :> {}", show_value(atoms, k), show_value(atoms, x))).collect::<Vec<_>>().join(" @@ ")),
        Value::Tuple(t) => format!("<<{}>>", t.iter().map(|x| show_value(atoms, x)).collect::<Vec<_>>().join(", ")),
    }
}

type PropPart = (String, u8, Expr, Option<Expr>, HashMap<String, Value>);

/// Splits a property into checkable forms: 0: <>P, 1: []<>P, 2: <>[]P, 3: P ~> Q, 4: []P (state
/// predicate), 5: [][A]_v.
/// Splits a property into the parts TLC checks separately: (name, kind, formula, second formula,
/// constant bindings). Kinds: 4 []P with P a state predicate (an invariant), 5 [][A]_v (an action
/// property, with v' = v as the second formula), 6 a state predicate (checked on the initial
/// states), 7 anything else (a liveness formula).
/// Whether e is an action (has primes or UNCHANGED outside ENABLED)
fn action_level(e: &Expr) -> bool {
    match e {
        Expr::Prime(_) | Expr::Un(UOp::Unchanged, _) => true,
        Expr::Un(UOp::Enabled, _) => false,
        _ => e.children().into_iter().any(action_level),
    }
}

fn split_property(g: &Gen, e: &Expr, env: &HashMap<String, Value>, name: &str, out: &mut Vec<PropPart>) -> R<()> {
    use Expr::*;
    let temporal = |x: &Expr| {
        x.any(&|y| matches!(y, Un(UOp::Always | UOp::Eventually, _) | Bin(BOp::LeadsTo, ..) | BoxAction(..) | Fair(..)))
    };
    let mut tag = String::new();
    let mut keys: Vec<&String> = env.keys().collect();
    keys.sort();
    for k in keys {
        if !tag.is_empty() {
            tag += ", ";
        }
        tag += &format!("{}={}", k.split("__").next().unwrap_or(k), show_value(g.atoms, &env[k]));
    }
    let disp = if tag.is_empty() { name.to_string() } else { format!("{name} [{tag}]") };
    match e {
        Label(_, _, b) => split_property(g, b, env, name, out),
        And(xs) => xs.iter().try_for_each(|x| split_property(g, x, env, name, out)),
        Quant(false, bs, body) if temporal(body) => {
            let mut err = Ok(());
            let r = g.ce.each_binding(bs, env, &mut |env2| {
                if let Err(m) = split_property(g, body, env2, name, out) {
                    err = Err(m);
                    return Ok(false);
                }
                Ok(true)
            });
            match r {
                // A bound that depends on the state: left whole, for the liveness checks to refuse
                // as TLC does
                Err(m) if m.contains("is not a constant") => Ok(out.push((disp, 7, e.clone(), None, env.clone()))),
                r => r.and(err),
            }
        }
        Un(UOp::Always, p) => match p.strip() {
            p if !temporal(p) && !action_level(p) => Ok(out.push((disp, 4, p.clone(), None, env.clone()))),
            // [][A]_v: every transition is an A step or leaves v unchanged (written v' = v, since v
            // need not be a tuple of variables, e.g. under a refinement mapping)
            BoxAction(a, v) if !temporal(a) => {
                let same = Bin(BOp::Eq, Prime(v.clone()).b(), v.clone());
                Ok(out.push((disp, 5, a.as_ref().clone(), Some(same), env.clone())))
            }
            _ => Ok(out.push((disp, 7, e.clone(), None, env.clone()))),
        },
        // A state predicate: TLC checks it on the initial states
        p if !temporal(p) && !action_level(p) => Ok(out.push((disp, 6, p.clone(), None, env.clone()))),
        p if temporal(p) => Ok(out.push((disp, 7, p.clone(), None, env.clone()))),
        _ => Err(format!("property {name}: an action formula must be under [] as [][A]_v ({})", short(e))),
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
    qcap: usize,
) -> R<HashMap<String, Ty>> {
    let bottom = Ty::Enum(vec![]);
    let mut cur: HashMap<String, Ty> = undeclared.iter().map(|v| (v.clone(), bottom.clone())).collect();
    // How many times each type grew after its first value. A range that settles within a few rounds
    // (e.g. `Cardinality(S)` or `x % 3` written into a variable) stays finite; one that keeps
    // growing (`x + 1`) is widened to unbounded
    let mut grew: HashMap<String, u32> = HashMap::new();
    for _ in 0..40 {
        let mut g = Gen::new(atoms, constants);
        g.scap = scap;
        g.qcap = qcap;
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
            let w = if old == bottom || j == old {
                j
            } else {
                let n = grew.entry(v.clone()).or_insert(0);
                *n += 1;
                if *n < WIDEN_AFTER {
                    j
                } else {
                    widen(&old, &j)
                }
            };
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

/// Rounds of growth after which an inferred integer range is widened to unbounded
const WIDEN_AFTER: u32 = 3;

/// Widens integers whose range changed from the previous type to unbounded.
pub fn widen(old: &Ty, new: &Ty) -> Ty {
    match (old, new) {
        (Ty::Enum(o), _) if o.is_empty() => new.clone(),
        (Ty::Int(a, b), Ty::Int(c, d)) if (a, b) != (c, d) => Ty::Int(if c < a { -BIG } else { *a }, if d > b { BIG } else { *b }),
        (Ty::Int(a, b) | Ty::IntAtom(a, b, _), Ty::IntAtom(c, d, x)) if (a, b) != (c, d) => {
            Ty::IntAtom(if c < a { -BIG } else { *a }, if d > b { BIG } else { *b }, x.clone())
        }
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
