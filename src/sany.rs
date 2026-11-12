//! The checks of names that SANY (the parser TLC runs first) makes and tla2rs repeats, so that a
//! spec SANY refuses stops with exit 150 as in TLC. Measured on SANY 2.19 (`tests/tlc/RejSany*`,
//! `tests/tlc/SanyScope*`):
//!
//! - A name is in scope after the statement that declares or defines it, never before: an
//!   operator parameter may be named like a VARIABLE, CONSTANT or definition that comes later in
//!   the module. In scope from the start are TRUE, FALSE, BOOLEAN, STRING and what the modules in
//!   EXTENDS export (their CONSTANTs, VARIABLEs and definitions that are not LOCAL, also those
//!   they extend; the standard modules export what `std_exports` lists). An INSTANCE brings the
//!   definitions of the instantiated module into scope at that point (LOCAL INSTANCE too, without
//!   exporting them); `N == INSTANCE M` brings only N. A RECURSIVE declaration puts the name in
//!   scope. A nested module sees what is in scope where it starts
//! - Every name used must be in scope (`Unknown operator`), also operator symbols such as `+`,
//!   unary minus (`-.`) and `\o`, and also in definitions nothing uses
//! - A declaration, definition, operator parameter, LET definition, bound variable or LAMBDA
//!   parameter may not reuse a name in scope (`Multiply-defined symbol`). A definition's own name
//!   is in scope in its parameters (`F(F) == ...` is refused) but not in its body (`F == \E F \in
//!   S : P` is fine) unless it is a function definition `f[x \in S] == e` or declared RECURSIVE.
//!   The sets of `\E x \in S, y \in T` are read outside the quantifier (T cannot use x). The same
//!   definition reached twice (a module extended along two paths, or extended and instantiated
//!   when it has no CONSTANT or VARIABLE) is one symbol; two different definitions of one name in
//!   two extended modules are only a warning for SANY, and are not refused here
//! - A label `l(p, q) :: e` must list exactly the bound variables introduced between it and the
//!   enclosing label or definition (a LET definition starts afresh; operator parameters and LET
//!   names do not count), each once

use crate::ast::*;
use crate::lexer::{R, SANY};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

/// A name in scope and the statement that introduced it (the module and name of the definition,
/// or a unique tag for an INSTANCE with substitutions). `decl` marks a CONSTANT or VARIABLE
#[derive(Clone, Debug, PartialEq)]
struct Sym {
    name: String,
    origin: String,
    decl: bool,
    /// Defined in a module without constants or variables: an INSTANCE gives the same
    /// definition, not a new one
    fixed: bool,
}

thread_local! {
    /// What each module checked so far exports to a module that extends it (`None` when it
    /// extends a module whose names are not known)
    static EXPORTS: RefCell<HashMap<String, Option<Vec<Sym>>>> = RefCell::new(HashMap::new());
    /// The keys SANY puts in each module's context (see `Ctx`), `None` when a module it reads is
    /// not known
    static CONTEXTS: RefCell<HashMap<String, Option<Ctx>>> = RefCell::new(HashMap::new());
}

/// What a key of a module's context names
#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind {
    Var,
    Const,
    /// A definition (also a theorem, a named ASSUME, a RECURSIVE declaration, an instance's name
    /// and the definitions it brings): what an INSTANCE of the module copies
    Def,
    /// A nested module
    Module,
}

/// The names SANY's context of a module holds after its built-in operators, in the order they
/// are first put there (`all`), and those of them a module that extends it takes over (`exported`,
/// in that order: all but the LOCAL ones). TLC prints a state's variables in the order of the
/// root module's context, a Java `Hashtable` keyed by name (see `var_order`). Measured on SANY
/// 2.19 with a dump of the context: EXTENDS adds what each module exports, in order, skipping
/// names already there; a declaration, definition, theorem, named ASSUME, RECURSIVE declaration
/// or nested module adds its name; `N == INSTANCE M` adds `N!d` for each definition d M exports,
/// then N; an unnamed INSTANCE adds the definitions M exports not there yet
#[derive(Clone, Default)]
struct Ctx {
    all: Vec<(String, Kind)>,
    exported: Vec<(String, Kind)>,
}

impl Ctx {
    fn add(&mut self, n: &str, k: Kind, export: bool) {
        if !self.all.iter().any(|(m, _)| m == n) {
            self.all.push((n.to_string(), k));
        }
        if export && !self.exported.iter().any(|(m, _)| m == n) {
            self.exported.push((n.to_string(), k));
        }
    }
}

/// The context keys module `m` exports (`None` when they are not known)
fn ctx_exports(m: &str) -> Option<Vec<(String, Kind)>> {
    if let Some(s) = std_exports(m) {
        return Some(s.into_iter().map(|s| (s.name, if s.decl { Kind::Var } else { Kind::Def })).collect());
    }
    CONTEXTS.with(|c| c.borrow().get(m).cloned().flatten()).map(|c| c.exported)
}

/// The number of built-in operators SANY puts in every module's context first (measured)
const SANY_BUILTINS: usize = 72;

/// The variables of root module `root` in the order TLC prints them in a state, or None when a
/// module it reads is not known. TLC takes them from SANY's context of the root module, a Java
/// `Hashtable` keyed by name (`String.hashCode`), and reverses the order the table enumerates
/// them in. The table starts with room for 11 and grows to 2n+1 when it holds three quarters of
/// its room and one more name comes; a name goes to the front of the chain of its slot, growing
/// walks the old slots from the last and each chain from the front, and enumerating walks the
/// slots from the last. The other names only decide when the table grows: the order of two
/// variables depends on their hashes and on how many names were in the table when each came
pub fn var_order(root: &str) -> Option<Vec<String>> {
    let ctx = CONTEXTS.with(|c| c.borrow().get(root).cloned().flatten())?;
    let hash = |n: &str| n.encode_utf16().fold(0i32, |h, c| h.wrapping_mul(31).wrapping_add(c as i32));
    let slot = |h: i32, cap: usize| (h & 0x7FFF_FFFF) as usize % cap;
    // The variables only, each chain from its front
    let mut table: Vec<Vec<(i32, String)>> = vec![vec![]; 11];
    let mut count = 0usize;
    let keys = std::iter::repeat_n(None, SANY_BUILTINS).chain(ctx.all.iter().map(Some));
    for key in keys {
        let cap = table.len();
        if count >= cap * 3 / 4 {
            let mut grown: Vec<Vec<(i32, String)>> = vec![vec![]; 2 * cap + 1];
            for chain in table.iter().rev() {
                for (h, n) in chain {
                    let i = slot(*h, grown.len());
                    grown[i].insert(0, (*h, n.clone()));
                }
            }
            table = grown;
        }
        if let Some((n, Kind::Var)) = key {
            let h = hash(n);
            let i = slot(h, table.len());
            table[i].insert(0, (h, n.clone()));
        }
        count += 1;
    }
    let mut order: Vec<String> = table.iter().rev().flat_map(|c| c.iter().map(|(_, n)| n.clone())).collect();
    order.reverse();
    Some(order)
}

/// The names the standard modules export (as SANY names operator symbols: `\leq`, `-.` for unary
/// minus), from the modules in TLC's jar. The modules a standard module instantiates LOCALly
/// (Naturals in Sequences, FiniteSets, TLC and Bags) export nothing
fn std_exports(m: &str) -> Option<Vec<Sym>> {
    const NAT: &[&str] = &["Nat", "+", "-", "*", "^", "<", ">", "\\leq", "\\geq", "%", "\\div", ".."];
    const TLC: &[&str] = &[
        "Print", "PrintT", "Assert", "JavaTime", "TLCGet", "TLCSet", ":>", "@@", "Permutations", "SortSeq",
        "RandomElement", "Any", "ToString", "TLCEval",
    ];
    let own: &[(&str, &[&str])] = match m {
        "Naturals" => &[("Naturals", NAT)],
        "Integers" => &[("Naturals", NAT), ("Integers", &["Int", "-."])],
        "Reals" => &[("Naturals", NAT), ("Integers", &["Int", "-."]), ("Reals", &["Real", "/", "Infinity"])],
        "RealTime" => {
            &[("Naturals", NAT), ("Integers", &["Int", "-."]), ("Reals", &["Real", "/", "Infinity"]), ("RealTime", &["now", "RTBound", "RTnow"])]
        }
        "Sequences" => &[("Sequences", &["Seq", "Len", "\\o", "Append", "Head", "Tail", "SubSeq", "SelectSeq"])],
        "FiniteSets" => &[("FiniteSets", &["IsFiniteSet", "Cardinality"])],
        "TLC" => &[("TLC", TLC)],
        "Bags" => &[
            ("TLC", TLC),
            (
                "Bags",
                &[
                    "IsABag", "BagToSet", "SetToBag", "BagIn", "EmptyBag", "\\oplus", "\\ominus", "BagUnion", "\\sqsubseteq",
                    "SubBag", "BagOfAll", "BagCardinality", "CopiesIn",
                ],
            ),
        ],
        "Toolbox" => &[("Toolbox", &["_TETrace", "_TEPosition"])],
        "Randomization" => &[("Randomization", &["RandomSubset", "RandomSetOfSubsets", "TestRandomSetOfSubsets"])],
        _ => return None,
    };
    Some(
        own.iter()
            .flat_map(|(o, ns)| ns.iter().map(move |n| Sym { name: n.to_string(), origin: o.to_string(), decl: *n == "now", fixed: *n != "now" }))
            .collect(),
    )
}

/// What module `m` exports (`Some(None)` when that is not known, `None` when it was not loaded)
fn exports(m: &str) -> Option<Option<Vec<Sym>>> {
    if let Some(s) = std_exports(m) {
        return Some(Some(s));
    }
    EXPORTS.with(|e| e.borrow().get(m).cloned())
}

/// Names built into TLA+: always in scope
fn builtin(n: &str) -> bool {
    matches!(
        n,
        "TRUE" | "FALSE" | "BOOLEAN" | "STRING" | "=" | "#" | "/=" | "\\in" | "\\notin" | "\\subseteq" | "\\cup" | "\\cap"
            | "\\" | "=>" | "<=>" | "~>" | "/\\" | "\\/" | "\\X" | "-+->" | "~"
    )
}

/// The name SANY gives an operator symbol the parser normalizes otherwise
fn sany_name(n: &str) -> &str {
    match n {
        "<=" => "\\leq",
        ">=" => "\\geq",
        n => n,
    }
}

fn clash(x: &str) -> String {
    format!("{SANY}Multiply-defined symbol '{x}': this definition or declaration conflicts with another one in scope.")
}

/// Checks module `m` (a module read from a file, after the modules it extends and instantiates
/// have been loaded) and the modules nested in it, and records what they export
pub fn check(m: &Module) -> R<()> {
    let ex = module(m, vec![], true)?;
    EXPORTS.with(|e| e.borrow_mut().insert(m.name.clone(), ex));
    Ok(())
}

/// The names in scope at a point of a module
#[derive(Clone, Default)]
struct Scope {
    syms: Vec<Sym>,
    names: HashSet<String>,
}

impl Scope {
    fn get(&self, n: &str) -> Option<&Sym> {
        if self.names.contains(n) { self.syms.iter().rev().find(|s| s.name == n) } else { None }
    }
    fn has(&self, n: &str) -> bool {
        self.names.contains(n) || builtin(n)
    }
    fn push(&mut self, s: Sym) {
        self.names.insert(s.name.clone());
        self.syms.push(s);
    }
}

/// Checks a module whose scope starts as `base` (what is in scope where a nested module starts)
/// and returns what it exports. `known` is whether every name in scope is known: not when the
/// module (or the one it is nested in) extends one tla2rs does not read
fn module(m: &Module, base: Vec<Sym>, mut known: bool) -> R<Option<Vec<Sym>>> {
    let mut scope = Scope::default();
    for s in base {
        scope.push(s);
    }
    let mut out: Vec<Sym> = vec![];
    let mut ctx = Ctx::default();
    let mut ctx_known = true;
    for e in &m.extends {
        match ctx_exports(e) {
            Some(keys) => keys.iter().for_each(|(n, k)| ctx.add(n, *k, true)),
            None => ctx_known = false,
        }
        match exports(e) {
            Some(Some(syms)) => {
                for s in syms {
                    if !out.contains(&s) {
                        out.push(s.clone());
                    }
                    if !scope.syms.contains(&s) {
                        scope.push(s);
                    }
                }
            }
            _ => known = false,
        }
    }
    let own = |n: &str, decl: bool| Sym { name: n.to_string(), origin: format!("{}.{n}", m.name), decl, fixed: false };
    let mut pending_rec: Vec<String> = vec![];
    // The name of a recursive function whose body was checked with its `#app` definition
    let mut checked_body: Option<String> = None;
    for u in &m.units {
        match u {
            Unit::Decl(n) | Unit::Theorem(n) => {
                if scope.has(n) {
                    return Err(clash(n));
                }
                let s = own(n, matches!(u, Unit::Decl(_)));
                scope.push(s.clone());
                out.push(s);
                let k = match u {
                    Unit::Decl(_) if m.variables.contains(n) => Kind::Var,
                    Unit::Decl(_) => Kind::Const,
                    _ => Kind::Def,
                };
                ctx.add(n, k, true);
            }
            Unit::Recursive(n) => {
                if scope.has(n) {
                    return Err(clash(n));
                }
                pending_rec.push(n.clone());
                ctx.add(n, Kind::Def, true);
                // Exported even when the definition is LOCAL (measured: a module that extends
                // one with `RECURSIVE F(_)` and `LOCAL F(n) == ...` may not define F)
                scope.push(own(n, false));
                out.push(own(n, false));
            }
            Unit::Assume(i) => Walker::new(&scope, known, &m.recursive).expr(&m.assumes[*i].expr)?,
            Unit::Def(i, fun) => {
                let d = &m.defs[*i];
                if let Some(f) = d.name.strip_suffix("#app") {
                    // `f[x \in S] == e` that refers to f: f is in scope in S and e
                    if scope.has(f) {
                        return Err(clash(f));
                    }
                    let mut sc = scope.clone();
                    sc.push(own(f, false));
                    let mut w = Walker::new(&sc, known, &m.recursive);
                    for p in &d.params {
                        w.bind_var(p)?;
                    }
                    w.expr(&d.body)?;
                    checked_body = Some(f.to_string());
                    continue;
                }
                if d.name.contains('#') {
                    continue;
                }
                match pending_rec.iter().position(|r| *r == d.name) {
                    Some(k) => {
                        pending_rec.remove(k);
                    }
                    None if scope.has(&d.name) => {
                        return Err(match scope.get(&d.name) {
                            Some(s) if !s.decl => format!("{SANY}Multiple declarations or definitions for symbol {}.", d.name),
                            _ => clash(&d.name),
                        })
                    }
                    None => {}
                }
                if checked_body.take().as_deref() != Some(d.name.as_str()) {
                    let mut sc = scope.clone();
                    if *fun {
                        sc.push(own(&d.name, false));
                    }
                    let mut w = Walker::new(&sc, known, &m.recursive);
                    for p in &d.params {
                        if *p == d.name {
                            return Err(format!("{SANY}Operator {p} already defined or declared."));
                        }
                        w.bind(p)?;
                    }
                    w.expr(&d.body)?;
                }
                ctx.add(&d.name, Kind::Def, !m.local_defs.contains(&d.name));
                let s = own(&d.name, false);
                if !scope.syms.contains(&s) {
                    scope.push(s.clone());
                }
                if !m.local_defs.contains(&d.name) && !out.contains(&s) {
                    out.push(s);
                }
            }
            Unit::Inst(i, local) => {
                let inst = &m.instances[*i];
                match ctx_exports(&inst.module) {
                    Some(keys) => {
                        for (n, _) in keys.iter().filter(|(_, k)| *k == Kind::Def) {
                            match &inst.name {
                                Some(p) => ctx.add(&format!("{p}!{n}"), Kind::Def, !local),
                                None => ctx.add(n, Kind::Def, !local),
                            }
                        }
                        if let Some(p) = &inst.name {
                            ctx.add(p, Kind::Def, !local);
                        }
                    }
                    None => ctx_known = false,
                }
                match &inst.name {
                    Some(n) => {
                        if scope.has(n) {
                            return Err(clash(n));
                        }
                        let mut w = Walker::new(&scope, known, &m.recursive);
                        for p in &inst.params {
                            if p == n {
                                return Err(format!("{SANY}Operator {p} already defined or declared."));
                            }
                            w.bind(p)?;
                        }
                        for (_, e) in &inst.subs {
                            w.arg(e)?;
                        }
                        let s = own(n, false);
                        scope.push(s.clone());
                        if !local {
                            out.push(s);
                        }
                    }
                    None => {
                        let mut w = Walker::new(&scope, known, &m.recursive);
                        for (_, e) in &inst.subs {
                            w.arg(e)?;
                        }
                        let Some(Some(syms)) = exports(&inst.module) else {
                            known = false;
                            continue;
                        };
                        // Without constants or variables the instance's definitions are the
                        // module's own; otherwise new ones, distinct from any other
                        let fresh = syms.iter().any(|s| s.decl);
                        for mut s in syms.into_iter().filter(|s| !s.decl) {
                            if fresh && !s.fixed {
                                s.origin = format!("{}#inst{i}", m.name);
                            }
                            match scope.get(&s.name) {
                                Some(old) if *old == s => {}
                                Some(_) => return Err(format!("{SANY}Multiple declarations or definitions for symbol {}.", s.name)),
                                None if builtin(&s.name) => return Err(clash(&s.name)),
                                None => {
                                    scope.push(s.clone());
                                    if !local {
                                        out.push(s);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Unit::Nested(i) => {
                let inner = &m.nested[*i];
                let ex = module(inner, scope.syms.clone(), known)?;
                EXPORTS.with(|e| e.borrow_mut().insert(inner.name.clone(), ex));
                ctx.add(&inner.name, Kind::Module, true);
            }
        }
    }
    CONTEXTS.with(|c| c.borrow_mut().insert(m.name.clone(), ctx_known.then_some(ctx)));
    // The module's own definitions are fixed when nothing in it is a constant or variable
    if !scope.syms.iter().any(|s| s.decl) {
        let prefix = format!("{}.", m.name);
        for s in out.iter_mut().filter(|s| s.origin.starts_with(&prefix)) {
            s.fixed = true;
        }
    }
    Ok(known.then_some(out))
}

/// Checks the names in the expressions of one definition (or ASSUME, or INSTANCE)
struct Walker<'a> {
    scope: &'a Scope,
    /// Whether an unknown name is an error (not when the module extends one tla2rs does not read)
    known: bool,
    /// The names declared RECURSIVE (also in LET)
    recursive: &'a [String],
    /// Parameters, bound variables and LET definitions in scope, innermost last
    locals: Vec<String>,
    /// The bound variables introduced since the enclosing label or definition
    label_bound: Vec<String>,
}

impl<'a> Walker<'a> {
    fn new(scope: &'a Scope, known: bool, recursive: &'a [String]) -> Self {
        Walker { scope, known, recursive, locals: vec![], label_bound: vec![] }
    }

    fn has(&self, n: &str) -> bool {
        self.scope.has(n) || self.locals.iter().any(|l| l == n)
    }

    /// Puts x in scope, refusing a name already there
    fn bind(&mut self, x: &str) -> R<()> {
        if !x.contains('#') && self.has(x) {
            return Err(clash(x));
        }
        self.locals.push(x.to_string());
        Ok(())
    }

    /// Like `bind`, for a bound variable (which a label inside must list)
    fn bind_var(&mut self, x: &str) -> R<()> {
        self.bind(x)?;
        if !x.contains('#') {
            self.label_bound.push(x.to_string());
        }
        Ok(())
    }

    fn resolve(&self, n: &str) -> R<()> {
        if !self.known || n.contains('#') || n.starts_with('@') {
            return Ok(());
        }
        // `N!Op` (an instance's operator) and `Op!lab` (a label) need N and Op (`!!` is an
        // operator symbol)
        let word = n.starts_with(|c: char| c.is_alphanumeric() || c == '_');
        let base = sany_name(if word { n.split('!').next().unwrap_or(n) } else { n });
        if self.has(base) {
            return Ok(());
        }
        if word {
            Err(format!("{SANY}Unknown operator: `{base}'."))
        } else {
            Err(format!("{SANY}Could not find declaration or definition of symbol '{base}'."))
        }
    }

    /// Runs f with the scope restored afterwards
    fn scoped(&mut self, f: impl FnOnce(&mut Self) -> R<()>) -> R<()> {
        let (l, b) = (self.locals.len(), self.label_bound.len());
        let r = f(self);
        self.locals.truncate(l);
        self.label_bound.truncate(b);
        r
    }

    /// An argument of an operator, which may be a LAMBDA (only there, or in a WITH substitution)
    fn arg(&mut self, e: &Expr) -> R<()> {
        match e {
            Expr::Lambda(ps, body) => self.scoped(|w| {
                for p in ps {
                    w.bind(p)?;
                }
                w.expr(body)
            }),
            e => self.expr(e),
        }
    }

    fn expr(&mut self, e: &Expr) -> R<()> {
        use Expr::*;
        match e {
            Num(_) | Str(_) | Bool(_) | At | RecCall(..) => Ok(()),
            Ident(n, _) => self.resolve(n),
            Call(n, args) => {
                if n.starts_with(crate::parser::UNBOUNDED) || n == "\\EE" || n == "\\AA" {
                    // Their bound variables are not kept
                    return Ok(());
                }
                if n == crate::parser::SUBEXPR {
                    for (k, a) in args.iter().enumerate() {
                        match a {
                            Ident(x, _) if k > 0 && ["<<", ">>", ":", "@"].contains(&x.as_str()) => {}
                            Call(l, la) if l.starts_with("#label") => la.iter().try_for_each(|x| self.expr(x))?,
                            Tuple(vs) if k > 0 => vs.iter().try_for_each(|x| self.expr(x))?,
                            a => self.expr(a)?,
                        }
                    }
                    return Ok(());
                }
                self.resolve(n)?;
                args.iter().try_for_each(|a| self.arg(a))
            }
            Un(op, x) => {
                if *op == UOp::Neg {
                    self.resolve("-.")?;
                }
                self.expr(x)
            }
            Bin(op, a, b) => {
                let sym = match op {
                    BOp::Add => Some("+"),
                    BOp::Sub => Some("-"),
                    BOp::Mul => Some("*"),
                    BOp::Div => Some("\\div"),
                    BOp::Mod => Some("%"),
                    BOp::Lt => Some("<"),
                    BOp::Le => Some("\\leq"),
                    BOp::Gt => Some(">"),
                    BOp::Ge => Some("\\geq"),
                    BOp::Range => Some(".."),
                    _ => None,
                };
                if let Some(s) = sym {
                    self.resolve(s)?;
                }
                self.expr(a)?;
                self.expr(b)
            }
            Quant(_, bs, body) | SetMap(body, bs) => {
                for (_, s) in bs {
                    self.expr(s)?;
                }
                self.scoped(|w| {
                    for (x, _) in bs {
                        w.bind_var(x)?;
                    }
                    w.expr(body)
                })
            }
            Choose(x, s, p) | SetFilter(x, s, p) | FunCons(x, s, p) => {
                self.expr(s)?;
                self.scoped(|w| {
                    w.bind_var(x)?;
                    w.expr(p)
                })
            }
            Lambda(..) => Err(format!("{SANY}LAMBDA expression used where an expression is required.")),
            Let(defs, body) => self.scoped(|w| {
                let mut checked_body: Option<&str> = None;
                for d in defs {
                    // `<<x, y>> \in S` binds x and y as `x == t[1]`, `y == t[2]`
                    let pattern = matches!(&d.body, App(t, i) if matches!(t.as_ref(), Ident(n, _) if n.starts_with('#')) && matches!(i.as_ref(), Num(_)));
                    if pattern {
                        w.bind_var(&d.name)?;
                        continue;
                    }
                    let fun_app = d.name.strip_suffix("#app");
                    let name = fun_app.unwrap_or(&d.name);
                    if fun_app.is_none() && checked_body == Some(name) {
                        // The function of a recursive function definition, checked with it
                        continue;
                    }
                    if w.has(name) {
                        return Err(clash(name));
                    }
                    let rec = fun_app.is_some() || w.recursive.contains(&d.name);
                    let saved = std::mem::take(&mut w.label_bound);
                    let r = w.scoped(|w| {
                        if rec {
                            w.locals.push(name.to_string());
                        }
                        for p in &d.params {
                            if *p == d.name {
                                return Err(format!("{SANY}Operator {p} already defined or declared."));
                            }
                            if fun_app.is_some() { w.bind_var(p)? } else { w.bind(p)? }
                        }
                        // The parameters of a LET definition are not listed by its labels
                        if fun_app.is_none() {
                            w.label_bound.clear();
                        }
                        w.expr(&d.body)
                    });
                    w.label_bound = saved;
                    r?;
                    if fun_app.is_some() {
                        checked_body = Some(name);
                    }
                    w.locals.push(name.to_string());
                }
                w.expr(body)
            }),
            Label(n, args, body) => {
                for a in args {
                    self.expr(a)?;
                }
                let Some(head) = n.strip_suffix("::") else { return self.expr(body) };
                let ps: Vec<&str> = match head.split_once('(') {
                    Some((_, rest)) => rest.trim_end_matches(')').split(',').filter(|p| !p.is_empty()).collect(),
                    None => vec![],
                };
                let l = head.split('(').next().unwrap_or(head);
                for (k, p) in ps.iter().enumerate() {
                    if ps[..k].contains(p) {
                        return Err(format!("{SANY}Repeated formal parameter {p} in label `{l}'."));
                    }
                    if !self.label_bound.iter().any(|x| x == p) {
                        return Err(format!("{SANY}Illegal parameter {p} of label `{l}'."));
                    }
                }
                if let Some(x) = self.label_bound.iter().find(|x| !ps.contains(&x.as_str())) {
                    return Err(format!("{SANY}Label {l} must contain formal parameter `{x}'."));
                }
                let saved = std::mem::take(&mut self.label_bound);
                let r = self.expr(body);
                self.label_bound = saved;
                r
            }
            e => e.children().into_iter().try_for_each(|c| self.expr(c)),
        }
    }
}
