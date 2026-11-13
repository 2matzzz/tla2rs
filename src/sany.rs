//! The checks of names that SANY (the parser TLC runs first) makes and tla2rs repeats, so that a
//! spec SANY refuses stops with exit 150 as in TLC, with SANY's report. Measured on SANY 2.19
//! (`tests/tlc/RejSany*`, `tests/tlc/SanyScope*`):
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
//!   unary minus (`-.`) and `\o`, and also in definitions nothing uses. SANY does not look at the
//!   arguments of an operator it cannot find. An operator that takes arguments, named without
//!   them where it is not an argument, is refused (`The operator F requires 1 arguments.`), and
//!   so is a call with another number of arguments, whose arguments SANY then does not look at
//! - A declaration, operator parameter or bound variable may not reuse a name in scope
//!   (`Multiply-defined symbol`, with where the other one is). A definition named like something
//!   in scope or like one of its own parameters is refused (`Operator F already defined or
//!   declared.`, `Function name ...` for `f[x \in S] == e`); after its body, the clash with a
//!   definition of as many parameters is only a warning, any other a second error. A definition's
//!   own name is not in scope in its body (`F == \E F \in S : P` is fine) unless it is a function
//!   definition or declared RECURSIVE. The sets of `\E x \in S, y \in T` are read outside the
//!   quantifier (T cannot use x). The same definition reached twice (a module extended along two
//!   paths, or extended and instantiated when it has no CONSTANT or VARIABLE) is one symbol; two
//!   different definitions of one name in two extended modules are only a warning for SANY, and
//!   are not refused here
//! - What an operator is passed must fit its parameter (an operator of as many parameters where
//!   the parameter takes some, anything else where it takes none; `Walker::args`), and a
//!   subexpression `Op!1` needs a definition named with its arguments
//! - A label `l(p, q) :: e` must list exactly the bound variables introduced between it and the
//!   enclosing label or definition (a LET definition starts afresh; operator parameters and LET
//!   names do not count), each once
//!
//! SANY reports every error of a module, in the order it meets them, and then its warnings. The
//! check runs on the module as parsed for compiling, where most positions are not kept; when it
//! finds errors, the module is parsed again with them (`parser::parse_module_sany`) and checked
//! again for the report

use crate::ast::*;
use crate::lexer::{R, SANY};
use crate::parser::{ARG_AT, NAME_AT, OP_AT};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

/// A name in scope and the statement that introduced it (the module and name of the definition,
/// or a unique tag for an INSTANCE with substitutions). `decl` marks a CONSTANT or VARIABLE.
/// `at` (where SANY places the statement) and `arity` (its number of parameters) take no part in
/// comparing two symbols
#[derive(Clone, Debug)]
struct Sym {
    name: String,
    origin: String,
    decl: bool,
    /// Defined in a module without constants or variables: an INSTANCE gives the same
    /// definition, not a new one
    fixed: bool,
    at: String,
    arity: usize,
    /// The number of arguments each parameter takes (0 for an ordinary one)
    params: Vec<usize>,
    /// For `N == INSTANCE M`: M
    inst: Option<String>,
}

impl PartialEq for Sym {
    fn eq(&self, o: &Sym) -> bool {
        self.name == o.name && self.origin == o.origin && self.decl == o.decl && self.fixed == o.fixed
    }
}

/// Errors and warnings of the module being checked: the position SANY gives each (empty when not
/// known) and the message
#[derive(Default)]
struct Diag {
    errors: Vec<(String, String)>,
    warnings: Vec<(String, String)>,
}

thread_local! {
    /// What each module checked so far exports to a module that extends it (`None` when it
    /// extends a module whose names are not known)
    static EXPORTS: RefCell<HashMap<String, Option<Vec<Sym>>>> = RefCell::new(HashMap::new());
    /// The keys SANY puts in each module's context (see `Ctx`), `None` when a module it reads is
    /// not known
    static CONTEXTS: RefCell<HashMap<String, Option<Ctx>>> = RefCell::new(HashMap::new());
    static DIAG: RefCell<Diag> = RefCell::new(Diag::default());
    /// The text of each module read from a file, by name, to parse again for a report
    static SOURCES: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
}

fn error(at: &str, msg: String) {
    DIAG.with(|d| d.borrow_mut().errors.push((at.to_string(), msg)));
}

thread_local! {
    /// See `take_warnings`
    static WARNED: RefCell<Vec<String>> = const { RefCell::new(vec![]) };
    /// SANY's warnings "in global context" for the module being checked
    static GLOBAL: RefCell<Vec<(String, String)>> = const { RefCell::new(vec![]) };
}

fn warning(at: &str, msg: String) {
    DIAG.with(|d| d.borrow_mut().warnings.push((at.to_string(), msg)));
}

/// Keeps the text of module `name` (see SOURCES)
pub fn remember_source(name: &str, src: &str) {
    SOURCES.with(|s| s.borrow_mut().insert(name.to_string(), src.to_string()));
}

/// A name from `parser::parse_module_sany` without its position, and the position
fn untag(n: &str) -> (&str, &str) {
    n.split_once(NAME_AT).unwrap_or((n, ""))
}

/// Where SANY places the definitions built into TLA+
const BUILTINS_AT: &str = "In module --TLA+ BUILTINS--";

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
    let place = |o: &str, n: &str| {
        crate::std_modules::STD_DEFS
            .iter()
            .find(|d| d.0 == o && d.1 == n)
            .map(|&(_, _, l1, c1, l2, c2, k)| (format!("line {l1}, col {c1} to line {l2}, col {c2} of module {o}"), k))
            .unwrap_or_default()
    };
    Some(
        own.iter()
            .flat_map(|(o, ns)| {
                ns.iter().map(move |n| {
                    let (at, arity) = place(o, n);
                    // The operator parameters of the standard modules' operators
                    let params = match *n {
                        "SelectSeq" => vec![0, 1],
                        "SortSeq" => vec![0, 2],
                        "BagOfAll" => vec![1, 0],
                        _ => vec![0; arity],
                    };
                    Sym { name: n.to_string(), origin: o.to_string(), decl: *n == "now", fixed: *n != "now", at, arity, params, inst: None }
                })
            })
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

/// After SANY: SANY's report of semantic errors, from `Semantic errors:` to the empty lines after
/// the last error or warning
pub const SEMANTIC: &str = "#sem ";

/// SANY's report of the errors and warnings in d: each with its position (when known), an empty
/// line and the message, then two empty lines
fn report(d: &Diag) -> String {
    let item = |(at, msg): &(String, String)| if at.is_empty() { format!("{msg}\n\n\n") } else { format!("{at}\n\n{msg}\n\n\n") };
    let mut s = "Semantic errors:\n\n".to_string();
    if !d.errors.is_empty() {
        s += &format!("*** Errors: {}\n\n", d.errors.len());
    }
    s.extend(d.errors.iter().map(item));
    if !d.warnings.is_empty() {
        s += &format!("*** Warnings: {}\n\n", d.warnings.len());
        s.extend(d.warnings.iter().map(item));
    }
    s
}

/// A semantic error at `at` (see SEMANTIC)
pub fn report_one(at: &str, msg: &str) -> String {
    format!("{SANY}{SEMANTIC}{}", report(&Diag { errors: vec![(at.to_string(), msg.to_string())], warnings: vec![] }))
}

fn clash(x: &str, other: &str) -> String {
    format!("Multiply-defined symbol '{x}': this definition or declaration conflicts \nwith the one at {other}.")
}

fn duplicate(x: &str, other: &str) -> String {
    format!("Multiple declarations or definitions for symbol {x}.  \nThis duplicates the one at {other}.")
}

/// Checks module `m` (a module read from a file, after the modules it extends and instantiates
/// have been loaded) and the modules nested in it, and records what they export
pub fn check(m: &Module) -> R<()> {
    DIAG.with(|d| *d.borrow_mut() = Diag::default());
    GLOBAL.with(|g| g.borrow_mut().clear());
    let ex = module(m, vec![], true);
    let global = GLOBAL.with(|g| std::mem::take(&mut *g.borrow_mut()));
    EXPORTS.with(|e| e.borrow_mut().insert(m.name.clone(), ex));
    let take = || DIAG.with(|d| std::mem::take(&mut *d.borrow_mut()));
    let d = take();
    if d.errors.is_empty() && !global.is_empty() {
        let item = |(at, msg): &(String, String)| format!("{at}\n\n{msg}\n\n\n");
        let mut s = format!("Semantic errors in global context:\n\n*** Warnings: {}\n\n", global.len());
        s.extend(global.iter().map(item));
        WARNED.with(|w| w.borrow_mut().push(s));
    }
    if d.errors.is_empty() && d.warnings.is_empty() {
        return Ok(());
    }
    // The same checks on the module parsed with the positions SANY reports (the same errors are
    // expected; if not, they are reported without positions)
    let src = SOURCES.with(|s| s.borrow().get(&m.name).cloned());
    let again = src.and_then(|src| crate::parser::parse_module_sany(&src).ok()).map(|m| {
        module(&m, vec![], true);
        take()
    });
    let d = match again {
        Some(again) if again.errors.len() == d.errors.len() && again.warnings.len() == d.warnings.len() => again,
        _ => d,
    };
    if d.errors.is_empty() {
        // SANY prints its warnings and goes on
        WARNED.with(|w| w.borrow_mut().push(report(&d)));
        return Ok(());
    }
    Err(format!("{SANY}{SEMANTIC}{}", report(&d)))
}

/// SANY's reports of the modules checked since the last call that had warnings and no errors, in
/// the order checked
pub fn take_warnings() -> Vec<String> {
    WARNED.with(|w| std::mem::take(&mut *w.borrow_mut()))
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
    /// Where the symbol n in scope is declared or defined, and whether it is a definition (not a
    /// CONSTANT, VARIABLE or built-in name), with its number of parameters
    fn place(&self, n: &str) -> Option<(String, bool, usize)> {
        match self.get(n) {
            Some(s) => Some((s.at.clone(), !s.decl, s.arity)),
            None if builtin(n) => Some((BUILTINS_AT.to_string(), false, 0)),
            None => None,
        }
    }
}

/// After a definition named like a symbol in scope (`place`): a warning when that is a definition
/// with as many parameters, an error otherwise. Whether the definition is then in scope (not after
/// an error)
fn redefined(name: &str, at: &str, arity: usize, place: Option<(String, bool, usize)>) -> bool {
    match place {
        Some((other, true, k)) if k == arity => warning(at, duplicate(name, &other)),
        Some((other, _, _)) => {
            error(at, clash(name, &other));
            return false;
        }
        None => {}
    }
    true
}

/// Checks a module whose scope starts as `base` (what is in scope where a nested module starts),
/// recording its errors (see DIAG), and returns what it exports. `known` is whether every name in
/// scope is known: not when the module (or the one it is nested in) extends one tla2rs does not
/// read
fn module(m: &Module, base: Vec<Sym>, mut known: bool) -> Option<Vec<Sym>> {
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
                        // Another definition of the name from another extended module: SANY
                        // warns "in global context"
                        if let Some(old) = scope.get(&s.name).filter(|o| !o.decl && !s.decl) {
                            let msg = format!("Warning: the definition of '{}' conflicts with \nits definition at {}.", s.name, old.at);
                            GLOBAL.with(|g| g.borrow_mut().push((s.at.clone(), msg)));
                        }
                        scope.push(s);
                    }
                }
            }
            _ => known = false,
        }
    }
    let own = |n: &str, decl: bool, at: &str, params: Vec<usize>| Sym {
        name: n.to_string(),
        origin: format!("{}.{n}", m.name),
        decl,
        fixed: false,
        at: at.to_string(),
        arity: params.len(),
        params,
        inst: None,
    };
    let params_of = |d: &Def| (0..d.params.len()).map(|k| d.arity.get(k).copied().unwrap_or(0)).collect::<Vec<usize>>();
    // The RECURSIVE declarations not defined yet, with their positions
    let mut pending_rec: Vec<(String, String)> = vec![];
    // The name of a recursive function whose body was checked with its `#app` definition
    let mut checked_body: Option<String> = None;
    for (k, u) in m.units.iter().enumerate() {
        let (at, arity) = m.unit_at.get(k).map(|(a, n)| (a.as_str(), *n)).unwrap_or(("", 0));
        match u {
            Unit::Decl(n) | Unit::Theorem(n) => {
                if let Some((other, _, _)) = scope.place(n) {
                    // A second declaration of the module's own CONSTANT or VARIABLE, of the same
                    // kind, is only a warning (`VARIABLE x, x`)
                    let kind = match (m.variables.contains(n), m.constants.contains(n)) {
                        (true, false) => Some(Kind::Var),
                        (false, true) => Some(Kind::Const),
                        _ => None,
                    };
                    let same = kind.is_some() && ctx.all.iter().find(|(x, _)| x == n).map(|(_, k)| *k) == kind;
                    if matches!(u, Unit::Decl(_)) && scope.get(n).is_some_and(|s| s.decl) && same {
                        warning(at, duplicate(n, &other));
                    } else {
                        error(at, clash(n, &other));
                    }
                    continue;
                }
                let s = own(n, matches!(u, Unit::Decl(_)), at, vec![0; arity]);
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
                pending_rec.push((n.clone(), at.to_string()));
                if let Some((other, _, _)) = scope.place(n) {
                    error(at, clash(n, &other));
                    continue;
                }
                ctx.add(n, Kind::Def, true);
                // Exported even when the definition is LOCAL (measured: a module that extends
                // one with `RECURSIVE F(_)` and `LOCAL F(n) == ...` may not define F)
                // What its parameters take is known once it is defined
                scope.push(own(n, false, at, vec![usize::MAX; arity]));
                out.push(own(n, false, at, vec![usize::MAX; arity]));
            }
            Unit::Assume(i) => Walker::new(&scope, known, &m.recursive).expr(&m.assumes[*i].expr),
            Unit::Def(i, fun) => {
                let d = &m.defs[*i];
                if let Some(f) = d.name.strip_suffix("#app") {
                    // `f[x \in S] == e` that refers to f: f is in scope in S and e, after the
                    // bound variables
                    let mut w = Walker::new(&scope, known, &m.recursive);
                    for p in &d.params {
                        w.bind_var(p);
                    }
                    w.fun_name(f, at);
                    w.expr(&d.body);
                    checked_body = Some(f.to_string());
                    continue;
                }
                if d.name.contains('#') {
                    continue;
                }
                let rec = match pending_rec.iter().position(|(r, _)| *r == d.name) {
                    Some(k) => {
                        pending_rec.remove(k);
                        // SANY places the symbol at its definition from now on
                        for s in scope.syms.iter_mut().chain(out.iter_mut()).filter(|s| s.name == d.name && s.origin == format!("{}.{}", m.name, d.name)) {
                            s.at = at.to_string();
                            s.params = params_of(d);
                        }
                        true
                    }
                    None => false,
                };
                let mut added = true;
                if checked_body.take().as_deref() != Some(d.name.as_str()) {
                    let mut w = Walker::new(&scope, known, &m.recursive);
                    if *fun {
                        // Checked once its bound variables are in scope
                        w.fun_def = Some((d.name.clone(), at.to_string()));
                    } else {
                        for (p, k) in d.params.iter().zip(d.arity.iter().chain(std::iter::repeat(&0))) {
                            w.bind(p, *k);
                        }
                        if !rec && w.has(&d.name) {
                            error(at, format!("Operator {} already defined or declared.", d.name));
                        }
                    }
                    w.expr(&d.body);
                    if !rec && !*fun {
                        added = redefined(&d.name, at, d.params.len(), scope.place(&d.name));
                    }
                }
                ctx.add(&d.name, Kind::Def, !m.local_defs.contains(&d.name));
                let s = own(&d.name, false, at, params_of(d));
                if added && !scope.syms.contains(&s) {
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
                        let mut w = Walker::new(&scope, known, &m.recursive);
                        for p in &inst.params {
                            w.bind(p, 0);
                        }
                        if w.has(n) {
                            error(at, format!("Operator {n} already defined or declared."));
                        }
                        for (_, e) in &inst.subs {
                            w.arg(e);
                        }
                        redefined(n, at, inst.params.len(), scope.place(n));
                        let mut s = own(n, false, at, (0..inst.params.len()).map(|k| inst.arity.get(k).copied().unwrap_or(0)).collect());
                        s.inst = Some(inst.module.clone());
                        scope.push(s.clone());
                        if !local {
                            out.push(s);
                        }
                    }
                    None => {
                        let mut w = Walker::new(&scope, known, &m.recursive);
                        for (_, e) in &inst.subs {
                            w.arg(e);
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
                                Some(old) => error(at, duplicate(&s.name, &old.at)),
                                None if builtin(&s.name) => error(at, clash(&s.name, BUILTINS_AT)),
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
                let ex = module(inner, scope.syms.clone(), known);
                EXPORTS.with(|e| e.borrow_mut().insert(inner.name.clone(), ex));
                ctx.add(&inner.name, Kind::Module, true);
            }
        }
    }
    for (n, at) in pending_rec {
        error(&at, format!("Symbol {n} declared in RECURSIVE statement but not defined."));
    }
    CONTEXTS.with(|c| c.borrow_mut().insert(m.name.clone(), ctx_known.then_some(ctx)));
    // The module's own definitions are fixed when nothing in it is a constant or variable
    if !scope.syms.iter().any(|s| s.decl) {
        let prefix = format!("{}.", m.name);
        for s in out.iter_mut().filter(|s| s.origin.starts_with(&prefix)) {
            s.fixed = true;
        }
    }
    known.then_some(out)
}

/// An argument of a call without the ARG_AT label around it in a tree from
/// `parser::parse_module_sany`, and the position the label gives (empty without one)
fn arg_at(e: &Expr) -> (&Expr, String) {
    match e {
        Expr::Label(n, _, b) if n.starts_with(ARG_AT) => (b, n[ARG_AT.len()..].to_string()),
        e => (e, String::new()),
    }
}

/// The number of arguments each parameter of d takes
fn let_params(d: &Def) -> Vec<usize> {
    (0..d.params.len()).map(|k| d.arity.get(k).copied().unwrap_or(0)).collect()
}

/// A parameter, bound variable or LET definition in scope: where SANY places it, its number of
/// parameters and whether it is a definition
struct Local {
    name: String,
    at: String,
    arity: usize,
    def: bool,
    /// The number of arguments each parameter takes
    params: Vec<usize>,
}

/// Checks the names in the expressions of one definition (or ASSUME, or INSTANCE)
struct Walker<'a> {
    scope: &'a Scope,
    /// Whether an unknown name is an error (not when the module extends one tla2rs does not read)
    known: bool,
    /// The names declared RECURSIVE (also in LET)
    recursive: &'a [String],
    /// Parameters, bound variables and LET definitions in scope, innermost last
    locals: Vec<Local>,
    /// The bound variables introduced since the enclosing label or definition
    label_bound: Vec<String>,
    /// The position of the label being entered, from the AT label the parser puts around it
    label_at: Option<String>,
    /// The positions of the operator applied in the expression being entered, from an OP_AT label
    op_at: Option<(String, String)>,
    /// A function definition `f[x \in S] == e` being checked, with its position: its name is
    /// checked once its bound variables are in scope
    fun_def: Option<(String, String)>,
}

impl<'a> Walker<'a> {
    fn new(scope: &'a Scope, known: bool, recursive: &'a [String]) -> Self {
        Walker { scope, known, recursive, locals: vec![], label_bound: vec![], label_at: None, op_at: None, fun_def: None }
    }

    fn has(&self, n: &str) -> bool {
        self.scope.has(n) || self.locals.iter().any(|l| l.name == n)
    }

    /// The number of parameters of the operator n in scope and the number of arguments each of
    /// them takes, also for `N!Op` of a named INSTANCE without parameters (None when not known)
    fn op_info(&self, n: &str) -> Option<(usize, Vec<usize>)> {
        if let Some((inst, op)) = n.split_once('!') {
            if self.locals.iter().any(|l| l.name == inst) {
                return None;
            }
            let s = self.scope.get(inst)?;
            let module = s.inst.as_ref().filter(|_| s.arity == 0)?;
            let syms = exports(module)??;
            let d = syms.iter().rev().find(|d| d.name == op && !d.decl)?;
            return Some((d.arity, d.params.clone()));
        }
        if let Some(l) = self.locals.iter().rev().find(|l| l.name == n) {
            return Some((l.arity, l.params.clone()));
        }
        self.scope.get(n).map(|s| (s.arity, s.params.clone()))
    }

    /// The arguments of the operator n called at `at_all` (where its name is at `at_name`), as
    /// SANY checks them against the operator's parameters: an operator's name or a LAMBDA where
    /// a parameter takes no arguments is refused, and so is anything but an operator of as many
    /// parameters where it takes some (measured on SANY 2.19, `tests/tlc/RejSanyOpArg*`)
    fn args(&mut self, n: &str, args: &[Expr], at_name: &str, at_all: &str) {
        let Some((_, params)) = self.op_info(n).filter(|(_, p)| p.len() == args.len() && !p.contains(&usize::MAX)) else {
            return args.iter().for_each(|a| self.arg(arg_at(a).0));
        };
        // From the operator's name to the closing parenthesis
        let whole = match (at_name.split_once(" to "), at_all.split_once(" to ")) {
            (Some((from, _)), Some((_, to))) => format!("{from} to {to}"),
            _ => at_all.to_string(),
        };
        // Reported after the arguments' own errors
        let mut wrongs = vec![];
        let mut wrong = |i: usize, j: usize| wrongs.push(format!("Argument number {} to operator '{}' \nshould be a {j}-parameter operator.", i + 1, sany_name(n)));
        for (i, (a, &j)) in args.iter().zip(&params).enumerate() {
            let (a, at) = arg_at(a);
            match a {
                Expr::Ident(x, xat) => {
                    let x = untag(x).0;
                    let xat = xat.text_if_known();
                    // An operator symbol passed as an argument (`SortSeq(s, <)`) is not checked
                    if !self.resolve(x, &xat, true) || !x.starts_with(|c: char| c.is_alphanumeric() || c == '_') {
                        continue;
                    }
                    let Some((k, _)) = self.op_info(x).or_else(|| self.place(x).map(|p| (p.2, vec![]))) else { continue };
                    if j == 0 && k > 0 {
                        error(&xat, format!("The operator {} requires {k} arguments.", sany_name(x)));
                    } else if j > 0 && k != j {
                        error(&xat, format!("Expected arity {j} but found operator of arity {k}."));
                        wrong(i, j);
                    }
                }
                Expr::Lambda(ps, _) if j == 0 => {
                    let _ = ps;
                    error(&at, "LAMBDA expression used where an expression is required.".into());
                }
                Expr::Lambda(ps, _) if ps.len() != j => {
                    error(at_name, format!("Lambda expression with arity {} used as argument {} of operator `{}', \nbut an operator of arity {j} is required.", ps.len(), i + 1, sany_name(n)));
                    wrong(i, j);
                }
                a if j > 0 && !matches!(a, Expr::Lambda(..)) => {
                    error(&at, format!("An expression appears as argument number {} (counting from 1) to operator '{}', in a position an operator is required.", i + 1, sany_name(n)));
                    wrong(i, j);
                }
                a => self.arg(a),
            }
        }
        for w in wrongs {
            error(&whole, w);
        }
    }

    /// See `Scope::place`, for locals too
    fn place(&self, n: &str) -> Option<(String, bool, usize)> {
        match self.locals.iter().rev().find(|l| l.name == n) {
            Some(l) => Some((l.at.clone(), l.def, l.arity)),
            None => self.scope.place(n),
        }
    }

    /// Puts x (a name with its position, see `untag`) in scope, with `arity` parameters, refusing
    /// a name already there (which then stays what it was). Whether it was put in scope
    fn bind(&mut self, x: &str, arity: usize) -> bool {
        let (n, at) = untag(x);
        if !n.contains('#') {
            if let Some((other, _, _)) = self.place(n) {
                error(at, clash(n, &other));
                return false;
            }
        }
        self.locals.push(Local { name: n.to_string(), at: at.to_string(), arity, def: false, params: vec![0; arity] });
        true
    }

    /// Like `bind`, for a bound variable (which a label inside must list)
    fn bind_var(&mut self, x: &str) {
        let n = untag(x).0;
        if self.bind(x, 0) && !n.contains('#') {
            self.label_bound.push(n.to_string());
        }
    }

    /// The name f of a function definition at `at`, once its bound variables are in scope
    fn fun_name(&mut self, f: &str, at: &str) {
        if self.has(f) {
            error(at, format!("Function name `{f}' already defined or declared."));
        } else {
            self.locals.push(Local { name: f.to_string(), at: at.to_string(), arity: 0, def: true, params: vec![] });
        }
    }

    /// Whether name n is in scope, recording SANY's error if not. An operator with parameters
    /// named alone, where it is not an argument (`arg`), is refused too
    fn resolve(&self, n: &str, at: &str, arg: bool) -> bool {
        // `@` names made for EXCEPT, not the operator `@@`
        if !self.known || n.contains('#') || (n.starts_with('@') && n != "@@") {
            return true;
        }
        // `N!Op` (an instance's operator) and `Op!lab` (a label) need N and Op (`!!` is an
        // operator symbol)
        let word = n.starts_with(|c: char| c.is_alphanumeric() || c == '_');
        let base = sany_name(if word { n.split('!').next().unwrap_or(n) } else { n });
        match self.place(base) {
            Some((_, _, k)) => {
                if word && !arg && k > 0 && !n.contains('!') {
                    error(at, format!("The operator {base} requires {k} arguments."));
                }
                // `N!Op` of a named INSTANCE, or `Op!lab` of a definition, named without the
                // arguments its operator takes
                if word && !arg && n.contains('!') {
                    if let Some((k, _)) = self.op_info(n).filter(|(k, _)| *k > 0) {
                        error(at, format!("The operator {n} requires {k} arguments."));
                    } else if let Some((_, true, k)) = self.place(base).filter(|p| p.2 > 0 && self.scope.get(base).is_none_or(|s| s.inst.is_none())) {
                        error(at, format!("The operator {base} requires {k} arguments."));
                    }
                }
                true
            }
            None if word => {
                error(at, format!("Unknown operator: `{base}'."));
                false
            }
            None => {
                error(at, format!("Could not find declaration or definition of symbol '{base}'."));
                false
            }
        }
    }

    /// Whether the operator symbol `sym` applied at `at` (see `op_at`) is in scope; if not,
    /// SANY's two errors, the second naming it an operator of `kind` (infix, prefix)
    fn resolve_sym(&self, sym: &str, kind: &str, at: Option<(String, String)>) -> bool {
        let (at_sym, at_all) = at.unwrap_or_default();
        if !self.resolve(sym, &at_sym, false) {
            error(&at_all, format!("Couldn't resolve {kind} operator symbol `{sym}'."));
            return false;
        }
        true
    }

    /// Runs f with the scope restored afterwards
    fn scoped(&mut self, f: impl FnOnce(&mut Self)) {
        let (l, b) = (self.locals.len(), self.label_bound.len());
        f(self);
        self.locals.truncate(l);
        self.label_bound.truncate(b);
    }

    /// An argument of an operator, which may be a LAMBDA (only there, or in a WITH substitution)
    /// or an operator's name
    fn arg(&mut self, e: &Expr) {
        match arg_at(e).0 {
            Expr::Lambda(ps, body) => self.scoped(|w| {
                for p in ps {
                    w.bind(p, 0);
                }
                w.expr(body)
            }),
            Expr::Ident(n, at) => {
                self.resolve(untag(n).0, &at.text_if_known(), true);
            }
            e => self.expr(e),
        }
    }

    fn expr(&mut self, e: &Expr) {
        use Expr::*;
        let op_at = self.op_at.take();
        match e {
            Num(_) | Str(_) | Bool(_) | At | RecCall(..) => {}
            Ident(n, at) => {
                self.resolve(untag(n).0, &at.text_if_known(), false);
            }
            Call(n, args) => {
                if n.starts_with(crate::parser::UNBOUNDED) || n == "\\EE" || n == "\\AA" {
                    // Their bound variables are not kept
                    return;
                }
                if n.starts_with(crate::parser::SUBEXPR) {
                    for (k, a) in args.iter().enumerate() {
                        match a {
                            Ident(x, _) if k > 0 && ["<<", ">>", ":", "@"].contains(&x.as_str()) => {}
                            Call(l, la) if l.starts_with("#label") => la.iter().for_each(|x| self.expr(x)),
                            Tuple(vs) if k > 0 => vs.iter().for_each(|x| self.expr(x)),
                            Ident(x, at) if k == 0 => {
                                let (x, at) = (untag(x).0, at.text_if_known());
                                if !self.resolve(x, &at, true) || builtin(x) {
                                    continue;
                                }
                                // Only a definition has subexpressions, and only applied to its
                                // arguments (SANY places that error from the name to the last
                                // selector)
                                match self.place(x) {
                                    Some((_, false, _)) => error(&at, format!("Cannot take subexpression of `{x}'.")),
                                    Some((_, true, k)) if k > 0 => {
                                        let last = crate::parser::subexpr_at(n).last().and_then(|l| l.split_once(" to ")).map(|(_, to)| to.to_string());
                                        let whole = match (at.split_once(" to "), last) {
                                            (Some((from, _)), Some(to)) => format!("{from} to {to}"),
                                            _ => at.clone(),
                                        };
                                        error(&whole, format!("The operator {x} requires {k} arguments."));
                                    }
                                    _ => {}
                                }
                            }
                            a => self.expr(a),
                        }
                    }
                    return;
                }
                let word = n.starts_with(|c: char| c.is_alphanumeric() || c == '_');
                let (at_name, at_all) = op_at.clone().unwrap_or_default();
                let found = if word || args.len() != 2 { self.resolve(n, &at_name, true) } else { self.resolve_sym(n, "infix", op_at) };
                // SANY does not look at the arguments of an operator it cannot find, or of one
                // called with as many arguments as it takes
                let arity = if word && self.known && !n.contains('!') { self.place(n).map(|p| p.2) } else { None };
                match arity {
                    _ if !found => {}
                    Some(k) if k != args.len() => error(&at_all, format!("The operator {n} requires {k} arguments.")),
                    _ if found => self.args(n, args, &at_name, &at_all),
                    _ => args.iter().for_each(|a| self.arg(arg_at(a).0)),
                }
            }
            Un(op, x) => {
                if *op != UOp::Neg || self.resolve_sym("-.", "prefix", op_at) {
                    self.expr(x)
                }
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
                if sym.map_or(true, |s| self.resolve_sym(s, "infix", op_at)) {
                    self.expr(a);
                    self.expr(b);
                }
            }
            Quant(_, bs, body) | SetMap(body, bs) => {
                for (_, s) in bs {
                    self.expr(s);
                }
                self.scoped(|w| {
                    for (x, _) in bs {
                        w.bind_var(x);
                    }
                    w.expr(body)
                })
            }
            Choose(x, s, p) | SetFilter(x, s, p) | FunCons(x, s, p) => {
                let fun = if matches!(e, FunCons(..)) { self.fun_def.take() } else { None };
                self.expr(s);
                self.scoped(|w| {
                    w.bind_var(x);
                    match fun {
                        // `f[<<a, b>> \in S] == e`: the names are bound by a LET inside
                        Some(f) if x.starts_with('#') => w.fun_def = Some(f),
                        Some((f, at)) => w.fun_name(&f, &at),
                        None => {}
                    }
                    w.expr(p)
                })
            }
            Lambda(..) => error("", "LAMBDA expression used where an expression is required.".into()),
            Let(defs, body) => self.scoped(|w| {
                let fun = w.fun_def.take();
                let mut checked_body: Option<&str> = None;
                for d in defs {
                    // `<<x, y>> \in S` binds x and y as `x == t[1]`, `y == t[2]`
                    let pattern = matches!(&d.body, App(t, i) if matches!(t.as_ref(), Ident(n, _) if n.starts_with('#')) && matches!(i.as_ref(), Num(_)));
                    if pattern {
                        w.bind_var(&d.name);
                        continue;
                    }
                    let (dname, at) = untag(&d.name);
                    let fun_app = dname.strip_suffix("#app");
                    let name = fun_app.unwrap_or(dname);
                    if fun_app.is_none() && checked_body == Some(name) {
                        // The function of a recursive function definition, checked with it
                        continue;
                    }
                    let rec = fun_app.is_some() || w.recursive.iter().any(|r| r == dname);
                    let saved = std::mem::take(&mut w.label_bound);
                    w.scoped(|w| {
                        for (p, k) in d.params.iter().zip(d.arity.iter().chain(std::iter::repeat(&0))) {
                            if fun_app.is_some() { w.bind_var(p) } else { w.bind(p, *k); }
                        }
                        if fun_app.is_some() {
                            w.fun_name(name, at);
                        } else if rec {
                            w.locals.push(Local { name: name.to_string(), at: at.to_string(), arity: d.params.len(), def: true, params: let_params(d) });
                        } else if w.has(name) {
                            error(at, format!("Operator {name} already defined or declared."));
                        }
                        // The parameters of a LET definition are not listed by its labels
                        if fun_app.is_none() {
                            w.label_bound.clear();
                        }
                        w.expr(&d.body)
                    });
                    w.label_bound = saved;
                    if fun_app.is_some() {
                        checked_body = Some(name);
                    }
                    // A function takes no parameters, unlike the `#app` operator it is checked with
                    let arity = if fun_app.is_some() { 0 } else { d.params.len() };
                    if rec || redefined(name, at, arity, w.place(name)) {
                        w.locals.push(Local { name: name.to_string(), at: at.to_string(), arity, def: true, params: if arity == 0 { vec![] } else { let_params(d) } });
                    }
                }
                if let Some((f, at)) = fun {
                    w.fun_name(&f, &at);
                }
                w.expr(body)
            }),
            Label(n, _, body) if n.starts_with(ARG_AT) => self.expr(body),
            Label(n, _, body) if n.starts_with(OP_AT) => {
                let (s, all) = n[OP_AT.len()..].split_once('\u{1}').unwrap_or_default();
                self.op_at = Some((s.to_string(), all.to_string()));
                self.expr(body)
            }
            Label(n, args, body) => {
                for a in args {
                    self.expr(a);
                }
                if let Some(at) = err_pos_of(n) {
                    if body.is_user_label() {
                        self.label_at = Some(at.to_string());
                        return self.expr(body);
                    }
                }
                let Some(head) = n.strip_suffix("::") else { return self.expr(body) };
                let at = self.label_at.take().unwrap_or_default();
                let ps: Vec<&str> = match head.split_once('(') {
                    Some((_, rest)) => rest.trim_end_matches(')').split(',').filter(|p| !p.is_empty()).collect(),
                    None => vec![],
                };
                let l = head.split('(').next().unwrap_or(head);
                for (k, p) in ps.iter().enumerate() {
                    if ps[..k].contains(p) {
                        return error("", format!("Repeated formal parameter {p} in label `{l}'."));
                    }
                    if !self.label_bound.iter().any(|x| x == p) {
                        return error("", format!("Illegal parameter {p} of label `{l}'."));
                    }
                }
                if let Some(x) = self.label_bound.iter().find(|x| !ps.contains(&x.as_str())) {
                    return error(&at, format!("Label {l} must contain formal parameter `{x}'."));
                }
                let saved = std::mem::take(&mut self.label_bound);
                self.expr(body);
                self.label_bound = saved;
            }
            e => e.children().into_iter().for_each(|c| self.expr(c)),
        }
    }
}
