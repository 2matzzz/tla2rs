//! `--emit-lib`: the generated checker as a library crate, for checking an implementation
//! against the spec from its tests (see "The checker as a library" in CLAUDE.md).
//!
//! The library is the checker's own code (`Output::rust`, so `init`, `next`, the invariants and
//! the state are the ones the checker runs) followed by a public module `conform`, made of
//! `CONFORM` below and of the conversions `Gen::lib_code` generates for the spec's types.

/// The text of a library crate's `src/lib.rs`: the checker `rust` and the module `conform` with
/// the generated `lib` part
pub fn lib_rs(rust: &str, lib: &str) -> String {
    let mut s = String::with_capacity(rust.len() + CONFORM.len() + lib.len() + 256);
    // An inner attribute has to come first, and a library exports names the checker keeps private
    s += "#![allow(unused, non_snake_case, unused_parens, unused_braces, private_interfaces, clippy::all)]\n";
    for line in rust.lines() {
        if !line.starts_with("#![allow(") {
            s += line;
            s.push('\n');
        }
    }
    s += "\n/// What an implementation's tests use (written by tla2rs --emit-lib)\npub mod conform {\nuse super::*;\n";
    s += CONFORM;
    s += lib;
    s += "}\n";
    s
}

/// The part of the module `conform` that is the same for every spec. It is a child module of the
/// checker's code, so it reaches the checker's private items, and its own names come before
/// theirs.
///
/// `next` is called outside a search here: `dd_fresh` returns true when no search runs on the
/// thread, so every successor is built.
pub const CONFORM: &str = r##"
use std::collections::{HashMap, HashSet, VecDeque};

/// A TLA+ value, to build a state from and to read one as
#[derive(Clone, Debug, PartialEq)]
pub enum Val {
    Bool(bool),
    Int(i64),
    Str(String),
    /// A model value
    Model(String),
    Set(Vec<Val>),
    /// A tuple or a sequence
    Seq(Vec<Val>),
    Rec(Vec<(String, Val)>),
    /// A function, as its pairs of argument and value
    Fun(Vec<(Val, Val)>),
    /// A value of a type this library cannot convert yet, as TLC prints it. It can be read, and
    /// no state can be built from it
    Opaque(String),
}

impl Val {
    pub fn str(s: &str) -> Val {
        Val::Str(s.to_string())
    }
    pub fn model(s: &str) -> Val {
        Val::Model(s.to_string())
    }
    pub fn set(xs: impl IntoIterator<Item = Val>) -> Val {
        Val::Set(xs.into_iter().collect())
    }
    pub fn seq(xs: impl IntoIterator<Item = Val>) -> Val {
        Val::Seq(xs.into_iter().collect())
    }
    pub fn rec<'a>(fs: impl IntoIterator<Item = (&'a str, Val)>) -> Val {
        Val::Rec(fs.into_iter().map(|(n, v)| (n.to_string(), v)).collect())
    }
    pub fn fun(ps: impl IntoIterator<Item = (Val, Val)>) -> Val {
        Val::Fun(ps.into_iter().collect())
    }
}

impl From<bool> for Val {
    fn from(b: bool) -> Val {
        Val::Bool(b)
    }
}

impl From<i64> for Val {
    fn from(n: i64) -> Val {
        Val::Int(n)
    }
}

impl From<&str> for Val {
    fn from(s: &str) -> Val {
        Val::str(s)
    }
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let list = |xs: &[Val]| xs.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
        match self {
            Val::Bool(b) => write!(f, "{}", if *b { "TRUE" } else { "FALSE" }),
            Val::Int(n) => write!(f, "{n}"),
            Val::Str(s) => write!(f, "{s:?}"),
            Val::Model(s) | Val::Opaque(s) => write!(f, "{s}"),
            Val::Set(xs) => write!(f, "{{{}}}", list(xs)),
            Val::Seq(xs) => write!(f, "<<{}>>", list(xs)),
            Val::Rec(fs) => write!(f, "[{}]", fs.iter().map(|(n, v)| format!("{n} |-> {v}")).collect::<Vec<_>>().join(", ")),
            Val::Fun(ps) if ps.is_empty() => write!(f, "<< >>"),
            Val::Fun(ps) => write!(f, "({})", ps.iter().map(|(k, v)| format!("{k} :> {v}")).collect::<Vec<_>>().join(" @@ ")),
        }
    }
}

fn mismatch(want: &str, v: &Val) -> String {
    format!("expected {want}, got {v}")
}

/// The number the checker gives a string or a model value
fn atom_of(v: &Val) -> Result<u16, String> {
    let (name, is_str) = match v {
        Val::Str(s) => (s, true),
        Val::Model(s) => (s, false),
        _ => return Err(mismatch("a string or a model value", v)),
    };
    match (0..ATOM_NAMES.len()).find(|&i| ATOM_NAMES[i] == name && IS_STR[i] == is_str) {
        Some(i) => Ok(i as u16),
        None => Err(format!("{v} is not a {} of the spec", if is_str { "string" } else { "model value" })),
    }
}

fn atom_val(a: u16) -> Val {
    let name = ATOM_NAMES[a as usize].to_string();
    if IS_STR[a as usize] {
        Val::Str(name)
    } else {
        Val::Model(name)
    }
}

/// The pairs of a function, however it is written: a tuple is the function over 1..n, a record
/// the function over its field names
fn fun_of(v: &Val) -> Option<Vec<(Val, Val)>> {
    match v {
        Val::Fun(ps) => Some(ps.clone()),
        Val::Seq(xs) => Some(xs.iter().enumerate().map(|(i, x)| (Val::Int(i as i64 + 1), x.clone())).collect()),
        Val::Rec(fs) => Some(fs.iter().map(|(n, x)| (Val::Str(n.clone()), x.clone())).collect()),
        _ => None,
    }
}

/// The elements of a tuple or sequence, also when it is written as a function over 1..n
fn seq_of(v: &Val) -> Option<Vec<Val>> {
    match v {
        Val::Seq(xs) => Some(xs.clone()),
        Val::Rec(fs) if fs.is_empty() => Some(vec![]),
        Val::Fun(ps) => {
            let mut out = vec![None; ps.len()];
            for (k, x) in ps {
                match k {
                    Val::Int(i) if *i >= 1 && (*i as usize) <= ps.len() && out[*i as usize - 1].is_none() => out[*i as usize - 1] = Some(x.clone()),
                    _ => return None,
                }
            }
            out.into_iter().collect()
        }
        _ => None,
    }
}

/// The fields of a record, also when it is written as a function over strings
fn rec_of(v: &Val) -> Option<Vec<(String, Val)>> {
    match v {
        Val::Rec(fs) => Some(fs.clone()),
        Val::Seq(xs) if xs.is_empty() => Some(vec![]),
        Val::Fun(ps) => ps.iter().map(|(k, x)| if let Val::Str(n) = k { Some((n.clone(), x.clone())) } else { None }).collect(),
        _ => None,
    }
}

fn field<'a>(fs: &'a [(String, Val)], name: &str) -> Result<&'a Val, String> {
    let mut it = fs.iter().filter(|(n, _)| n == name);
    match (it.next(), it.next()) {
        (Some((_, v)), None) => Ok(v),
        (None, _) => Err(format!("the record has no field {name}")),
        _ => Err(format!("the record has the field {name} twice")),
    }
}

/// A function read from the state, written as TLC prints it: a tuple over 1..n, a record over
/// strings
fn canon_fun(ps: Vec<(Val, Val)>) -> Val {
    if ps.iter().enumerate().all(|(i, (k, _))| *k == Val::Int(i as i64 + 1)) {
        return Val::Seq(ps.into_iter().map(|(_, v)| v).collect());
    }
    if ps.iter().all(|(k, _)| matches!(k, Val::Str(_))) {
        return Val::Rec(ps.into_iter().map(|(k, v)| if let Val::Str(n) = k { (n, v) } else { unreachable!() }).collect());
    }
    Val::Fun(ps)
}

/// A state of the spec
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Abs(State);

impl Abs {
    /// The state as TLC prints it
    pub fn show(&self) -> String {
        show(&self.0)
    }

    /// The value of each variable, in the order of `VARIABLES`
    pub fn vars(&self) -> Vec<(&'static str, Val)> {
        var_vals(&self.0)
    }

    pub fn get(&self, var: &str) -> Option<Val> {
        self.vars().into_iter().find(|(n, _)| *n == var).map(|(_, v)| v)
    }

    /// Whether every variable is within its type (the type invariant, or the type tla2rs inferred)
    pub fn in_type(&self) -> bool {
        eval(|| pack(&self.0).is_some()).unwrap_or(false)
    }
}

impl std::fmt::Debug for Abs {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.show())
    }
}

/// Runs a part of the checker's code. Where the spec fails to evaluate (an operator applied
/// outside its domain, a false Assert, a set or sequence that outgrows the capacity the library
/// was written with), that code panics with a value of the checker's own: here it is TLC's
/// message. (The panic itself is still printed by the test's panic hook.)
fn eval<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(x) => Ok(x),
        Err(e) => match e.downcast::<EvalErr>() {
            Ok(e) => Err(e.msg().to_string()),
            Err(e) => std::panic::resume_unwind(e),
        },
    }
}

fn eval_or_panic<T>(f: impl FnOnce() -> T) -> T {
    eval(f).unwrap_or_else(|m| panic!("the spec failed to evaluate: {m}"))
}

/// The name of the action a label of a step stands for ("RMPrepare"), as in TLC's traces
pub fn action_name(l: u32) -> &'static str {
    LABELS[l as usize].split(" line ").next().unwrap_or("?")
}

/// The initial states. Panics with TLC's message if the spec fails to evaluate
pub fn initial_states() -> Vec<Abs> {
    let mut v = Vec::new();
    eval_or_panic(|| init(&mut v));
    let mut seen = HashSet::new();
    v.into_iter().map(Abs).filter(|s| seen.insert(*s)).collect()
}

/// The successors of `s` by the next-state relation, each with the label of its action, without
/// duplicates. Stuttering steps the spec takes are among them. CONSTRAINT and ACTION_CONSTRAINT
/// do not apply here (see `Graph`). Panics with TLC's message if the spec fails to evaluate
pub fn successors(s: Abs) -> Vec<(Abs, u32)> {
    try_successors(s).unwrap_or_else(|m| panic!("the spec failed to evaluate: {m}"))
}

fn try_successors(s: Abs) -> Result<Vec<(Abs, u32)>, String> {
    let mut v = Vec::new();
    eval(|| next(&s.0, &mut v))?;
    let mut seen = HashSet::new();
    Ok(v.into_iter().map(|(t, l)| (Abs(t), l)).filter(|e| seen.insert(*e)).collect())
}

/// How a run of the implementation left the spec
#[derive(Clone, Debug)]
pub enum Violation {
    /// The first state is not an initial state of the spec
    NotInitial,
    /// A variable is outside its type
    OutOfType,
    /// No action takes the state before to this one. `enabled` is what the spec allows from the
    /// state before: the action and the state it leads to
    NoSuchStep { enabled: Vec<(&'static str, Abs)> },
    /// The step is one of the spec, but not of the action the implementation said it took
    WrongAction { claimed: String, actual: Vec<&'static str> },
    /// An INVARIANT of the configuration is false in the state
    Invariant(&'static str),
    /// The step violates an action property (`[][A]_v`) of the configuration
    ActionProperty(&'static str),
    /// The spec failed to evaluate here (TLC's message): the successors of the state before, an
    /// invariant or an action property
    Eval(String),
}

impl std::fmt::Display for Violation {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Violation::NotInitial => write!(f, "the state is not an initial state of the spec"),
            Violation::OutOfType => write!(f, "a variable is outside its type"),
            Violation::NoSuchStep { enabled } => {
                let mut names: Vec<&str> = vec![];
                for (n, _) in enabled {
                    if !names.contains(n) {
                        names.push(n);
                    }
                }
                write!(f, "no action of the spec makes this step; from the state before it allows: {}", if names.is_empty() { "nothing".to_string() } else { names.join(", ") })
            }
            Violation::WrongAction { claimed, actual } => write!(f, "the step is not one of {claimed}; it is one of: {}", actual.join(", ")),
            Violation::Invariant(n) => write!(f, "invariant {n} is violated"),
            Violation::ActionProperty(n) => write!(f, "action property {n} is violated"),
            Violation::Eval(m) => write!(f, "the spec failed to evaluate: {m}"),
        }
    }
}

fn check_state(s: Abs) -> Result<(), Violation> {
    if !s.in_type() {
        return Err(Violation::OutOfType);
    }
    match eval(|| INVARIANTS.iter().find(|(_, f)| !f(&s.0))).map_err(Violation::Eval)? {
        Some((name, _)) => Err(Violation::Invariant(name)),
        None => Ok(()),
    }
}

/// Checks a run of the implementation against the spec one step at a time: each state the
/// implementation reports must be a successor of the one before by the next-state relation, or
/// the same state (a stuttering step), and must satisfy the invariants. Only the current state is
/// kept, so the size of the spec's state space does not matter.
///
/// Where the spec fails to evaluate, the error is `Violation::Eval` with TLC's message.
pub struct Checker {
    cur: Abs,
    /// The states visited
    pub states: HashSet<Abs>,
    /// The steps taken that changed the state, once for each action that explains the step
    pub steps: HashSet<(Abs, Abs, u32)>,
}

impl Checker {
    /// Starts a run in `s0`, which must be an initial state
    pub fn begin(s0: Abs) -> Result<Checker, Violation> {
        if !s0.in_type() {
            return Err(Violation::OutOfType);
        }
        let mut inits = Vec::new();
        eval(|| init(&mut inits)).map_err(Violation::Eval)?;
        if !inits.contains(&s0.0) {
            return Err(Violation::NotInitial);
        }
        check_state(s0)?;
        Ok(Checker { cur: s0, states: HashSet::from([s0]), steps: HashSet::new() })
    }

    pub fn current(&self) -> Abs {
        self.cur
    }

    /// The implementation moved to `s1`. `claimed` is the name of the action it says it took, if
    /// it says. Returns the labels of the actions that explain the step: none for a stuttering
    /// step. After an error the run stays where it was.
    pub fn step(&mut self, s1: Abs, claimed: Option<&str>) -> Result<Vec<u32>, Violation> {
        if s1 == self.cur {
            return Ok(vec![]);
        }
        if !s1.in_type() {
            return Err(Violation::OutOfType);
        }
        let succ = try_successors(self.cur).map_err(Violation::Eval)?;
        let by: Vec<u32> = succ.iter().filter(|(t, _)| *t == s1).map(|(_, l)| *l).collect();
        if by.is_empty() {
            let enabled = succ.iter().filter(|(t, _)| *t != self.cur).map(|(t, l)| (action_name(*l), *t)).collect();
            return Err(Violation::NoSuchStep { enabled });
        }
        if let Some(c) = claimed {
            if !by.iter().any(|l| action_name(*l) == c) {
                return Err(Violation::WrongAction { claimed: c.to_string(), actual: by.iter().map(|l| action_name(*l)).collect() });
            }
        }
        if let Some((name, _)) = eval(|| ACTION_PROPS.iter().find(|(_, f)| !f(&self.cur.0, &s1.0))).map_err(Violation::Eval)? {
            return Err(Violation::ActionProperty(name));
        }
        check_state(s1)?;
        for l in &by {
            self.steps.insert((self.cur, s1, *l));
        }
        self.states.insert(s1);
        self.cur = s1;
        Ok(by)
    }
}

/// The reachable state graph of the spec without its stuttering steps, built in memory by the
/// checker's `init` and `next`: what coverage is measured against, and where a test finds the
/// way to a transition it has not taken. As in the checker, a state outside the CONSTRAINT and a
/// step outside the ACTION_CONSTRAINT are left out. For a model small enough to hold: every state
/// and transition is kept.
pub struct Graph {
    pub states: Vec<Abs>,
    pub index: HashMap<Abs, usize>,
    /// (from, to, label of the action), each once
    pub edges: Vec<(usize, usize, u32)>,
    /// The edges leaving each state
    pub out: Vec<Vec<usize>>,
    /// The initial states
    pub initial: Vec<usize>,
}

impl Graph {
    pub fn explore() -> Graph {
        if HAS_VIEW || !PERMS.is_empty() {
            panic!("conform::Graph does not support a spec with VIEW or SYMMETRY: its states would not be the checker's");
        }
        let mut g = Graph { states: vec![], index: HashMap::new(), edges: vec![], out: vec![], initial: vec![] };
        let mut queue = VecDeque::new();
        for s in initial_states() {
            if eval_or_panic(|| constraint(&s.0)) {
                g.index.insert(s, g.states.len());
                g.initial.push(g.states.len());
                queue.push_back(g.states.len());
                g.states.push(s);
                g.out.push(vec![]);
            }
        }
        while let Some(i) = queue.pop_front() {
            for (t, l) in successors(g.states[i]) {
                if !eval_or_panic(|| in_model(&g.states[i].0, &t.0)) {
                    continue;
                }
                let j = match g.index.get(&t) {
                    Some(j) => *j,
                    None => {
                        let j = g.states.len();
                        g.index.insert(t, j);
                        g.states.push(t);
                        g.out.push(vec![]);
                        queue.push_back(j);
                        j
                    }
                };
                if i != j {
                    g.out[i].push(g.edges.len());
                    g.edges.push((i, j, l));
                }
            }
        }
        g
    }

    /// The labels of the actions on the graph's edges, in the order first met
    pub fn actions(&self) -> Vec<u32> {
        let mut seen = HashSet::new();
        self.edges.iter().map(|e| e.2).filter(|l| seen.insert(*l)).collect()
    }

    /// For each edge, whether `steps` (a `Checker`'s) holds it
    pub fn covered(&self, steps: &HashSet<(Abs, Abs, u32)>) -> Vec<bool> {
        self.edges.iter().map(|&(i, j, l)| steps.contains(&(self.states[i], self.states[j], l))).collect()
    }

    /// A shortest path of edges from an initial state to state `to` that uses none of `blocked`
    pub fn path_to(&self, to: usize, blocked: &HashSet<usize>) -> Option<Vec<usize>> {
        let mut via: Vec<Option<usize>> = vec![None; self.states.len()];
        let mut seen = vec![false; self.states.len()];
        let mut queue = VecDeque::new();
        for &i in &self.initial {
            seen[i] = true;
            queue.push_back(i);
        }
        while let Some(i) = queue.pop_front() {
            if i == to {
                let mut path = vec![];
                let mut at = to;
                while let Some(e) = via[at] {
                    path.push(e);
                    at = self.edges[e].0;
                }
                path.reverse();
                return Some(path);
            }
            for &e in &self.out[i] {
                let j = self.edges[e].1;
                if !seen[j] && !blocked.contains(&e) {
                    seen[j] = true;
                    via[j] = Some(e);
                    queue.push_back(j);
                }
            }
        }
        None
    }
}
"##;
