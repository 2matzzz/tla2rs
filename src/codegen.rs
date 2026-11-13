//! Generates a Rust model checker from fully expanded expressions.
//!
//! - A state is a `Copy` struct with one field per variable
//! - Init / Next are compiled in continuation-passing style, threading the remaining conjuncts
//!   through and emitting a nested block for each branch
//! - Constant subexpressions are evaluated at compile time and emitted as literals

use crate::ast::*;
use crate::lexer::R;
use crate::types::*;
use crate::value::*;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write;

/// What computing a constant made that TLC makes each time it evaluates the expression (see
/// `Gen::note_folded`)
#[derive(Default)]
struct Made {
    strs: Vec<u32>,
    /// The positions of TLC's EXCEPT warnings
    warns: Vec<String>,
}

#[derive(Clone, Default)]
pub struct Env {
    /// Bound variables and `@`: name -> (Rust expression, type)
    locals: HashMap<String, (String, Ty)>,
    /// Primed variables that have already been assigned
    primed: HashMap<String, (String, Ty)>,
    init: bool,
    /// The action the successors are labelled with in traces (an index into `labels`)
    label: Option<u32>,
    /// Still splitting the next-state relation into actions as TLC does (see `gen_split`)
    split: bool,
    /// While splitting: the definition the action is named after, and the position of the
    /// innermost part with a POS label
    aname: Option<String>,
    apos: Option<String>,
    /// Bound variables whose index within their type is known.
    /// Used as a function argument, they skip the conversion from atom value to index.
    idx: HashMap<String, (Ty, String)>,
    /// Variable holding the successor state under construction; created from `*s` on the first
    /// assignment
    work: Option<String>,
    /// Inside ENABLED: a successor need not determine every variable (as in TLC)
    partial: bool,
    /// Inside an ENABLED written in an instantiated module: a substituted variable is bound by its
    /// name (see gen_phantom)
    phantom: bool,
    /// Computing whether an action is enabled (ENABLED, or for fairness), which TLC's error
    /// messages name
    enabled: bool,
    /// Bound variables whose value is known at compile time (an unrolled \\A or recursive call)
    vals: HashMap<String, Value>,
    /// Inside the function of a recursive operator that assigns variables (`rec_action_fn`, by
    /// its key): the end of the action returns the state built so far instead of emitting it
    sink: Option<String>,
    /// Computing whether an action is enabled: the label of the block that the first successor
    /// leaves with `true`, since TLC stops at the first successor it finds
    pub en_exit: Option<String>,
}

pub struct Gen<'a> {
    /// The position of the action-level CASE about to be generated (see `gen_action`)
    case_at: Option<String>,
    /// The module's definitions without arguments (TLC keeps the value of those of constant level)
    pub zero_defs: HashSet<String>,
    /// How deep recursive operators are being unrolled in an action
    unroll: u32,
    pub atoms: &'a Atoms,
    pub ce: ConstEval<'a>,
    pub vars: Vec<(String, Ty)>,
    /// The variables in the order TLC prints them in a state (see `sany::var_order`)
    pub print_order: Vec<String>,
    tys: Vec<Ty>,
    ty_ids: HashMap<Ty, usize>,
    convs: BTreeSet<(usize, usize)>,
    /// Whether `subsets_tlc` is used
    need_subsets: bool,
    pub labels: Vec<String>,
    /// The number of actions the next-state relation splits into (see `gen_split`)
    pub actions: usize,
    /// The module whose Java methods TLC evaluates arithmetic with: Integers when the spec loads
    /// it (or Reals), else Naturals (see `gen_int`)
    pub int_module: &'static str,
    /// The operator whose argument `gen_int` generates next: its Java method's name, and whether
    /// it takes one argument and gives an interval
    int_op: Option<(&'static str, bool, bool)>,
    /// The comparison whose argument `gen_int` generates next: its symbol as TLC names it, and
    /// whether this is the first argument
    int_cmp: Option<(&'static str, bool)>,
    /// Strings numbered from here on may be made while exploring: the checker notes when it makes
    /// one (`str_made` in the runtime)
    pub track_from: u32,
    /// Whether the checker notes a string it makes (STR_ORDER)
    pub str_notes: bool,
    tmp: usize,
    /// While Some, the EXCEPT warnings of folded constants go here instead of into the code:
    /// TLC evaluates the set of a `\E` it splits the next-state relation through once, when it
    /// reads the spec (see `split_warns`)
    split_warning: Option<Vec<String>>,
    /// The EXCEPT warnings TLC prints while it splits the next-state relation into actions
    pub split_warns: Vec<String>,
    /// The strings TLC makes then, in the order made
    pub split_strs: Vec<u32>,
    /// Maximum cardinality of a sparse set (SSet)
    pub scap: usize,
    /// Maximum length of a sequence (QCAP); 0 while no bound is known
    pub qcap: usize,
    /// During type inference, collects the types of assigned values
    pub infer: Option<HashMap<String, Ty>>,
    /// During type inference, the first error met computing a value assigned to each variable
    pub infer_errs: HashMap<String, String>,
    /// Rust functions for recursive operators, per (RecDef index, argument types): name and return
    /// type once settled
    rec_done: HashMap<(usize, Vec<Ty>), (String, Ty)>,
    /// Those being generated, with their return type so far (innermost last)
    rec_progress: Vec<((usize, Vec<Ty>), Ty)>,
    rec_names: HashMap<(usize, Vec<Ty>), String>,
    /// Function name -> its code (the latest version)
    rec_code: std::collections::BTreeMap<String, String>,
    /// Functions for recursive operators that assign variables, per key (`rec_action_fn`): the
    /// name, the sets of variables assigned when it returns (numbers of `assigned_sets`), and
    /// whether these are settled
    ract: HashMap<String, (String, BTreeSet<u32>, bool)>,
    /// The sets of variables (indexes into `vars`) a function of `gen_rec_action` may have
    /// assigned when it returns a state, numbered in the order found: the function returns each
    /// state with the number of its set
    assigned_sets: Vec<Vec<usize>>,
    /// The recursive operators made for `\A x \in S : B` in actions (see `forall_rec`), by x and B
    forall_recs: HashMap<String, usize>,
    ract_progress: Vec<String>,
    /// The position of each definition's body (from its POS label), for a recursive operator
    /// unrolled while splitting the next-state relation
    pub def_pos: HashMap<String, String>,
    /// The definitions of each INSTANCE: the prefix of their hidden names (`M#iK#`), the prefix
    /// TLC names them with (`N!` or nothing), and the number of constants and variables
    /// substituted
    pub inst_prefixes: Vec<(String, String, usize)>,
    /// For each name a BIND label binds, while `is_const` walks it: whether its expression is
    /// constant (printing or not), and whether computing it prints (see `bind_const`)
    bconst: std::cell::RefCell<HashMap<String, (bool, bool)>>,
    /// For each name a BIND label binds, whether its expression depends on the state
    bstate: std::cell::RefCell<HashMap<String, bool>>,
}

/// The local holding the value bound to the substituted variable `n` of an instance while
/// computing whether an action is enabled (see `Gen::gen_phantom`)
fn phantom(n: &str) -> String {
    format!("'{n}")
}

fn rid(n: &str) -> String {
    format!("l_{}", n.replace(|c: char| !c.is_ascii_alphanumeric() && c != '_', "_"))
}

impl<'a> Gen<'a> {
    pub fn new(atoms: &'a Atoms, constants: &'a HashMap<String, Value>) -> Self {
        Gen {
            print_order: vec![],
            case_at: None,
            zero_defs: HashSet::new(),
            unroll: 0,
            atoms,
            ce: ConstEval { atoms, constants },
            vars: vec![],
            tys: vec![],
            ty_ids: HashMap::new(),
            convs: BTreeSet::new(),
            need_subsets: false,
            labels: vec!["Init".into(), "Next".into()],
            actions: 0,
            int_module: "Naturals",
            int_op: None,
            int_cmp: None,
            track_from: u32::MAX,
            str_notes: false,
            tmp: 0,
            split_warning: None,
            split_warns: vec![],
            split_strs: vec![],
            scap: 8,
            qcap: 0,
            infer: None,
            infer_errs: HashMap::new(),
            rec_done: HashMap::new(),
            rec_progress: vec![],
            rec_names: HashMap::new(),
            rec_code: std::collections::BTreeMap::new(),
            ract: HashMap::new(),
            assigned_sets: vec![],
            forall_recs: HashMap::new(),
            ract_progress: vec![],
            def_pos: HashMap::new(),
            inst_prefixes: vec![],
            bconst: Default::default(),
            bstate: Default::default(),
        }
    }

    fn fresh(&mut self, p: &str) -> String {
        self.tmp += 1;
        format!("__{p}{}", self.tmp)
    }

    pub fn label_id(&mut self, n: &str) -> u32 {
        if let Some(i) = self.labels.iter().position(|x| x == n) {
            return i as u32;
        }
        self.labels.push(n.into());
        (self.labels.len() - 1) as u32
    }

    /// Registers a type (along with its element, domain and codomain types) so helpers are
    /// emitted for it.
    fn ty_id(&mut self, t: &Ty) -> R<usize> {
        if let Some(&i) = self.ty_ids.get(t) {
            return Ok(i);
        }
        match t {
            Ty::Set(e) => {
                if matches!(e.as_ref(), Ty::IntAtom(..)) && self.has_str(e) {
                    return Err("a set that may hold both strings and integers is not supported (TLC stops with an error when it builds one with both)".into());
                }
                self.ty_id(e)?;
            }
            // Over a large or unbounded type: the set of its (key, value) pairs
            Ty::PFun(_, c) | Ty::Bag(c) if is_sparse_fun(t) => {
                if matches!(t, Ty::PFun(..)) && c.size() == Some(0) {
                    return Err("a function over part of a large type whose values have no type yet".into());
                }
                self.ty_id(&fun_pairs(t))?;
            }
            Ty::PFun(d, c) => {
                self.ty_id(d)?;
                self.ty_id(c)?;
                self.ty_id(&pfun_repr(d, c))?;
            }
            Ty::Bag(e) => {
                self.ty_id(e)?;
                self.ty_id(&bag_fun(e))?;
            }
            Ty::Seq(e) => {
                if self.qcap == 0 {
                    return Err("sequences whose length changes need a maximum length: add `Len(x) <= N` to TypeOK or a CONSTRAINT, or pass -seqcap N".into());
                }
                self.ty_id(e)?;
            }
            Ty::Opt(e) => {
                self.ty_id(e)?;
            }
            Ty::Fun(d, c) => {
                d.size().ok_or("function domain must be a finite scalar type")?;
                self.ty_id(d)?;
                self.ty_id(c)?;
            }
            Ty::Rec(fs) => {
                for (_, f) in fs {
                    self.ty_id(f)?;
                }
            }
            Ty::IntAtom(..) => {}
            _ => {}
        }
        let i = self.tys.len();
        self.tys.push(t.clone());
        self.ty_ids.insert(t.clone(), i);
        Ok(i)
    }

    /// `x \in set` (a constant set) when x may be a string and the set holds integers or the other
    /// way around: compared element by element as TLC does, which stops on a string against an
    /// integer. None when no such comparison can happen.
    fn member_mixed(&mut self, x: &str, xt: &Ty, set: &BTreeSet<Value>) -> R<Option<String>> {
        let mut j = xt.clone();
        let mut mixed = false;
        for e in set {
            let Ok(et) = ty_of_value(e) else { return Ok(None) };
            if !matches!(et, Ty::Int(..) | Ty::Enum(_) | Ty::IntAtom(..)) {
                return Ok(None);
            }
            mixed |= self.str_meets_int(xt, &et);
            j = join(&j, &et)?;
        }
        if !mixed {
            return Ok(None);
        }
        let xc = self.coerce(x.to_string(), xt, &j)?;
        let parts: Vec<String> = set.iter().map(|e| Ok(format!("mixed_eq(__x, {})", self.lit(e, &j)?))).collect::<R<_>>()?;
        Ok(Some(format!("{{ let __x = {xc}; {} }}", if parts.is_empty() { "false".into() } else { parts.join(" || ") })))
    }

    /// Whether a value of type `t` may be a string
    fn has_str(&self, t: &Ty) -> bool {
        match t {
            Ty::Enum(d) | Ty::IntAtom(_, _, d) => d.iter().any(|&a| !self.atoms.is_model(a)),
            _ => false,
        }
    }

    /// Whether t has a set that may hold both strings and integers, which tla2rs cannot represent
    fn mixed_set(&self, t: &Ty) -> bool {
        match t {
            Ty::Set(e) if matches!(e.as_ref(), Ty::IntAtom(..)) && self.has_str(e) => true,
            Ty::Set(e) | Ty::Seq(e) | Ty::Opt(e) | Ty::Bag(e) | Ty::Fun(_, e) | Ty::PFun(_, e) => self.mixed_set(e),
            Ty::Rec(fs) => fs.iter().any(|(_, t)| self.mixed_set(t)),
            _ => false,
        }
    }

    /// `a = b` as TLC evaluates it (`a.equals(b)`) where a and b hold strings and integers in
    /// places where the other holds the other kind (`{x} = {5}` with x a string; measured on TLC
    /// 2.19, `tests/tlc/StrIntSet*`). Sets of different sizes are unequal; otherwise TLC compares
    /// their elements in its order, pair by pair, and stops at the first pair that is unequal. A
    /// model value is unequal to anything but itself, and a string compared with an integer stops
    /// TLC with an error worded by the value on the left. Tuples compare element by element
    fn str_int_eq(&mut self, ac: &str, at: &Ty, bc: &str, bt: &Ty) -> R<String> {
        let leaf = |t: &Ty| matches!(t, Ty::Enum(_) | Ty::IntAtom(..) | Ty::Int(..));
        match (at, bt) {
            (Ty::Set(ea), Ty::Set(eb)) => {
                let (x, y, p, q) = (self.fresh("x"), self.fresh("y"), self.fresh("p"), self.fresh("q"));
                let (nx, ny) = (self.s_card(&x, at), self.s_card(&y, bt));
                let (ix, iy) = (self.s_iter(&x, at)?, self.s_iter(&y, bt)?);
                let inner = self.str_int_eq(&p, ea, &q, eb)?;
                Ok(format!("{{ let ({x}, {y}) = ({ac}, {bc}); {nx} == {ny} && {{ let __all = {ix}.zip({iy}).all(|({p}, {q})| {inner}); __all }} }}"))
            }
            (Ty::Rec(fa), Ty::Rec(fb)) if tuple_elems(at).is_some() && tuple_elems(bt).is_some() => {
                if fa.len() != fb.len() {
                    return Ok(format!("{{ let _ = {ac}; let _ = {bc}; false }}"));
                }
                let (x, y) = (self.fresh("x"), self.fresh("y"));
                let mut parts = vec![];
                for (i, ((_, ta), (_, tb))) in fa.iter().zip(fb).enumerate() {
                    let f = rec_field(fa.len(), i);
                    parts.push(self.str_int_eq(&format!("{x}{f}"), ta, &format!("{y}{f}"), tb)?);
                }
                Ok(format!("{{ let ({x}, {y}) = ({ac}, {bc}); {} }}", parts.join(" && ")))
            }
            (a, b) if leaf(a) && leaf(b) => {
                let as_i64 = |c: &str, t: &Ty| match t {
                    Ty::Enum(_) => format!("(i64::MIN + ({c}) as i64)"),
                    _ => format!("(({c}) as i64)"),
                };
                Ok(format!("str_int_eq({}, {})", as_i64(ac, a), as_i64(bc, b)))
            }
            _ => Err("comparing values that hold strings where the other holds integers is supported only for sets and tuples".into()),
        }
    }

    /// Whether comparing values of types `a` and `b` may compare a string with an integer, which TLC
    /// stops on (a model value compares unequal with anything)
    fn str_meets_int(&self, a: &Ty, b: &Ty) -> bool {
        let int = |t: &Ty| matches!(t, Ty::Int(..) | Ty::IntAtom(..));
        (self.has_str(a) && int(b)) || (int(a) && self.has_str(b))
    }

    /// How TLC compares values of types `a` and `b` when a tuple meets something else. A tuple of
    /// another length or a model value is unequal to it; an integer, boolean, string, record, set,
    /// or function makes TLC stop with an error. A function over 1..n is not compiled (Err).
    fn tuple_cmp(&self, a: &Ty, b: &Ty) -> R<Cmp> {
        // Several parts: an error anywhere wins, then a part that is never equal
        let all = |parts: Vec<Cmp>| {
            parts.iter().find(|c| matches!(c, Cmp::Fails(_))).cloned().unwrap_or(if parts.contains(&Cmp::Unequal) {
                Cmp::Unequal
            } else {
                Cmp::Normal
            })
        };
        // A value that may be a model value: unequal when it is one, compared as its other kind
        // otherwise (types::VAL_FIELD); join refuses the kinds that cannot be compared. TLC
        // compares a string with a tuple by its characters (see tuple_str_eq), which is not done
        // for a string held beside a value of another kind
        if crate::types::val_ty(a).is_some() || crate::types::val_ty(b).is_some() {
            let tupleish = |t: &Ty| tuple_elems(t).is_some() || matches!(t, Ty::Seq(_)) || crate::types::val_ty(t).is_some_and(|v| tuple_elems(v).is_some() || matches!(v, Ty::Seq(_)));
            let strs = |t: &Ty| match t {
                Ty::Rec(fs) => fs.iter().any(|(n, t)| n == crate::types::ATOM_FIELD && matches!(t, Ty::Opt(e) if self.has_str(e))),
                t => self.has_str(t),
            };
            if (strs(a) && tupleish(b)) || (tupleish(a) && strs(b)) {
                return Err("comparing a value that may be a string with a sequence held beside model values is not supported".into());
            }
            return Ok(Cmp::Normal);
        }
        // An optional field (of a record among records of other fields) compares as its value
        if let (Ty::Opt(x), y) | (y, Ty::Opt(x)) = (a, b) {
            return Ok(match self.tuple_cmp(x, y)? {
                Cmp::Fails(m) => Cmp::Fails(m),
                _ => Cmp::Normal,
            });
        }
        if let (Ty::Seq(_), t) | (t, Ty::Seq(_)) = (a, b) {
            if seq_elems(t).is_none() && !matches!(t, Ty::Enum(v) if v.is_empty()) {
                return self.tuple_vs(t).map(|c| if c == Cmp::Normal { Cmp::Normal } else { c });
            }
        }
        Ok(match (tuple_elems(a), tuple_elems(b)) {
            (Some(x), Some(y)) if x.len() != y.len() => Cmp::Unequal,
            (Some(x), Some(y)) => all(x.iter().zip(&y).map(|(s, t)| self.tuple_cmp(s, t)).collect::<R<_>>()?),
            // The empty tuple is the function over the empty set, so it compares with a function
            // over part of a type
            (Some(x), None) if x.is_empty() && matches!(b, Ty::PFun(..)) => Cmp::Normal,
            (None, Some(y)) if y.is_empty() && matches!(a, Ty::PFun(..)) => Cmp::Normal,
            (Some(_), None) => self.tuple_vs(b)?,
            (None, Some(_)) => self.tuple_vs(a)?,
            (None, None) => match (a, b) {
                (Ty::Rec(x), Ty::Rec(y)) => all(
                    x.iter()
                        .filter_map(|(n, s)| y.iter().find(|(m, _)| m == n).map(|(_, t)| self.tuple_cmp(s, t)))
                        .collect::<R<_>>()?,
                ),
                // Only an error carries over: empty sets can still be equal
                (Ty::Set(x), Ty::Set(y)) | (Ty::Fun(_, x), Ty::Fun(_, y)) => {
                    match self.tuple_cmp(x, y)? {
                        Cmp::Fails(m) => Cmp::Fails(m),
                        _ => Cmp::Normal,
                    }
                }
                _ => Cmp::Normal,
            },
        })
    }

    /// `tuple_cmp` of a tuple against a value of the non-tuple type `t`
    fn tuple_vs(&self, t: &Ty) -> R<Cmp> {
        Ok(match t {
            Ty::Enum(v) if v.is_empty() => Cmp::Normal,
            Ty::Enum(v) if v.iter().all(|&a| self.atoms.is_model(a)) => Cmp::Unequal,
            // A sequence, or a function over 1..n, compares with a tuple as TLA+ identifies them; a
            // function over other integers is unequal to it
            Ty::Seq(_) => Cmp::Normal,
            Ty::Fun(d, _) if seq_domain(d).is_some() => Cmp::Normal,
            Ty::Fun(d, _) if matches!(d.as_ref(), Ty::Int(..)) => Cmp::Unequal,
            _ => Cmp::Fails(format!("Attempted to compare a tuple with a value of type {t:?}")),
        })
    }

    /// `a = b` when one side is a tuple (or sequence) and the other may be a string. TLC asks the
    /// value on the left: a tuple compares itself with the characters of a string, element by
    /// element; a string asked about a tuple stops with an error. A model value is unequal to both,
    /// and an integer cannot be compared with a tuple. None when neither side is such a pair.
    fn tuple_str_eq(&mut self, ac: &str, at: &Ty, bc: &str, bt: &Ty, env: &Env) -> R<Option<String>> {
        let tupleish = |t: &Ty| tuple_elems(t).is_some() || matches!(t, Ty::Seq(_));
        let atoms_of = |t: &Ty| match t {
            Ty::Enum(d) | Ty::IntAtom(_, _, d) => d.clone(),
            _ => vec![],
        };
        if tupleish(at) && self.has_str(bt) {
            let (t, s) = (self.fresh("t"), self.fresh("s"));
            let mut chain = String::new();
            for a in atoms_of(bt) {
                if self.atoms.is_model(a) {
                    continue;
                }
                let chars: Vec<String> = self.atoms.name(a).chars().map(|c| c.to_string()).collect();
                let elems: Vec<(String, Ty)> = match at {
                    Ty::Seq(e) => (0..chars.len()).map(|i| (format!("{t}.at({})", i + 1), e.as_ref().clone())).collect(),
                    _ => {
                        let es = tuple_elems(at).unwrap();
                        let n = es.len();
                        es.into_iter().enumerate().map(|(i, e)| (format!("{t}{}", rec_field(n, i)), e.clone())).collect()
                    }
                };
                let mut parts = vec![];
                match at {
                    Ty::Seq(_) => parts.push(format!("{t}.len as usize == {}", chars.len())),
                    _ if elems.len() != chars.len() => parts.push("false".into()),
                    _ => {}
                }
                if parts.iter().all(|p| p != "false") {
                    for ((code, et), ch) in elems.iter().zip(&chars) {
                        self.atoms.intern(false, ch);
                        let mut env2 = env.clone();
                        env2.bind("#elem", code.clone(), et.clone());
                        let eq = Expr::Bin(BOp::Eq, Expr::Ident("#elem".into(), NOPOS).b(), Expr::Str(ch.clone()).b());
                        parts.push(self.gen_as(&eq, &env2, &Ty::Bool)?);
                    }
                }
                let lit = self.lit(&Value::Atom(a), bt)?;
                write!(chain, "if {s} == {lit} {{ {} }} else ", parts.join(" && ")).unwrap();
            }
            let other = if matches!(bt, Ty::IntAtom(..)) {
                let tid = self.ty_id(bt)?;
                let msg = "Attempted to check equality of a tuple with {}";
                format!("if {s} >= i64::MIN + 65536 {{ let __b: bool = eval_error(format!({msg:?}, fmt_{tid}(&{s}))); __b }} else {{ false }}")
            } else {
                "false".into()
            };
            return Ok(Some(format!("{{ let {t} = {ac}; let {s} = {bc}; {chain}{{ {other} }} }}")));
        }
        if self.has_str(at) && tupleish(bt) {
            let s = self.fresh("s");
            let models: Vec<String> =
                atoms_of(at).into_iter().filter(|&a| self.atoms.is_model(a)).map(|a| self.lit(&Value::Atom(a), at)).collect::<R<_>>()?;
            let (tid, bid) = (self.ty_id(at)?, self.ty_id(bt)?);
            let msg = "Attempted to check equality of string {} with non-string:\n{}";
            let fail = format!("{{ let __b: bool = eval_error(format!({msg:?}, fmt_{tid}(&{s}), fmt_{bid}(&__q))); __b }}");
            let unequal = if models.is_empty() { "false".to_string() } else { models.iter().map(|m| format!("{s} == {m}")).collect::<Vec<_>>().join(" || ") };
            return Ok(Some(format!("{{ let {s} = {ac}; let __q = {bc}; if {unequal} {{ false }} else {fail} }}")));
        }
        Ok(None)
    }

    pub fn ty_id_pub(&mut self, t: &Ty) -> R<usize> {
        self.ty_id(t)
    }

    /// For a function domain `1..n` or `DOMAIN q` (q a sequence), the code of its length
    fn seq_domain_len(&mut self, s: &Expr, env: &Env) -> Option<R<String>> {
        match s.strip() {
            Expr::Bin(BOp::Range, lo, hi) if matches!(self.try_const(lo, env), Some(Value::Int(1))) => {
                Some(self.gen_int(hi, env).map(|(c, _)| format!("({c}).max(0)")))
            }
            Expr::Un(UOp::Domain, q) => match self.gen(q, env, None) {
                Ok((c, Ty::Seq(_))) => Some(Ok(format!("(({c}).len as i64)"))),
                _ => None,
            },
            _ => None,
        }
    }

    /// `code`, which gives a string made by an operation that may be one of `ids`, noting the
    /// string it makes when that may be one numbered for the strings made while exploring
    fn note_made(&mut self, code: String, ids: &[u32]) -> String {
        if !ids.iter().any(|&a| a >= self.track_from) {
            return code;
        }
        self.str_notes = true;
        format!("{{ let __s: u16 = {code}; str_made(__s); __s }}")
    }

    /// The code `c` of a constant, after noting the strings made while computing it (in `made`)
    /// that may be made while exploring, and TLC's warnings about an EXCEPT: TLC makes and warns
    /// when it evaluates the expression (a definition without arguments, which TLC evaluates
    /// when it starts, makes and warns then only)
    /// The statements that note what computing a constant made (see `note_folded`), for a
    /// constant the compiler evaluates without generating code for it (a condition, the set of
    /// an unrolled `\A`, the arguments of an unrolled recursive operator)
    fn fold_notes(&mut self, made: &Made) -> String {
        let mut out = String::new();
        for at in &made.warns {
            write!(out, "except_warning({at:?}); ").unwrap();
        }
        for a in made.strs.iter().filter(|&&a| a >= self.track_from) {
            self.str_notes = true;
            write!(out, "str_made({a}u16); ").unwrap();
        }
        out
    }

    fn note_folded(&mut self, c: String, made: &Made) -> String {
        if self.split_warning.is_some() {
            for &a in &made.strs {
                if !self.split_strs.contains(&a) {
                    self.split_strs.push(a);
                }
            }
        }
        let notes: Vec<String> = match self.split_warning {
            Some(_) => vec![],
            None => made.strs.iter().filter(|&&a| a >= self.track_from).map(|a| format!("str_made({a}u16); ")).collect(),
        };
        if !notes.is_empty() {
            self.str_notes = true;
        }
        let mut warns: Vec<String> = made.warns.iter().map(|at| format!("except_warning({at:?}); ")).collect();
        if let Some(w) = &mut self.split_warning {
            w.extend(made.warns.iter().cloned());
            warns.clear();
        }
        if notes.is_empty() && warns.is_empty() {
            return c;
        }
        format!("{{ {}{}{c} }}", warns.concat(), notes.concat())
    }

    /// `op` (Len, Head, Tail, Append, \o) on strings from the state: a match over every string the
    /// operands can be, with each result string interned now. A model value is an error, as in
    /// TLC (it is not a sequence).
    fn string_table(&mut self, op: &str, a: &str, operands: &[(Vec<u32>, Option<String>)]) -> R<(String, Ty)> {
        let atoms = self.atoms;
        let text = |x: u32| -> Option<String> { (!atoms.is_model(x)).then(|| atoms.name(x)) };
        let cases: Vec<Vec<u32>> = match operands {
            [(da, _)] => da.iter().map(|&x| vec![x]).collect(),
            [(da, _), (db, _)] => da.iter().flat_map(|&x| db.iter().map(move |&y| vec![x, y])).collect(),
            _ => unreachable!(),
        };
        // Every result is a string interned now (16-bit ids)
        let room = (1usize << 16).saturating_sub(self.atoms.len());
        if cases.len() > room {
            return Err(format!("`{op}` over {} combinations of strings from the state: more than the {room} strings that can still be added (strings are 16-bit ids)", cases.len()));
        }
        let b = operands.get(1).and_then(|(_, c)| c.clone());
        let mut arms = String::new();
        let mut res_ids = vec![];
        let mut lens = vec![];
        let msg = format!("`{op}` of a value that is not a string");
        for c in &cases {
            let pat = match c.len() {
                1 => format!("{}", c[0]),
                _ => format!("({}, {})", c[0], c[1]),
            };
            let (Some(x), y) = (text(c[0]), c.get(1).map(|&y| text(y))) else {
                write!(arms, "{pat} => eval_error({msg:?}.to_string()), ").unwrap();
                continue;
            };
            if matches!(y, Some(None)) {
                write!(arms, "{pat} => eval_error({msg:?}.to_string()), ").unwrap();
                continue;
            }
            let y = y.flatten();
            let chars: Vec<char> = x.chars().collect();
            let out: Result<String, &str> = match op {
                "Head" => chars.first().map(|c| c.to_string()).ok_or("Attempted to apply Head to the empty sequence."),
                "Tail" => if chars.is_empty() { Err("Attempted to apply Tail to the empty sequence.") } else { Ok(chars[1..].iter().collect()) },
                "Append" | "\\o" => Ok(x.clone() + &y.unwrap()),
                _ => Ok(String::new()),
            };
            let body = match (op, out) {
                ("Len", _) => {
                    lens.push(chars.len() as i64);
                    format!("{}i64", chars.len())
                }
                (_, Ok(s)) => {
                    let id = self.atoms.intern(false, &s);
                    res_ids.push(id);
                    format!("{id}u16")
                }
                (_, Err(m)) => format!("arith_error({m:?}.to_string())"),
            };
            write!(arms, "{pat} => {body}, ").unwrap();
        }
        let scrut = match &b {
            Some(bc) => format!("({a}, {bc})"),
            None => a.to_string(),
        };
        // Any other value lies outside the operand's type, which packing reports too
        let code = format!("(match {scrut} {{ {arms}_ => type_error(\"string\", \"\") }})");
        Ok(if op == "Len" {
            (code, Ty::Int(lens.iter().copied().min().unwrap_or(0), lens.iter().copied().max().unwrap_or(0)))
        } else {
            res_ids.sort();
            res_ids.dedup();
            (self.note_made(code, &res_ids), Ty::Enum(res_ids))
        })
    }

    /// SubSeq(q, m, n) on strings from the state: for each string q can be, a table of its
    /// substrings by (m, n), interned now
    fn substring_table(&mut self, qc: &str, d: &[u32], mc: &str, nc: &str) -> R<(String, Ty)> {
        let empty = self.atoms.intern(false, "");
        let mut res = vec![empty];
        let mut arms = String::new();
        let mut total = 0;
        for &a in d {
            if self.atoms.is_model(a) {
                write!(arms, "{a} => eval_error(\"`SubSeq` of a value that is not a string\".to_string()), ").unwrap();
                continue;
            }
            let chars: Vec<char> = self.atoms.name(a).chars().collect();
            let l = chars.len();
            total += l * l;
            if total > 1 << 22 {
                return Err(format!("`SubSeq` on strings from the state: a table of {total} substrings is too large (at most {})", 1 << 22));
            }
            let mut table = vec![];
            for i in 0..l {
                for j in 0..l {
                    let id = if i <= j { self.atoms.intern(false, &chars[i..=j].iter().collect::<String>()) } else { empty };
                    res.push(id);
                    table.push(id.to_string());
                }
            }
            write!(
                arms,
                "{a} => {{ const T: [u16; {}] = [{}]; if __m > __n {{ {empty}u16 }} \
                 else if __m < 1 || __m > {l} {{ arith_error(\"The second argument of SubSeq must be in the domain of its first argument.\".to_string()) }} \
                 else if __n > {l} {{ arith_error(\"The third argument of SubSeq must be in the domain of its first argument.\".to_string()) }} \
                 else {{ T[((__m - 1) * {l} + __n - 1) as usize] }} }}, ",
                l * l,
                table.join(", ")
            )
            .unwrap();
        }
        res.sort();
        res.dedup();
        let code = format!("{{ let __m: i64 = {mc}; let __n: i64 = {nc}; match {qc} {{ {arms}_ => type_error(\"string\", \"\") }} }}");
        Ok((self.note_made(code, &res), Ty::Enum(res)))
    }

    /// Whether the value `x` of type `xt` is in [d -> r]: a function (sequences, bags, records
    /// and partial functions included) whose domain is d and whose values are in r. TLC answers
    /// FALSE for a model value and stops with an error for any other value that is not a function.
    fn fun_set_member(&mut self, x: &str, xt: &Ty, d: &Expr, r: &Expr, s: &Expr, env: &Env) -> R<String> {
        let not_fun = |g: &mut Self| -> R<String> {
            let tid = g.ty_id(xt)?;
            // TLC prints the set of functions as its value
            let set = match g.try_const(s, env) {
                Some(v) => crate::compile::show_value(g.atoms, &v),
                None => short(s),
            };
            let set = set.replace('{', "{{").replace('}', "}}");
            let msg = format!("Attempted to check if \n{{}}\nwhich is not a TLC function value, is in the set of functions:\n{set}");
            Ok(format!("{{ let __b: bool = eval_error(format!({msg:?}, fmt_{tid}(&{x}))); __b }}"))
        };
        let in_r = |g: &mut Self, v: &str, t: &Ty| -> R<String> {
            let e = g.fresh("e");
            let inner = g.gen_member(&e, t, r, env)?;
            Ok(format!("{{ let {e} = {v}; {inner} }}"))
        };
        match xt {
            Ty::Enum(ids) => {
                let strs: Vec<String> = ids.iter().filter(|&&a| !self.atoms.is_model(a)).map(|a| a.to_string()).collect();
                if strs.is_empty() {
                    return Ok("false".into());
                }
                let err = not_fun(self)?;
                return Ok(format!("(if matches!({x}, {}) {{ {err} }} else {{ false }})", strs.join(" | ")));
            }
            Ty::Bool | Ty::Int(..) | Ty::IntAtom(..) | Ty::Set(_) => return not_fun(self),
            // A sequence is a function over 1..Len
            Ty::Seq(et) => {
                let Some(dv) = self.try_const(d, env) else {
                    let mut env2 = env.clone();
                    env2.locals.insert("#seq".into(), (x.to_string(), xt.clone()));
                    let (dc, dt) = self.gen(d, env, None)?;
                    let range = Expr::Bin(BOp::Range, Expr::Num(1).b(), Expr::Call("Len".into(), vec![Expr::Ident("#seq".into(), NOPOS)]).b());
                    let (rc, rt) = self.gen(&range, &env2, Some(&dt))?;
                    let t = join(&dt, &rt)?;
                    let same = format!("({} == {})", self.coerce(dc, &dt, &t)?, self.coerce(rc, &rt, &t)?);
                    let all = in_r(self, "__v", et)?;
                    return Ok(format!("({same} && {x}.iter().all(|__v| {all}))"));
                };
                let dom = dv.as_set()?;
                let n = dom.len();
                if !(1..=n as i64).all(|i| dom.contains(&Value::Int(i))) {
                    return Ok("false".into());
                }
                let all = in_r(self, "__v", et)?;
                return Ok(format!("(({x}).len as usize == {n} && {x}.iter().all(|__v| {all}))"));
            }
            _ => {}
        }
        let Some(dv) = self.try_const(d, env) else {
            // D from the state: compare it with the domain of x, then test the values
            let (dom_c, dom_t, vals) = match xt {
                Ty::PFun(dt, _) | Ty::Bag(dt) if is_sparse_fun(xt) => {
                    let st = Ty::Set(dt.clone());
                    let empty = self.s_empty(&st)?;
                    let add = self.s_add("__s", "__k", &st)?;
                    let v = in_r(self, "__v", &fun_kv(xt).1)?;
                    (format!("{{ let mut __s = {empty}; for (__k, _) in ({x}).iter() {{ {add} }} __s }}"), st, format!("({x}).iter().all(|(_, __v)| {v})"))
                }
                Ty::Fun(dt, ct) => {
                    let st = Ty::Set(dt.clone());
                    let all = Value::Set(dt.enumerate().into_iter().collect());
                    let v = in_r(self, "__v", ct)?;
                    (self.lit(&all, &st)?, st, format!("{x}.iter().all(|&__v| {v})"))
                }
                Ty::PFun(dt, _) | Ty::Bag(dt) => {
                    let st = Ty::Set(dt.clone());
                    let did = self.ty_id(dt)?;
                    let empty = self.s_empty(&st)?;
                    let add = self.s_add("__s", &format!("dec_{did}(__i as u64)"), &st)?;
                    let (present, val, vt) = match xt {
                        Ty::PFun(_, ct) => ("__p.0", "__p.1", ct.as_ref().clone()),
                        _ => ("(__p > 0)", "__p", Ty::Int(1, crate::types::BIG)),
                    };
                    let v = in_r(self, val, &vt)?;
                    (
                        format!("{{ let mut __s = {empty}; for (__i, &__p) in {x}.iter().enumerate() {{ if {present} {{ {add} }} }} __s }}"),
                        st,
                        format!("{x}.iter().all(|&__p| !{present} || {v})"),
                    )
                }
                Ty::Rec(fs) => {
                    let ids: Vec<u32> = fs.iter().map(|(k, _)| self.atoms.intern(false, k)).collect();
                    let mut sorted = ids.clone();
                    sorted.sort();
                    let st = Ty::Set(Ty::Enum(sorted).into());
                    let empty = self.s_empty(&st)?;
                    let mut build = format!("let mut __s = {empty}; ");
                    let mut conj = vec!["true".to_string()];
                    for (i, (_, ft)) in fs.iter().enumerate() {
                        let fp = format!("{x}{}", rec_field(fs.len(), i));
                        let add = self.s_add("__s", &format!("{}u16", ids[i]), &st)?;
                        match ft {
                            Ty::Opt(inner) => {
                                write!(build, "if {fp}.0 {{ {add} }} ").unwrap();
                                let m = in_r(self, &format!("{fp}.1"), inner)?;
                                conj.push(format!("(!{fp}.0 || {m})"));
                            }
                            ft => {
                                build.push_str(&add);
                                conj.push(in_r(self, &fp, ft)?);
                            }
                        }
                    }
                    (format!("{{ {build} __s }}"), st, format!("({})", conj.join(" && ")))
                }
                _ => return Err(format!("membership of {xt:?} in [D -> R] is not supported: {}", short(s))),
            };
            let (dc, dt) = self.gen(d, env, Some(&dom_t))?;
            let t = join(&dt, &dom_t)?;
            let same = format!("({} == {})", self.coerce(dc, &dt, &t)?, self.coerce(dom_c, &dom_t, &t)?);
            return Ok(format!("({same} && {vals})"));
        };
        let dom = dv.as_set()?.clone();
        Ok(match xt {
            Ty::Fun(dt, ct) => {
                if dt.enumerate().into_iter().collect::<BTreeSet<_>>() != dom {
                    return Ok("false".into());
                }
                let all = in_r(self, "__v", ct)?;
                format!("{x}.iter().all(|&__v| {all})")
            }
            // A sparse one: as many keys as D has elements, each in D
            Ty::PFun(dt, _) | Ty::Bag(dt) if is_sparse_fun(xt) => {
                if dom.len() > self.scap || dom.iter().any(|k| !dt.conforms(k)) {
                    return Ok("false".into());
                }
                let dl = self.lit(&Value::Set(dom.clone()), &Ty::Set(dt.clone()))?;
                let all = in_r(self, "__v", &fun_kv(xt).1)?;
                format!("{{ let __d = {dl}; ({x}).len as usize == {} && ({x}).iter().all(|(__k, __v)| __d.contains(&__k) && {all}) }}", dom.len())
            }
            // Present keys must be exactly the domain
            Ty::PFun(dt, _) | Ty::Bag(dt) => {
                let keys = dt.enumerate();
                if dom.iter().any(|k| !keys.contains(k)) {
                    return Ok("false".into());
                }
                let mask: Vec<String> = keys.iter().map(|k| dom.contains(k).to_string()).collect();
                let (present, val, vt) = match xt {
                    Ty::PFun(_, ct) => ("__p.0", "__p.1", ct.as_ref().clone()),
                    _ => ("(__p > 0)", "__p", Ty::Int(1, crate::types::BIG)),
                };
                let all = in_r(self, val, &vt)?;
                format!(
                    "{{ const D: [bool; {}] = [{}]; {x}.iter().enumerate().all(|(__i, &__p)| {present} == D[__i] && (!D[__i] || {all})) }}",
                    keys.len(),
                    mask.join(", ")
                )
            }
            // A record is a function over its field names
            Ty::Rec(fs) => {
                let names: BTreeSet<Value> = fs.iter().map(|(k, _)| Value::Atom(self.atoms.intern(false, k))).collect();
                if !dom.is_subset(&names) {
                    return Ok("false".into());
                }
                let mut conj = vec!["true".to_string()];
                for (i, (k, ft)) in fs.iter().enumerate() {
                    let fp = format!("{x}{}", rec_field(fs.len(), i));
                    let want = dom.contains(&Value::Atom(self.atoms.intern(false, k)));
                    match ft {
                        Ty::Opt(inner) => {
                            let m = in_r(self, &format!("{fp}.1"), inner)?;
                            conj.push(if want { format!("({fp}.0 && {m})") } else { format!("!{fp}.0") });
                        }
                        ft if want => conj.push(in_r(self, &fp, ft)?),
                        _ => return Ok("false".into()),
                    }
                }
                format!("({})", conj.join(" && "))
            }
            _ => return Err(format!("membership of {xt:?} in [D -> R] is not supported: {}", short(s))),
        })
    }

    /// Whether `b` is a bag held in the state (a constant bag is a plain function value)
    fn is_bag(&mut self, b: &Expr, env: &Env) -> bool {
        matches!(b.strip(), Expr::Ident(n, _) if n == "EmptyBag") || matches!(self.gen(b, env, None), Ok((_, Ty::Bag(_))))
            || matches!(b.strip(), Expr::Call(f, _) if f == "SetToBag")
    }

    /// The code of the bag `b` and its element type; with `elem`, converted to bags of that type
    fn bag_of(&mut self, b: &Expr, env: &Env, elem: Option<&Ty>) -> R<(String, Ty)> {
        if let Some(v) = self.try_const(b, env) {
            let m = crate::value::as_fun(&v).ok_or(format!("{v:?} is not a bag"))?;
            let e = match elem {
                Some(e) => e.clone(),
                None => match ty_of_value(&Value::Set(m.keys().cloned().collect()))? {
                    Ty::Set(e) => *e,
                    _ => unreachable!(),
                },
            };
            let bt = Ty::Bag(e.clone().into());
            return Ok((self.lit(&v, &bt)?, e));
        }
        let want = elem.map(|e| Ty::Bag(e.clone().into()));
        let (c, t) = self.gen(b, env, want.as_ref())?;
        // <<>> (the type of a variable that has only been EmptyBag so far) is the empty bag, and a
        // tuple of counts is a bag over 1..n
        if matches!(&t, Ty::Rec(fs) if is_tuple_fields(fs)) {
            let Ty::Rec(fs) = &t else { unreachable!() };
            let e = match elem {
                Some(e) => e.clone(),
                None if fs.is_empty() => Ty::Enum(vec![]),
                None => Ty::Int(1, fs.len() as i64),
            };
            let bt = Ty::Bag(e.clone().into());
            return Ok((self.coerce(c, &t, &bt)?, e));
        }
        let Ty::Bag(e) = &t else { return Err(format!("a bag operator applied to {t:?}, which is not a bag")) };
        match elem {
            Some(w) if w != e.as_ref() => Ok((self.coerce(c, &t, &Ty::Bag(w.clone().into()))?, w.clone())),
            _ => Ok((c, e.as_ref().clone())),
        }
    }

    /// The set of elements of a bag (BagToSet, and DOMAIN of a bag)
    fn bag_domain(&mut self, b: &Expr, env: &Env) -> R<(String, Ty)> {
        let (bc, e) = self.bag_of(b, env, None)?;
        let st = Ty::Set(e.clone().into());
        let empty = self.s_empty(&st)?;
        if is_sparse_fun(&Ty::Bag(e.clone().into())) {
            let add = self.s_add("__s", "__k", &st)?;
            return Ok((format!("{{ let __b = {bc}; let mut __s = {empty}; for (__k, _) in __b.iter() {{ {add} }} __s }}"), st));
        }
        let eid = self.ty_id(&e)?;
        let add = self.s_add("__s", &format!("dec_{eid}(__i as u64)"), &st)?;
        Ok((format!("{{ let __b = {bc}; let mut __s = {empty}; for __i in 0..__b.len() {{ if __b[__i] > 0 {{ {add} }} }} __s }}"), st))
    }

    /// The value of `q` as a sequence (converting a tuple or a function over 1..n), and its type
    fn as_seq(&mut self, q: &Expr, env: &Env, op: &str) -> R<(String, Ty)> {
        let (c, t) = self.gen_val(q, env)?;
        if let Ty::Seq(_) = t {
            return Ok((c, t));
        }
        // A string from the state is the sequence of its one-character strings, as TLC treats it
        // here (the result is a tuple, not a string)
        if let Ty::Enum(d) = &t {
            let mut arms = String::new();
            let mut chars: Vec<u32> = vec![];
            let mut longest = 0;
            for &a in d {
                if self.atoms.is_model(a) {
                    write!(arms, "{a} => eval_error(\"`{op}` of a model value, which is not a sequence\".to_string()), ").unwrap();
                    continue;
                }
                let cs: Vec<u32> = self.atoms.name(a).chars().map(|ch| self.atoms.intern(false, &ch.to_string())).collect();
                longest = longest.max(cs.len());
                chars.extend(&cs);
                let items: Vec<String> = cs.iter().map(|x| format!("{x}u16")).collect();
                write!(arms, "{a} => Sq::from_slice(&[{}]), ", items.join(", ")).unwrap();
            }
            if longest > self.qcap {
                return Err(format!("`{op}` of a string of {longest} characters, longer than the {} elements a sequence holds here; raise it with -seqcap", self.qcap));
            }
            chars.sort();
            chars.dedup();
            let st = Ty::Seq(Ty::Enum(chars).into());
            self.ty_id(&st)?;
            return Ok((format!("{{ let __q: Sq<u16, QCAP> = match {c} {{ {arms}_ => type_error(\"string\", \"\") }}; __q }}"), st));
        }
        let el = seq_elem_join(&[&t]).map_err(|_| self.seq_op_err(op, &t))?;
        let st = Ty::Seq(el.into());
        Ok((self.coerce(c, &t, &st)?, st))
    }

    fn seq_op_err(&self, op: &str, t: &Ty) -> String {
        match t {
            Ty::Enum(_) => format!("`{op}` on strings is only supported in constant expressions"),
            _ => format!("`{op}` of a value of type {t:?}, which is not a sequence"),
        }
    }

    /// The length of a tuple or a function over 1..n
    fn seq_len_of(&self, t: &Ty) -> R<usize> {
        match t {
            Ty::Fun(d, _) if seq_domain(d).is_some() => Ok(seq_domain(d).unwrap()),
            Ty::Rec(fs) if is_tuple_fields(fs) => Ok(fs.len()),
            t => Err(self.seq_op_err("Len", t)),
        }
    }

    /// Identifiers in the body of a recursive operator bound outside it (by the call site), sorted
    fn rec_free(&self, rd: &crate::expand::RecDef) -> Vec<String> {
        fn walk(e: &Expr, bound: &mut Vec<String>, out: &mut Vec<String>) {
            let binders: Vec<String> = match e {
                Expr::Quant(_, bs, _) | Expr::SetMap(_, bs) => bs.iter().map(|(x, _)| x.clone()).collect(),
                Expr::Choose(x, ..) | Expr::SetFilter(x, ..) | Expr::FunCons(x, ..) => vec![x.clone()],
                Expr::Except(_, ups) => ups
                    .iter()
                    .flat_map(|(p, _)| p.iter().filter_map(|s| match s {
                        Path::Field(k) if k.starts_with('@') => Some(k.clone()),
                        _ => None,
                    }))
                    .collect(),
                _ => vec![],
            };
            let n = bound.len();
            bound.extend(binders);
            if let Expr::Ident(x, _) = e {
                if !bound.contains(x) && !out.contains(x) {
                    out.push(x.clone());
                }
            }
            // The arguments of a call site are only a trace (an operator passed is named there);
            // a BIND label binds its names in the expressions after them and in its body
            if let Expr::Label(l, a, b) = e {
                if is_bind(l) {
                    for p in a.chunks(2) {
                        if let [Expr::Ident(x, _), v] = p {
                            walk(v, bound, out);
                            bound.push(x.clone());
                        }
                    }
                }
                walk(b, bound, out);
            } else {
                for c in e.children() {
                    walk(c, bound, out);
                }
            }
            bound.truncate(n);
        }
        let mut bound = rd.params.clone();
        let mut out = vec![];
        walk(&rd.body, &mut bound, &mut out);
        out.retain(|x| {
            !self.is_var(x)
                && !self.ce.constants.contains_key(x)
                && !x.starts_with("@model:")
                && !["BOOLEAN", "Nat", "Int"].contains(&x.as_str())
        });
        out.sort();
        out
    }

    /// The Rust function for the recursive operator `rd` called with arguments of types `tys`
    /// (its parameters, then the free variables of `rec_free`): its name and return type. The
    /// return type is found by generating the body until the type settles, starting from a few
    /// guesses; integer ranges that keep growing are widened to unbounded.
    fn rec_fn(&mut self, i: usize, rd: &crate::expand::RecDef, tys: Vec<Ty>, reads: &[String], primes: &[String], enabled: bool) -> R<(String, Ty)> {
        let key = (i, tys.clone());
        if let Some(r) = self.rec_done.get(&key) {
            return Ok(r.clone());
        }
        if !self.rec_names.contains_key(&key) && self.rec_names.keys().filter(|(j, _)| *j == i).count() >= 8 {
            return Err(format!("recursive operator `{}`: the types of its arguments keep changing between calls", rd.name));
        }
        let n = self.rec_names.len();
        let name = self.rec_names.entry(key.clone()).or_insert(format!("rec_{n}")).clone();
        if let Some((_, t)) = self.rec_progress.iter().rev().find(|(k, _)| *k == key) {
            return Ok((name, t.clone()));
        }
        let free = self.rec_free(rd);
        let names: Vec<String> = rd.params.iter().chain(&free).chain(reads).cloned().collect();
        let mut env = Env::default();
        let mut sig = String::new();
        // ENABLED in the body is evaluated on the current state, passed as `s`
        if enabled {
            sig += "s: &State, ";
        }
        // Arguments are passed by reference: every value type is Copy, and a set held as an array
        // or a state's variables can be kilobytes, copied at each call and each level of recursion
        for (k, (x, t)) in names.iter().zip(&tys).enumerate() {
            env.locals.insert(x.clone(), (format!("(*a{k})"), t.clone()));
            write!(sig, "a{k}: &{}, ", t.repr()).unwrap();
        }
        for (k, (x, t)) in primes.iter().zip(&tys[names.len()..]).enumerate() {
            let a = format!("a{}", names.len() + k);
            env.primed.insert(x.clone(), (format!("(*{a})"), t.clone()));
            write!(sig, "{a}: &{}, ", t.repr()).unwrap();
        }
        let mut last_err = String::new();
        // The type of a call not resolved yet: a body that iterates over the result of its
        // recursive call (a set built from smaller ones) needs a set, and one that applies it (a
        // function built from the one at a smaller argument) a function over the domain the body
        // builds its value on
        let mut seeds = vec![Ty::Enum(vec![]), Ty::Int(0, 0), Ty::Bool, Ty::Set(Ty::Enum(vec![]).into())];
        // The values the body can take, through IF: one without a recursive call (a base case)
        // gives its type
        let mut values = vec![];
        let mut todo = vec![rd.body.clone()];
        while let Some(e) = todo.pop() {
            match e {
                // The names a BIND label binds, written out (see `gen_bind`)
                Expr::Label(n, a, b) if is_bind(&n) => todo.push(unbind(&a, &b)),
                Expr::Label(_, _, b) => todo.push(*b),
                Expr::If(_, a, b) => {
                    todo.push(*b);
                    todo.push(*a);
                }
                e => values.push(e),
            }
        }
        for value in values {
            if let Expr::FunCons(_, dom, _) = &value {
                if let Ok((_, Ty::Set(dt))) = self.gen(dom, &env, None) {
                    for c in [Ty::Bool, Ty::Int(0, 0), Ty::Enum(vec![])] {
                        seeds.push(Ty::Fun(dt.clone(), c.into()));
                    }
                }
            } else if !value.any(&|x| matches!(x, Expr::RecCall(..))) {
                if let Ok((_, t)) = self.gen(&value, &env, None) {
                    if !seeds.contains(&t) {
                        seeds.push(t);
                    }
                }
            }
        }
        for seed in seeds {
            let mut ret = seed;
            for round in 0..30 {
                self.rec_progress.push((key.clone(), ret.clone()));
                let r = self.gen(&rd.body, &env, None);
                self.rec_progress.pop();
                let (code, t) = match r {
                    Ok(x) => x,
                    Err(e) => {
                        last_err = e;
                        break;
                    }
                };
                let Ok(j) = join(&ret, &t) else {
                    last_err = format!("type mismatch: {ret:?} vs {t:?}");
                    break;
                };
                let next = if round >= 3 { crate::compile::widen(&ret, &j) } else { j };
                if next != ret {
                    ret = next;
                    continue;
                }
                let code = self.coerce(code, &t, &ret)?;
                self.ty_id(&ret)?;
                let f = format!(
                    "fn {name}({sig}) -> {} {{ rec_enter({:?}); let __r: {} = {{ {code} }}; rec_leave(); __r }}\n",
                    ret.repr(),
                    rd.name,
                    ret.repr()
                );
                self.rec_code.insert(name.clone(), f);
                if self.rec_progress.is_empty() {
                    self.rec_done.insert(key, (name.clone(), ret.clone()));
                }
                return Ok((name, ret));
            }
        }
        Err(format!("recursive operator `{}`: {last_err}", rd.name))
    }

    /// The variables that the recursive operator `i` reads, and those it reads primed, including
    /// through the recursive operators it calls
    /// (and whether it, or one it calls, has ENABLED)
    fn rec_reads(&self, i: usize) -> R<(Vec<String>, Vec<String>, bool)> {
        let mut todo = vec![i];
        let mut seen = BTreeSet::new();
        let (mut reads, mut primes) = (BTreeSet::new(), BTreeSet::new());
        let mut enabled = false;
        while let Some(j) = todo.pop() {
            if !seen.insert(j) {
                continue;
            }
            let rd = crate::expand::rec_def(j);
            enabled |= rd.body.any(&|e| matches!(e, Expr::Un(UOp::Enabled, _)));
            self.collect_reads(&rd.body, false, &mut reads, &mut primes, &mut todo);
        }
        Ok((reads.into_iter().collect(), primes.into_iter().collect(), enabled))
    }

    fn collect_reads(&self, e: &Expr, primed: bool, reads: &mut BTreeSet<String>, primes: &mut BTreeSet<String>, todo: &mut Vec<usize>) {
        match e {
            Expr::Ident(n, _) if self.is_var(n) => {
                if primed {
                    primes.insert(n.clone());
                } else {
                    reads.insert(n.clone());
                }
            }
            Expr::Prime(x) => self.collect_reads(x, true, reads, primes, todo),
            // ENABLED reads the current state, which is passed whole (see rec_fn)
            Expr::Un(UOp::Enabled, _) => {}
            Expr::Un(UOp::Unchanged, x) => {
                self.collect_reads(x, false, reads, primes, todo);
                self.collect_reads(x, true, reads, primes, todo);
            }
            Expr::RecCall(j, args) => {
                todo.push(*j);
                for a in args {
                    self.collect_reads(a, primed, reads, primes, todo);
                }
            }
            _ => {
                for c in e.children() {
                    self.collect_reads(c, primed, reads, primes, todo);
                }
            }
        }
    }

    /// The functions generated for recursive operators, with the depth guard they share
    pub fn rec_functions(&self) -> String {
        let mut s = format!(
            "thread_local! {{ static REC_DEPTH: std::cell::Cell<u32> = const {{ std::cell::Cell::new(0) }}; \
             static REC_BASE: std::cell::Cell<usize> = const {{ std::cell::Cell::new(0) }}; }}\n\
             // The stack used since the outermost call is measured from the address of a local (a\n\
             // local variable: the address of a literal would be a static)\n\
             fn rec_enter(name: &str) {{ let marker = 0u8; let here = std::hint::black_box(&marker) as *const u8 as usize; REC_DEPTH.with(|d| {{ let n = d.get() + 1; \
             if n == 1 {{ REC_BASE.with(|b| b.set(here)); }} \
             if REC_BASE.with(|b| b.get()).abs_diff(here) > {} {{ d.set(0); eval_error(format!(\"`{{name}}` recursed {{n}} levels deep and ran out of stack (TLC overflows its stack at a smaller depth)\")) }} \
             d.set(n); }}) }}\n\
             fn rec_leave() {{ REC_DEPTH.with(|d| d.set(d.get() - 1)) }}\n",
            crate::value::REC_STACK_BYTES
        );
        for c in self.rec_code.values() {
            s += c;
        }
        s
    }

    /// Rewrites (e)' as e with every variable in it primed
    fn prime_vars(&self, e: &Expr) -> Expr {
        match e {
            Expr::Ident(n, _) if self.is_var(n) => Expr::Prime(e.clone().b()),
            Expr::Prime(_) => e.clone(),
            Expr::Label(n, ..) if n.starts_with(crate::ast::SUBVAR) => Expr::Prime(e.clone().b()),
            _ => map_children(e, &|c| self.prime_vars(c)),
        }
    }

    fn is_var(&self, n: &str) -> bool {
        self.vars.iter().any(|(v, _)| v == n)
    }

    fn var_ty(&self, n: &str) -> Ty {
        self.vars.iter().find(|(v, _)| v == n).unwrap().1.clone()
    }

    fn is_const(&self, e: &Expr, env: &Env) -> bool {
        match e {
            // Print and PrintT print each time they are evaluated, except in a definition of
            // constant level without arguments: TLC computes its value once, when it starts (and
            // prints then, see compile.rs)
            Expr::Call(n, _) if n == "PrintT" || n == "Print" => false,
            Expr::Label(n, a, b) if a.is_empty() && self.zero_defs.contains(n) => self.is_const_quiet(b, env),
            Expr::Label(n, a, b) if is_bind(n) => {
                self.bind_const(a, env);
                self.is_const(b, env)
            }
            Expr::Ident(n, _) if !env.locals.contains_key(n) && self.bconst.borrow().contains_key(n) => {
                let (c, prints) = self.bconst.borrow()[n];
                c && !prints
            }
            // A call site keeps its arguments only as a trace: the body has them substituted. A
            // definition of an instantiated module takes the module's variables as leading
            // arguments even where its body reads none of them
            Expr::Label(_, _, b) => self.is_const(b, env),
            Expr::Prime(_) | Expr::At | Expr::Un(UOp::Unchanged | UOp::Enabled, _) => false,
            Expr::Ident(n, _) => !(self.is_var(n) || env.locals.contains_key(n) && !env.vals.contains_key(n)),
            _ => e.children().into_iter().all(|c| self.is_const(c, env)),
        }
    }

    /// Notes for each name the BIND label with the pairs `pairs` binds whether its expression is
    /// constant, and whether computing it prints (a name read in a definition of constant level
    /// without arguments is part of its value, computed when TLC starts; elsewhere, one that
    /// prints is evaluated where it is used)
    fn bind_const(&self, pairs: &[Expr], env: &Env) {
        for p in pairs.chunks(2) {
            if let [Expr::Ident(n, _), x] = p {
                let c = self.is_const_quiet(x, env);
                let prints = x.any(&|y| match y {
                    Expr::Call(f, _) => f == "Print" || f == "PrintT",
                    Expr::Ident(m, _) => self.bconst.borrow().get(m).is_some_and(|b| b.1),
                    _ => false,
                });
                self.bconst.borrow_mut().insert(n.clone(), (c, prints));
            }
        }
    }

    /// Whether e is constant, printing or not
    fn is_const_quiet(&self, e: &Expr, env: &Env) -> bool {
        match e {
            Expr::Prime(_) | Expr::At | Expr::Un(UOp::Unchanged | UOp::Enabled, _) => false,
            Expr::Label(n, a, b) if is_bind(n) => {
                self.bind_const(a, env);
                self.is_const_quiet(b, env)
            }
            Expr::Ident(n, _) if !env.locals.contains_key(n) && self.bconst.borrow().contains_key(n) => self.bconst.borrow()[n].0,
            Expr::Ident(n, _) => !(self.is_var(n) || env.locals.contains_key(n) && !env.vals.contains_key(n)),
            // The arguments of a call site are only a trace (see is_const)
            Expr::Label(_, _, b) => self.is_const_quiet(b, env),
            _ => e.children().into_iter().all(|c| self.is_const_quiet(c, env)),
        }
    }

    fn try_const(&self, e: &Expr, env: &Env) -> Option<Value> {
        if self.is_const(e, env) {
            self.ce.eval(e, &env.vals).ok()
        } else {
            None
        }
    }

    /// `try_const`, and the strings made and the EXCEPT warnings while computing the value (see
    /// `note_folded`)
    fn try_const_made(&self, e: &Expr, env: &Env) -> (Option<Value>, Made) {
        if !e.any(&|x| matches!(x, Expr::Except(..))) {
            self.atoms.log_start();
            let v = self.try_const(e, env);
            return (v, Made { strs: self.atoms.log_end(), warns: vec![] });
        }
        if !self.is_const(e, env) {
            return (None, Made::default());
        }
        // TLC warned about the definitions without arguments when it started
        let e = crate::compile::uncache_prints(e, &self.zero_defs);
        let saved = crate::value::PRINTED.with(|p| p.replace(Some(vec![])));
        self.atoms.log_start();
        let v = self.ce.eval(&e, &env.vals).ok();
        let strs = self.atoms.log_end();
        let lines = crate::value::PRINTED.with(|p| p.replace(saved)).unwrap_or_default();
        let head = format!("{}Warning: The EXCEPT was applied to non-existing fields of the value at\n", crate::value::WARNING_MARK);
        let warns = lines.iter().filter_map(|l| l.first()?.strip_prefix(head.as_str()).map(str::to_string)).collect();
        (v, Made { strs, warns })
    }

    // ---------------------------------------------------------------- Sets (bitmasks and SSet)

    /// 0-based position of the constant index `i` into a tuple of `n` elements
    fn tuple_index(&self, i: &Expr, env: &Env, n: usize) -> R<usize> {
        match self.try_const(i, env) {
            Some(Value::Int(k)) if k >= 1 && k as u64 <= n as u64 => Ok(k as usize - 1),
            Some(Value::Int(k)) => Err(format!("tuple index {k} is outside 1..{n}")),
            _ => Err(format!("a tuple can only be indexed by a constant integer (got {})", short(i))),
        }
    }

    /// An EXCEPT step `[i]` into a tuple with i not constant: `!p[i] ... = v` becomes
    /// `!p = CASE i = 1 -> [@ EXCEPT ![1] ... = v] [] ... [] OTHER -> @`, since each element of a
    /// tuple may have its own type (an index outside the tuple leaves it unchanged, as in TLC)
    /// `warn` is where the value is written, for TLC's warning about an index outside the tuple
    fn split_dynamic_index(&mut self, t: &Ty, path: &[Path], val: &Expr, env: &Env, warn: Option<&str>) -> (Vec<Path>, Expr) {
        let mut cur = Some(t.clone());
        for (j, p) in path.iter().enumerate() {
            if let (Path::Idx(i), Some(Ty::Rec(fs))) = (p, &cur) {
                if is_tuple_fields(fs) && self.try_const(i, env).is_none() {
                    self.tmp += 1;
                    let at = format!("@dyn{}", self.tmp);
                    let base = Expr::Ident(at.clone(), NOPOS);
                    let arm_base = match warn {
                        Some(w) => except_at(w, base.clone()),
                        None => base.clone(),
                    };
                    let arms = (1..=fs.len())
                        .map(|k| {
                            let mut inner: Vec<Path> = vec![Path::Idx(Expr::Num(k as i64))];
                            inner.extend(path[j + 1..].iter().cloned());
                            // Within the arm the index is k, which lets constant tests on it pick
                            // the branch meant for this element's type
                            let v = replace_expr(val, i, &Expr::Num(k as i64));
                            let arm = Expr::Except(arm_base.clone().b(), vec![(inner, v)]);
                            (Expr::Bin(BOp::Eq, i.clone().b(), Expr::Num(k as i64).b()), Expr::Label("#per-element".into(), vec![], arm.b()))
                        })
                        .collect();
                    let mut outer: Vec<Path> = path[..j].to_vec();
                    outer.push(Path::Field(at));
                    let other = match warn {
                        Some(w) => Expr::Label(format!("{EXCEPT_WARN}{w}"), vec![], base.b()),
                        None => base,
                    };
                    return (outer, Expr::Case(arms, Some(other.b())));
                }
            }
            cur = match (&cur, p) {
                (Some(c), Path::Field(k)) if k.starts_with('@') => Some(c.clone()),
                (Some(Ty::Rec(fs)), Path::Idx(i)) if is_tuple_fields(fs) => {
                    self.tuple_index(i, env, fs.len()).ok().map(|k| fs[k].1.clone())
                }
                (Some(c), p) => Self::path_type(c, std::slice::from_ref(p)),
                (None, _) => None,
            };
        }
        (path.to_vec(), val.clone())
    }

    /// Rewrites the steps of an EXCEPT path that index into a tuple (`![k][1]`) as steps into the
    /// field the element is stored in
    fn resolve_path(&self, t: &Ty, path: &[Path], env: &Env) -> R<Vec<Path>> {
        let mut cur = Some(t.clone());
        let mut out = vec![];
        for p in path {
            let step = match (p, &cur) {
                (Path::Idx(i), Some(Ty::Rec(fs))) if is_tuple_fields(fs) => Path::Field(tuple_field(self.tuple_index(i, env, fs.len())?)),
                // A record is a function from its field names: !["a"] is !.a
                (Path::Idx(i), Some(Ty::Rec(fs))) => match self.try_const(i, env) {
                    Some(Value::Atom(a)) if fs.iter().any(|(n, _)| *n == self.atoms.name(a)) => Path::Field(self.atoms.name(a)),
                    _ => p.clone(),
                },
                _ => p.clone(),
            };
            cur = match &cur {
                Some(c) => Self::path_type(c, std::slice::from_ref(&step)),
                None => None,
            };
            out.push(step);
        }
        Ok(out)
    }

    /// Type at the end of an EXCEPT path
    fn path_type(t: &Ty, path: &[Path]) -> Option<Ty> {
        let mut cur = t.clone();
        for p in path {
            cur = match (p, &cur) {
                (Path::Field(k), _) if k.starts_with('@') => continue,
                (Path::Idx(_), Ty::Fun(_, c) | Ty::PFun(_, c)) => c.as_ref().clone(),
                (Path::Idx(_), Ty::Seq(e)) => e.as_ref().clone(),
                (Path::Field(k), Ty::Rec(fs)) => match &fs.iter().find(|(n, _)| n == k)?.1 {
                    Ty::Opt(i) => i.as_ref().clone(),
                    t => t.clone(),
                },
                _ => return None,
            };
        }
        Some(cur)
    }

    /// `t` with the type at the end of the EXCEPT path replaced by `new`
    fn set_path_type(t: &Ty, path: &[Path], new: &Ty) -> Ty {
        let Some((p, rest)) = path.split_first() else { return new.clone() };
        match (p, t) {
            (Path::Field(k), _) if k.starts_with('@') => Self::set_path_type(t, rest, new),
            (Path::Idx(_), Ty::Fun(d, c)) => Ty::Fun(d.clone(), Self::set_path_type(c, rest, new).into()),
            (Path::Idx(_), Ty::PFun(d, c)) => Ty::PFun(d.clone(), Self::set_path_type(c, rest, new).into()),
            (Path::Idx(_), Ty::Seq(e)) => Ty::Seq(Self::set_path_type(e, rest, new).into()),
            (Path::Field(k), Ty::Rec(fs)) => Ty::Rec(
                fs.iter()
                    .map(|(n, ft)| {
                        if n != k {
                            return (n.clone(), ft.clone());
                        }
                        let nt = match ft {
                            Ty::Opt(i) => Ty::Opt(Self::set_path_type(i, rest, new).into()),
                            ft => Self::set_path_type(ft, rest, new),
                        };
                        (n.clone(), nt)
                    })
                    .collect(),
            ),
            _ => t.clone(),
        }
    }

    fn elem_of(st: &Ty) -> Ty {
        match st {
            Ty::Set(e) => e.as_ref().clone(),
            _ => unreachable!(),
        }
    }

    fn s_empty(&mut self, st: &Ty) -> R<String> {
        self.ty_id(st)?;
        Ok(if is_sparse(st) { format!("{}::new()", st.repr().replace('<', "::<")) } else { "0u128".into() })
    }

    /// Statement adding element x (in the element type's representation) to acc
    fn s_add(&mut self, acc: &str, x: &str, st: &Ty) -> R<String> {
        let eid = self.ty_id(&Self::elem_of(st))?;
        Ok(if is_sparse(st) { format!("{acc}.insert({x});") } else { format!("{acc} |= bit_{eid}({x});") })
    }

    /// Statement setting the value at key `k` of `acc`, a function over part of a type or a bag of
    /// type `ft` (a count of 0 takes the element out of a bag). `k` is in the key type's
    /// representation.
    /// A record whose fields are all present (code `c` of type `t`) as the function over strings
    /// it is: a function over part of the type of its names. Any other value is left as it is
    fn rec_as_fun(&mut self, c: String, t: Ty, env: &Env) -> R<(String, Ty)> {
        let Ty::Rec(fs) = &t else { return Ok((c, t)) };
        if fs.is_empty() || fs.iter().any(|(n, ft)| !crate::compile::field_name(n) || matches!(ft, Ty::Opt(_))) {
            return Ok((c, t));
        }
        let mut keys = vec![];
        let (mut dt, mut ct) = (Ty::Enum(vec![]), fs[0].1.clone());
        for (n, ft) in fs {
            let (kc, kt) = self.gen(&Expr::Str(n.clone()), env, None)?;
            dt = join(&dt, &kt)?;
            ct = join(&ct, ft)?;
            keys.push((kc, kt));
        }
        let pt = Ty::PFun(dt.clone().into(), ct.clone().into());
        self.ty_id(&pt)?;
        let mut b = format!("{{ let __r = {c}; let mut __o = {}; ", Self::default_code(&pt));
        for (i, ((kc, kt), (_, ft))) in keys.into_iter().zip(fs).enumerate() {
            let k = self.coerce(kc, &kt, &dt)?;
            let v = self.coerce(format!("__r{}", crate::types::rec_field(fs.len(), i)), ft, &ct)?;
            b += &self.fun_put("__o", &k, &v, &pt)?;
            b += " ";
        }
        Ok((b + "__o }", pt))
    }

    fn fun_put(&mut self, acc: &str, k: &str, v: &str, ft: &Ty) -> R<String> {
        let (kt, _) = fun_kv(ft);
        Ok(match ft {
            Ty::PFun(..) if is_sparse_fun(ft) => format!("{acc}.put({k}, {v});"),
            Ty::Bag(_) if is_sparse_fun(ft) => format!("{{ let (__k, __n): (_, i64) = ({k}, {v}); if __n > 0 {{ {acc}.put(__k, __n); }} else {{ {acc}.del(&__k); }} }}"),
            Ty::PFun(..) => format!("{acc}[idx_{}({k})] = (true, {v});", self.ty_id(&kt)?),
            _ => format!("{acc}[idx_{}({k})] = {v};", self.ty_id(&kt)?),
        })
    }

    /// The count of `k` in the bag `b` (a place) of type `bt`: 0 when it is not in it
    fn bag_count(&mut self, b: &str, k: &str, bt: &Ty) -> R<String> {
        if is_sparse_fun(bt) {
            return Ok(format!("{b}.get(&{k}).unwrap_or(0)"));
        }
        let eid = self.ty_id(&fun_kv(bt).0)?;
        Ok(format!("{{ let __i = enc_{eid}({k}); if __i == u64::MAX {{ 0 }} else {{ {b}[__i as usize] }} }}"))
    }

    /// An iterator over the (key, value) entries of `f` (a place), a function over part of a type
    /// or a bag of type `ft`. With `ordered`, in TLC's order of the keys (a sparse one is sorted
    /// by the Rust order of its keys, which differs for some key types).
    fn fun_iter(&mut self, f: &str, ft: &Ty, ordered: bool) -> R<String> {
        let (kt, vt) = fun_kv(ft);
        if is_sparse_fun(ft) {
            if ordered && needs_tlc_order(&kt) {
                let cmp = self.tlc_cmp(&kt, "(&__x.0)", "(&__y.0)")?;
                return Ok(format!(
                    "{{ let mut __v: Vec<({}, {})> = ({f}).iter().collect(); __v.sort_by(|__x, __y| {cmp}); __v }}.into_iter()",
                    kt.repr(),
                    vt.repr()
                ));
            }
            return Ok(format!("({f}).iter()"));
        }
        let kid = self.ty_id(&kt)?;
        Ok(match ft {
            Ty::PFun(..) => format!("({f}).iter().enumerate().filter(|(_, __p)| __p.0).map(|(__i, __p)| (dec_{kid}(__i as u64), __p.1))"),
            _ => format!("({f}).iter().enumerate().filter(|(_, __c)| **__c > 0).map(|(__i, __c)| (dec_{kid}(__i as u64), *__c))"),
        })
    }

    /// Whether `[x \in S |-> e]` over this S is evaluated only where it is applied, as TLC does: S
    /// cannot be enumerated (Nat, Int, STRING, Seq(T), or a product with one of them) or has more
    /// elements than a function over part of a type is held as an array for
    fn lazy_domain(&self, s: &Expr, env: &Env) -> bool {
        match s.strip() {
            Expr::Ident(n, _) if ["Nat", "Int", "STRING"].contains(&n.as_str()) => {
                !env.locals.contains_key(n) && !self.is_var(n) && !self.ce.constants.contains_key(n)
            }
            Expr::Call(f, a) if f == "Seq" && a.len() == 1 => true,
            Expr::Call(f, parts) if f == "\\X" => parts.iter().any(|p| self.lazy_domain(p, env)),
            s => matches!(self.try_const(s, env), Some(Value::Set(v)) if v.len() as u64 > DENSE_MAX),
        }
    }

    /// How TLC prints a function over a set it cannot enumerate (see `lazy_fun_string`), when f is
    /// one whose domain TLC prints as tla2rs can: Nat, Int, STRING, `Seq(S)` and products of
    /// those and of finite sets, the finite ones printed as their values
    fn lazy_fun_shown(&mut self, f: &Expr, env: &Env) -> Option<String> {
        let d = self.lazy_fun_domain(f, env)?;
        if self.try_const(d, env).is_some() {
            return None;
        }
        lazy_fun_string(f, &mut |p| self.lazy_set_shown(p, env))
    }

    /// A domain part of a function over a set TLC cannot enumerate, as TLC prints its value
    fn lazy_set_shown(&mut self, s: &Expr, env: &Env) -> Option<String> {
        match s.strip() {
            Expr::Ident(n, _) if ["Nat", "Int", "STRING"].contains(&n.as_str()) && self.lazy_domain(s, env) => Some(n.clone()),
            Expr::Call(f, a) if f == "Seq" && a.len() == 1 => Some(format!("Seq({})", self.lazy_set_shown(&a[0], env)?)),
            Expr::Call(f, parts) if f == "\\X" => {
                let ps: Vec<String> = parts.iter().map(|p| self.lazy_set_shown(p, env)).collect::<Option<_>>()?;
                Some(format!("({})", ps.join(" \\X ")))
            }
            // TLC prints an interval as written
            Expr::Bin(BOp::Range, a, b) => match (self.try_const(a, env)?, self.try_const(b, env)?) {
                (Value::Int(a), Value::Int(b)) => Some(format!("{a}..{b}")),
                _ => None,
            },
            s => Some(crate::compile::show_value(self.atoms, &self.try_const(s, env)?)),
        }
    }

    /// The domain of `f` when it is a function evaluated only where it is applied (see
    /// `lazy_domain`), possibly with EXCEPT
    fn lazy_fun_domain<'e>(&self, f: &'e Expr, env: &Env) -> Option<&'e Expr> {
        match f.strip() {
            Expr::FunCons(_, s, _) if self.lazy_domain(s, env) => Some(s),
            Expr::Except(b, _) => self.lazy_fun_domain(b, env),
            _ => None,
        }
    }

    /// `f[k]` for a function `f` evaluated only where it is applied (`lazy_fun_domain`), with `k`
    /// held in the variable `kc` of type `kt`. As in TLC, the argument must be in the domain, and
    /// EXCEPT replaces the value at its keys.
    fn lazy_apply(&mut self, f: &Expr, kc: &str, kt: &Ty, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        match f.strip() {
            Expr::FunCons(v, s, body) => {
                // Used as a format string in the checker
                let shown = self.lazy_fun_shown(f, env).unwrap_or_else(|| lazy_fun_text(v, s)).replace('{', "{{").replace('}', "}}");
                let mem = self.gen_member(kc, kt, s, env)?;
                let mut env2 = env.clone();
                env2.locals.insert(v.clone(), (kc.to_string(), kt.clone()));
                env2.idx.remove(v);
                let (bc, bt) = self.gen(body, &env2, want)?;
                let tid = self.ty_id(kt)?;
                let msg = format!("In applying the function\n{shown},\nthe first argument is:\n{{}}\nwhich is not in its domain.");
                Ok((format!("{{ if !({mem}) {{ eval_error(format!({msg:?}, fmt_{tid}(&{kc}))) }} {bc} }}"), bt))
            }
            Expr::Except(base, ups) => {
                let Some(((path, val), rest)) = ups.split_last() else { return self.lazy_apply(base, kc, kt, env, want) };
                let prev = Expr::Except(base.clone(), rest.to_vec());
                let at_name = path.iter().find_map(|p| match p {
                    Path::Field(n) if n.starts_with('@') => Some(n.clone()),
                    _ => None,
                });
                let steps: Vec<&Path> = path.iter().filter(|p| !matches!(p, Path::Field(n) if n.starts_with('@'))).collect();
                let [Path::Idx(a)] = steps.as_slice() else {
                    return Err(format!("EXCEPT with a path of more than one index on a function over a set that cannot be enumerated: {}", short(f)));
                };
                let (ac, at) = self.gen(a, env, Some(kt))?;
                let av = self.fresh("a");
                // @ is the value before this update at the key it replaces
                let (pa, pat) = self.lazy_apply(&prev, &av, &at, env, want)?;
                let mut env2 = env.clone();
                env2.locals.insert("@".into(), (pa.clone(), pat.clone()));
                if let Some(n) = at_name {
                    env2.locals.insert(n, (pa, pat.clone()));
                }
                let (vc, vt) = self.gen(val, &env2, want.or(Some(&pat)))?;
                let (pc, pt) = self.lazy_apply(&prev, kc, kt, env, want)?;
                let j = join(kt, &at)?;
                // A key outside the domain leaves the function unchanged, as in TLC
                let dom = self.lazy_fun_domain(f, env).unwrap().clone();
                let in_dom = self.gen_member(&av, &at, &dom, env)?;
                let t = Self::layout(want, join(&vt, &pt)?);
                let (vc, pc) = (self.coerce(vc, &vt, &t)?, self.coerce(pc, &pt, &t)?);
                let same = format!("{} == {}", self.coerce(kc.to_string(), kt, &j)?, self.coerce(av.clone(), &at, &j)?);
                match except_pos(base) {
                    // TLC warns about a key outside the domain when it evaluates the EXCEPT
                    Some(p) => {
                        let inv = self.fresh("in");
                        Ok((format!("{{ let {av} = {ac}; let {inv} = {in_dom}; if !{inv} {{ except_warning({p:?}); }} if {same} && {inv} {{ {vc} }} else {{ {pc} }} }}"), t))
                    }
                    None => Ok((format!("{{ let {av} = {ac}; if {same} && {in_dom} {{ {vc} }} else {{ {pc} }} }}"), t)),
                }
            }
            _ => unreachable!(),
        }
    }

    /// The subsets of the set `c` of type `st`, in TLC's order: by size, then by their elements in
    /// order. A set held as an array is mapped onto a bitmask over its elements (in TLC's order).
    fn subsets_iter(&mut self, c: &str, st: &Ty) -> R<String> {
        if !matches!(st, Ty::Set(_)) {
            return Err(format!("SUBSET of {st:?}"));
        }
        self.need_subsets = true;
        if !is_sparse(st) {
            return Ok(format!("subsets_tlc({c}).into_iter()"));
        }
        let it = self.s_iter(c, st)?;
        let et = Self::elem_of(st);
        let empty = self.s_empty(st)?;
        let add = self.s_add("__s", "__e[__i as usize]", st)?;
        Ok(format!(
            "{{ let __e: Vec<{}> = {it}.collect(); let __n = __e.len(); \
             subsets_tlc(if __n >= 128 {{ u128::MAX }} else {{ (1u128 << __n) - 1 }}).into_iter().map(move |__m| {{ let mut __s = {empty}; for __i in bits(__m) {{ {add} }} __s }}) }}",
            et.repr()
        ))
    }

    fn s_iter(&mut self, c: &str, st: &Ty) -> R<String> {
        let et = Self::elem_of(st);
        let eid = self.ty_id(&et)?;
        if is_sparse(st) && needs_tlc_order(&et) {
            // The array is sorted by the Rust order of the elements, which for a set held as a
            // bitmask is not TLC's: iterate in TLC's order, which decides CHOOSE and the order
            // successors are generated in
            let cmp = self.tlc_cmp(&et, "x", "y")?;
            return Ok(format!(
                "{{ let mut __v: Vec<{}> = ({c}).iter().collect(); __v.sort_by(|x, y| {cmp}); __v }}.into_iter()",
                et.repr()
            ));
        }
        Ok(if is_sparse(st) { format!("({c}).iter()") } else { format!("bits({c}).map(dec_{eid})") })
    }

    /// An expression comparing `a` and `b` (references to values of type `t`) in TLC's order
    fn tlc_cmp(&mut self, t: &Ty, a: &str, b: &str) -> R<String> {
        Ok(match t {
            Ty::Set(_) if !is_sparse(t) => format!("tlc_set_cmp(*{a}, *{b})"),
            // A sorted array whose elements Rust orders otherwise than TLC: by size, then the
            // elements in TLC's order
            Ty::Set(e) if needs_tlc_order(e) => {
                let (ix, iy) = (self.s_iter(&format!("(*{a})"), t)?, self.s_iter(&format!("(*{b})"), t)?);
                let inner = self.tlc_cmp(e, "__fa", "__fb")?;
                format!("{a}.len.cmp(&{b}.len).then_with(|| {ix}.zip({iy}).map(|(__fa, __fb)| {{ let (__fa, __fb) = (&__fa, &__fb); {inner} }}).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal))")
            }
            // A sparse function or bag: its pairs sort by key, so the Rust order of the set of pairs
            // is TLC's (by the size of the domain, then key and value pair by pair) when it is so
            // for keys and values
            Ty::PFun(..) | Ty::Bag(_) if is_sparse_fun(t) => {
                let (kt, vt) = fun_kv(t);
                if !needs_tlc_order(&kt) && !needs_tlc_order(&vt) {
                    return Ok(format!("{a}.cmp({b})"));
                }
                let kc = self.tlc_cmp(&kt, "(&__p.0)", "(&__q.0)")?;
                let vc = self.tlc_cmp(&vt, "(&__p.1)", "(&__q.1)")?;
                let (ix, iy) = (self.fun_iter("__x", t, true)?, self.fun_iter("__y", t, true)?);
                format!(
                    "{{ let (__x, __y) = ({a}, {b}); __x.len.cmp(&__y.len).then_with(|| {ix}.zip({iy}).map(|(__p, __q)| {kc}.then_with(|| {vc})).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal)) }}"
                )
            }
            // A function over part of a type, as TLC compares functions: by the size of the
            // domain, then key and value pair by pair
            Ty::PFun(_, c) => {
                let vc = self.tlc_cmp(c, "(&__x[__i].1)", "(&__y[__j].1)")?;
                format!(
                    "{{ let (__x, __y) = ({a}, {b}); let __dx: Vec<usize> = (0..__x.len()).filter(|&i| __x[i].0).collect(); \
                     let __dy: Vec<usize> = (0..__y.len()).filter(|&i| __y[i].0).collect(); \
                     __dx.len().cmp(&__dy.len()).then_with(|| __dx.iter().zip(__dy.iter()).map(|(&__i, &__j)| __i.cmp(&__j).then_with(|| {vc})).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal)) }}"
                )
            }
            // A bag compares as the function it is
            Ty::Bag(_) => format!(
                "{{ let (__x, __y) = ({a}, {b}); let __dx: Vec<usize> = (0..__x.len()).filter(|&i| __x[i] > 0).collect(); \
                 let __dy: Vec<usize> = (0..__y.len()).filter(|&i| __y[i] > 0).collect(); \
                 __dx.len().cmp(&__dy.len()).then_with(|| __dx.iter().zip(__dy.iter()).map(|(&__i, &__j)| __i.cmp(&__j).then_with(|| __x[__i].cmp(&__y[__j]))).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal)) }}"
            ),
            // Records of different fields, as TLC compares records: by the number of fields, then
            // name and value field by field (the fields are in TLC's order of names)
            Ty::Rec(fs) if !is_tuple_fields(fs) && fs.iter().any(|(_, t)| matches!(t, Ty::Opt(_))) => {
                if t.tlc_perm().is_some() {
                    let id = self.ty_id(t)?;
                    return Ok(format!("enc_{id}(*{a}).cmp(&enc_{id}(*{b}))"));
                }
                let mut present = vec![];
                let mut arms = vec![];
                for (i, (_, ft)) in fs.iter().enumerate() {
                    let fp = rec_field(fs.len(), i);
                    match ft {
                        Ty::Opt(inner) => {
                            present.push(format!("__x{fp}.0"));
                            let c = self.tlc_cmp(inner, &format!("(&__x{fp}.1)"), &format!("(&__y{fp}.1)"))?;
                            arms.push(format!("{i} => {c}"));
                        }
                        ft => {
                            present.push("true".into());
                            let c = self.tlc_cmp(ft, &format!("(&__x{fp})"), &format!("(&__y{fp})"))?;
                            arms.push(format!("{i} => {c}"));
                        }
                    }
                }
                let px = present.join(", ");
                let py = px.replace("__x", "__y");
                // TLC orders model values before other values (see types::ATOM_FIELD)
                let first = match fs.iter().position(|(n, _)| n == crate::types::ATOM_FIELD) {
                    Some(i) => {
                        let fp = rec_field(fs.len(), i);
                        format!("if ({a}){fp}.0 != ({b}){fp}.0 {{ if ({a}){fp}.0 {{ std::cmp::Ordering::Less }} else {{ std::cmp::Ordering::Greater }} }} else ")
                    }
                    None => String::new(),
                };
                format!(
                    "{{ {first}{{ let (__x, __y) = ({a}, {b}); let __fx: Vec<usize> = [{px}].iter().enumerate().filter(|p| *p.1).map(|p| p.0).collect(); \
                     let __fy: Vec<usize> = [{py}].iter().enumerate().filter(|p| *p.1).map(|p| p.0).collect(); \
                     __fx.len().cmp(&__fy.len()).then_with(|| __fx.iter().zip(__fy.iter()).map(|(&__i, &__j)| __i.cmp(&__j).then_with(|| if __i != __j {{ std::cmp::Ordering::Equal }} else {{ match __i {{ {}, _ => unreachable!() }} }})).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal)) }} }}",
                    arms.join(", ")
                )
            }
            Ty::Rec(fs) if needs_tlc_order(t) => {
                let mut parts = vec![];
                for (i, (_, ft)) in fs.iter().enumerate() {
                    let fp = rec_field(fs.len(), i);
                    parts.push(self.tlc_cmp(ft, &format!("(&{a}{fp})"), &format!("(&{b}{fp})"))?);
                }
                let mut code = parts.pop().unwrap();
                while let Some(p) = parts.pop() {
                    code = format!("{p}.then_with(|| {code})");
                }
                code
            }
            Ty::Fun(_, c) if needs_tlc_order(t) => {
                let inner = self.tlc_cmp(c, "__fa", "__fb")?;
                format!("{a}.iter().zip({b}.iter()).map(|(__fa, __fb)| {inner}).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal)")
            }
            Ty::Seq(e) if needs_tlc_order(t) => {
                let inner = self.tlc_cmp(e, "__fa", "__fb")?;
                format!("{a}.len.cmp(&{b}.len).then_with(|| {a}.slice().iter().zip({b}.slice().iter()).map(|(__fa, __fb)| {inner}).find(|o| o.is_ne()).unwrap_or(std::cmp::Ordering::Equal))")
            }
            _ => format!("{a}.cmp({b})"),
        })
    }

    fn s_card(&mut self, c: &str, st: &Ty) -> String {
        if is_sparse(st) {
            // `len` is a field (u8), not a method
            format!("(({c}).len as i64)")
        } else {
            format!("(({c}).count_ones() as i64)")
        }
    }

    /// TLC's message when it compares a value of type xt with a value it cannot compare it with
    /// (`compareTo`, as in a search of a sorted set), for a tuple or a string (measured)
    fn compare_fails_msg(&self, xt: &Ty) -> Option<&'static str> {
        if tuple_elems(xt).is_some() {
            Some("Attempted to compare the function {} with the value:\n{}")
        } else if matches!(xt, Ty::Enum(v) if !v.is_empty() && v.iter().all(|&a| !self.atoms.is_model(a))) {
            Some("Attempted to compare string {} with non-string:\n{}")
        } else {
            None
        }
    }

    /// Whether x (of type xt) is a member of set c (of type st)
    fn s_has(&mut self, c: &str, st: &Ty, x: &str, xt: &Ty) -> R<String> {
        let et = Self::elem_of(st);
        match self.tuple_cmp(xt, &et)? {
            Cmp::Normal => {}
            Cmp::Unequal => return Ok("false".into()),
            // TLC compares only against the elements present, so an empty set is no error. The set
            // is sorted: TLC searches it, comparing x first with the element in the middle
            Cmp::Fails(m) => {
                let empty = if is_sparse(st) { format!("(({c}).len == 0)") } else { format!("({c} == 0)") };
                if let Some(f) = self.compare_fails_msg(xt) {
                    let it = self.s_iter(c, st)?;
                    let n = self.s_card(c, st);
                    let (xid, eid) = (self.ty_id(xt)?, self.ty_id(&et)?);
                    let fail = format!(
                        "{{ let __e = {it}.nth(({n} / 2) as usize).unwrap(); let __b: bool = eval_error(format!({f:?}, ppr(&fmt_{xid}(&{x})), ppr(&fmt_{eid}(&__e)))); __b }}"
                    );
                    return Ok(format!("(if {empty} {{ false }} else {fail})"));
                }
                return Ok(format!("(if {empty} {{ false }} else {{ {} }})", eval_error_bool(&m)));
            }
        }
        if matches!(&et, Ty::Enum(v) if v.is_empty()) {
            return Ok("false".into());
        }
        if self.str_meets_int(xt, &et) {
            // Compare with each element as TLC does, which stops on a string against an integer
            let j = join(xt, &et)?;
            let xc = self.coerce(x.to_string(), xt, &j)?;
            let ec = self.coerce("__e".into(), &et, &j)?;
            let it = self.s_iter(c, st)?;
            return Ok(format!("{{ let __x = {xc}; let __any = {it}.any(|__e| mixed_eq(__x, {ec})); __any }}"));
        }
        if narrows(xt, &et) {
            // x may hold a model value stored as an integer-or-model-value: compare in the joined
            // type rather than convert x (which fails at run time on an integer)
            let j = join(xt, &et)?;
            let jst = Ty::Set(j.clone().into());
            if is_sparse(st) && is_sparse(&jst) && self.tuple_cmp(xt, &j)? == Cmp::Normal && !self.str_meets_int(xt, &j) && !narrows(xt, &j) {
                // Compare x with each element converted, as a membership test in the converted set
                // would, without building and sorting that set at each test (a test in a loop over
                // another set built it once per element there)
                let Ok(xc) = self.coerce_soft(x.to_string(), xt, &j) else { return Ok("false".into()) };
                let eq = self.eq_into("__e", &et, "__x", &j)?;
                return Ok(format!("{{ let __x = {xc}; let __any = ({c}).iter().any(|__e| {eq}); __any }}"));
            }
            let cc = self.coerce(c.to_string(), st, &jst)?;
            let v = self.fresh("s");
            let inner = self.s_has(&v, &jst, x, xt)?;
            return Ok(format!("{{ let {v} = {cc}; {inner} }}"));
        }
        if is_sparse(st) {
            let Ok(xc) = self.coerce_soft(x.to_string(), xt, &et) else { return Ok("false".into()) };
            return Ok(format!("({c}).contains(&{xc})"));
        }
        let widens = join(xt, &et).ok().as_ref() == Some(&et);
        if !xt.is_scalar() || !(xt.kind_eq(&et) || widens || matches!((xt, &et), (Ty::Rec(_), Ty::Rec(_)))) {
            return Ok("false".into());
        }
        let eid = self.ty_id(&et)?;
        let Ok(xc) = self.coerce_soft(x.to_string(), xt, &et) else { return Ok("false".into()) };
        Ok(format!("{{ let __i = enc_{eid}({xc}); __i != u64::MAX && ({c} >> __i) & 1 == 1 }}"))
    }

    /// Whether e (of type et) equals x (of type j, which et widens to), as `coerce(e, et, j) == x`
    /// compares, without building the converted value: a tuple against a sequence compares the
    /// length and then element by element
    fn eq_into(&mut self, e: &str, et: &Ty, x: &str, j: &Ty) -> R<String> {
        if et == j {
            return Ok(format!("({e} == {x})"));
        }
        if let (Some(ts), Ty::Seq(se)) = (tuple_elems(et), j) {
            let ts: Vec<Ty> = ts.into_iter().cloned().collect();
            let n = ts.len();
            // Converted, a tuple longer than the sequences' capacity stops for a larger one
            let mut parts = vec![format!("({n} > QCAP && seq_too_long(QCAP))"), format!("({x}).len == {n}")];
            for (k, t) in ts.iter().enumerate() {
                parts.push(self.eq_into(&format!("({e}){}", rec_field(n, k)), t, &format!("({x}).items[{k}]"), se)?);
            }
            return Ok(format!("(!{} && {})", parts[0], parts[1..].join(" && ")));
        }
        if let (Ty::Rec(a), Ty::Rec(b)) = (et, j) {
            let plain = |t: &Ty| !matches!(t, Ty::Opt(_));
            if a.len() == b.len() && a.iter().zip(b).all(|((m, s), (n, t))| m == n && plain(s) && plain(t)) {
                let n = a.len();
                let mut parts = vec![];
                for (k, ((_, s), (_, t))) in a.iter().zip(b).enumerate() {
                    let f = rec_field(n, k);
                    parts.push(self.eq_into(&format!("({e}){f}"), s, &format!("({x}){f}"), t)?);
                }
                return Ok(format!("({})", parts.join(" && ")));
            }
        }
        let ec = self.coerce(e.to_string(), et, j)?;
        Ok(format!("({ec} == {x})"))
    }

    /// Type coercion that returns Err when the value might not fit the target type (e.g. a field
    /// the target requires is absent)
    fn coerce_soft(&mut self, code: String, from: &Ty, to: &Ty) -> R<String> {
        if let (Ty::Rec(a), Ty::Rec(b)) = (from, to) {
            // It does not fit if `from` has a field that `to` lacks
            if a.iter().any(|(n, _)| !b.iter().any(|(m, _)| m == n)) {
                return Err("record fields do not fit".into());
            }
        }
        if narrows(from, to) {
            return Err("an integer does not fit a model value".into());
        }
        self.coerce(code, from, to)
    }

    fn s_bin(&mut self, op: BOp, a: &str, b: &str, st: &Ty) -> String {
        if is_sparse(st) {
            match op {
                BOp::Cup => format!("({a}).union(&{b})"),
                BOp::Cap => format!("({a}).inter(&{b})"),
                _ => format!("({a}).minus(&{b})"),
            }
        } else {
            match op {
                BOp::Cup => format!("({a} | {b})"),
                BOp::Cap => format!("({a} & {b})"),
                _ => format!("({a} & !{b})"),
            }
        }
    }

    /// Default value of a type (used for omitted fields and unused SSet slots)
    fn default_code(t: &Ty) -> String {
        match t {
            Ty::Bag(_) | Ty::PFun(..) if is_sparse_fun(t) => Self::default_code(&fun_pairs(t)),
            Ty::Bag(e) => format!("[0i64; {}]", e.size().unwrap_or(0)),
            Ty::PFun(d, c) => Self::default_code(&pfun_repr(d, c)),
            Ty::Bool => "false".into(),
            Ty::Int(..) | Ty::IntAtom(..) => "0i64".into(),
            Ty::Enum(_) => "0u16".into(),
            Ty::Rec(fs) => rec_build(&fs.iter().map(|(_, t)| Self::default_code(t)).collect::<Vec<_>>()),
            Ty::Opt(t) => format!("(false, {})", Self::default_code(t)),
            Ty::Fun(d, c) => format!("[{}; {}]", Self::default_code(c), d.size().unwrap_or(0)),
            Ty::Set(_) if is_sparse(t) => format!("{}::new()", t.repr().replace('<', "::<")),
            Ty::Set(_) => "0u128".into(),
            Ty::Seq(_) => format!("{}::new()", t.repr().replace('<', "::<")),
        }
    }

    // ---------------------------------------------------------------- Value literals

    pub fn lit(&mut self, v: &Value, t: &Ty) -> R<String> {
        Ok(match (v, t) {
            // A value of another kind among model values (see types::VAL_FIELD)
            (v, Ty::Rec(fs)) if crate::types::has_val(fs) && !matches!(v, Value::Atom(_) | Value::Rec(_)) => {
                let m = [(crate::types::VAL_FIELD.to_string(), v.clone())].into_iter().collect();
                return self.lit(&Value::Rec(m), t);
            }
            (Value::Bool(b), _) => b.to_string(),
            (Value::Int(i), _) => format!("{i}i64"),
            (Value::Atom(a), Ty::IntAtom(..)) => format!("(i64::MIN + {a}i64)"),
            // A model value among records (see types::ATOM_FIELD)
            (Value::Atom(a), Ty::Rec(fs)) if crate::types::has_atoms(fs) => {
                let m = [(crate::types::ATOM_FIELD.to_string(), Value::Atom(*a))].into_iter().collect();
                return self.lit(&Value::Rec(m), t);
            }
            (Value::Atom(a), _) => format!("{a}u16"),
            (v, Ty::PFun(..) | Ty::Bag(_)) if is_sparse_fun(t) && crate::value::as_fun(v).is_some() => {
                self.ty_id(t)?;
                let (kt, vt) = fun_kv(t);
                let mut code = Self::default_code(t);
                for (k, x) in crate::value::as_fun(v).unwrap() {
                    code = format!("{code}.with_put({}, {})", self.lit(&k, &kt)?, self.lit(&x, &vt)?);
                }
                code
            }
            (v, Ty::PFun(d, c)) if crate::value::as_fun(v).is_some() => {
                self.ty_id(t)?;
                let m = crate::value::as_fun(v).unwrap();
                let mut parts = vec![];
                for k in d.enumerate() {
                    parts.push(match m.get(&k) {
                        Some(x) => format!("(true, {})", self.lit(x, c)?),
                        None => format!("(false, {})", Self::default_code(c)),
                    });
                }
                format!("[{}]", parts.iter().map(|p| format!("{p},")).collect::<String>())
            }
            (v, Ty::Bag(e)) if crate::value::as_fun(v).is_some() => {
                self.ty_id(t)?;
                let m = crate::value::as_fun(v).unwrap();
                let parts: Vec<String> = e.enumerate().iter().map(|k| match m.get(k) {
                    Some(Value::Int(c)) => format!("{c}i64"),
                    _ => "0i64".into(),
                }).collect();
                format!("[{}]", parts.iter().map(|p| format!("{p},")).collect::<String>())
            }
            (Value::Tuple(xs), Ty::Seq(e)) => {
                if xs.len() > self.qcap {
                    return Err(format!("a sequence of length {} is longer than the maximum length {}", xs.len(), self.qcap));
                }
                let parts: Vec<String> = xs.iter().map(|x| self.lit(x, e)).collect::<R<_>>()?;
                format!("{}::from_slice(&[{}])", t.repr().replace('<', "::<"), parts.join(", "))
            }
            (Value::Tuple(xs), Ty::Fun(d, c)) if seq_domain(d) == Some(xs.len()) => {
                self.ty_id(t)?;
                let parts: Vec<String> = xs.iter().map(|x| self.lit(x, c)).collect::<R<_>>()?;
                format!("[{}]", parts.iter().map(|p| format!("{p},")).collect::<String>())
            }
            (Value::Tuple(xs), Ty::Rec(fs)) if is_tuple_fields(fs) && xs.len() == fs.len() => {
                let parts: Vec<String> = xs.iter().zip(fs).map(|(x, (_, ft))| self.lit(x, ft)).collect::<R<_>>()?;
                rec_build(&parts)
            }
            (Value::Rec(m), Ty::Rec(fs)) if !is_tuple_fields(fs) => {
                let mut parts = vec![];
                for (k, ft) in fs {
                    parts.push(match (ft, m.get(k)) {
                        (Ty::Opt(i), Some(v)) => format!("(true, {})", self.lit(v, i)?),
                        (Ty::Opt(_), None) => Self::default_code(ft),
                        (ft, Some(v)) => self.lit(v, ft)?,
                        (_, None) => return Err("record field mismatch".into()),
                    });
                }
                rec_build(&parts)
            }
            (Value::Set(xs), Ty::Set(e)) if is_sparse(t) => {
                let mut c = self.s_empty(t)?;
                for x in xs {
                    c = format!("{c}.with({})", self.lit(x, e)?);
                }
                c
            }
            (Value::Set(xs), Ty::Set(e)) => {
                self.ty_id(t)?;
                let mut m: u128 = 0;
                for x in xs {
                    m |= 1u128 << e.enc(x).ok_or("set element outside its type")?;
                }
                format!("{m}u128")
            }
            (Value::Fun(m), Ty::Fun(d, c)) => {
                self.ty_id(t)?;
                let mut s = String::from("[");
                for k in d.enumerate() {
                    s += &self.lit(m.get(&k).ok_or("function domain mismatch")?, c)?;
                    s += ",";
                }
                s + "]"
            }
            _ => return Err(format!("cannot write {v:?} as {t:?}")),
        })
    }

    /// Writes the value using the expected type's layout if given, otherwise a type derived from
    /// the value
    fn lit_auto(&mut self, v: &Value, want: Option<&Ty>) -> R<(String, Ty)> {
        if let Some(w) = want {
            if w.conforms(v) {
                return Ok((self.lit(v, w)?, w.clone()));
            }
        }
        let t = ty_of_value(v)?;
        Ok((self.lit(v, &t)?, t))
    }

    // ---------------------------------------------------------------- Type coercion

    fn trivial(from: &Ty, to: &Ty) -> bool {
        match (from, to) {
            (Ty::Set(_), Ty::Set(_)) => from == to,
            (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) => d1 == d2 && Self::trivial(c1, c2),
            (Ty::Rec(a), Ty::Rec(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.0 == y.0 && Self::trivial(&x.1, &y.1))
            }
            (Ty::Opt(a), Ty::Opt(b)) => Self::trivial(a, b),
            (Ty::Opt(_), _) | (_, Ty::Opt(_)) => false,
            _ => true,
        }
    }

    fn coerce(&mut self, code: String, from: &Ty, to: &Ty) -> R<String> {
        if let (Some(a), Some(b)) = (tuple_elems(from), tuple_elems(to)) {
            if a.len() != b.len() {
                return Err(format!(
                    "a tuple of length {} used where a tuple of length {} is expected",
                    a.len(),
                    b.len()
                ));
            }
        }
        if from == to || (from.kind_eq(to) && Self::trivial(from, to)) {
            return Ok(code);
        }
        // The empty type (e.g. the element type of {}) coerces to any type
        if let (Ty::Set(e), Ty::Set(_)) = (from, to) {
            if matches!(e.as_ref(), Ty::Enum(v) if v.is_empty()) {
                return self.s_empty(to);
            }
        }
        if matches!(from, Ty::Enum(v) if v.is_empty()) && !matches!(to, Ty::Enum(_)) {
            // No value has this type, so the code cannot produce one: it stops (e.g. CHOOSE from
            // an empty set) and must still run to report that
            return Ok(format!("{{ let __u: {} = {{ let _ = {code}; unreachable!() }}; __u }}", to.repr()));
        }
        match (from, to) {
            // A model value as a value that is a record or a model value (see types::ATOM_FIELD),
            // and a value of another kind as one that is that or a model value (VAL_FIELD)
            (Ty::Enum(_), Ty::Rec(fs)) if crate::types::has_atoms(fs) => self.box_into(code, from, fs, crate::types::ATOM_FIELD),
            (_, Ty::Rec(fs)) if crate::types::has_val(fs) && crate::types::boxable(from) => self.box_into(code, from, fs, crate::types::VAL_FIELD),
            // The other way: the model value, or the value of the other kind, which fails on
            // anything else
            (Ty::Rec(fs), Ty::Enum(_) | Ty::IntAtom(..)) if crate::types::has_atoms(fs) => {
                let (c, t) = self.unbox(code, from, crate::types::ATOM_FIELD)?;
                self.coerce(c, &t, to)
            }
            (Ty::Rec(fs), _) if crate::types::has_val(fs) && crate::types::boxable(to) => {
                let (c, t) = self.unbox(code, from, crate::types::VAL_FIELD)?;
                self.coerce(c, &t, to)
            }
            // The function over the empty set, built as the empty record (its domain has no
            // element, so the record of no fields is the same value)
            (Ty::Rec(a), Ty::Fun(d, _) | Ty::PFun(d, _)) if a.is_empty() && d.size() == Some(0) => {
                Ok(format!("{{ let _ = {code}; {} }}", Self::default_code(to)))
            }
            (Ty::Set(a), Ty::Set(b)) if !is_sparse(from) && !is_sparse(to) && a.kind_eq(b) && Self::trivial(a, b) => {
                let (a, b) = (self.ty_id(from)?, self.ty_id(to)?);
                self.convs.insert((a, b));
                Ok(format!("conv_{a}_{b}({code})"))
            }
            (Ty::Fun(d1, c1), Ty::Fun(d2, c2)) if d1 == d2 => {
                let f = self.fresh("f");
                let o = self.fresh("o");
                let inner = self.coerce(format!("{f}[__i]"), c1, c2)?;
                // Annotate the type explicitly: context does not always determine from_fn's type
                Ok(format!(
                    "{{ let {f} = {code}; let {o}: {} = std::array::from_fn(|__i| {inner}); {o} }}",
                    to.repr()
                ))
            }
            (Ty::Rec(a), Ty::Rec(b)) => {
                // Per field of b: coerce from a if present, else leave it absent (if optional)
                let r = self.fresh("r");
                let mut parts = vec![];
                for (n, bt) in b {
                    let part = match a.iter().position(|(m, _)| m == n) {
                        Some(i) => {
                            let at = &a[i].1;
                            let src = format!("{r}{}", rec_field(a.len(), i));
                            match (at, bt) {
                                (Ty::Opt(x), Ty::Opt(y)) => {
                                    let o = self.fresh("o");
                                    let inner = self.coerce(format!("{o}.1"), x, y)?;
                                    format!("{{ let {o} = {src}; if {o}.0 {{ (true, {inner}) }} else {{ {} }} }}", Self::default_code(bt))
                                }
                                (x, Ty::Opt(y)) => format!("(true, {})", self.coerce(src.clone(), x, y)?),
                                (Ty::Opt(x), y) => {
                                    let o = self.fresh("o");
                                    let inner = self.coerce(format!("{o}.1"), x, y)?;
                                    format!("{{ let {o} = {src}; if !{o}.0 {{ type_error(\"record without field\", \"{n}\") }} {inner} }}")
                                }
                                (x, y) => self.coerce(src.clone(), x, y)?,
                            }
                        }
                        None => match bt {
                            Ty::Opt(_) => Self::default_code(bt),
                            _ => return Err(format!("record has no field `{n}`")),
                        },
                    };
                    parts.push(part);
                }
                Ok(format!("{{ let {r} = {code}; {} }}", rec_build(&parts)))
            }
            (Ty::Set(_), Ty::Set(_)) => {
                // Coerce element by element and rebuild the set
                let et = Self::elem_of(from);
                let tt = Self::elem_of(to);
                let x = self.fresh("x");
                let acc = self.fresh("acc");
                let it = self.s_iter(&code, from)?;
                let xc = self.coerce(x.clone(), &et, &tt)?;
                let add = self.s_add(&acc, &xc, to)?;
                let empty = self.s_empty(to)?;
                Ok(format!("{{ let mut {acc} = {empty}; for {x} in {it} {{ {add} }} {acc} }}"))
            }
            (Ty::Enum(x), Ty::Set(_) | Ty::Fun(..) | Ty::Seq(_)) if x.is_empty() => Err("empty enum".into()),
            (Ty::Rec(fs), Ty::Bag(_) | Ty::PFun(..)) if fs.is_empty() => Ok(Self::default_code(to)),
            // To or from a sparse function or bag: entry by entry
            (Ty::Fun(..) | Ty::PFun(..), Ty::PFun(..)) | (Ty::Bag(_), Ty::Bag(_)) if is_sparse_fun(from) || is_sparse_fun(to) => {
                let (f, o) = (self.fresh("f"), self.fresh("o"));
                let (it, fk, fv) = match from {
                    Ty::Fun(d, c) => {
                        let did = self.ty_id(d)?;
                        (format!("{f}.iter().enumerate().map(|(__i, &__v)| (dec_{did}(__i as u64), __v))"), d.as_ref().clone(), c.as_ref().clone())
                    }
                    _ => {
                        let (fk, fv) = fun_kv(from);
                        (self.fun_iter(&f, from, false)?, fk, fv)
                    }
                };
                let (tk, tv) = fun_kv(to);
                let kc = self.coerce("__k".into(), &fk, &tk)?;
                let vc = self.coerce("__v".into(), &fv, &tv)?;
                let put = self.fun_put(&o, &kc, &vc, to)?;
                Ok(format!("{{ let {f} = {code}; let mut {o} = {}; for (__k, __v) in {it} {{ {put} }} {o} }}", Self::default_code(to)))
            }
            (Ty::Rec(fs), Ty::Bag(e)) if is_tuple_fields(fs) && is_sparse_fun(to) => {
                let r = self.fresh("r");
                let mut s = format!("{{ let {r} = {code}; let mut __o = {}; ", Self::default_code(to));
                for (k, (_, ft)) in fs.iter().enumerate() {
                    let n = k as i64 + 1;
                    let kc = self.coerce(format!("{n}i64"), &Ty::Int(n, n), e)?;
                    let vc = self.coerce(format!("{r}{}", rec_field(fs.len(), k)), ft, &Ty::Int(-BIG, BIG))?;
                    s += &self.fun_put("__o", &kc, &vc, to)?;
                }
                Ok(s + "__o }")
            }
            // A function over all of a type as one over part of it, and between partial functions
            (Ty::Fun(d1, c1), Ty::PFun(d2, c2)) if d1 != d2 => {
                let mid = Ty::PFun(d1.clone(), c2.clone());
                let c = self.coerce(code, from, &mid)?;
                self.coerce(c, &mid, to)
            }
            (Ty::Fun(d1, c1), Ty::PFun(d2, c2)) if d1 == d2 => {
                let inner = self.coerce("__x".into(), c1, c2)?;
                Ok(format!("{{ let __f = {code}; let __o: {} = std::array::from_fn(|__i| {{ let __x = __f[__i]; (true, {inner}) }}); __o }}", to.repr()))
            }
            (Ty::PFun(d1, c1), Ty::PFun(d2, c2)) => {
                let (aid, bid) = (self.ty_id(d1)?, self.ty_id(d2)?);
                let inner = self.coerce("__x".into(), c1, c2)?;
                Ok(format!(
                    "{{ let __f = {code}; let mut __o = {}; for (__i, &(__p, __x)) in __f.iter().enumerate() {{ if __p {{ __o[idx_{bid}(dec_{aid}(__i as u64))] = (true, {inner}); }} }} __o }}",
                    Self::default_code(to)
                ))
            }
            // A tuple of counts as a bag over 1..n
            (Ty::Rec(fs), Ty::Bag(e)) if is_tuple_fields(fs) => {
                let eid = self.ty_id(e)?;
                let r = self.fresh("r");
                let mut s = format!("{{ let {r} = {code}; let mut __o = {}; ", Self::default_code(to));
                for k in 0..fs.len() {
                    write!(s, "__o[idx_{eid}({}i64)] = {r}{}; ", k + 1, rec_field(fs.len(), k)).unwrap();
                }
                Ok(s + "__o }")
            }
            // Bags over different element types: move each count to its element's place
            (Ty::Bag(a), Ty::Bag(b)) => {
                let (aid, bid) = (self.ty_id(a)?, self.ty_id(b)?);
                let r = self.fresh("r");
                Ok(format!(
                    "{{ let {r} = {code}; let mut __o = {}; for (__i, &__c) in {r}.iter().enumerate() {{ if __c > 0 {{ __o[idx_{bid}(dec_{aid}(__i as u64))] = __c; }} }} __o }}",
                    Self::default_code(to)
                ))
            }
            // Between tuples, functions over 1..n, and sequences
            (_, Ty::Seq(e)) if seq_elems(from).is_some() => {
                let (r, q) = (self.fresh("r"), self.fresh("q"));
                let mut s = format!("{{ let {r} = {code}; let mut {q} = {}; ", Self::default_code(to));
                match from {
                    Ty::Seq(fe) => {
                        let x = self.fresh("x");
                        let xc = self.coerce(x.clone(), fe, e)?;
                        write!(s, "for {x} in {r}.iter() {{ {q}.push({xc}); }} ").unwrap();
                    }
                    Ty::Fun(_, fc) => {
                        let x = self.fresh("x");
                        let xc = self.coerce(x.clone(), fc, e)?;
                        write!(s, "for &{x} in {r}.iter() {{ {q}.push({xc}); }} ").unwrap();
                    }
                    _ => {
                        let n = seq_elems(from).unwrap().len();
                        for (k, t) in seq_elems(from).unwrap().iter().enumerate() {
                            let xc = self.coerce(format!("{r}{}", rec_field(n, k)), t, e)?;
                            write!(s, "{q}.push({xc}); ").unwrap();
                        }
                    }
                }
                Ok(s + &format!("{q} }}"))
            }
            (Ty::Seq(fe), _) if seq_elems(to).is_some() => {
                // A sequence used as a tuple or a function over 1..n: its length must match
                let r = self.fresh("r");
                let (n, body) = match to {
                    Ty::Fun(d, c) => {
                        let n = seq_domain(d).unwrap();
                        let parts: Vec<String> = (0..n).map(|k| self.coerce(format!("{r}.items[{k}]"), fe, c)).collect::<R<_>>()?;
                        (n, format!("[{}]", parts.iter().map(|p| format!("{p},")).collect::<String>()))
                    }
                    _ => {
                        let ts: Vec<Ty> = tuple_elems(to).unwrap().into_iter().cloned().collect();
                        let parts: Vec<String> =
                            ts.iter().enumerate().map(|(k, t)| self.coerce(format!("{r}.items[{k}]"), fe, t)).collect::<R<_>>()?;
                        (ts.len(), rec_build(&parts))
                    }
                };
                Ok(format!(
                    "{{ let {r} = {code}; if {r}.len as usize != {n} {{ eval_error(format!(\"a sequence of length {{}} is used where one of length {n} is expected\", {r}.len)) }} {body} }}"
                ))
            }
            (Ty::Rec(fs), Ty::Fun(d, c)) if is_tuple_fields(fs) && seq_domain(d) == Some(fs.len()) => {
                let r = self.fresh("r");
                let parts: Vec<String> = fs.iter().enumerate().map(|(k, (_, t))| self.coerce(format!("{r}{}", rec_field(fs.len(), k)), t, c)).collect::<R<_>>()?;
                Ok(format!("{{ let {r} = {code}; [{}] }}", parts.iter().map(|p| format!("{p},")).collect::<String>()))
            }
            (Ty::Fun(d, c), Ty::Rec(fs)) if is_tuple_fields(fs) && seq_domain(d) == Some(fs.len()) => {
                let r = self.fresh("r");
                let parts: Vec<String> = fs.iter().enumerate().map(|(k, (_, t))| self.coerce(format!("{r}[{k}]"), c, t)).collect::<R<_>>()?;
                Ok(format!("{{ let {r} = {code}; {} }}", rec_build(&parts)))
            }
            (Ty::Enum(_), Ty::IntAtom(..)) => Ok(format!("(i64::MIN + ({code}) as i64)")),
            (Ty::IntAtom(..), Ty::Enum(_)) => {
                let a = self.fresh("a");
                Ok(format!(
                    "{{ let {a} = {code}; if {a} >= i64::MIN + 65536 {{ eval_error(format!(\"the integer {{}} is used where a model value is expected\", {a})) }} ({a} - i64::MIN) as u16 }}"
                ))
            }
            _ if from.kind_eq(to) => Ok(code),
            _ => Err(format!("type mismatch: cannot use {from:?} as {to:?}")),
        }
    }

    /// A value of type `from` as one of the record type with fields `fs` that holds it in `field`
    /// (see types::ATOM_FIELD, VAL_FIELD), with the other fields absent
    fn box_into(&mut self, code: String, from: &Ty, fs: &[(String, Ty)], field: &str) -> R<String> {
        let mut parts = vec![];
        for (n, ft) in fs {
            parts.push(match ft {
                Ty::Opt(inner) if n == field => format!("(true, {})", self.coerce(code.clone(), from, inner)?),
                ft => Self::default_code(ft),
            });
        }
        Ok(rec_build(&parts))
    }

    /// The value in `field` (types::ATOM_FIELD or VAL_FIELD) of a value of the record type `t`, and
    /// its type: where a value of one kind is needed (a function applied, a set iterated, a model
    /// value compared with one), any other value stops the checker with an error
    fn unbox(&mut self, code: String, t: &Ty, field: &str) -> R<(String, Ty)> {
        let Ty::Rec(fs) = t else { unreachable!() };
        let i = fs.iter().position(|(n, _)| n == field).ok_or(format!("{t:?} has no field {field}"))?;
        let Ty::Opt(inner) = &fs[i].1 else { unreachable!() };
        let kind = match inner.as_ref() {
            Ty::Enum(_) => "a model value",
            Ty::Bool => "a Boolean",
            Ty::Set(_) => "a set",
            Ty::Seq(_) | Ty::Rec(_) => "a sequence",
            Ty::Bag(_) => "a bag",
            _ => "a function",
        };
        let tid = self.ty_id(t)?;
        let (fp, u) = (rec_field(fs.len(), i), self.fresh("u"));
        let msg = format!("The value {{}} is used where {kind} is expected");
        Ok((
            format!("{{ let {u} = {code}; if !{u}{fp}.0 {{ eval_error(format!({msg:?}, fmt_{tid}(&{u}))) }} {u}{fp}.1 }}"),
            inner.as_ref().clone(),
        ))
    }

    /// An expression whose value is applied or taken apart: a value that may also be a model value
    /// (see types::VAL_FIELD) is used as the value of the other kind
    fn gen_val(&mut self, e: &Expr, env: &Env) -> R<(String, Ty)> {
        let (c, t) = self.gen(e, env, None)?;
        self.val_of(c, t)
    }

    fn val_of(&mut self, c: String, t: Ty) -> R<(String, Ty)> {
        match &t {
            Ty::Rec(fs) if crate::types::has_val(fs) => self.unbox(c, &t, crate::types::VAL_FIELD),
            _ => Ok((c, t)),
        }
    }

    pub fn gen_as(&mut self, e: &Expr, env: &Env, t: &Ty) -> R<String> {
        let (c, got) = self.gen(e, env, Some(t))?;
        self.coerce(c, &got, t)
    }

    /// Uses the expected type if it subsumes the join, otherwise the join itself
    fn layout(want: Option<&Ty>, j: Ty) -> Ty {
        if let Some(w) = want {
            // A value that may also be a model value is not a layout of the value alone
            if crate::types::val_ty(w).is_some() && crate::types::val_ty(&j).is_none() {
                return j;
            }
            if join(w, &j).ok().as_ref() == Some(w) {
                return w.clone();
            }
        }
        j
    }

    // ---------------------------------------------------------------- Expressions

    pub fn gen(&mut self, e: &Expr, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        let (c, t) = self.gen_inner(e, env, want)?;
        // An operation TLC performs inside a value built from what is written there, when it can
        // fail (see FpSource in the runtime). A string compared with a tuple fails in the string's
        // own comparison, which TLC does not report so (`<<"a">> \in {"ab"}`, measured)
        let can_fail = c.contains("eval_error") || c.contains("mixed_eq(");
        if can_fail && !c.contains("Attempted to check equality of string") && self.fp_source(e, env) {
            return Ok((format!("{{ let __fp = FpSource::enter(); {c} }}"), t));
        }
        Ok((c, t))
    }

    /// Whether TLC evaluates e by asking a value built from an expression written in the spec
    /// (a set, tuple or record written out, a set of functions or records, a product, or set
    /// operations on those): membership in it, whether it is a subset, or applying it. Not `=`:
    /// `<<1, 2>> # s` fails in the tuple's comparison, which TLC does not report so (measured)
    fn fp_source(&mut self, e: &Expr, env: &Env) -> bool {
        use Expr::*;
        match e.strip() {
            Bin(BOp::In | BOp::NotIn, _, s) => self.built(s, env),
            Bin(BOp::Subseteq, a, _) => self.built(a, env),
            App(f, _) => self.built(f, env),
            _ => false,
        }
    }

    /// Whether TLC builds the value of e from e as written when it evaluates e (a definition of
    /// constant level has a value computed when TLC starts)
    fn built(&mut self, e: &Expr, env: &Env) -> bool {
        use Expr::*;
        match e {
            Label(n, _, b) if n.starts_with('#') => self.built(b, env),
            Label(_, _, b) => !self.is_const(e, env) && self.built(b, env),
            SetLit(_) | Tuple(_) | RecLit(_) => true,
            // TLC holds a set of functions or records it can enumerate as the set of its elements,
            // which it does not count as built there (`k \notin [{1} -> {1}]`, measured)
            RecSet(_) | FunSet(..) => self.try_const(e, env).is_none(),
            Call(f, _) => f == "\\X",
            Bin(BOp::Cup | BOp::Cap | BOp::SetMinus, a, b) => self.built(a, env) || self.built(b, env),
            _ => false,
        }
    }

    fn gen_inner(&mut self, e: &Expr, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        // The index of an EXCEPT outside a tuple (see EXCEPT_WARN)
        if let Expr::Label(n, _, b) = e {
            if let Some(at) = n.strip_prefix(EXCEPT_WARN) {
                let (c, t) = self.gen(b, env, want)?;
                return Ok((format!("{{ except_warning({at:?}); {c} }}"), t));
            }
        }
        use Expr::*;
        // A definition of constant level: its value (see is_const)
        if matches!(e, Label(..)) {
            if let (Some(v), made) = self.try_const_made(e, env) {
                let (c, t) = self.lit_auto(&v, want)?;
                return Ok((self.note_folded(c, &made), t));
            }
        }
        if let Label(n, pairs, body) = e {
            if is_bind(n) {
                let (lets, env2, body) = self.gen_bind(pairs, body, env)?;
                let (c, t) = self.gen(&body, &env2, want)?;
                // The value is kept in a variable: a temporary at the end of the block that
                // borrows a cell (an iterator over the bound set) would outlive it
                return Ok((if lets.is_empty() { c } else { format!("{{ {lets}let __bv = {c}; __bv }}") }, t));
            }
        }
        // An operator of the CommunityModules evaluated only when compiling (see ast::CONST_ONLY)
        let mut x = e;
        while let Label(n, _, b) = x {
            if let Some(why) = n.strip_prefix(crate::ast::CONST_ONLY) {
                return Err(why.to_string());
            }
            x = b;
        }
        // Where a CASE or CHOOSE is written, for TLC's error message (see ast::AT)
        let at = err_at(e);
        let e = e.strip();
        // A constant bag is built by SetToBag below, which gives it the type of a bag (its value
        // alone is a function, over part of a type when its elements are records with different
        // fields)
        let bag = matches!(e, Call(f, _) if f == "SetToBag");
        if !bag {
            if let (Some(v), made) = self.try_const_made(e, env) {
                let (c, t) = self.lit_auto(&v, want)?;
                return Ok((self.note_folded(c, &made), t));
            }
        }
        // A constant comparison that TLC fails to evaluate fails when the checker evaluates it
        if matches!(e, Bin(BOp::Eq | BOp::Neq | BOp::In | BOp::NotIn, ..)) && self.is_const(e, env) {
            if let Err(m) = self.ce.eval(e, &HashMap::new()) {
                if crate::value::is_eval_failure(&m) {
                    return Ok((eval_error_bool(&m), Ty::Bool));
                }
            }
        }
        Ok(match e {
            Ident(n, _) => {
                if let Some((c, t)) = env.locals.get(n) {
                    (c.clone(), t.clone())
                } else if self.is_var(n) {
                    if env.init {
                        env.primed.get(n).cloned().ok_or(format!("Init reads `{n}` before assigning it"))?
                    } else {
                        (format!("s.v_{n}"), self.var_ty(n))
                    }
                } else if n == "EmptyBag" {
                    let t = match want {
                        Some(Ty::Bag(e)) => Ty::Bag(e.clone()),
                        _ => Ty::Bag(Ty::Enum(vec![]).into()),
                    };
                    (Self::default_code(&t), t)
                } else if n == "JavaTime" {
                    return Err("JavaTime is not supported: it reads the clock, so no two runs agree".into());
                } else if let Some(x) = crate::value::bound_expr(n) {
                    // A name a BIND label binds and code generation writes out, read in the body of
                    // a recursive operator (see `gen_bind`)
                    return self.gen(&x, env, want);
                } else {
                    return Err(format!("unknown identifier `{n}` (missing CONSTANT in cfg?)"));
                }
            }
            At => env.locals.get("@").cloned().ok_or("`@` outside EXCEPT")?,
            // A substituted variable of an instance: what it stands for, primed; while computing
            // whether an action is enabled, the value bound to its name (see gen_action)
            Prime(x) if crate::ast::subvar_of(x).is_some() => {
                let (n, b) = crate::ast::subvar_of(x).unwrap();
                if !env.phantom {
                    return self.gen(&Prime(b.clone().b()), env, want);
                }
                match env.locals.get(&phantom(n)) {
                    Some(x) => x.clone(),
                    // Not bound yet: TLC fails on evaluation, naming the variable
                    None => {
                        let (_, t) = self.gen(b, env, want)?;
                        let mut msg = undefined_ident(n, &NOPOS);
                        if let Some(at) = crate::ast::subvar_pos(x) {
                            msg = format!("{msg}\n{at}");
                        }
                        (format!("{{ let __v: {} = eval_error({msg:?}.into()); __v }}", t.repr()), t)
                    }
                }
            }
            Prime(x) => match x.strip() {
                Ident(n, at) if self.is_var(n) => match env.primed.get(n) {
                    Some(x) => x.clone(),
                    // As in TLC, fail only on evaluation (harmless if the branch is never reached)
                    None => {
                        let t = self.var_ty(n);
                        (format!("{{ let __v: {} = eval_error({:?}.into()); __v }}", t.repr(), undefined_ident(n, at)), t)
                    }
                },
                x => {
                    let primed = self.prime_vars(x);
                    return self.gen(&primed, env, want);
                }
            },
            Call(f, args) => match (f.as_str(), args.as_slice()) {
                ("TLCEval", [x]) => self.gen(x, env, want)?,
                (FORALL_NTH, [s, k]) => {
                    let (it, et, ix) = self.iter_of_indexed(s, env)?;
                    let kc = self.gen_as(k, env, &Ty::Int(1, BIG))?;
                    let val = match ix {
                        Some(_) => format!("dec_{}(__e)", self.ty_id(&et)?),
                        None => "__e".into(),
                    };
                    (format!("{{ let __e = {it}.nth(({kc} - 1) as usize).unwrap(); {val} }}"), et)
                }
                // An unbounded quantifier or CHOOSE: TLC stops when it evaluates one
                (f, []) if crate::parser::unbounded_error(f).is_some() => {
                    let t = want.cloned().unwrap_or(if f.contains("CHOOSE") { Ty::Enum(vec![]) } else { Ty::Bool });
                    let msg = crate::parser::unbounded_error(f).unwrap();
                    (format!("{{ let __v: {} = eval_error({msg:?}.to_string()); __v }}", t.repr()), t)
                }
                // ToString of a value from the state: a table, indexed by the value's encoding, of
                // the strings of every value of its type, interned now
                // ToString of a value from the state: the string of every value of its type is
                // interned now. A Boolean, integer, string, model value or tuple of them indexes a
                // table by its encoding; other values print at run time and look their string up.
                // ToString of a function over a set TLC cannot enumerate: its text, the same each time
                ("ToString", [x]) if self.lazy_fun_shown(x, env).is_some() => {
                    let s = self.lazy_fun_shown(x, env).unwrap();
                    let id = self.atoms.intern(false, &s);
                    let code = self.lit(&Value::Atom(id), &Ty::Enum(vec![id]))?;
                    return Ok((self.note_made(code, &[id]), Ty::Enum(vec![id])));
                }
                ("ToString", [x]) => {
                    let (c, t) = self.gen(x, env, None)?;
                    fn scalar_or_tuple(t: &Ty) -> bool {
                        match t {
                            Ty::Bool | Ty::Int(..) | Ty::Enum(_) | Ty::IntAtom(..) => true,
                            Ty::Rec(fs) => is_tuple_fields(fs) && fs.iter().all(|(_, t)| scalar_or_tuple(t)),
                            _ => false,
                        }
                    }
                    if let Some((a, b)) = disordered_ty(&t) {
                        return Err(crate::types::disordered_error(&a, &b));
                    }
                    let room = (1usize << 16).saturating_sub(self.atoms.len());
                    let tid = self.ty_id(&t)?;
                    let too_many = || {
                        format!(
                            "ToString of {}: its type {t:?} has more values than the {room} strings that can still be added (strings are 16-bit ids; -setcap and -seqcap bound sets and sequences)",
                            short(x)
                        )
                    };
                    if scalar_or_tuple(&t) {
                        let n = t.size().filter(|&n| n <= room as u64).ok_or_else(too_many)?;
                        let ids: Vec<u32> = t.enumerate().iter().map(|v| self.atoms.intern(false, &crate::compile::show_value(self.atoms, v))).collect();
                        let table: Vec<String> = ids.iter().map(|i| i.to_string()).collect();
                        let mut res = ids.clone();
                        res.sort();
                        res.dedup();
                        let code = format!("{{ const T: [u16; {n}] = [{}]; T[idx_{tid}({c})] }}", table.join(", "));
                        return Ok((self.note_made(code, &res), Ty::Enum(res)));
                    }
                    let vals = crate::types::all_values(&t, self.qcap, self.scap, room).ok_or_else(too_many)?;
                    let mut table: Vec<(String, u32)> = vals
                        .iter()
                        .map(|v| {
                            let s = crate::compile::show_value(self.atoms, v);
                            let id = self.atoms.intern(false, &s);
                            (s, id)
                        })
                        .collect();
                    table.sort();
                    table.dedup();
                    let mut res: Vec<u32> = table.iter().map(|(_, i)| *i).collect();
                    res.sort();
                    res.dedup();
                    let rows: Vec<String> = table.iter().map(|(s, i)| format!("({s:?}, {i})")).collect();
                    let code = format!(
                        "{{ static T: [(&str, u16); {}] = [{}]; let __k = fmt_{tid}(&{c}); match T.binary_search_by(|(s, _)| (*s).cmp(__k.as_str())) {{ \
                         Ok(__i) => T[__i].1, Err(_) => eval_error(format!(\"ToString of {{__k}}: TLC prints this value in a way that depends on how it was built (an empty function prints as << >> or <<>>)\")) }} }}",
                        rows.len(),
                        rows.join(", ")
                    );
                    (self.note_made(code, &res), Ty::Enum(res))
                }
                ("RandomElement", [SetLit(xs)]) if xs.len() == 1 => self.gen(&xs[0], env, want)?,
                ("RandomElement", _) => return Err("RandomElement over a set from the state is not supported: TLC picks an element at random".into()),
                ("TLCGet" | "TLCSet", _) => return Err(format!("{f} is not supported: it reads or writes TLC's search state")),
                ("IsFiniteSet", [s]) => {
                    let (c, t) = self.gen(s, env, None)?;
                    if !matches!(t, Ty::Set(_)) {
                        return Err("IsFiniteSet of a non-set".into());
                    }
                    (format!("{{ let _ = {c}; true }}"), Ty::Bool)
                }
                ("Assert", [p, m]) => {
                    let pc = self.gen_as(p, env, &Ty::Bool)?;
                    let shown = match self.try_const(m, env) {
                        Some(v) => crate::compile::show_value(self.atoms, &v),
                        None => short(m),
                    };
                    let msg = format!("The first argument of Assert evaluated to FALSE; the second argument was:\n{shown}");
                    (format!("(if {pc} {{ true }} else {{ assert_error({msg:?}.to_string()) }})"), Ty::Bool)
                }
                // Print and PrintT write to stdout as TLC does, when the checker evaluates them
                // (d :> e) @@ f, with f over a whole type that d's type lies in: f with the entry at
                // d replaced. Otherwise :> and @@ build a function over part of a type (below).
                ("@@", [l, f])
                    if matches!(l.strip(), Call(op, a) if op == ":>" && a.len() == 2)
                        && matches!(self.gen(f, env, want), Ok((_, Ty::Fun(fd, _))) if {
                            let Call(_, de) = l.strip() else { unreachable!() };
                            matches!(self.gen(&de[0], env, None), Ok((_, kt)) if join(&kt, &fd).is_ok_and(|j| j == *fd))
                        }) =>
                {
                    let Call(_, de) = l.strip() else { unreachable!() };
                    let (fc, ft) = self.gen(f, env, want)?;
                    let Ty::Fun(d, c) = &ft else { return Err("@@ of a value that is not a function".into()) };
                    let did = self.ty_id(d)?;
                    let kc = self.gen_as(&de[0], env, d)?;
                    let vc = self.gen_as(&de[1], env, c)?;
                    let (t, i) = (self.fresh("t"), self.fresh("i"));
                    (
                        format!("{{ let mut {t} = {fc}; let {i} = enc_{did}({kc}); if {i} == u64::MAX {{ type_error(\"function argument\", \"\") }} {t}[{i} as usize] = {vc}; {t} }}"),
                        ft,
                    )
                }
                // d :> e over values from the state: a function over part of d's type
                (":>", [d, v]) => {
                    let (dc, dt) = self.gen(d, env, None)?;
                    let (vc, vt) = self.gen(v, env, None)?;
                    let ft = Ty::PFun(dt.clone().into(), vt.into());
                    self.ty_id(&ft)?;
                    let put = self.fun_put("__o", &dc, &vc, &ft)?;
                    (format!("{{ let mut __o = {}; {put} __o }}", Self::default_code(&ft)), ft)
                }
                // f @@ g: f where it is defined, g elsewhere
                ("@@", [a, b]) => {
                    let (ac, at) = self.gen(a, env, None)?;
                    let (ac, at) = self.rec_as_fun(ac, at, env)?;
                    let (bc, bt) = self.gen(b, env, None)?;
                    let (bc, bt) = self.rec_as_fun(bc, bt, env)?;
                    let (ad, acod) = pfun_parts(&at).ok_or(format!("@@ of {at:?}, which is not a function"))?;
                    let (bd, bcod) = pfun_parts(&bt).ok_or(format!("@@ of {bt:?}, which is not a function"))?;
                    let ft = Ty::PFun(join(&ad, &bd)?.into(), join(&acod, &bcod)?.into());
                    let ac = self.coerce(ac, &at, &ft)?;
                    let bc = self.coerce(bc, &bt, &ft)?;
                    if is_sparse_fun(&ft) {
                        return Ok((format!("{{ let (mut __a, __b) = ({ac}, {bc}); for (__k, __v) in __b.iter() {{ if __a.get(&__k).is_none() {{ __a.put(__k, __v); }} }} __a }}"), ft));
                    }
                    (format!("{{ let (mut __a, __b) = ({ac}, {bc}); for __i in 0..__a.len() {{ if !__a[__i].0 {{ __a[__i] = __b[__i]; }} }} __a }}"), ft)
                }
                // Permutations of a set from the state: every bijection of it onto itself
                ("Permutations", [x]) => {
                    let (c, t) = self.gen(x, env, None)?;
                    let Ty::Set(et) = &t else { return Err("Permutations of a non-set".into()) };
                    let ft = Ty::PFun(et.clone(), et.clone());
                    let st = Ty::Set(ft.clone().into());
                    let it = self.s_iter(&c, &t)?;
                    let empty = self.s_empty(&st)?;
                    let add = self.s_add("__s", "__f", &st)?;
                    let put = self.fun_put("__f", "__e[__k]", "__e[__p[__k]]", &ft)?;
                    (
                        format!(
                            "{{ let __e: Vec<{}> = {it}.collect(); let mut __s = {empty}; let mut __p: Vec<usize> = (0..__e.len()).collect(); \
                             loop {{ let mut __f = {}; for __k in 0..__e.len() {{ {put} }} {add} \
                             let mut __k = __p.len(); while __k > 1 && __p[__k - 2] >= __p[__k - 1] {{ __k -= 1; }} if __k <= 1 {{ break; }} \
                             let mut __l = __p.len() - 1; while __p[__l] <= __p[__k - 2] {{ __l -= 1; }} __p.swap(__k - 2, __l); __p[__k - 1..].reverse(); }} __s }}",
                            et.repr(),
                            Self::default_code(&ft)
                        ),
                        st,
                    )
                }
                ("PrintT", [x]) if self.lazy_fun_shown(x, env).is_some() => {
                    let s = self.lazy_fun_shown(x, env).unwrap();
                    (format!("{{ tlc_print(ppr({s:?})); true }}"), Ty::Bool)
                }
                ("Print", [x, v]) if self.lazy_fun_shown(x, env).is_some() => {
                    let s = self.lazy_fun_shown(x, env).unwrap();
                    let (vc, vt) = self.gen(v, env, want)?;
                    let vid = self.ty_id(&vt)?;
                    (format!("{{ let __v = {vc}; tlc_print(format!(\"{{}}  {{}}\", ppr({s:?}), ppr(&fmt_{vid}(&__v)))); __v }}"), vt)
                }
                ("PrintT", [x]) => {
                    let (c, t) = self.gen(x, env, None)?;
                    let id = self.ty_id(&t)?;
                    (format!("{{ tlc_print(ppr(&fmt_{id}(&{c}))); true }}"), Ty::Bool)
                }
                // TLC prints both arguments, two spaces apart
                ("Print", [x, v]) => {
                    let (c, t) = self.gen(x, env, None)?;
                    let id = self.ty_id(&t)?;
                    let (vc, vt) = self.gen(v, env, want)?;
                    let vid = self.ty_id(&vt)?;
                    (format!("{{ let __x = {c}; let __v = {vc}; tlc_print(format!(\"{{}}  {{}}\", ppr(&fmt_{id}(&__x)), ppr(&fmt_{vid}(&__v)))); __v }}"), vt)
                }
                ("^", [a, b]) => {
                    let (ac, (alo, ahi)) = self.gen_int_of("Expt", false, false, a, env)?;
                    let (bc, (blo, bhi)) = self.gen_int_of("Expt", false, false, b, env)?;
                    // Monotone in both arguments when both are natural numbers
                    let t = match (alo >= 0, int_pow(alo, blo.max(0)), int_pow(ahi, bhi)) {
                        (true, Some(lo), Some(hi)) if hi <= BIG => Ty::Int(if alo == 0 { 0 } else { lo }, hi.max(1)),
                        _ => Ty::Int(-BIG, BIG),
                    };
                    (
                        format!("{{ let (__a, __b): (i64, i64) = ({ac}, {bc}); if __b < 0 {{ arith_error(format!(\"{{}}^{{}}: the exponent must be a natural number\", __a, __b)) }} match __a.checked_pow(__b as u32) {{ Some(v) => v, None => arith_error(format!(\"{{}}^{{}} overflows\", __a, __b)) }} }}"),
                        t,
                    )
                }
                ("SetToBag", [x]) => {
                    let (c, t) = self.gen(x, env, None)?;
                    let Ty::Set(e) = &t else { return Err("SetToBag of a non-set".into()) };
                    let bt = Ty::Bag(e.clone());
                    self.ty_id(&bt)?;
                    let it = self.s_iter(&c, &t)?;
                    let put = self.fun_put("__b", "__x", "1", &bt)?;
                    (format!("{{ let mut __b = {}; for __x in {it} {{ {put} }} __b }}", Self::default_code(&bt)), bt)
                }
                ("BagToSet", [b]) => self.bag_domain(b, env)?,
                ("BagIn" | "CopiesIn", [x, b]) => {
                    let (bc, e) = self.bag_of(b, env, None)?;
                    let xc = self.gen_as(x, env, &e)?;
                    let count = self.bag_count("__b", "__x", &Ty::Bag(e.into()))?;
                    let get = format!("{{ let __b = {bc}; let __x = {xc}; {count} }}");
                    if f == "BagIn" {
                        (format!("({get} > 0)"), Ty::Bool)
                    } else {
                        (get, Ty::Int(0, BIG))
                    }
                }
                ("\\oplus" | "\\ominus" | "\\sqsubseteq", [a, b]) if self.is_bag(a, env) || self.is_bag(b, env) => {
                    let (_, ea) = self.bag_of(a, env, None)?;
                    let (_, eb) = self.bag_of(b, env, None)?;
                    let e = join(&ea, &eb)?;
                    let (ac, _) = self.bag_of(a, env, Some(&e))?;
                    let (bc, _) = self.bag_of(b, env, Some(&e))?;
                    let bt = Ty::Bag(e.into());
                    self.ty_id(&bt)?;
                    if is_sparse_fun(&bt) {
                        return Ok(match f.as_str() {
                            "\\oplus" => (format!("{{ let (mut __a, __b) = ({ac}, {bc}); for (__k, __c) in __b.iter() {{ let __n = __a.get(&__k).unwrap_or(0) + __c; __a.put(__k, __n); }} __a }}"), bt),
                            "\\ominus" => (
                                format!("{{ let (mut __a, __b) = ({ac}, {bc}); for (__k, __c) in __b.iter() {{ let __n = __a.get(&__k).unwrap_or(0) - __c; if __n > 0 {{ __a.put(__k, __n); }} else {{ __a.del(&__k); }} }} __a }}"),
                                bt,
                            ),
                            _ => (format!("{{ let (__a, __b) = ({ac}, {bc}); let __le = __a.iter().all(|(__k, __c)| __c <= __b.get(&__k).unwrap_or(0)); __le }}"), Ty::Bool),
                        });
                    }
                    match f.as_str() {
                        "\\oplus" => (format!("{{ let (mut __a, __b) = ({ac}, {bc}); for __i in 0..__a.len() {{ __a[__i] += __b[__i]; }} __a }}"), bt),
                        "\\ominus" => (format!("{{ let (mut __a, __b) = ({ac}, {bc}); for __i in 0..__a.len() {{ __a[__i] = (__a[__i] - __b[__i]).max(0); }} __a }}"), bt),
                        _ => (format!("{{ let (__a, __b) = ({ac}, {bc}); let __le = __a.iter().zip(__b.iter()).all(|(x, y)| x <= y); __le }}"), Ty::Bool),
                    }
                }
                // A function whose values are positive integers (an atom is held below every integer)
                ("IsABag", [b]) => {
                    let (c, t) = self.gen(b, env, None)?;
                    let ints = |t: &Ty| matches!(t, Ty::Int(..) | Ty::IntAtom(..));
                    let test = match &t {
                        Ty::Bag(_) => "true".to_string(),
                        Ty::Bool | Ty::Int(..) | Ty::IntAtom(..) | Ty::Enum(_) | Ty::Set(_) => "false".into(),
                        Ty::Fun(_, r) if ints(r) => "__b.iter().all(|&x| x > 0)".into(),
                        Ty::Seq(r) if ints(r) => "__b.iter().all(|x| x > 0)".into(),
                        Ty::Fun(_, r) if !ints(r) => "__b.len() == 0".into(),
                        Ty::Seq(r) if !ints(r) => "__b.len == 0".into(),
                        Ty::Rec(fs) if !fs.iter().any(|(_, t)| matches!(t, Ty::Opt(_))) => {
                            let parts: Vec<String> = fs
                                .iter()
                                .enumerate()
                                .map(|(k, (_, ft))| if ints(ft) { format!("__b{} > 0", rec_field(fs.len(), k)) } else { "false".into() })
                                .collect();
                            if parts.is_empty() { "true".into() } else { parts.join(" && ") }
                        }
                        _ => return Err(format!("IsABag of {t:?} is not supported")),
                    };
                    (format!("{{ let __b = {c}; let _ = &__b; let __r: bool = {test}; __r }}"), Ty::Bool)
                }
                ("BagCardinality", [b]) => {
                    let (bc, e) = self.bag_of(b, env, None)?;
                    if is_sparse_fun(&Ty::Bag(e.into())) {
                        return Ok((format!("{{ let __b = {bc}; let __n: i64 = __b.iter().map(|(_, __c)| __c).sum(); __n }}"), Ty::Int(0, BIG)));
                    }
                    (format!("{{ let __b = {bc}; let __n: i64 = __b.iter().sum(); __n }}"), Ty::Int(0, BIG))
                }
                ("BagUnion", [s]) => {
                    let (c, t) = self.gen(s, env, None)?;
                    let Ty::Set(bt) = &t else { return Err("BagUnion of a non-set".into()) };
                    let Ty::Bag(_) = bt.as_ref() else { return Err("BagUnion of a set of values that are not bags".into()) };
                    let it = self.s_iter(&c, &t)?;
                    if is_sparse_fun(bt) {
                        return Ok((
                            format!("{{ let mut __a = {}; for __b in {it} {{ for (__k, __c) in __b.iter() {{ let __n = __a.get(&__k).unwrap_or(0) + __c; __a.put(__k, __n); }} }} __a }}", Self::default_code(bt)),
                            bt.as_ref().clone(),
                        ));
                    }
                    (format!("{{ let mut __a = {}; for __b in {it} {{ for __i in 0..__a.len() {{ __a[__i] += __b[__i]; }} }} __a }}", Self::default_code(bt)), bt.as_ref().clone())
                }
                ("BagOfAll", [Lambda(ps, body), b]) if ps.len() == 1 => {
                    let (bc, e) = self.bag_of(b, env, None)?;
                    let eid = self.ty_id(&e)?;
                    let mut env2 = env.clone();
                    let x = rid(&ps[0]);
                    env2.locals.insert(ps[0].clone(), (x.clone(), e.clone()));
                    let (yc, yt) = self.gen(body, &env2, None)?;
                    let rt = Ty::Bag(yt.clone().into());
                    self.ty_id(&rt)?;
                    let yid = self.ty_id(&yt)?;
                    if let Some(msg) = crate::value::bag_of_all_literal(self.atoms, body) {
                        return Ok((format!("{{ let _ = {bc}; let __v: {} = eval_error({msg:?}.to_string()); __v }}", rt.repr()), rt));
                    }
                    let bt = Ty::Bag(e.into());
                    if is_sparse_fun(&bt) || is_sparse_fun(&rt) {
                        let it = self.fun_iter("__b", &bt, false)?;
                        let count = self.bag_count("__r", "__y", &rt)?;
                        let put = self.fun_put("__r", "__y", &format!("{count} + __c"), &rt)?;
                        return Ok((format!("{{ let __b = {bc}; let mut __r = {}; for ({x}, __c) in {it} {{ let __y = {yc}; {put} }} __r }}", Self::default_code(&rt)), rt));
                    }
                    (
                        format!("{{ let __b = {bc}; let mut __r = {}; for __i in 0..__b.len() {{ if __b[__i] > 0 {{ let {x} = dec_{eid}(__i as u64); __r[idx_{yid}({yc})] += __b[__i]; }} }} __r }}", Self::default_code(&rt)),
                        rt,
                    )
                }
                // Every bag whose counts are at most b's, collected into a set of bags
                ("SubBag", [b]) => {
                    let (bc, e) = self.bag_of(b, env, None)?;
                    let bt = Ty::Bag(e.into());
                    let st = Ty::Set(bt.clone().into());
                    let empty = self.s_empty(&st)?;
                    if is_sparse_fun(&bt) {
                        // A counter per element of b, each counting up to its count in b
                        let add = self.s_add("__s", "__g", &st)?;
                        let (kt, _) = fun_kv(&bt);
                        return Ok((
                            format!(
                                "{{ let __b = {bc}; let __e: Vec<({}, i64)> = __b.iter().collect(); let mut __s = {empty}; let mut __c = vec![0i64; __e.len()]; \
                                 loop {{ let mut __g = {}; for __k in 0..__e.len() {{ if __c[__k] > 0 {{ __g.put(__e[__k].0, __c[__k]); }} }} {add} \
                                 let mut __k = 0; while __k < __e.len() {{ if __c[__k] < __e[__k].1 {{ __c[__k] += 1; break; }} __c[__k] = 0; __k += 1; }} \
                                 if __k == __e.len() {{ break; }} }} __s }}",
                                kt.repr(),
                                Self::default_code(&bt)
                            ),
                            st,
                        ));
                    }
                    let add = self.s_add("__s", "__c", &st)?;
                    (
                        format!(
                            "{{ let __b = {bc}; let mut __s = {empty}; let mut __c = {}; loop {{ {add} \
                             let mut __k = 0; while __k < __b.len() {{ if __c[__k] < __b[__k] {{ __c[__k] += 1; break; }} __c[__k] = 0; __k += 1; }} \
                             if __k == __b.len() {{ break; }} }} __s }}",
                            Self::default_code(&bt)
                        ),
                        st,
                    )
                }
                // Counted without building the set (which could outgrow a sparse set's capacity)
                ("Cardinality", [s]) if matches!(s.strip(), Call(f, _) if f == "\\X") && self.try_const(s, env).is_none() => {
                    let Call(_, parts) = s.strip() else { unreachable!() };
                    let mut codes = vec![];
                    for p in parts {
                        let (c, _) = self.gen(&Call("Cardinality".into(), vec![p.clone()]), env, None)?;
                        codes.push(format!("({c})"));
                    }
                    (format!("({})", codes.join(" * ")), Ty::Int(0, BIG))
                }
                ("Cardinality", [s]) if matches!(s.strip(), Bin(BOp::Range, ..)) && self.try_const(s, env).is_none() => {
                    let Bin(_, a, b) = s.strip() else { unreachable!() };
                    let (ac, (alo, _)) = self.gen_int(a, env)?;
                    let (bc, (_, bhi)) = self.gen_int(b, env)?;
                    (format!("(({bc}) - ({ac}) + 1).max(0)"), Ty::Int(0, (bhi as i128 - alo as i128 + 1).clamp(0, BIG as i128) as i64))
                }
                ("Cardinality", [s]) if matches!(s.strip(), Un(UOp::Subset, _)) && self.try_const(s, env).is_none() => {
                    let Un(_, x) = s.strip() else { unreachable!() };
                    let (c, t) = self.gen(x, env, None)?;
                    let Ty::Set(el) = &t else { return Err("SUBSET of a non-set".into()) };
                    let n = if is_sparse(&t) { crate::types::set_cap(&t, self.scap) as u32 } else { el.size().unwrap_or(0) as u32 };
                    let hi = if n >= 62 { BIG } else { 1i64 << n };
                    (format!("(1i64 << {})", self.s_card(&c, &t)), Ty::Int(1, hi))
                }
                ("Cardinality", [s]) => {
                    let (c, t) = self.gen_val(s, env)?;
                    let Ty::Set(el) = &t else { return Err("Cardinality of a non-set".into()) };
                    let hi = if is_sparse(&t) { BIG } else { el.size().unwrap_or(0) as i64 };
                    (self.s_card(&c, &t), Ty::Int(0, hi))
                }
                // A product of sets from the state, as a value: its tuples collected into a set
                ("\\X", _) => {
                    let (it, et, ix) = self.iter_of_indexed(e, env)?;
                    let st = Ty::Set(et.clone().into());
                    let acc = self.fresh("acc");
                    let x = self.fresh("x");
                    let val = match ix {
                        Some(_) => format!("dec_{}({x})", self.ty_id(&et)?),
                        None => x.clone(),
                    };
                    let add = self.s_add(&acc, &val, &st)?;
                    let empty = self.s_empty(&st)?;
                    (format!("{{ let mut {acc} = {empty}; for {x} in {it} {{ {add} }} {acc} }}"), st)
                }
                // A string from the state as a sequence of characters: the result for every string
                // the operand can be is computed here, and looked up at run time
                ("Len" | "Head" | "Tail", [q]) if matches!(self.gen(q, env, None), Ok((_, Ty::Enum(_)))) => {
                    let (c, t) = self.gen(q, env, None)?;
                    let Ty::Enum(d) = &t else { unreachable!() };
                    self.string_table(f, &c, &[(d.clone(), None)])?
                }
                ("SubSeq", [q, m, n]) if matches!(self.gen(q, env, None), Ok((_, Ty::Enum(_)))) => {
                    let (qc, qt) = self.gen(q, env, None)?;
                    let Ty::Enum(d) = &qt else { unreachable!() };
                    let (mc, _) = self.gen_int(m, env)?;
                    let (nc, _) = self.gen_int(n, env)?;
                    self.substring_table(&qc, d, &mc, &nc)?
                }
                ("Append" | "\\o", [a, b]) if matches!(self.gen(a, env, None), Ok((_, Ty::Enum(_)))) => {
                    let (ac, at) = self.gen(a, env, None)?;
                    let (bc, bt) = self.gen(b, env, None)?;
                    let (Ty::Enum(da), Ty::Enum(db)) = (&at, &bt) else {
                        // TLC stops with an error when it evaluates this
                        let Ty::Enum(da) = &at else { unreachable!() };
                        let bid = self.ty_id(&bt)?;
                        let msg = "Evaluating an expression of the form t \\o s when s is not a string:\n{}";
                        return Ok((format!("{{ let _ = {ac}; let __b = {bc}; let __v: u16 = eval_error(format!({msg:?}, fmt_{bid}(&__b))); __v }}"), Ty::Enum(da.clone())));
                    };
                    self.string_table(f, &ac, &[(da.clone(), None), (db.clone(), Some(bc))])?
                }
                ("Len", [q]) => {
                    let (c, t) = self.gen_val(q, env)?;
                    match &t {
                        Ty::Seq(_) => (format!("(({c}).len as i64)"), Ty::Int(0, self.qcap as i64)),
                        _ => {
                            let n = self.seq_len_of(&t)?;
                            (format!("{{ let _ = {c}; {n}i64 }}"), Ty::Int(n as i64, n as i64))
                        }
                    }
                }
                ("Append", [q, x]) => {
                    let (qc, qt) = self.gen_val(q, env)?;
                    let (xc, xt) = self.gen(x, env, None)?;
                    let el = join(&seq_elem_join(&[&qt]).map_err(|_| self.seq_op_err("Append", &qt))?, &xt)?;
                    let st = Ty::Seq(el.clone().into());
                    let qc = self.coerce(qc, &qt, &st)?;
                    let xc = self.coerce(xc, &xt, &el)?;
                    let v = self.fresh("q");
                    (format!("{{ let mut {v} = {qc}; {v}.push({xc}); {v} }}"), st)
                }
                ("Head", [q]) => {
                    let (qc, st) = self.as_seq(q, env, "Head")?;
                    let Ty::Seq(e) = &st else { unreachable!() };
                    (format!("({qc}).head()"), e.as_ref().clone())
                }
                ("Tail", [q]) => {
                    let (qc, st) = self.as_seq(q, env, "Tail")?;
                    (format!("({qc}).tail()"), st)
                }
                ("SubSeq", [q, m, n]) => {
                    let (qc, st) = self.as_seq(q, env, "SubSeq")?;
                    let (mc, _) = self.gen_int(m, env)?;
                    let (nc, _) = self.gen_int(n, env)?;
                    // TLC's message shows the sequence and the index
                    let id = self.ty_id(&st)?;
                    let msg = |which: &str| format!("The {which} argument of SubSeq must be in the domain of its first argument:\n{{}}\n, but instead it is\n{{}}");
                    (
                        format!(
                            "{{ let __q = {qc}; let (__m, __n): (i64, i64) = ({mc}, {nc}); if __m <= __n {{ \
                             if __m < 1 || __m > __q.len as i64 {{ arith_error(format!({:?}, fmt_{id}(&__q), __m)) }} \
                             if __n > __q.len as i64 {{ arith_error(format!({:?}, fmt_{id}(&__q), __n)) }} }} __q.sub(__m, __n) }}",
                            msg("second"),
                            msg("third")
                        ),
                        st,
                    )
                }
                ("\\o", [a, b]) => {
                    let (ac, at) = self.gen_val(a, env)?;
                    // A tuple followed by a string: the string as its characters (TLC)
                    let (bc, bt) = if matches!(self.gen(b, env, None), Ok((_, Ty::Enum(_)))) { self.as_seq(b, env, "\\o")? } else { self.gen_val(b, env)? };
                    let el = seq_elem_join(&[&at, &bt]).map_err(|_| self.seq_op_err("\\o", &at))?;
                    let st = Ty::Seq(el.into());
                    let ac = self.coerce(ac, &at, &st)?;
                    let bc = self.coerce(bc, &bt, &st)?;
                    (format!("({ac}).concat(&{bc})"), st)
                }
                ("SelectSeq", [q, Lambda(ps, body)]) if ps.len() == 1 => {
                    let (qc, st) = self.as_seq(q, env, "SelectSeq")?;
                    let Ty::Seq(e) = &st else { unreachable!() };
                    let mut env2 = env.clone();
                    let x = rid(&ps[0]);
                    env2.locals.insert(ps[0].clone(), (x.clone(), e.as_ref().clone()));
                    let pc = self.gen_as(body, &env2, &Ty::Bool)?;
                    let r = self.fresh("q");
                    (format!("{{ let mut {r} = {}; for {x} in ({qc}).iter() {{ if {pc} {{ {r}.push({x}); }} }} {r} }}", Self::default_code(&st)), st)
                }
                ("SortSeq", [q, Lambda(ps, body)]) if ps.len() == 2 => {
                    let (qc, st) = self.as_seq(q, env, "SortSeq")?;
                    let Ty::Seq(e) = &st else { unreachable!() };
                    let mut env2 = env.clone();
                    let (a, b) = (rid(&ps[0]), rid(&ps[1]));
                    env2.locals.insert(ps[0].clone(), (a.clone(), e.as_ref().clone()));
                    env2.locals.insert(ps[1].clone(), (b.clone(), e.as_ref().clone()));
                    let pc = self.gen_as(body, &env2, &Ty::Bool)?;
                    let r = self.fresh("q");
                    (
                        format!(
                            "{{ let mut {r} = {qc}; for __i in 1..{r}.len as usize {{ let mut __j = __i; while __j > 0 {{ \
                             let ({a}, {b}) = ({r}.items[__j], {r}.items[__j - 1]); if !({pc}) {{ break; }} {r}.items.swap(__j, __j - 1); __j -= 1; }} }} {r} }}"
                        ),
                        st,
                    )
                }
                ("Seq", _) => return Err("Seq(S) is only supported on the right of \\in".into()),
                _ => return Err(format!("unknown operator `{f}`")),
            },
            Un(UOp::Not, x) => (format!("(!{})", self.gen_as(x, env, &Ty::Bool)?), Ty::Bool),
            // ENABLED A: whether A has a successor from the current state
            Un(UOp::Enabled, x) if env.init => {
                // In Init, ENABLED is evaluated on the state assigned so far (TLC fails on a
                // variable not assigned yet)
                match self.vars.iter().find(|(v, _)| !env.primed.contains_key(v)) {
                    Some((v, _)) => {
                        // TLC names the first variable not assigned yet that the action reads
                        fn first_read(e: &Expr, unset: &dyn Fn(&str) -> bool) -> Option<(String, Pos)> {
                            match e {
                                Expr::Ident(n, at) if unset(n) => Some((n.clone(), *at)),
                                Expr::Prime(_) => None,
                                e => e.children().into_iter().find_map(|c| first_read(c, unset)),
                            }
                        }
                        let unset = |n: &str| self.is_var(n) && !env.primed.contains_key(n);
                        let (v, at) = first_read(x, &unset).unwrap_or((v.clone(), NOPOS));
                        (eval_error_bool(&undefined_ident(&v, &at)), Ty::Bool)
                    }
                    None => {
                        let fields: Vec<String> =
                            self.vars.iter().map(|(v, _)| format!("v_{v}: {}", env.primed[v].0)).collect();
                        let mut inner = env.clone();
                        inner.init = false;
                        inner.primed.clear();
                        inner.work = None;
                        let (c, _) = self.gen(&Un(UOp::Enabled, x.clone()), &inner, None)?;
                        (format!("{{ let __st = State {{ {} }}; let s = &__st; {c} }}", fields.join(", ")), Ty::Bool)
                    }
                }
            }
            Un(UOp::Enabled, x) => {
                let mut inner = env.clone();
                inner.split = false;
                inner.primed.clear();
                inner.work = None;
                inner.init = false;
                inner.partial = true;
                inner.enabled = true;
                inner.phantom = matches!(x.as_ref(), Label(n, ..) if n == crate::ast::ENINST);
                let exit = self.fresh("en");
                inner.en_exit = Some(exit.clone());
                let mut code = String::new();
                self.gen_action(&[x.as_ref().clone()], &inner, &mut code)?;
                (format!("('{exit}: {{ {code} false }})"), Ty::Bool)
            }
            Un(UOp::Neg, x) => {
                let (c, (lo, hi)) = self.gen_int_of("Neg", true, false, x, env).map_err(|_| "negation of a non-integer".to_string())?;
                (format!("(-{c})"), Ty::Int(-hi, -lo))
            }
            Un(UOp::Domain, f) => {
                let (_, ft) = self.gen_val(f, env)?;
                if let Ty::Bag(_) = &ft {
                    return self.bag_domain(f, env);
                }
                if let Ty::PFun(d, _) = &ft {
                    let (fc, _) = self.gen_val(f, env)?;
                    let st = Ty::Set(d.clone());
                    let empty = self.s_empty(&st)?;
                    if is_sparse_fun(&ft) {
                        let add = self.s_add("__s", "__k", &st)?;
                        return Ok((format!("{{ let __f = {fc}; let mut __s = {empty}; for (__k, _) in __f.iter() {{ {add} }} __s }}"), st));
                    }
                    let did = self.ty_id(d)?;
                    let add = self.s_add("__s", &format!("dec_{did}(__i as u64)"), &st)?;
                    return Ok((format!("{{ let __f = {fc}; let mut __s = {empty}; for __i in 0..__f.len() {{ if __f[__i].0 {{ {add} }} }} __s }}"), st));
                }
                if let Ty::Seq(_) = &ft {
                    let (fc, _) = self.gen_val(f, env)?;
                    let st = Ty::Set(Ty::Int(1, self.qcap as i64).into());
                    if self.qcap > 128 {
                        // More than 128 indices: a sorted array of 1..Len
                        let empty = self.s_empty(&st)?;
                        let add = self.s_add("__s", "__k", &st)?;
                        return Ok((format!("{{ let __n = ({fc}).len as i64; let mut __s = {empty}; for __k in 1..=__n {{ {add} }} __s }}"), st));
                    }
                    self.ty_id(&st)?;
                    return Ok((format!("{{ let __n = ({fc}).len as u32; if __n >= 128 {{ u128::MAX }} else {{ (1u128 << __n) - 1 }} }}"), st));
                }
                if let Some(el) = tuple_elems(&ft) {
                    // A tuple of n elements is a function over 1..n
                    let n = el.len();
                    let st = Ty::Set(Ty::Int(1, n as i64).into());
                    self.ty_id(&st)?;
                    let mask: u128 = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
                    return Ok((format!("{mask}u128"), st));
                }
                let Ty::Fun(d, _) = ft else { return Err("DOMAIN of a non-function".into()) };
                let st = Ty::Set(d.clone());
                self.ty_id(&st)?;
                let n = d.size().unwrap();
                let mask: u128 = if n >= 128 { u128::MAX } else { (1u128 << n) - 1 };
                (format!("{mask}u128"), st)
            }
            // UNCHANGED e for an expression that is not a tuple of variables is e' = e
            Un(UOp::Unchanged, x) if Self::unchanged_vars(x, &mut vec![]).is_err() => {
                return self.gen(&Bin(BOp::Eq, self.prime_vars(x).b(), x.clone()), env, want);
            }
            Un(UOp::Unchanged, x) => {
                let mut names = vec![];
                Self::unchanged_vars(x, &mut names)?;
                let mut parts = vec![];
                for v in names {
                    let (p, _) = env.primed.get(&v).cloned().ok_or(format!("UNCHANGED {v} before {v}' is decided"))?;
                    let (c, _) = self.gen(&Ident(v.clone(), NOPOS), env, None)?;
                    parts.push(format!("{p} == {c}"));
                }
                (format!("({})", if parts.is_empty() { "true".into() } else { parts.join(" && ") }), Ty::Bool)
            }
            // UNION {e : x \in S} and UNION {A, B, ...}: the union of the sets as they are built
            Un(UOp::Union, x) if matches!(x.strip(), SetMap(..) | SetLit(_)) => {
                let we = want.cloned();
                match x.strip() {
                    SetMap(f, bs) => {
                        let mut env2 = env.clone();
                        let mut heads = vec![];
                        for (x, s) in bs {
                            let (it, et, ix) = self.iter_of_indexed(s, &env2)?;
                            let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                            heads.push((it, lx));
                        }
                        let (fc, ft) = self.gen(f, &env2, we.as_ref())?;
                        if !matches!(ft, Ty::Set(_)) {
                            return Err("UNION of a set whose elements are not sets".into());
                        }
                        let st = Self::layout(we.as_ref(), ft.clone());
                        let fc = self.coerce(fc, &ft, &st)?;
                        let acc = self.fresh("acc");
                        let mut body = format!("{acc} = {};", self.s_bin(BOp::Cup, &acc, &fc, &st));
                        for (it, lx) in heads.into_iter().rev() {
                            body = format!("for {lx} in {it} {{ {body} }}");
                        }
                        let empty = self.s_empty(&st)?;
                        (format!("{{ let mut {acc} = {empty}; {body} {acc} }}"), st)
                    }
                    SetLit(xs) => {
                        let mut parts = vec![];
                        let mut t = Ty::Enum(vec![]);
                        for x in xs {
                            let (c, ct) = self.gen(x, env, we.as_ref())?;
                            if !matches!(ct, Ty::Set(_)) {
                                return Err("UNION of a set whose elements are not sets".into());
                            }
                            t = join(&t, &ct)?;
                            parts.push((c, ct));
                        }
                        let st = Self::layout(we.as_ref(), t);
                        let mut code = self.s_empty(&st)?;
                        for (c, ct) in parts {
                            let c = self.coerce(c, &ct, &st)?;
                            code = self.s_bin(BOp::Cup, &code, &c, &st);
                        }
                        (code, st)
                    }
                    _ => unreachable!(),
                }
            }
            // SUBSET S of a set in the state, as a value: a set of sets, in TLC's order
            Un(UOp::Subset, x) => {
                let (c, t) = self.gen(x, env, None)?;
                let it = self.subsets_iter(&c, &t)?;
                let st = Ty::Set(t.clone().into());
                let acc = self.fresh("acc");
                let add = self.s_add(&acc, "__t", &st)?;
                let empty = self.s_empty(&st)?;
                (format!("{{ let mut {acc} = {empty}; for __t in {it} {{ {add} }} {acc} }}"), st)
            }
            // UNION S of a set of sets from the state
            Un(UOp::Union, x) => {
                let (c, t) = self.gen(x, env, None)?;
                let Ty::Set(inner) = &t else { return Err("UNION of a non-set".into()) };
                if !matches!(inner.as_ref(), Ty::Set(_)) {
                    return Err("UNION of a set whose elements are not sets".into());
                }
                let rt = inner.as_ref().clone();
                let it = self.s_iter(&c, &t)?;
                let acc = self.fresh("acc");
                let empty = self.s_empty(&rt)?;
                let cup = self.s_bin(BOp::Cup, &acc, "__u", &rt);
                (format!("{{ let mut {acc} = {empty}; for __u in {it} {{ {acc} = {cup}; }} {acc} }}"), rt)
            }
            Un(op, _) => return Err(format!("{op:?} is not supported here")),
            Bin(op, a, b) => self.gen_bin(*op, a, b, env, want)?,
            And(xs) | Or(xs) => {
                let sep = if matches!(e, And(_)) { " && " } else { " || " };
                let parts: Vec<String> = xs.iter().map(|x| self.gen_as(x, env, &Ty::Bool)).collect::<R<_>>()?;
                (format!("({})", parts.join(sep)), Ty::Bool)
            }
            // A constant condition picks its branch here, so the other need not type-check (TLC
            // never evaluates it either)
            If(c, a, b) if matches!(self.try_const(c, env), Some(Value::Bool(_))) => {
                let (Some(Value::Bool(t)), made) = self.try_const_made(c, env) else { unreachable!() };
                let (code, t) = self.gen(if t { a } else { b }, env, want)?;
                let notes = self.fold_notes(&made);
                if notes.is_empty() {
                    return Ok((code, t));
                }
                return Ok((format!("{{ {notes}{code} }}"), t));
            }
            If(c, a, b) => {
                let c = self.gen_as(c, env, &Ty::Bool)?;
                let (ac, at) = self.gen(a, env, want)?;
                let (bc, bt) = self.gen(b, env, want.or(Some(&at)))?;
                let t = Self::layout(want, join(&at, &bt)?);
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                (format!("(if {c} {{ {ac} }} else {{ {bc} }})"), t)
            }
            Case(arms, other) => {
                let mut parts = vec![];
                let mut t = Ty::Enum(vec![]);
                for (p, v) in arms {
                    let pc = self.gen_as(p, env, &Ty::Bool)?;
                    let (vc, vt) = match (v, self.gen(v, env, want)) {
                        // An arm made for one element of a tuple (see split_dynamic_index) that
                        // does not fit its type fails only if it is taken
                        (Label(n, _, _), Err(m)) if n == "#per-element" => {
                            (format!("eval_error({:?}.to_string())", format!("EXCEPT at an index from the state: {m}")), Ty::Enum(vec![]))
                        }
                        (_, r) => r?,
                    };
                    t = join(&t, &vt)?;
                    parts.push((pc, vc, vt));
                }
                let oth = match other {
                    Some(o) => {
                        let (oc, ot) = self.gen(o, env, want)?;
                        t = join(&t, &ot)?;
                        Some((oc, ot))
                    }
                    None => None,
                };
                let t = Self::layout(want, t);
                let mut s = String::from("(");
                for (pc, vc, vt) in parts {
                    let vc = self.coerce(vc, &vt, &t)?;
                    write!(s, "if {pc} {{ {vc} }} else ").unwrap();
                }
                match oth {
                    Some((oc, ot)) => s += &format!("{{ {} }})", self.coerce(oc, &ot, &t)?),
                    None => s += &format!("{{ eval_error({:?}.into()) }})", with_at(crate::value::CASE_NONE, &at)),
                }
                (s, t)
            }
            Quant(ex, bs, body) => {
                if bs.iter().any(|(_, s)| self.try_const(s, env).is_some_and(|v| v.as_set().is_ok_and(|x| x.is_empty()))) {
                    return Ok(((!*ex).to_string(), Ty::Bool));
                }
                let mut env2 = env.clone();
                let mut heads = vec![];
                // The first bound variable varies fastest, as in TLC (which matters for where an
                // evaluation error stops the search)
                for (x, s) in bs.iter().rev() {
                    let (it, et, ix) = self.iter_of_indexed(s, &env2)?;
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    heads.push((it, lx));
                }
                let mut code = self.gen_as(body, &env2, &Ty::Bool)?;
                let m = if *ex { "any" } else { "all" };
                for (it, lx) in heads.into_iter().rev() {
                    code = format!("({it}).{m}(|{lx}| {code})");
                }
                (code, Ty::Bool)
            }
            SetLit(xs) => {
                let mut parts = vec![];
                let mut et = Ty::Enum(vec![]);
                let we = match want {
                    Some(Ty::Set(w)) => Some(w.as_ref().clone()),
                    _ => None,
                };
                let mut tys = vec![];
                for x in xs {
                    let (c, t) = self.gen(x, env, we.as_ref())?;
                    et = join(&et, &t)?;
                    parts.push(c);
                    tys.push(t);
                }
                let st = Self::layout(want, Ty::Set(et.into()));
                let el = Self::elem_of(&st);
                let acc = self.fresh("acc");
                let mut body = format!("let mut {acc} = {}; ", self.s_empty(&st)?);
                for (c, t) in parts.iter().zip(&tys) {
                    let c = self.coerce(c.clone(), t, &el)?;
                    body += &self.s_add(&acc, &c, &st)?;
                }
                (format!("{{ {body} {acc} }}"), st)
            }
            SetFilter(x, s, p) => {
                let (it, et, ix) = self.iter_of_indexed(s, env)?;
                let st = Ty::Set(et.clone().into());
                let mut env2 = env.clone();
                let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                let pc = self.gen_as(p, &env2, &Ty::Bool)?;
                let acc = self.fresh("acc");
                let empty = self.s_empty(&st)?;
                let elem = env2.locals[x].0.clone();
                let add = self.s_add(&acc, &elem, &st)?;
                (format!("{{ let mut {acc} = {empty}; for {lx} in {it} {{ if {pc} {{ {add} }} }} {acc} }}"), st)
            }
            SetMap(f, bs) => {
                let mut env2 = env.clone();
                let mut heads = vec![];
                for (x, s) in bs {
                    let (it, et, ix) = self.iter_of_indexed(s, &env2)?;
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    heads.push((it, lx));
                }
                let we = match want {
                    Some(Ty::Set(w)) => Some(w.as_ref().clone()),
                    _ => None,
                };
                let (fc, ft) = self.gen(f, &env2, we.as_ref())?;
                let st = Self::layout(want, Ty::Set(ft.clone().into()));
                let el = Self::elem_of(&st);
                let fc = self.coerce(fc, &ft, &el)?;
                let acc = self.fresh("acc");
                let mut body = self.s_add(&acc, &fc, &st)?;
                for (it, lx) in heads.into_iter().rev() {
                    body = format!("for {lx} in {it} {{ {body} }}");
                }
                let empty = self.s_empty(&st)?;
                (format!("{{ let mut {acc} = {empty}; {body} {acc} }}"), st)
            }
            // Over Nat, say (one over a large finite set is built as any other)
            FunCons(x, s, _) if self.lazy_domain(s, env) && self.try_const(s, env).is_none() => {
                return Err(format!(
                    "the function {} is over a set that cannot be enumerated: it is only supported applied to an argument (`f[x]`, also after EXCEPT) or in `x \\in DOMAIN f`, where TLC evaluates it without enumerating its domain",
                    lazy_fun_text(x, s)
                ))
            }
            // [k \in 1..n |-> e] (or over DOMAIN of a sequence) with n from the state is a sequence
            FunCons(x, s, body) if self.try_const(s, env).is_none() && self.seq_domain_len(s, env).is_some() => {
                let nc = self.seq_domain_len(s, env).unwrap()?;
                let mut env2 = env.clone();
                let lx = rid(x);
                env2.locals.insert(x.clone(), (lx.clone(), Ty::Int(1, self.qcap.max(1) as i64)));
                let (bc, bt) = self.gen(body, &env2, None)?;
                let st = Ty::Seq(bt.into());
                self.ty_id(&st)?;
                let q = self.fresh("q");
                (format!("{{ let mut {q} = {}; for {lx} in 1..=({nc}) {{ {q}.push({bc}); }} {q} }}", Self::default_code(&st)), st)
            }
            // [x \in S |-> e] with S from the state: a function over part of S's element type
            FunCons(x, s, body) if self.try_const(s, env).is_none() => {
                let (it, et, ix) = self.iter_of_indexed(s, env)?;
                let mut env2 = env.clone();
                let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                let (bc, bt) = self.gen(body, &env2, None)?;
                let ft = Ty::PFun(et.clone().into(), bt.into());
                self.ty_id(&ft)?;
                let key = env2.locals[x].0.clone();
                let put = if is_sparse_fun(&ft) {
                    self.fun_put("__o", &key, &bc, &ft)?
                } else {
                    format!("__o[idx_{}({key})] = (true, {bc});", self.ty_id(&et)?)
                };
                (format!("{{ let mut __o = {}; for {lx} in {it} {{ {put} }} __o }}", Self::default_code(&ft)), ft)
            }
            FunCons(x, s, body) => {
                let dv = self.ce.eval(s, &HashMap::new()).map_err(|m| format!("function domain must be constant: {m}"))?;
                let dt = elem_ty_of_domain(dv.as_set()?)?;
                let did = self.ty_id(&dt)?;
                let wc = match want {
                    Some(Ty::Fun(wd, wc)) if **wd == dt => Some(wc.as_ref().clone()),
                    _ => None,
                };
                let mut env2 = env.clone();
                let lx = rid(x);
                env2.locals.insert(x.clone(), (lx.clone(), dt.clone()));
                let (bc, bt) = self.gen(body, &env2, wc.as_ref())?;
                let ct = match &wc {
                    Some(w) if join(w, &bt).ok().as_ref() == Some(w) => w.clone(),
                    _ => bt.clone(),
                };
                let bc = self.coerce(bc, &bt, &ct)?;
                let ft = Ty::Fun(dt.clone().into(), ct.clone().into());
                self.ty_id(&ft)?;
                (
                    format!(
                        "{{ let __f: {} = std::array::from_fn(|__i| {{ let {lx}: {} = dec_{did}(__i as u64); {bc} }}); __f }}",
                        ft.repr(),
                        dt.repr()
                    ),
                    ft,
                )
            }
            RecLit(fs) => {
                let mut fs: Vec<(String, Expr)> = fs.clone();
                fs.sort_by(|a, b| field_cmp(&a.0, &b.0));
                let wf: Option<Vec<(String, Ty)>> = match want {
                    Some(Ty::Rec(w)) => Some(w.clone()),
                    _ => None,
                };
                let mut parts = vec![];
                let mut tys = vec![];
                for (k, v) in &fs {
                    let w = wf.as_ref().and_then(|w| w.iter().find(|(n, _)| n == k).map(|x| match &x.1 {
                        Ty::Opt(i) => i.as_ref().clone(),
                        t => t.clone(),
                    }));
                    let (c, t) = self.gen(v, env, w.as_ref())?;
                    // Adopt the requested type only when the value's range fits within it (widening
                    // only, so always sound). Never narrow: the requested type is not necessarily
                    // the declared one and may come from a record built in a sibling branch (an
                    // `epoch |-> 0` branch once narrowed it and dropped the `epoch |-> 1` states)
                    let t = match (&w, &t) {
                        (Some(Ty::Int(wl, wh)), Ty::Int(l, h)) if wl <= l && h <= wh => w.clone().unwrap(),
                        _ => t,
                    };
                    parts.push(c);
                    tys.push((k.clone(), t));
                }
                (rec_build(&parts), Ty::Rec(tys))
            }
            // A function over Nat, Int, STRING, ...: its body, at the argument
            App(f, x) if self.lazy_fun_domain(f, env).is_some() => {
                let (xc, xt) = self.gen(x, env, None)?;
                let k = self.fresh("k");
                let (c, t) = self.lazy_apply(f, &k, &xt, env, want)?;
                (format!("{{ let {k} = {xc}; {c} }}"), t)
            }
            // A tuple of variables applied to a constant index (`dag[1]` with `dag == <<vs, es>>`):
            // that variable, without building the tuple. Reading a variable cannot fail, so
            // skipping the others changes nothing
            App(f, x) if matches!(unlabel(f), Tuple(es) if self.var_tuple(es, env)) && self.try_const(x, env).is_some() => {
                let Tuple(es) = unlabel(f) else { unreachable!() };
                let k = self.tuple_index(x, env, es.len())?;
                return self.gen(&es[k], env, want);
            }
            App(f, x) => {
                let (fc, ft) = self.gen_val(f, env)?;
                if let Ty::Rec(fs) = &ft {
                    if is_tuple_fields(fs) {
                        if self.try_const(x, env).is_some() {
                            let k = self.tuple_index(x, env, fs.len())?;
                            return Ok((format!("({fc}){}", rec_field(fs.len(), k)), fs[k].1.clone()));
                        }
                        // An index from the state: the elements as one type, chosen at run time
                        let mut t = Ty::Enum(vec![]);
                        for (_, ft) in fs {
                            t = join(&t, ft).map_err(|e| format!("indexing a tuple with an index that is not constant needs elements of one type: {e}"))?;
                        }
                        let (ic, _) = self.gen_int(x, env)?;
                        let (r, i) = (self.fresh("r"), self.fresh("i"));
                        let mut arms = String::new();
                        for (k, (_, ft)) in fs.iter().enumerate() {
                            let c = self.coerce(format!("{r}{}", rec_field(fs.len(), k)), ft, &t)?;
                            write!(arms, "{} => {c}, ", k + 1).unwrap();
                        }
                        // TLC's message shows the tuple
                        let tid = self.ty_id(&ft)?;
                        return Ok((
                            format!(
                                "{{ let {r} = {fc}; let {i}: i64 = {ic}; match {i} {{ {arms}_ => eval_error(format!(\"Attempted to apply tuple\\n{{}}\\nto integer {{}} which is out of domain.\", fmt_{tid}(&{r}), {i})) }} }}"
                            ),
                            t,
                        ));
                    }
                }
                if let Ty::Seq(e) = &ft {
                    let (ic, _) = self.gen_int(x, env)?;
                    return Ok((format!("({fc}).at({ic})"), e.as_ref().clone()));
                }
                if let (Ty::PFun(d, c), true) = (&ft, is_sparse_fun(&ft)) {
                    let xc = self.gen_as(x, env, d)?;
                    return Ok((
                        format!("{{ let __f = {fc}; match __f.get(&{xc}) {{ Some(__v) => __v, None => eval_error(\"Attempted to apply a function to an argument not in its domain\".into()) }} }}"),
                        c.as_ref().clone(),
                    ));
                }
                if let (Ty::Bag(e), true) = (&ft, is_sparse_fun(&ft)) {
                    let xc = self.gen_as(x, env, e)?;
                    return Ok((
                        format!("{{ let __b = {fc}; match __b.get(&{xc}) {{ Some(__c) => __c, None => eval_error(\"Attempted to apply a bag to an element not in it\".into()) }} }}"),
                        Ty::Int(1, BIG),
                    ));
                }
                if let Ty::PFun(d, c) = &ft {
                    let did = self.ty_id(d)?;
                    let xc = self.gen_as(x, env, d)?;
                    return Ok((
                        format!("{{ let __f = {fc}; let __i = enc_{did}({xc}); if __i == u64::MAX || !__f[__i as usize].0 {{ eval_error(\"Attempted to apply a function to an argument not in its domain\".into()) }} __f[__i as usize].1 }}"),
                        c.as_ref().clone(),
                    ));
                }
                // A bag applied to an element: its count, an error for an element not in it
                if let Ty::Bag(e) = &ft {
                    let eid = self.ty_id(e)?;
                    let xc = self.gen_as(x, env, e)?;
                    return Ok((
                        format!("{{ let __b = {fc}; let __i = enc_{eid}({xc}); if __i == u64::MAX || __b[__i as usize] == 0 {{ eval_error(\"Attempted to apply a bag to an element not in it\".into()) }} __b[__i as usize] }}"),
                        Ty::Int(1, BIG),
                    ));
                }
                // A record is a function from its field names: r["a"] is r.a
                if let Ty::Rec(fs) = &ft {
                    if let Some(Value::Atom(a)) = self.try_const(x, env) {
                        let k = self.atoms.name(a);
                        if fs.iter().any(|(n, _)| *n == k) {
                            return self.gen(&Expr::Field(f.clone(), k), env, want);
                        }
                    }
                }
                let Ty::Fun(d, c) = ft else { return Err(format!("applying a non-function: {f:?}")) };
                // If the argument is a bound variable with a known index, use it without conversion
                if let Ident(n, _) = x.strip() {
                    if let Some((t, iv)) = env.idx.get(n) {
                        if *t == *d {
                            return Ok((format!("({fc})[{iv} as usize]"), *c));
                        }
                    }
                }
                let did = self.ty_id(&d)?;
                let xc = self.gen_as(x, env, &d)?;
                (format!("({fc})[idx_{did}({xc})]"), *c)
            }
            Field(r, k) => {
                let (rc, rt) = self.gen(r, env, None)?;
                // An element of a set that has no elements yet (while types are inferred from a
                // variable that starts as {}): there is no value to take the field of
                if rt == Ty::Enum(vec![]) {
                    return Ok((format!("{{ let _ = {rc}; type_error(\"a record\", \"with a field {k}\") }}"), Ty::Enum(vec![])));
                }
                let Ty::Rec(fs) = rt else { return Err(format!("field .{k} of a non-record")) };
                let i = fs.iter().position(|(n, _)| n == k).ok_or(format!("no field {k}"))?;
                let fp = rec_field(fs.len(), i);
                match &fs[i].1 {
                    Ty::Opt(t) => {
                        let o = self.fresh("o");
                        (
                            format!("{{ let {o} = ({rc}){fp}; if !{o}.0 {{ eval_error(\"Attempted to access a nonexistent field `{k}` of a record\".into()) }} {o}.1 }}"),
                            t.as_ref().clone(),
                        )
                    }
                    t => (format!("({rc}){fp}"), t.clone()),
                }
            }
            Except(f, ups) => {
                // TLC warns about an argument or field the value does not have, naming where the
                // value is written
                let warn = match except_pos(f) {
                    Some(at) => format!(" else {{ except_warning({at:?}); }}"),
                    None => String::new(),
                };
                let (fc, ft0) = self.gen(f, env, want)?;
                let ups: Vec<(Vec<Path>, Expr)> = ups
                    .iter()
                    .map(|(p, v)| {
                        let (p, v) = self.split_dynamic_index(&ft0, p, v, env, except_pos(f).as_deref());
                        Ok((self.resolve_path(&ft0, &p, env)?, v))
                    })
                    .collect::<R<_>>()?;
                let ups = &ups;
                // Widen to include the types of the written values (when writing a wider value into
                // a narrower function; type inference relies on this too)
                let mut ft = ft0.clone();
                for (path, val) in ups {
                    let Some(cur) = Self::path_type(&ft, path) else { continue };
                    let mut env2 = env.clone();
                    env2.locals.insert("@".into(), ("__at".into(), cur.clone()));
                    if let Some(Path::Field(n)) = path.iter().find(|p| matches!(p, Path::Field(k) if k.starts_with('@'))) {
                        env2.locals.insert(n.clone(), ("__at".into(), cur.clone()));
                    }
                    if let Ok((_, vt)) = self.gen(val, &env2, Some(&cur)) {
                        if let Ok(j) = join(&cur, &vt) {
                            if j != cur {
                                ft = Self::set_path_type(&ft, path, &j);
                            }
                        }
                    }
                }
                let fc = if ft != ft0 { self.coerce(fc, &ft0, &ft)? } else { fc };
                let t = self.fresh("t");
                let mut s = format!("{{ let mut {t} = {fc}; ");
                for (path, val) in ups {
                    let mut place = t.clone();
                    let mut cur = ft.clone();
                    let mut conds = vec![];
                    let mut at_name = None;
                    for p in path {
                        match (p, &cur) {
                            // Name of this EXCEPT's @, attached during expansion
                            (Path::Field(k), _) if k.starts_with('@') => at_name = Some(k.clone()),
                            // An index outside the sequence leaves it unchanged, as in TLC
                            (Path::Idx(i), Ty::Seq(e)) => {
                                let (ic, _) = self.gen_int(i, env)?;
                                let iv = self.fresh("i");
                                write!(s, "let {iv}: i64 = {ic}; ").unwrap();
                                conds.push(format!("{iv} >= 1 && {iv} <= ({place}).len as i64"));
                                place = format!("{place}.items[({iv} - 1) as usize]");
                                cur = e.as_ref().clone();
                            }
                            (Path::Idx(i), Ty::Fun(d, c)) => {
                                // A bound variable with a known index needs neither conversion nor
                                // a bounds check
                                let known = match i.strip() {
                                    Expr::Ident(n, _) => env.idx.get(n).filter(|(t, _)| *t == **d).map(|(_, v)| v.clone()),
                                    _ => None,
                                };
                                match known {
                                    Some(iv) => place = format!("{place}[{iv} as usize]"),
                                    None => {
                                        let did = self.ty_id(d)?;
                                        let ic = self.gen_as(i, env, d)?;
                                        let iv = self.fresh("i");
                                        // An index outside the domain is a no-op (as in TLC)
                                        write!(s, "let {iv} = enc_{did}({ic}); ").unwrap();
                                        conds.push(format!("{iv} != u64::MAX"));
                                        place = format!("{place}[{iv} as usize]");
                                    }
                                }
                                cur = c.as_ref().clone();
                            }
                            // A function over part of a type: a key outside its domain leaves it
                            // unchanged, as in TLC
                            (Path::Idx(i), Ty::PFun(d, c)) => {
                                let ic = self.gen_as(i, env, d)?;
                                let iv = self.fresh("i");
                                if is_sparse_fun(&cur) {
                                    // Looked up only once the steps before it are known to apply
                                    write!(s, "let {iv} = {ic}; ").unwrap();
                                    conds.push(format!("({place}).find(&{iv}).is_ok()"));
                                    place = format!("{place}.items[({place}).find(&{iv}).unwrap()].1");
                                } else {
                                    let did = self.ty_id(d)?;
                                    write!(s, "let {iv} = enc_{did}({ic}); ").unwrap();
                                    conds.push(format!("{iv} != u64::MAX && {place}[{iv} as usize].0"));
                                    place = format!("{place}[{iv} as usize].1");
                                }
                                cur = c.as_ref().clone();
                            }
                            (Path::Field(k), Ty::Rec(fs)) => {
                                let i = fs.iter().position(|(n, _)| n == k).ok_or(format!("no field {k}"))?;
                                match &fs[i].1 {
                                    // EXCEPT on an absent field is a no-op
                                    Ty::Opt(t) => {
                                        let fp = rec_field(fs.len(), i);
                                        conds.push(format!("{place}{fp}.0"));
                                        place = format!("{place}{fp}.1");
                                        cur = t.as_ref().clone();
                                    }
                                    t => {
                                        place = format!("{place}{}", rec_field(fs.len(), i));
                                        cur = t.clone();
                                    }
                                }
                            }
                            _ => return Err("EXCEPT path does not match the value's type".into()),
                        }
                    }
                    let at = self.fresh("at");
                    let mut env2 = env.clone();
                    env2.locals.insert("@".into(), (at.clone(), cur.clone()));
                    if let Some(n) = at_name {
                        env2.locals.insert(n, (at.clone(), cur.clone()));
                    }
                    let vc = self.gen_as(val, &env2, &cur)?;
                    let read_at = if vc.contains(&at) { format!("let {at} = {place}; ") } else { String::new() };
                    if conds.is_empty() {
                        write!(s, "{read_at}{place} = {vc}; ").unwrap();
                    } else {
                        write!(s, "if {} {{ {read_at}{place} = {vc}; }}{warn} ", conds.join(" && ")).unwrap();
                    }
                }
                (s + &t + " }", ft)
            }
            Tuple(xs) => {
                // Tuples are represented as records with fields #00001, #00002, ...
                let mut parts = vec![];
                let mut tys = vec![];
                for (i, x) in xs.iter().enumerate() {
                    let w = match want {
                        Some(Ty::Rec(fs)) => fs.get(i).map(|f| f.1.clone()),
                        _ => None,
                    };
                    let (c, t) = self.gen(x, env, w.as_ref())?;
                    parts.push(c);
                    tys.push((tuple_field(i), t));
                }
                (rec_build(&parts), Ty::Rec(tys))
            }
            Choose(x, s, p) => {
                // The first element in iteration order that satisfies p. Sets iterate in TLC's
                // order of values (ascending integers, strings and model values in order of first
                // appearance, records and tuples element by element), so this is TLC's choice
                let (it, et, ix) = self.iter_of_indexed(s, env)?;
                let mut env2 = env.clone();
                let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                let pc = self.gen_as(p, &env2, &Ty::Bool)?;
                let val = env2.locals[x].0.clone();
                let r = self.fresh("r");
                (
                    format!(
                        "{{ let mut {r}: Option<{}> = None; for {lx} in {it} {{ if {pc} {{ {r} = Some({val}); break; }} }} \
                         match {r} {{ Some(v) => v, None => eval_error({:?}.into()) }} }}",
                        et.repr(),
                        with_at(crate::value::CHOOSE_NONE, &at)
                    ),
                    et,
                )
            }
            // [S -> T] with S from the state, as a value: the set of those functions
            FunSet(..) => {
                let (it, et, _) = self.iter_of_indexed(e, env)?;
                let st = Ty::Set(et.into());
                let empty = self.s_empty(&st)?;
                let add = self.s_add("__s", "__f", &st)?;
                (format!("{{ let mut __s = {empty}; for __f in {it} {{ {add} }} __s }}"), st)
            }
            // [a : S, b : T] with sets from the state, as a value: every record, collected
            RecSet(fs) => {
                let mut fs = fs.clone();
                fs.sort_by(|a, b| field_cmp(&a.0, &b.0));
                let (mut open, mut close, mut names, mut tys) = (String::new(), String::new(), vec![], vec![]);
                for (k, se) in &fs {
                    let (c, t) = self.gen(se, env, None)?;
                    let Ty::Set(et) = &t else { return Err(format!("[{k} : S] with S not a set")) };
                    let it = self.s_iter(&c, &t)?;
                    let v = self.fresh("f");
                    write!(open, "for {v} in {it} {{ ").unwrap();
                    close.push('}');
                    names.push(v);
                    tys.push((k.clone(), et.as_ref().clone()));
                }
                let st = Ty::Set(Ty::Rec(tys).into());
                let acc = self.fresh("acc");
                let add = self.s_add(&acc, &rec_build(&names), &st)?;
                let empty = self.s_empty(&st)?;
                (format!("{{ let mut {acc} = {empty}; {open}{add} {close} {acc} }}"), st)
            }
            Let(..) | Label(..) => unreachable!(),
            Lambda(..) => return Err("LAMBDA is only supported as the argument of an operator parameter".into()),
            RecCall(i, args) => {
                // Constant arguments were folded above when the whole call evaluates; otherwise
                // call a Rust function generated for the operator
                let rd = crate::expand::rec_def(*i);
                let (reads, primes, enabled) = self.rec_reads(*i)?;
                let mut codes = vec![];
                let mut tys = vec![];
                let mut state_arg = String::new();
                if enabled {
                    state_arg = if env.init {
                        // In Init: the state assigned so far, once it is complete
                        if let Some((v, _)) = self.vars.iter().find(|(v, _)| !env.primed.contains_key(v)) {
                            return Err(format!("recursive operator `{}` evaluates ENABLED in Init before {v} is assigned", rd.name));
                        }
                        let fields: Vec<String> = self.vars.iter().map(|(v, _)| format!("v_{v}: {}", env.primed[v].0)).collect();
                        format!("&State {{ {} }}, ", fields.join(", "))
                    } else {
                        "s, ".into()
                    };
                }
                for a in args {
                    // Integer arguments are passed unbounded: their ranges change from call to call
                    // (n, n - 1, ...), and one function serves them all
                    let (c, t) = self.gen(a, env, None)?;
                    let w = unbounded_ints(&t);
                    codes.push(self.coerce(c, &t, &w)?);
                    tys.push(w);
                }
                // Bound variables of the call site that the body refers to are passed along
                for f in self.rec_free(&rd) {
                    // A name a BIND label outside binds and code generation writes out (see
                    // `gen_bind`): its value
                    let (c, t) = match env.locals.get(&f) {
                        None if crate::value::bound_expr(&f).is_some() => self.gen(&Ident(f.clone(), NOPOS), env, None)?,
                        x => x.cloned().ok_or(format!("recursive operator `{}`: unknown identifier `{f}`", rd.name))?,
                    };
                    codes.push(c);
                    tys.push(t);
                }
                // So are the variables it reads (in Init, the values assigned so far) and the primed
                // variables it reads, which must be determined before the call
                for v in &reads {
                    let (c, t) = self.gen(&Ident(v.clone(), NOPOS), env, None)?;
                    let vt = self.var_ty(v);
                    codes.push(self.coerce(c, &t, &vt)?);
                    tys.push(vt);
                }
                for v in &primes {
                    let Some((c, t)) = env.primed.get(v).cloned() else {
                        return Err(format!(
                            "recursive operator `{}` reads {v}' where the action has not determined it, which is not supported",
                            rd.name
                        ));
                    };
                    let vt = self.var_ty(v);
                    codes.push(self.coerce(c, &t, &vt)?);
                    tys.push(vt);
                }
                let (name, ret) = self.rec_fn(*i, &rd, tys, &reads, &primes, enabled)?;
                let args: Vec<String> = codes.iter().map(|c| format!("&({c})")).collect();
                (format!("{name}({state_arg}{})", args.join(", ")), ret)
            }
            // [A]_v is A \/ UNCHANGED v
            BoxAction(a, v) => return self.gen(&Or(vec![a.as_ref().clone(), Un(UOp::Unchanged, v.clone())]), env, want),
            Fair(..) => return Err("temporal formula in a state expression".into()),
            Num(_) | Str(_) | Bool(_) => unreachable!("constants are folded"),
        })
    }

    fn gen_bin(&mut self, op: BOp, a: &Expr, b: &Expr, env: &Env, want: Option<&Ty>) -> R<(String, Ty)> {
        use BOp::*;
        // S \subseteq "Reals" (Real): each element of S is checked against the string, which fails
        if op == Subseteq && matches!(self.try_const(b, env), Some(Value::Atom(x)) if !self.atoms.is_model(x)) {
            let y = self.fresh("sub");
            let e = Expr::Quant(false, vec![(y.clone(), a.clone())], Expr::Bin(In, Expr::Ident(y, NOPOS).b(), b.clone().b()).b());
            return self.gen(&e, env, want);
        }
        Ok(match op {
            Implies | Equiv => {
                let ac = self.gen_as(a, env, &Ty::Bool)?;
                let bc = self.gen_as(b, env, &Ty::Bool)?;
                let s = if op == Implies { format!("(!{ac} || {bc})") } else { format!("({ac} == {bc})") };
                (s, Ty::Bool)
            }
            Eq | Neq => {
                let (ac, at) = self.gen(a, env, None)?;
                let (bc, bt) = self.gen(b, env, Some(&at))?;
                if let Some(c) = self.tuple_str_eq(&ac, &at, &bc, &bt, env)? {
                    return Ok((if op == Eq { c } else { format!("!{c}") }, Ty::Bool));
                }
                // Still evaluate both sides, which may stop with an error as in TLC
                match self.tuple_cmp(&at, &bt)? {
                    Cmp::Normal => {}
                    Cmp::Unequal => return Ok((format!("{{ let _ = {ac}; let _ = {bc}; {} }}", op == Neq), Ty::Bool)),
                    Cmp::Fails(m) => {
                        // As TLC reports it, with both values, for a tuple and an integer
                        let f = match (tuple_elems(&at).is_some(), &bt, &at, tuple_elems(&bt).is_some()) {
                            (true, Ty::Int(..), _, _) => Some("Attempted to check equality of the function {} with the value:\n{}"),
                            (_, _, Ty::Int(..), true) => Some("Attempted to check equality of integer {} with non-integer:\n{}"),
                            _ => None,
                        };
                        if let Some(f) = f {
                            let (aid, bid) = (self.ty_id(&at)?, self.ty_id(&bt)?);
                            let code = format!(
                                "{{ let __a = {ac}; let __b = {bc}; let __r: bool = eval_error(format!({f:?}, ppr(&fmt_{aid}(&__a)), ppr(&fmt_{bid}(&__b)))); __r }}"
                            );
                            return Ok((code, Ty::Bool));
                        }
                        return Ok((format!("{{ let _ = {ac}; let _ = {bc}; {} }}", eval_error_bool(&m)), Ty::Bool));
                    }
                }
                let t = join(&at, &bt)?;
                // Sets of strings compared with sets of integers, which tla2rs cannot hold as one
                // type: compared as TLC compares them, without joining the types
                if self.mixed_set(&t) && !self.mixed_set(&at) && !self.mixed_set(&bt) {
                    let mut c = self.str_int_eq(&ac, &at, &bc, &bt)?;
                    if self.built(a, env) {
                        c = format!("{{ let __fp = FpSource::enter(); {c} }}");
                    }
                    return Ok((if op == Eq { c } else { format!("!{c}") }, Ty::Bool));
                }
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                if matches!(t, Ty::IntAtom(..)) && self.has_str(&t) && self.str_meets_int(&at, &bt) {
                    // A string and an integer: TLC stops with an error when it compares them
                    let neg = if op == Eq { "" } else { "!" };
                    return Ok((format!("{neg}mixed_eq({ac}, {bc})"), Ty::Bool));
                }
                // A comparison with the empty set or sequence reads the length, rather than build
                // an empty array of the capacity's width and compare every slot
                if is_sparse(&t) || matches!(t, Ty::Seq(_)) {
                    let empty = if is_sparse(&t) { self.s_empty(&t)? } else { format!("{}::from_slice(&[])", t.repr().replace('<', "::<")) };
                    let other = if bc == empty { Some(&ac) } else if ac == empty { Some(&bc) } else { None };
                    if let Some(o) = other {
                        return Ok((format!("(({o}).len {} 0)", if op == Eq { "==" } else { "!=" }), Ty::Bool));
                    }
                }
                (format!("({ac} {} {bc})", if op == Eq { "==" } else { "!=" }), Ty::Bool)
            }
            Lt | Le | Gt | Ge => {
                // As TLC names them in its errors (Naturals names >= as >)
                let sym = match op {
                    Lt => "<",
                    Le => "<=",
                    Gt => ">",
                    _ if self.int_module == "Naturals" => ">",
                    _ => ">=",
                };
                self.int_cmp = Some((sym, true));
                let (ac, _) = self.gen_int(a, env)?;
                self.int_cmp = Some((sym, false));
                let (bc, _) = self.gen_int(b, env)?;
                let o = match op {
                    Lt => "<",
                    Le => "<=",
                    Gt => ">",
                    _ => ">=",
                };
                (format!("({ac} {o} {bc})"), Ty::Bool)
            }
            In | NotIn if matches!(b.strip(), Expr::Un(UOp::Domain, _)) && matches!(a.strip(), Expr::Str(_)) => {
                // "f" \in DOMAIN r: whether the record has that field
                let (Expr::Str(k), Expr::Un(_, r)) = (a.strip(), b.strip()) else { unreachable!() };
                let (rc, rt) = self.gen(r, env, None)?;
                let has = match &rt {
                    Ty::Rec(fs) => match fs.iter().position(|(n, _)| n == k) {
                        Some(i) if matches!(fs[i].1, Ty::Opt(_)) => format!("({rc}){}.0", rec_field(fs.len(), i)),
                        Some(_) => "true".into(),
                        None => "false".into(),
                    },
                    _ => return Err("only `\"field\" \\in DOMAIN record` and DOMAIN of functions are supported".into()),
                };
                (if op == NotIn { format!("!{has}") } else { has }, Ty::Bool)
            }
            In | NotIn => {
                let (xc, xt) = self.gen(a, env, None)?;
                let x = self.fresh("x");
                let m = self.gen_member(&x, &xt, b, env)?;
                let neg = if op == NotIn { "!" } else { "" };
                (format!("{neg}{{ let {x} = {xc}; {m} }}"), Ty::Bool)
            }
            // A \subseteq Nat (or Int, or any set that is not a value here) is A \in SUBSET B
            Subseteq
                if matches!(b.strip(), Expr::Ident(n, _) if n == "Nat" || n == "Int" || n == "STRING")
                    || matches!(b.strip(), Expr::Call(f, a) if f == "Seq" && a.len() == 1) =>
            {
                let (ac, at) = self.gen(a, env, None)?;
                let x = self.fresh("x");
                let m = self.gen_member(&x, &at, &Expr::Un(UOp::Subset, b.clone().into()), env)?;
                (format!("{{ let {x} = {ac}; {m} }}"), Ty::Bool)
            }
            Subseteq => {
                let (ac, at) = self.gen_val(a, env)?;
                let (bc, bt) = self.gen(b, env, Some(&at))?;
                let (bc, bt) = self.val_of(bc, bt)?;
                let t = join(&at, &bt)?;
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                if is_sparse(&t) {
                    (format!("({ac}).subseteq(&{bc})"), Ty::Bool)
                } else {
                    (format!("(({ac}) & !({bc}) == 0)"), Ty::Bool)
                }
            }
            Cup | Cap | SetMinus => {
                let (ac, at) = self.gen(a, env, want)?;
                let (ac, at) = self.val_of(ac, at)?;
                let (bc, bt) = self.gen(b, env, want.or(Some(&at)))?;
                let (bc, bt) = self.val_of(bc, bt)?;
                let t = Self::layout(want, join(&at, &bt)?);
                let ac = self.coerce(ac, &at, &t)?;
                let bc = self.coerce(bc, &bt, &t)?;
                (self.s_bin(op, &ac, &bc, &t), t)
            }
            LeadsTo => return Err("~> in a state expression".into()),
            // a..b with bounds from the state, as a value: a set over the integers both bounds can be
            Range => {
                let (ac, (alo, _)) = self.gen_int_of("DotDot", false, true, a, env)?;
                let (bc, (_, bhi)) = self.gen_int_of("DotDot", false, true, b, env)?;
                let st = Ty::Set(Ty::Int(alo, bhi.max(alo)).into());
                let acc = self.fresh("acc");
                let add = self.s_add(&acc, "__k", &st)?;
                let empty = self.s_empty(&st)?;
                (format!("{{ let mut {acc} = {empty}; for __k in ({ac})..=({bc}) {{ {add} }} {acc} }}"), st)
            }
            Add | Sub | Mul | Div | Mod => {
                let method = match op {
                    Add => "Plus",
                    Sub => "Minus",
                    Mul => "Times",
                    Div => "Divide",
                    _ => "Mod",
                };
                let (ac, (alo, ahi)) = self.gen_int_of(method, false, false, a, env)?;
                let (bc, (blo, bhi)) = self.gen_int_of(method, false, false, b, env)?;
                // Compute ranges in i128 and clamp to BIG. Otherwise an operation such as
                // subtracting two unbounded integers (Nat / Int) overflows i64, corrupting the
                // range into a type that admits only a single value
                let clamp = |x: i128| x.clamp(-(BIG as i128), BIG as i128) as i64;
                let (al, ah, bl, bh) = (alo as i128, ahi as i128, blo as i128, bhi as i128);
                let (s, t) = match op {
                    Add => (format!("({ac} + {bc})"), Ty::Int(clamp(al + bl), clamp(ah + bh))),
                    Sub => (format!("({ac} - {bc})"), Ty::Int(clamp(al - bh), clamp(ah - bl))),
                    Mul => {
                        let c = [al * bl, al * bh, ah * bl, ah * bh];
                        (format!("({ac} * {bc})"), Ty::Int(clamp(*c.iter().min().unwrap()), clamp(*c.iter().max().unwrap())))
                    }
                    Div => {
                        let m = alo.abs().max(ahi.abs());
                        let f = if self.int_module == "Naturals" { "tla_div_nat" } else { "tla_div" };
                        (format!("{f}({ac}, {bc})"), Ty::Int(-m, m))
                    }
                    _ => (format!("tla_mod({ac}, {bc})"), Ty::Int(0, clamp((bh - 1).max(0)))),
                };
                (s, t)
            }
        })
    }

    /// `gen_int` of an argument of the arithmetic operator whose Java method in TLC is `method`
    /// (`neg`: it takes one argument; `interval`: it gives an interval)
    fn gen_int_of(&mut self, method: &'static str, neg: bool, interval: bool, e: &Expr, env: &Env) -> R<(String, (i64, i64))> {
        self.int_op = Some((method, neg, interval));
        self.gen_int(e, env)
    }

    fn gen_int(&mut self, e: &Expr, env: &Env) -> R<(String, (i64, i64))> {
        let op = self.int_op.take();
        let cmp = self.int_cmp.take();
        let (c, t) = self.gen(e, env, None)?;
        match t {
            Ty::Int(lo, hi) => Ok((c, (lo, hi))),
            // An integer or a model value (`x # None => x + 1 > 0`): a model value reaching
            // arithmetic or a comparison is an evaluation error, as in TLC. TLC evaluates
            // arithmetic with Java methods and names the one that failed to cast the model value
            Ty::IntAtom(lo, hi, _) => {
                let fail = match (op, cmp) {
                    // A comparison is TLC's own evaluation error (exit 255)
                    (_, Some((sym, first))) => {
                        let which = if first { "first" } else { "second" };
                        format!(
                            "arith_error(format!(\"The {which} argument of {sym} should be an integer, but instead it is:\\n{{}}\", ATOMS[(__n - i64::MIN) as usize]))"
                        )
                    }
                    (Some((method, neg, interval)), None) => {
                        let v = "tlc2.value.impl.";
                        let args = if neg { format!("{v}IntValue") } else { format!("{v}IntValue,{v}IntValue") };
                        let ret = if interval { "IntervalValue" } else { "IntValue" };
                        let m = format!(
                            "Attempted to apply the operator overridden by the Java method\npublic static {v}{ret} tlc2.module.{}.{method}({args}),\nbut it produced the following error:\nCannot cast {v}ModelValue to {v}IntValue",
                            self.int_module
                        );
                        format!("eval_error({m:?}.to_string())")
                    }
                    (None, None) => "eval_error(format!(\"Attempted to use the model value {} as an integer\", ATOMS[(__n - i64::MIN) as usize]))".into(),
                };
                Ok((format!("{{ let __n: i64 = {c}; if __n < i64::MIN + 65536 {{ {fail} }} __n }}"), (lo, hi)))
            }
            // No value has this type (an element of the empty tuple, say), so the code cannot
            // produce one: it stops, and still runs to report that
            Ty::Enum(v) if v.is_empty() => Ok((format!("{{ let __u: i64 = {{ let _ = {c}; unreachable!() }}; __u }}"), (0, 0))),
            t => Err(format!("expected an integer, got {t:?} in {e:?}")),
        }
    }

    /// Iterator expression over a set, and its element type
    fn iter_of(&mut self, s: &Expr, env: &Env) -> R<(String, Ty)> {
        let (it, et, _) = self.iter_of_indexed(s, env)?;
        Ok((it, et))
    }

    /// Iterator and element type. When the set is the element type's full domain, iterates over
    /// indices instead (using them as function arguments avoids converting from atom values)
    fn iter_of_indexed(&mut self, s: &Expr, env: &Env) -> R<(String, Ty, Option<String>)> {
        let s = s.strip();
        if let Some((it, et, indexed)) = self.big_set_iter(s, env)? {
            return Ok((it, et, indexed.then(String::new)));
        }
        if let (Some(v), made) = self.try_const_made(s, env) {
            let set = v.as_set()?;
            let Ty::Set(et) = ty_of_value(&v)? else { unreachable!() };
            if set.is_empty() {
                return Ok(("std::iter::empty::<u16>()".into(), Ty::Enum(vec![]), None));
            }
            // If this set covers the whole element type, iterate over 0..n and carry the index
            if let Some(n) = et.size() {
                let mut all = et.enumerate();
                all.sort();
                if all.into_iter().collect::<BTreeSet<_>>() == *set {
                    return Ok((self.note_folded(format!("(0..{n}u64)"), &made), *et, Some(String::new())));
                }
            }
            let mut parts = vec![];
            for x in set {
                parts.push(self.lit(x, &et)?);
            }
            // rustc takes minutes over a temporary array of thousands of values, not over a static
            let it = match parts.len() > LIT_TABLE && const_lit(&et) {
                true => format!("{{ static __A: [{}; {}] = [{}]; __A.iter().copied() }}", et.repr(), parts.len(), parts.join(", ")),
                false => format!("[{}].into_iter()", parts.join(", ")),
            };
            return Ok((self.note_folded(it, &made), *et, None));
        }
        // A product of sets that depend on the state, in TLC's order (the first element varies
        // slowest)
        if let Expr::Call(f, parts) = s {
            if f == "\\X" {
                let mut heads = vec![];
                let mut tys = vec![];
                let mut vals = vec![];
                for part in parts {
                    let (it, et, ix) = self.iter_of_indexed(part, env)?;
                    let lx = self.fresh("x");
                    let val = match ix {
                        Some(_) => format!("dec_{}({lx})", self.ty_id(&et)?),
                        None => lx.clone(),
                    };
                    heads.push((it, lx));
                    vals.push(val);
                    tys.push(et);
                }
                let tt = tuple_ty(tys)?;
                let v = self.fresh("v");
                let mut body = format!("{v}.push(({},));", vals.join(", "));
                for (it, lx) in heads.into_iter().rev() {
                    body = format!("for {lx} in {it} {{ {body} }}");
                }
                return Ok((format!("{{ let mut {v}: Vec<{}> = Vec::new(); {body} {v} }}.into_iter()", tt.repr()), tt, None));
            }
        }
        // [1..n -> T] with n from the state: the sequences of length n over T, in the same order
        // as below (TLC's functions over 1..n are tuples)
        if let Expr::FunSet(d, r) = s {
            if let Expr::Bin(BOp::Range, lo, hi) = d.as_ref() {
                if matches!(lo.as_ref(), Expr::Num(1)) && self.try_const(d, env).is_none() {
                    let (hc, _) = self.gen_int(hi, env)?;
                    let (rit, rt, rix) = self.iter_of_indexed(r, env)?;
                    let rid_ = self.ty_id(&rt)?;
                    let rval = if rix.is_some() { format!("dec_{rid_}(__r)") } else { "__r".to_string() };
                    let st = Ty::Seq(rt.clone().into());
                    self.ty_id(&st)?;
                    let code = format!(
                        "{{ let __n = ({hc}).max(0) as usize; let __r: Vec<{}> = {rit}.map(|__r| {rval}).collect(); let mut __v: Vec<{}> = Vec::new(); \
                         if !__r.is_empty() || __n == 0 {{ let mut __c = vec![0usize; __n]; loop {{ let mut __f = {}; \
                         for __k in 0..__n {{ __f.push(__r[__c[__k]]); }} __v.push(__f); \
                         let mut __k = __n; loop {{ if __k == 0 {{ break; }} __k -= 1; __c[__k] += 1; if __c[__k] < __r.len() {{ break; }} __c[__k] = 0; if __k == 0 {{ __k = usize::MAX; break; }} }} \
                         if __k == usize::MAX || __n == 0 {{ break; }} }} }} __v }}.into_iter()",
                        rt.repr(),
                        st.repr(),
                        Self::default_code(&st)
                    );
                    return Ok((code, st, None));
                }
            }
        }
        // SUBSET of a set that depends on the state, in TLC's order (smaller subsets first)
        // [S -> T] with S from the state: every function over S's elements into T, the values
        // varying fastest at the last element of S (TLC's order of these functions)
        if let Expr::FunSet(d, r) = s {
            let (dc, dty) = self.gen(d, env, None)?;
            let Ty::Set(det) = &dty else { return Err("[S -> T] where S is not a set".into()) };
            let (rit, rt, rix) = self.iter_of_indexed(r, env)?;
            let rid_ = self.ty_id(&rt)?;
            let rval = if rix.is_some() { format!("dec_{rid_}(__r)") } else { "__r".to_string() };
            let ft = Ty::PFun(det.clone(), rt.clone().into());
            self.ty_id(&ft)?;
            let put = self.fun_put("__f", "__d[__k]", "__r[__c[__k]]", &ft)?;
            let dit = self.s_iter(&dc, &dty)?;
            let code = format!(
                "{{ let __d: Vec<{}> = {dit}.collect(); let __r: Vec<{}> = {rit}.map(|__r| {rval}).collect(); let mut __v: Vec<{}> = Vec::new(); \
                 if !__r.is_empty() || __d.is_empty() {{ let mut __c = vec![0usize; __d.len()]; loop {{ let mut __f = {}; \
                 for __k in 0..__d.len() {{ {put} }} __v.push(__f); \
                 let mut __k = __d.len(); loop {{ if __k == 0 {{ break; }} __k -= 1; __c[__k] += 1; if __c[__k] < __r.len() {{ break; }} __c[__k] = 0; if __k == 0 {{ __k = usize::MAX; break; }} }} \
                 if __k == usize::MAX || __d.is_empty() {{ break; }} }} }} __v }}.into_iter()",
                det.repr(),
                rt.repr(),
                ft.repr(),
                Self::default_code(&ft)
            );
            return Ok((code, ft, None));
        }
        if let Expr::Un(UOp::Subset, x) = s {
            let (c, t) = self.gen_val(x, env)?;
            let it = self.subsets_iter(&c, &t)?;
            return Ok((it, t, None));
        }
        if let Expr::Bin(BOp::Range, a, b) = s {
            let (ac, (alo, _)) = self.gen_int(a, env)?;
            let (bc, (_, bhi)) = self.gen_int(b, env)?;
            return Ok((format!("({ac}..={bc})"), Ty::Int(alo, bhi), None));
        }
        // A constant set too large to fold, such as the filter of a large set of records: computed
        // once, into a vector, as an array of limited capacity cannot hold more than MAX_CAP
        // elements. Iterated in the order of such an array (see `s_iter`)
        if let Expr::SetFilter(x, inner, p) = s {
            if self.is_const(s, env) {
                let (it, et, ix) = self.iter_of_indexed(inner, env)?;
                let st = Ty::Set(et.clone().into());
                if is_sparse(&st) {
                    let mut env2 = env.clone();
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    let pc = self.gen_as(p, &env2, &Ty::Bool)?;
                    let elem = env2.locals[x].0.clone();
                    let tr = et.repr();
                    let order = if needs_tlc_order(&et) {
                        format!("__v.sort_by(|x, y| {});", self.tlc_cmp(&et, "x", "y")?)
                    } else {
                        String::new()
                    };
                    let code = format!(
                        "{{ static __S: std::sync::OnceLock<Vec<{tr}>> = std::sync::OnceLock::new(); \
                         __S.get_or_init(|| {{ let mut __v: Vec<{tr}> = Vec::new(); for {lx} in {it} {{ if {pc} {{ __v.push({elem}); }} }} \
                         __v.sort(); __v.dedup(); {order} __v }}).iter().copied() }}"
                    );
                    return Ok((code, et, None));
                }
            }
        }
        let (c, t) = self.gen_val(s, env)?;
        let Ty::Set(et) = &t else { return Err(format!("cannot iterate over {t:?}")) };
        let it = self.s_iter(&c, &t)?;
        Ok((it, et.as_ref().clone(), None))
    }

    /// A constant set of more than BIG_SET elements built from sets of functions, products, sets
    /// of records and SUBSET: an iterator that enumerates it from its parts (written out), in the
    /// order of its value, which is the order its elements would be written out in (see
    /// `BigSet`). Also whether it iterates over the indices of the element type (the set is the
    /// whole type). None for any other set
    fn big_set_iter(&mut self, s: &Expr, env: &Env) -> R<Option<(String, Ty, bool)>> {
        if !matches!(s, Expr::FunSet(..) | Expr::RecSet(_) | Expr::Un(UOp::Subset, _)) && !matches!(s, Expr::Call(f, _) if f == "\\X") {
            return Ok(None);
        }
        if !self.is_const(s, env) {
            return Ok(None);
        }
        let mut made = Made::default();
        let Some(b) = self.big_parts(s, env, &mut made) else { return Ok(None) };
        let n = b.size();
        if n <= BIG_SET as f64 || n >= (1u64 << 62) as f64 {
            return Ok(None);
        }
        let n = n as u64;
        let et = b.ty()?;
        if et.size() == Some(n) {
            return Ok(Some((self.note_folded(format!("(0..{n}u64)"), &made), et, true)));
        }
        let mut pre = String::new();
        let f = self.big_nth(&b, &et, &mut pre)?;
        let code = format!("{{ {pre}(0..{n}u64).map({f}) }}");
        Ok(Some((self.note_folded(code, &made), et, false)))
    }

    /// The parts of a constant set (see `big_set_iter`); None if one is empty or cannot be
    /// computed
    fn big_parts(&self, s: &Expr, env: &Env, made: &mut Made) -> Option<BigSet> {
        let lit = |e: &Expr, made: &mut Made| -> Option<Vec<Value>> {
            let (v, m) = self.try_const_made(e, env);
            made.strs.extend(m.strs);
            made.warns.extend(m.warns);
            let v: Vec<Value> = v?.as_set().ok()?.iter().cloned().collect();
            (!v.is_empty()).then_some(v)
        };
        Some(match s.strip() {
            Expr::FunSet(d, r) => BigSet::Fun(lit(d, made)?, self.big_parts(r, env, made)?.into()),
            Expr::Call(f, ps) if f == "\\X" => BigSet::Prod(ps.iter().map(|p| self.big_parts(p, env, made)).collect::<Option<_>>()?),
            Expr::RecSet(fs) => {
                let mut v = fs.iter().map(|(k, p)| Some((k.clone(), self.big_parts(p, env, made)?))).collect::<Option<Vec<_>>>()?;
                v.sort_by(|a, b| field_cmp(&a.0, &b.0));
                BigSet::Rec(v)
            }
            // At most 20 elements, as when the set is computed (`subsets_tlc` holds them all)
            Expr::Un(UOp::Subset, x) => BigSet::Subset(lit(x, made).filter(|v| v.len() <= 20)?),
            e => BigSet::Lit(lit(e, made)?),
        })
    }

    /// Defines (in `pre`) a closure from the index of an element of b to the element, of type t,
    /// and returns its name
    fn big_nth(&mut self, b: &BigSet, t: &Ty, pre: &mut String) -> R<String> {
        let f = self.fresh("nth");
        // The parts by mixed radix, the first varying slowest
        let digits = |sizes: &[u64]| -> Vec<String> {
            (0..sizes.len()).map(|j| format!("(__i / {}u64 % {}u64)", sizes[j + 1..].iter().product::<u64>(), sizes[j])).collect()
        };
        let body = match b {
            BigSet::Lit(xs) => {
                let parts: Vec<String> = xs.iter().map(|x| self.lit(x, t)).collect::<R<_>>()?;
                let a = self.fresh("lit");
                writeln!(pre, "let {a}: [{}; {}] = [{}];", t.repr(), xs.len(), parts.join(", ")).unwrap();
                format!("{a}[__i as usize]")
            }
            BigSet::Fun(d, r) => {
                let rt = r.ty()?;
                let g = self.big_nth(r, &rt, pre)?;
                let parts: Vec<String> = digits(&vec![r.size() as u64; d.len()]).into_iter().map(|i| format!("{g}{i}")).collect();
                let at = |k: &Value| d.iter().position(|x| x == k).ok_or_else(|| format!("{k:?} outside the domain of {t:?}"));
                match t {
                    Ty::Rec(fs) if is_tuple_fields(fs) => {
                        let ps: Vec<String> = parts.into_iter().zip(fs).map(|(p, (_, ct))| self.coerce(p, &rt, ct)).collect::<R<_>>()?;
                        rec_build(&ps)
                    }
                    Ty::Fun(dt, ct) => {
                        let mut s = String::from("[");
                        for k in dt.enumerate() {
                            s += &self.coerce(parts[at(&k)?].clone(), &rt, ct)?;
                            s += ",";
                        }
                        s + "]"
                    }
                    Ty::PFun(..) if is_sparse_fun(t) => {
                        self.ty_id(t)?;
                        let (kt, vt) = fun_kv(t);
                        let mut s = Self::default_code(t);
                        for (k, p) in d.iter().zip(parts) {
                            s = format!("{s}.with_put({}, {})", self.lit(k, &kt)?, self.coerce(p, &rt, &vt)?);
                        }
                        s
                    }
                    Ty::PFun(dt, ct) => {
                        self.ty_id(t)?;
                        let mut s = String::from("[");
                        for k in dt.enumerate() {
                            s += &match d.iter().position(|x| *x == k) {
                                Some(j) => format!("(true, {})", self.coerce(parts[j].clone(), &rt, ct)?),
                                None => format!("(false, {})", Self::default_code(ct)),
                            };
                            s += ",";
                        }
                        s + "]"
                    }
                    _ => return Err(format!("cannot build a function of type {t:?}")),
                }
            }
            BigSet::Prod(ps) => {
                let Some(fs) = tuple_elems(t).filter(|fs| fs.len() == ps.len()) else {
                    return Err(format!("cannot build a tuple of type {t:?}"));
                };
                let fs: Vec<Ty> = fs.into_iter().cloned().collect();
                let sizes: Vec<u64> = ps.iter().map(|p| p.size() as u64).collect();
                let mut parts = vec![];
                for ((p, i), ft) in ps.iter().zip(digits(&sizes)).zip(&fs) {
                    let pt = p.ty()?;
                    let g = self.big_nth(p, &pt, pre)?;
                    parts.push(self.coerce(format!("{g}{i}"), &pt, ft)?);
                }
                rec_build(&parts)
            }
            BigSet::Rec(ps) => {
                let Ty::Rec(fs) = t else { return Err(format!("cannot build a record of type {t:?}")) };
                let sizes: Vec<u64> = ps.iter().map(|(_, p)| p.size() as u64).collect();
                let mut got = HashMap::new();
                for ((k, p), i) in ps.iter().zip(digits(&sizes)) {
                    let pt = p.ty()?;
                    let g = self.big_nth(p, &pt, pre)?;
                    got.insert(k.clone(), (format!("{g}{i}"), pt));
                }
                let mut parts = vec![];
                for (k, ft) in fs {
                    let Some((c, pt)) = got.remove(k) else { return Err(format!("no field {k} in {t:?}")) };
                    parts.push(match ft {
                        Ty::Opt(i) => format!("(true, {})", self.coerce(c, &pt, i)?),
                        ft => self.coerce(c, &pt, ft)?,
                    });
                }
                rec_build(&parts)
            }
            BigSet::Subset(xs) => {
                let et = Self::elem_of(t);
                let parts: Vec<String> = xs.iter().map(|x| self.lit(x, &et)).collect::<R<_>>()?;
                let (a, m) = (self.fresh("lit"), self.fresh("subs"));
                self.need_subsets = true;
                writeln!(pre, "let {a}: [{}; {}] = [{}];", et.repr(), xs.len(), parts.join(", ")).unwrap();
                writeln!(pre, "let {m}: Vec<u128> = subsets_tlc((1u128 << {}) - 1);", xs.len()).unwrap();
                let empty = self.s_empty(t)?;
                let add = self.s_add("__s", &format!("{a}[__b as usize]"), t)?;
                format!("{{ let mut __s = {empty}; for __b in bits({m}[__i as usize]) {{ {add} }} __s }}")
            }
        };
        writeln!(pre, "let {f} = move |__i: u64| -> {} {{ {body} }};", t.repr()).unwrap();
        Ok(f)
    }

    /// Binds a variable in the environment, also recording its index when iterating by index
    fn bind_iter(&mut self, env: &mut Env, name: &str, et: &Ty, indexed: bool) -> R<(String, String)> {
        let lx = rid(name);
        if indexed {
            let id = self.ty_id(et)?;
            // The loop variable is an index; decode it via table lookup where the value is needed
            env.locals.insert(name.to_string(), (format!("dec_{id}({lx})"), et.clone()));
            env.idx.insert(name.to_string(), (et.clone(), lx.clone()));
            return Ok((lx.clone(), lx));
        }
        env.locals.insert(name.to_string(), (lx.clone(), et.clone()));
        env.idx.remove(name);
        Ok((lx.clone(), lx))
    }

    /// `x \in S`, where the value of x is already held in the variable named by `x`.
    fn gen_member(&mut self, x: &str, xt: &Ty, s: &Expr, env: &Env) -> R<String> {
        // TLC makes the strings of a constant set when it evaluates the membership (the set is
        // evaluated here only if it has an operation that can make one: it may be large)
        let ops = ["\\o", "Append", "Head", "Tail", "SubSeq", "ToString"];
        let made = match s.any(&|e| matches!(e, Expr::Call(f, _) if ops.contains(&f.as_str())) || matches!(e, Expr::Except(..))) {
            true => self.try_const_made(s, env).1,
            false => Made::default(),
        };
        let code = self.gen_member_of(x, xt, s, env)?;
        Ok(self.note_folded(code, &made))
    }

    /// Whether TLC holds the value of e as a set of its elements (a set written out, a set from the
    /// state or a definition, `{f(y) : y \in S}`, or a union of such sets), which it unites with
    /// another set into a new set without sorting it (`SetEnumValue.cup`)
    fn enum_like(e: &Expr) -> bool {
        match e.strip() {
            Expr::SetLit(_) | Expr::Ident(_, _) | Expr::SetMap(..) => true,
            Expr::Bin(BOp::Cup, a, b) => Self::enum_like(a) || Self::enum_like(b),
            _ => false,
        }
    }

    /// `x \in S` where x is a string and S holds tuples, or the other way round, and TLC builds S
    /// where it is used without sorting it, so that it asks each element whether it equals x (see
    /// `tuple_str_eq`): `{f(y) : y \in S}`, and `A \cup B` with A held as a set of its elements
    /// (`enum_like`). Measured on TLC 2.19 (`tests/tlc/TupleStrCup`): TLC unites A with B by
    /// copying A's elements and adding B's, unsorted, so `s \in TS \cup {}` asks each tuple of TS
    /// while `s \in TS` searches the sorted TS and fails; when A is empty the union is B itself.
    /// None for any other membership
    fn member_unsorted(&mut self, x: &str, xt: &Ty, s: &Expr, env: &Env) -> R<Option<String>> {
        let s = s.strip();
        let (a, b) = match s {
            Expr::Bin(BOp::Cup, a, b) if Self::enum_like(a) => (a.as_ref(), Some(b.as_ref())),
            Expr::SetMap(..) => (s, None),
            _ => return Ok(None),
        };
        let tupleish = |t: &Ty| tuple_elems(t).is_some() || matches!(t, Ty::Seq(_));
        let Ok((_, st)) = self.gen(s, env, None) else { return Ok(None) };
        let Ty::Set(et) = &st else { return Ok(None) };
        if !((tupleish(et) && self.has_str(xt)) || (self.has_str(et) && tupleish(xt))) {
            return Ok(None);
        }
        let et = et.as_ref().clone();
        let e = self.fresh("e");
        let Some(eq) = self.tuple_str_eq(&e, &et, x, xt, env)? else { return Ok(None) };
        let Some(b) = b else {
            let (sc, t) = self.gen(s, env, Some(&st))?;
            let sc = self.coerce(sc, &t, &st)?;
            let it = self.s_iter("__set", &st)?;
            return Ok(Some(format!("{{ let __set = {sc}; let __any = {it}.any(|{e}| {eq}); __any }}")));
        };
        if matches!(a.strip(), Expr::SetLit(xs) if xs.is_empty()) {
            return self.gen_member_of(x, xt, b, env).map(Some);
        }
        let (ac, at) = self.gen(a, env, Some(&st))?;
        let ac = self.coerce(ac, &at, &st)?;
        let (bc, bt) = self.gen(b, env, Some(&st))?;
        let bc = self.coerce(bc, &bt, &st)?;
        let in_b = self.gen_member_of(x, xt, b, env)?;
        let n = self.s_card("__a", &st);
        let (ia, ib) = (self.s_iter("__a", &st)?, self.s_iter("__b", &st)?);
        Ok(Some(format!(
            "{{ let __a = {ac}; let __b = {bc}; if {n} == 0 {{ {in_b} }} else {{ let __any = {ia}.chain({ib}).any(|{e}| {eq}); __any }} }}"
        )))
    }

    fn gen_member_of(&mut self, x: &str, xt: &Ty, s: &Expr, env: &Env) -> R<String> {
        use Expr::*;
        // A set written out where it is used, holding tuples and x a string or the other way
        // round: TLC asks each element, in the order written, whether it equals x (a set from a
        // definition or the state is sorted first, and comparing then fails)
        if let SetLit(xs) = s {
            let elems: Vec<(String, Ty)> = xs.iter().map(|e| self.gen(e, env, Some(xt))).collect::<R<_>>().unwrap_or_default();
            let mut special = false;
            let mut parts = vec![];
            for (c, t) in &elems {
                match self.tuple_str_eq(c, t, x, xt, env)? {
                    Some(code) => {
                        special = true;
                        parts.push(code);
                    }
                    None => {
                        let mut env2 = env.clone();
                        env2.bind("#elem", c.clone(), t.clone());
                        env2.bind("#x", x.to_string(), xt.clone());
                        let eq = Bin(BOp::Eq, Ident("#elem".into(), NOPOS).b(), Ident("#x".into(), NOPOS).b());
                        parts.push(self.gen_as(&eq, &env2, &Ty::Bool)?);
                    }
                }
            }
            if special {
                return Ok(format!("({})", parts.join(" || ")));
            }
        }
        if let Some(code) = self.member_unsorted(x, xt, s, env)? {
            return Ok(code);
        }
        // Whether TLC builds the set here as written, or has it sorted (see the clash below)
        let written = self.built(s, env);
        let s = s.strip();
        // TLC stops with an error on a tuple in SUBSET S, [a : S], BOOLEAN, Nat, Int, or a..b, and
        // treats it as a function in [S -> T]; none of these is compiled
        if tuple_elems(xt).is_some() {
            // A tuple is the function over 1..n of its elements: in [D -> R] when D is 1..n and
            // each element is in R
            if let FunSet(d, r) = s {
                let n = tuple_elems(xt).unwrap().len();
                let one_to_n: BTreeSet<Value> = (1..=n as i64).map(Value::Int).collect();
                let same_domain = match self.try_const(d, env) {
                    Some(dv) if dv.as_set()? != &one_to_n => return Ok("false".into()),
                    Some(_) => "true".to_string(),
                    // D from the state: compare it with 1..n
                    None => {
                        let (dc, dt) = self.gen(d, env, None)?;
                        let (rc, rt) = self.gen(&Bin(BOp::Range, Num(1).b(), Num(n as i64).b()), env, Some(&dt))?;
                        let t = join(&dt, &rt)?;
                        format!("({} == {})", self.coerce(dc, &dt, &t)?, self.coerce(rc, &rt, &t)?)
                    }
                };
                let els: Vec<Ty> = tuple_elems(xt).unwrap().into_iter().cloned().collect();
                let mut conj = vec![same_domain];
                for (k, et) in els.iter().enumerate() {
                    let e = self.fresh("e");
                    let inner = self.gen_member(&e, et, r, env)?;
                    conj.push(format!("{{ let {e} = {x}{}; {inner} }}", rec_field(n, k)));
                }
                return Ok(format!("({})", conj.join(" && ")));
            }
            if matches!(s, Un(UOp::Subset, _) | RecSet(_) | Bin(BOp::Range, ..))
                || matches!(s, Ident(n, _) if ["BOOLEAN", "Nat", "Int", "STRING"].contains(&n.as_str()))
            {
                return Ok(eval_error_bool(&format!("Attempted to check if the tuple {x} is an element of {}", short(s))));
            }
        }
        match s {
            Un(UOp::Subset, t) => {
                let Ty::Set(et) = xt else { return Ok("false".into()) };
                let e = self.fresh("e");
                let inner = self.gen_member(&e, et, t, env)?;
                let it = self.s_iter(x, xt)?;
                // Bound first: an iterator borrowing x must not outlive the block x lives in
                return Ok(format!("{{ let __all = {it}.all(|{e}| {inner}); __all }}"));
            }
            // A sparse function: its keys in D and its values in R, and as many keys as D has
            // elements, which needs D finite (TLC fails to compare a domain with Nat, Int or STRING)
            FunSet(d, r) if matches!(xt, Ty::PFun(..)) && is_sparse_fun(xt) && self.try_const(d, env).is_none() => {
                if let Ident(n, _) = d.strip() {
                    if ["Nat", "Int", "STRING"].contains(&n.as_str()) && !env.locals.contains_key(n) {
                        let dt = Ty::Set(fun_kv(xt).0.into());
                        let (dc, _) = self.gen(&Un(UOp::Domain, Ident("#f".into(), NOPOS).b()), &{
                            let mut e2 = env.clone();
                            e2.locals.insert("#f".into(), (x.to_string(), xt.clone()));
                            e2
                        }, None)?;
                        let did = self.ty_id(&dt)?;
                        let msg = format!("Attempted to check equality of the set {{}} with the value:\n{n}");
                        return Ok(format!("{{ let __b: bool = eval_error(format!({msg:?}, fmt_{did}(&{dc}))); __b }}"));
                    }
                }
                return self.fun_set_member(x, xt, d, r, s, env);
            }
            FunSet(d, r) if matches!(xt, Ty::PFun(..)) && !is_sparse_fun(xt) => {
                let Ty::PFun(dt, ct) = xt else { unreachable!() };
                let did = self.ty_id(dt)?;
                let (e, k) = (self.fresh("e"), self.fresh("k"));
                let in_d = self.gen_member(&k, dt, d, env)?;
                let in_r = self.gen_member(&e, ct, r, env)?;
                return Ok(format!(
                    "{{ let __all = ({x}).iter().enumerate().all(|(__i, &(__p, {e}))| {{ let {k} = dec_{did}(__i as u64); __p == {in_d} && (!__p || {in_r}) }}); __all }}"
                ));
            }
            FunSet(d, r) => return self.fun_set_member(x, xt, d, r, s, env),
            Un(UOp::Domain, f) if self.lazy_fun_domain(f, env).is_some() => {
                let d = self.lazy_fun_domain(f, env).unwrap().clone();
                return self.gen_member(x, xt, &d, env);
            }
            RecSet(fs) => {
                let Ty::Rec(xf) = xt else { return Ok("false".into()) };
                let mut fs = fs.clone();
                fs.sort_by(|a, b| field_cmp(&a.0, &b.0));
                if fs.len() != xf.len() || fs.iter().zip(xf).any(|(a, b)| a.0 != b.0) {
                    return Ok("false".into());
                }
                let mut parts = vec![];
                for (i, ((_, se), (_, ft))) in fs.iter().zip(xf).enumerate() {
                    let e = self.fresh("e");
                    let inner = self.gen_member(&e, ft, se, env)?;
                    parts.push(format!("{{ let {e} = {x}{}; {inner} }}", rec_field(xf.len(), i)));
                }
                return Ok(format!("({})", parts.join(" && ")));
            }
            // Membership in A \X B is decided element by element, also for constant sets (that
            // avoids enumerating a large product)
            Call(f, parts) if f == "\\X" => {
                let Some(el) = tuple_elems(xt) else {
                    // TLC answers FALSE for a string or model value and stops with an error for
                    // anything else that is not a tuple
                    if matches!(xt, Ty::Enum(_)) {
                        return Ok("false".into());
                    }
                    // A function over 1..n is the tuple of its values
                    if let Ty::Fun(d, c) = xt {
                        if seq_domain(d) != Some(parts.len()) {
                            return Ok("false".into());
                        }
                        let mut conj = vec![];
                        for (i, part) in parts.iter().enumerate() {
                            let e = self.fresh("e");
                            let inner = self.gen_member(&e, c, part, env)?;
                            conj.push(format!("{{ let {e} = {x}[{i}]; {inner} }}"));
                        }
                        return Ok(format!("({})", conj.join(" && ")));
                    }
                    // As TLC reports it, with both values
                    if let (Ok((sc, st)), Ok(xid)) = (self.gen(s, env, None), self.ty_id(xt)) {
                        let sid = self.ty_id(&st)?;
                        let f = "Attempted to check if non-tuple\n{}\nis in the set of tuples:\n{}";
                        return Ok(format!(
                            "{{ let __s = {sc}; let __r: bool = eval_error(format!({f:?}, ppr(&fmt_{xid}(&{x})), ppr(&fmt_{sid}(&__s)))); __r }}"
                        ));
                    }
                    return Ok(eval_error_bool(&format!("Attempted to check if a non-tuple value of type {xt:?} is an element of a cartesian product")));
                };
                if el.len() != parts.len() {
                    return Ok("false".into());
                }
                let el: Vec<Ty> = el.into_iter().cloned().collect();
                let mut conj = vec![];
                for (i, (part, et)) in parts.iter().zip(&el).enumerate() {
                    let e = self.fresh("e");
                    let inner = self.gen_member(&e, et, part, env)?;
                    conj.push(format!("{{ let {e} = {x}{}; {inner} }}", rec_field(el.len(), i)));
                }
                return Ok(format!("({})", conj.join(" && ")));
            }
            Call(f, a) if f == "Seq" && a.len() == 1 => {
                let e = self.fresh("e");
                return Ok(match xt {
                    Ty::Seq(et) => {
                        let inner = self.gen_member(&e, et, &a[0], env)?;
                        // Bound first: an iterator borrowing x must not outlive the block x lives in
                        format!("{{ let __all = ({x}).iter().all(|{e}| {inner}); __all }}")
                    }
                    Ty::Fun(d, c) if seq_domain(d).is_some() => {
                        let inner = self.gen_member(&e, c, &a[0], env)?;
                        format!("{{ let __all = ({x}).iter().all(|&{e}| {inner}); __all }}")
                    }
                    Ty::Rec(fs) if is_tuple_fields(fs) => {
                        let mut conj = vec!["true".to_string()];
                        for (k, (_, t)) in fs.iter().enumerate() {
                            let inner = self.gen_member(&e, t, &a[0], env)?;
                            conj.push(format!("{{ let {e} = {x}{}; {inner} }}", rec_field(fs.len(), k)));
                        }
                        format!("({})", conj.join(" && "))
                    }
                    _ => "false".into(),
                });
            }
            Ident(n, _) if n == "BOOLEAN" => return Ok(matches!(xt, Ty::Bool).to_string()),
            Ident(n, _) if n == "Any" => return Ok("true".into()),
            // x \in UNION {[1..n -> S] : n \in R}: the length in R and each element in S
            _ if crate::compile::bounded_seq(s).is_some() && matches!(xt, Ty::Seq(_)) => {
                let (r, el) = crate::compile::bounded_seq(s).unwrap();
                let Ty::Seq(et) = xt else { unreachable!() };
                let (l, e) = (self.fresh("l"), self.fresh("e"));
                let in_r = self.gen_member(&l, &Ty::Int(0, self.qcap as i64), r, env)?;
                let in_s = self.gen_member(&e, et, el, env)?;
                return Ok(format!("{{ let {l} = ({x}).len as i64; let __all = {in_r} && ({x}).iter().all(|{e}| {in_s}); __all }}"));
            }
            Ident(n, _) if n == "Nat" => {
                return Ok(if matches!(xt, Ty::Int(..) | Ty::IntAtom(..)) { format!("({x} >= 0)") } else { "false".into() })
            }
            // TRUE for a string, FALSE for a model value, and an error for anything else, as in TLC
            Ident(n, _) if n == "STRING" && !env.locals.contains_key(n) => {
                let err = |what: &str| format!("Attempted to check if the value:\n{what}\nis an element of STRING.");
                return Ok(match xt {
                    Ty::Enum(d) => {
                        let strs: Vec<String> = d.iter().filter(|&&a| !self.atoms.is_model(a)).map(|a| a.to_string()).collect();
                        match strs.len() {
                            0 => "false".into(),
                            n if n == d.len() => "true".into(),
                            _ => format!("matches!({x}, {})", strs.join(" | ")),
                        }
                    }
                    Ty::IntAtom(..) => {
                        let tid = self.ty_id(xt)?;
                        format!(
                            "(if {x} < i64::MIN + 65536 {{ IS_STR[({x} - i64::MIN) as usize] }} else {{ let __b: bool = eval_error(format!({:?}, fmt_{tid}(&{x}))); __b }})",
                            err("{}")
                        )
                    }
                    _ => {
                        let tid = self.ty_id(xt)?;
                        format!("{{ let __b: bool = eval_error(format!({:?}, fmt_{tid}(&{x}))); __b }}", err("{}"))
                    }
                });
            }
            Ident(n, _) if n == "Int" => {
                return Ok(match xt {
                    Ty::Int(..) => "true".into(),
                    Ty::IntAtom(..) => format!("({x} >= i64::MIN + 65536)"),
                    _ => "false".into(),
                })
            }
            Bin(BOp::Range, a, b) => {
                let (ac, _) = self.gen_int_of("DotDot", false, true, a, env)?;
                let (bc, _) = self.gen_int_of("DotDot", false, true, b, env)?;
                // A value that is not an integer: TLC stops with an error
                let fail = |id: usize| {
                    format!(
                        "{{ let (__a, __b) = ({ac}, {bc}); eval_error(format!(\"Attempted to check if the value:\\n{{}}\\nis in the integer interval {{}}..{{}}\", ppr(&fmt_{id}(&{x})), __a, __b)) }}"
                    )
                };
                return Ok(match xt {
                    Ty::Int(..) => format!("({ac} <= {x} && {x} <= {bc})"),
                    Ty::IntAtom(..) => {
                        let id = self.ty_id(xt)?;
                        format!("(if {x} >= i64::MIN + 65536 {{ {ac} <= {x} && {x} <= {bc} }} else {} )", fail(id))
                    }
                    _ => {
                        let id = self.ty_id(xt)?;
                        fail(id)
                    }
                });
            }
            Bin(op @ (BOp::Cup | BOp::Cap | BOp::SetMinus), a, b) if self.try_const(s, env).is_none() => {
                let l = self.gen_member(x, xt, a, env)?;
                let r = self.gen_member(x, xt, b, env)?;
                return Ok(match op {
                    BOp::Cup => format!("({l} || {r})"),
                    BOp::Cap => format!("({l} && {r})"),
                    _ => format!("({l} && !{r})"),
                });
            }
            // x \in UNION {S}: x \in S, without enumerating S. With more sets TLC compares them to
            // build the set of sets, which fails for a set it cannot enumerate (measured)
            Un(UOp::Union, ss) if matches!(ss.strip(), SetLit(v) if v.len() == 1) && self.try_const(s, env).is_none() => {
                let SetLit(ss) = ss.strip() else { unreachable!() };
                return self.gen_member(x, xt, &ss[0], env);
            }
            SetFilter(y, t, p) if self.try_const(s, env).is_none() => {
                let m = self.gen_member(x, xt, t, env)?;
                let mut env2 = env.clone();
                env2.locals.insert(y.clone(), (x.to_string(), xt.clone()));
                let pc = self.gen_as(p, &env2, &Ty::Bool)?;
                return Ok(format!("({m} && {pc})"));
            }
            _ => {}
        }
        if let Some(v) = self.try_const(s, env) {
            // A string (Real of the Reals module is the string "Reals"): TLC fails when it
            // evaluates the membership
            if let Value::Atom(a) = v {
                if !self.atoms.is_model(a) {
                    let tid = self.ty_id(xt)?;
                    let msg = format!("Attempted to check if the value:\n{{}}\nis an element of the string {}", self.atoms.show(a));
                    return Ok(format!("{{ let __b: bool = eval_error(format!({msg:?}, fmt_{tid}(&{x}))); __b }}"));
                }
            }
            let set = v.as_set()?;
            if let Some(code) = self.member_mixed(x, xt, set)? {
                return Ok(code);
            }
            let mut fits: Vec<&Value> = vec![];
            let mut clash = None;
            for e in set {
                match self.tuple_cmp(xt, &ty_of_value(e)?).map_err(|m| format!("{m}: {}", short(s)))? {
                    Cmp::Normal if xt.conforms(e) => fits.push(e),
                    Cmp::Normal | Cmp::Unequal => {}
                    Cmp::Fails(m) => clash = Some(m),
                }
            }
            if let Some(m) = clash {
                // TLC stops comparing x with an element it cannot compare it with. If other
                // elements might match first, whether it stops depends on its order: reject
                if !fits.is_empty() {
                    return Err(format!("{m}: {}", short(s)));
                }
                // A set from a definition is sorted: TLC searches it, comparing x first with the
                // element in the middle
                if !written {
                    if let Some(f) = self.compare_fails_msg(xt) {
                        let e = set.iter().nth(set.len() / 2).unwrap();
                        let et = crate::ppr::ppr(&crate::compile::show_value(self.atoms, e));
                        let xid = self.ty_id(xt)?;
                        return Ok(format!("{{ let __b: bool = eval_error(format!({f:?}, ppr(&fmt_{xid}(&{x})), {et:?})); __b }}"));
                    }
                }
                return Ok(eval_error_bool(&m));
            }
            if fits.is_empty() {
                return Ok("false".into());
            }
            let Ty::Set(mut et) = ty_of_value(&v)? else { unreachable!() };
            if narrows(xt, &et) {
                et = join(xt, &et)?.into();
            }
            let st = Ty::Set(et.clone());
            // Element by element, also for a set of more than 128 possible elements (records of
            // different fields), which would be an array of limited capacity
            if fits.len() <= 8 || !xt.is_scalar() || is_sparse(&st) {
                let lits: Vec<String> = fits.iter().map(|e| self.lit(e, xt)).collect::<R<_>>()?;
                // A chain of thousands of comparisons nests too deep for rustc: search a sorted copy
                if lits.len() > LIT_TABLE {
                    let tr = xt.repr();
                    let v = match const_lit(xt) {
                        true => format!("{{ static __A: [{tr}; {}] = [{}]; __A.to_vec() }}", lits.len(), lits.join(", ")),
                        false => format!("vec![{}]", lits.join(", ")),
                    };
                    return Ok(format!(
                        "{{ static __S: std::sync::OnceLock<Vec<{tr}>> = std::sync::OnceLock::new(); \
                         __S.get_or_init(|| {{ let mut __v: Vec<{tr}> = {v}; __v.sort(); __v }}).binary_search(&{x}).is_ok() }}"
                    ));
                }
                let parts: Vec<String> = lits.iter().map(|l| format!("{x} == {l}")).collect();
                return Ok(format!("({})", parts.join(" || ")));
            }
            let mask = self.lit(&v, &st)?;
            let eid = self.ty_id(&et)?;
            let xc = self.coerce(x.to_string(), xt, &et)?;
            return Ok(format!("{{ let __i = enc_{eid}({xc}); __i != u64::MAX && ({mask} >> __i) & 1 == 1 }}"));
        }
        if let SetLit(xs) = s {
            let mut parts = vec![];
            let mut clash = None;
            let mut comparable = false;
            for e in xs {
                let (c, t) = self.gen(e, env, Some(xt))?;
                if self.str_meets_int(xt, &t) {
                    let j = join(xt, &t)?;
                    let xc = self.coerce(x.to_string(), xt, &j)?;
                    let c = self.coerce(c, &t, &j)?;
                    parts.push(format!("mixed_eq({xc}, {c})"));
                    comparable = true;
                    continue;
                }
                match self.tuple_cmp(xt, &t)? {
                    Cmp::Normal => comparable = true,
                    Cmp::Unequal => {
                        parts.push(format!("{{ let _ = {c}; false }}"));
                        continue;
                    }
                    Cmp::Fails(m) => {
                        clash = Some(m);
                        parts.push(format!("{{ let _ = {c}; false }}"));
                        continue;
                    }
                }
                if narrows(&t, xt) {
                    // Compare in the joined type (converting the element could fail at run time)
                    let j = join(xt, &t)?;
                    let xc = self.coerce(x.to_string(), xt, &j)?;
                    let c = self.coerce(c, &t, &j)?;
                    parts.push(format!("{xc} == {c}"));
                } else if let Ok(c) = self.coerce_soft(c, &t, xt) {
                    parts.push(format!("{x} == {c}"));
                }
            }
            if let Some(m) = clash {
                if comparable {
                    return Err(format!("{m}: {}", short(s)));
                }
                return Ok(format!("({} || {})", parts.join(" || "), eval_error_bool(&m)));
            }
            return Ok(if parts.is_empty() { "false".into() } else { format!("({})", parts.join(" || ")) });
        }
        let (sc, st) = self.gen_val(s, env)?;
        if !matches!(st, Ty::Set(_)) {
            return Err(format!("\\in a non-set: {s:?}"));
        }
        self.s_has(&sc, &st, x, xt)
    }

    // ---------------------------------------------------------------- Actions

    /// Processes the conjuncts in `work` in order. Once all are consumed, emits code that pushes
    /// the successor state onto `out`.
    pub fn gen_action(&mut self, work: &[Expr], env: &Env, out: &mut String) -> R<()> {
        use Expr::*;
        let Some((h, rest)) = work.split_first() else {
            return self.emit_state(env, out);
        };
        let with = |x: Vec<Expr>| -> Vec<Expr> { x.into_iter().chain(rest.iter().cloned()).collect() };
        if let Label(n, pairs, body) = h {
            if is_bind(n) {
                // Where TLC computes successors, it evaluates the names again at each use (see
                // `expand::float_binds`): they are written out
                if n == BIND_ACT && env.primed.len() < self.vars.len() {
                    return self.gen_action(&with(vec![unbind(pairs, body)]), env, out);
                }
                let (lets, env2, body) = self.gen_bind(pairs, body, env)?;
                writeln!(out, "{lets}").unwrap();
                return self.gen_action(&with(vec![body]), &env2, out);
            }
        }
        if env.split && !env.init && self.gen_split(h, rest, env, out)? {
            return Ok(());
        }
        if env.phantom && !env.init {
            if let Some(r) = self.gen_phantom(h, rest, env, out) {
                return r;
            }
        }
        match h.strip() {
            // [A]_v is A \/ UNCHANGED v (TLC follows both)
            BoxAction(a, v) => {
                let e = Or(vec![a.as_ref().clone(), Un(UOp::Unchanged, v.clone())]);
                return self.gen_action(&with(vec![e]), env, out);
            }
            // UNCHANGED <<x, e>>: as TLC does, a variable is assigned (or compared) and any other
            // expression is compared as e' = e, in order
            Un(UOp::Unchanged, x) if Self::unchanged_vars(x, &mut vec![]).is_err() => {
                let mut leaves = vec![];
                Self::unchanged_leaves(x, &mut leaves);
                let parts = leaves
                    .into_iter()
                    .map(|l| match l.strip() {
                        Ident(n, _) if self.is_var(n) => Un(UOp::Unchanged, l.clone().b()),
                        _ => Bin(BOp::Eq, Prime(l.clone().b()).b(), l.b()),
                    })
                    .collect();
                return self.gen_action(&with(parts), env, out);
            }
            _ => {}
        }
        // As in TLC, \/ and \E branch while some variables are still unassigned (so the number of
        // generated successors matches TLC). Once all are assigned, the rest is evaluated as a
        // boolean expression.
        let open = env.primed.len() < self.vars.len();
        let action = open && (h.is_action() || env.init);
        if !open && h.is_action() && !self.only_reads_assigned(h, env) {
            return Err(format!("unsupported action form: {}", short(h)));
        }
        // Where an action-level CASE is written (see ast::AT): kept from its label to the CASE
        if let Label(n, _, b) = h {
            if let Some(p) = err_pos_of(n).filter(|_| matches!(b.strip(), Case(..))) {
                self.case_at = Some(p.to_string());
            }
        }
        let case_at = if matches!(h, Label(..)) { None } else { self.case_at.take() };
        match h {
            Label(_, _, body) => return self.gen_action(&with(vec![body.as_ref().clone()]), env, out),
            And(xs) => return self.gen_action(&with(xs.clone()), env, out),
            Or(xs) if open => {
                for x in xs {
                    out.push_str("{\n");
                    // Renew per branch so writes in one branch do not leak into the others
                    let env2 = self.renew_work(env, out);
                    self.gen_action(&with(vec![x.clone()]), &env2, out)?;
                    out.push_str("}\n");
                }
                return Ok(());
            }
            Quant(true, bs, body) if open => {
                if let Some(made) = bs.iter().find_map(|(_, s)| match self.try_const_made(s, env) {
                    (Some(v), made) if v.as_set().is_ok_and(|x| x.is_empty()) => Some(made),
                    _ => None,
                }) {
                    let notes = self.fold_notes(&made);
                    out.push_str(&notes);
                    return Ok(());
                }
                let mut env2 = env.clone();
                let mut closes = 0;
                // TLC varies the first bound variable fastest: `\E x \in S, y \in T` loops over T
                // outside and S inside. The sets cannot refer to the other variables (SANY rejects
                // that), so the order of the loops is free
                for (x, s) in bs.iter().rev() {
                    let split = env.split && !self.mentions_state(s);
                    if split {
                        self.split_warning = Some(vec![]);
                    }
                    let r = self.iter_of_indexed(s, &env2);
                    if split {
                        let w = self.split_warning.take().unwrap();
                        self.split_warns.extend(w);
                    }
                    let (it, et, ix) = match r {
                        Ok(x) => x,
                        // During inference, proceed past sets of still-unknown type, treating the
                        // bound variable as an element of some type
                        Err(_) if self.infer.is_some() => (String::new(), Ty::Enum(vec![]), None),
                        Err(e) => return Err(e),
                    };
                    let (lx, _) = self.bind_iter(&mut env2, x, &et, ix.is_some())?;
                    writeln!(out, "for {lx} in {it} {{").unwrap();
                    closes += 1;
                    // Renew on every iteration so writes from the previous one do not carry over
                    env2 = self.renew_work(&env2, out);
                }
                // While splitting, TLC makes an action of each element: the actions of the body
                // count once per element
                let sizes: Option<Vec<usize>> = bs
                    .iter()
                    .map(|(_, s)| self.try_const(s, env).and_then(|v| v.as_set().ok().map(|x| x.len())))
                    .collect();
                let before = self.actions;
                self.gen_action(&with(vec![body.as_ref().clone()]), &env2, out)?;
                if let (true, Some(sizes)) = (env.split, sizes) {
                    self.actions = before + (self.actions - before) * sizes.iter().product::<usize>();
                }
                out.push_str(&"}\n".repeat(closes));
                return Ok(());
            }
            // \A over a constant set is the conjunction over its elements, in TLC's order (the
            // first bound variable varies fastest), so it can assign variables
            Quant(false, bs, body)
                if action && !self.only_reads_assigned(h, env)
                    || env.init && body.any(&|e| matches!(e, Ident(n, _) if self.is_var(n) && !env.primed.contains_key(n))) =>
            {
                let mut all = Made::default();
                let sets: Option<Vec<(String, Vec<Value>)>> = bs
                    .iter()
                    .map(|(x, s)| {
                        let (v, made) = self.try_const_made(s, env);
                        all.warns.extend(made.warns);
                        all.strs.extend(made.strs);
                        Some((x.clone(), v?.as_set().ok()?.iter().cloned().collect()))
                    })
                    .collect();
                match sets {
                    Some(sets) => {
                    let notes = self.fold_notes(&all);
                    out.push_str(&notes);
                    let total: usize = sets.iter().map(|(_, v)| v.len()).product();
                    let mut env2 = env.clone();
                    let mut items = vec![];
                    for k in 0..total {
                        let mut b = body.as_ref().clone();
                        let mut r = k;
                        for (x, vals) in &sets {
                            let v = &vals[r % vals.len()];
                            r /= vals.len();
                            let t = ty_of_value(v)?;
                            let code = self.lit(v, &t)?;
                            let y = self.fresh(&format!("{x}_e"));
                            env2.bind(&y, code, t);
                            env2.vals.insert(y.clone(), v.clone());
                            b = rename_ident(&b, x, &y);
                        }
                        items.push(b);
                    }
                    return self.gen_action(&with(items), &env2, out);
                    }
                    // In Init, a condition on what is assigned so far: evaluated as a boolean below
                    None if env.init => {}
                    None => return self.gen_forall(bs, body, rest, env, out),
                }
            }
            // A recursive operator called with constant arguments in an action: its body, with
            // the arguments bound (as TLC evaluates it), so that it can assign variables
            RecCall(i, args) if open && self.rec_assigns(*i, env) => {
                // TLC evaluates an argument where the body first reads its parameter: noted here
                // only for a parameter the body reads
                let rd = crate::expand::rec_def(*i);
                let mut all = Made::default();
                let vals: Option<Vec<Value>> = args
                    .iter()
                    .zip(rd.params.iter().map(Some).chain(std::iter::repeat(None)))
                    .map(|(a, p)| {
                        let (v, made) = self.try_const_made(a, env);
                        if p.is_some_and(|p| rd.body.any(&|e| matches!(e, Ident(n, _) if n == p))) {
                            all.warns.extend(made.warns);
                            all.strs.extend(made.strs);
                        }
                        v
                    })
                    .collect();
                let Some(vals) = vals else {
                    return self.gen_rec_action(*i, args, rest, env, out);
                };
                let notes = self.fold_notes(&all);
                out.push_str(&notes);
                if self.unroll >= 2000 {
                    return Err(format!("recursive operator `{}` in an action recurses more than 2000 levels", crate::expand::rec_def(*i).name));
                }
                let rd = crate::expand::rec_def(*i);
                let mut b = rd.body.clone();
                let mut env2 = env.clone();
                for (p, v) in rd.params.iter().zip(&vals) {
                    let t = ty_of_value(v)?;
                    let code = self.lit(v, &t)?;
                    let y = self.fresh(&format!("{p}_r"));
                    env2.bind(&y, code, t);
                    env2.vals.insert(y.clone(), v.clone());
                    b = rename_ident(&b, p, &y);
                }
                if env.split {
                    if let Some(p) = self.def_pos.get(&rd.name) {
                        b = at_pos(p, b);
                    }
                }
                self.unroll += 1;
                let r = self.gen_action(&with(vec![Label(rd.name.clone(), args.clone(), b.b())]), &env2, out);
                self.unroll -= 1;
                return r;
            }
            // The elements of `\A x \in S : B` (S from the state) from the i-th on (gen_forall)
            Call(f, a) if f == FORALL_REST => {
                let [Ident(key, _), Ident(x, _), b, Num(i), set] = a.as_slice() else { unreachable!() };
                let (els, et) = env.locals[key].clone();
                if self.only_reads_assigned(b, env) {
                    // Nothing left to assign: B holds for each remaining element
                    let k = self.fresh("k");
                    let mut env2 = env.clone();
                    env2.bind(x, format!("{els}[{k}]"), et);
                    let c = match self.gen_as(b, &env2, &Ty::Bool) {
                        Err(_) if self.infer.is_some() => "true".into(),
                        r => r?,
                    };
                    writeln!(out, "if ({i}..{els}.len()).all(|{k}| {c}) {{").unwrap();
                    self.gen_action(rest, env, out)?;
                    out.push_str("}\n");
                    return Ok(());
                }
                // The next element may assign: one level per element the set can hold
                match et.size() {
                    Some(n) if *i as u64 >= n => return self.gen_action(rest, env, out),
                    _ if *i == 0 => {}
                    Some(n) if n <= 16 => {}
                    // A set that can hold more: the remaining elements are walked at run time
                    _ if self.infer.is_none() => {
                        let id = self.forall_rec(x, b);
                        let call = RecCall(id, vec![set.clone(), Num(i + 1)]);
                        return self.gen_action(&with(vec![call]), env, out);
                    }
                    _ => return self.gen_action(rest, env, out),
                }
                writeln!(out, "if {els}.len() <= {i} {{").unwrap();
                let env0 = self.renew_work(env, out);
                self.gen_action(rest, &env0, out)?;
                out.push_str("} else {\n");
                let mut env2 = self.renew_work(env, out);
                let e = self.fresh("e");
                writeln!(out, "let {e} = {els}[{i}];").unwrap();
                env2.bind(x, e, et);
                let next = Call(FORALL_REST.into(), vec![Ident(key.clone(), NOPOS), Ident(x.clone(), NOPOS), b.clone(), Num(i + 1), set.clone()]);
                self.gen_action(&with(vec![b.clone(), next]), &env2, out)?;
                out.push_str("}\n");
                return Ok(());
            }
            If(c, a, b) if action => {
                // A condition known here (as in an unrolled recursive operator): only its branch
                if let (Some(Value::Bool(cv)), made) = self.try_const_made(c, env) {
                    let notes = self.fold_notes(&made);
                    out.push_str(&notes);
                    let e = if cv { a } else { b };
                    return self.gen_action(&with(vec![e.as_ref().clone()]), env, out);
                }
                let cc = match self.gen_as(c, env, &Ty::Bool) {
                    Err(_) if self.infer.is_some() => "true".into(),
                    r => r?,
                };
                writeln!(out, "if {cc} {{").unwrap();
                let e1 = self.renew_work(env, out);
                self.gen_action(&with(vec![a.as_ref().clone()]), &e1, out)?;
                out.push_str("} else {\n");
                let e2 = self.renew_work(env, out);
                self.gen_action(&with(vec![b.as_ref().clone()]), &e2, out)?;
                out.push_str("}\n");
                return Ok(());
            }
            // TLC computes successors through a CASE among the conjuncts of an action, also one that
            // assigns nothing (which matters for its error message)
            Case(arms, other) => {
                for (i, (p, v)) in arms.iter().enumerate() {
                    let pc = match self.gen_as(p, env, &Ty::Bool) {
                        Err(_) if self.infer.is_some() => "true".into(),
                        r => r?,
                    };
                    writeln!(out, "{}if {pc} {{", if i > 0 { "else " } else { "" }).unwrap();
                    let e = self.renew_work(env, out);
                    self.gen_action(&with(vec![v.clone()]), &e, out)?;
                    out.push_str("}\n");
                }
                out.push_str("else {\n");
                let eo = self.renew_work(env, out);
                match other {
                    Some(o) => self.gen_action(&with(vec![o.as_ref().clone()]), &eo, out)?,
                    None => {
                        // TLC's message names what it was computing
                        let when = if env.enabled { "ENABLED" } else if env.init { "initial states" } else { "next states" };
                        let msg = with_at(&format!("In computing {when}, TLC encountered a CASE with no conditions true."), &case_at);
                        writeln!(out, "eval_error({msg:?}.into());").unwrap();
                    }
                }
                out.push_str("}\n");
                return Ok(());
            }
            Bin(BOp::Implies, a, b) if action => {
                // a => B is IF a THEN B ELSE TRUE
                let e = If(a.clone(), b.clone(), Bool(true).b());
                return self.gen_action(&with(vec![e]), env, out);
            }
            Bin(BOp::Eq, lhs, rhs) => {
                if let Some(v) = self.target(lhs, env) {
                    let t = self.var_ty(&v);
                    if self.infer.is_some() {
                        match self.gen(rhs, env, Some(&t)) {
                            Ok((_, rt)) => self.record(&v, rt),
                            Err(e) => {
                                self.infer_errs.entry(v.clone()).or_insert(e);
                            }
                        }
                        let mut env2 = env.clone();
                        env2.primed.insert(v, ("__inferred".into(), t));
                        return self.gen_action(rest, &env2, out);
                    }
                    let mut env2 = env.clone();
                    let w = self.work_var(&mut env2, out);
                    let place = format!("{w}.v_{v}");
                    // x' = [x EXCEPT ...] updates the state under construction in place
                    // (avoiding a copy out and back in)
                    match rhs.strip() {
                        Except(base, ups) if matches!(base.strip(), Ident(n, _) if *n == v) => {
                            self.gen_except_into(&place, ups, &t, &env2, except_pos(base), out)?;
                        }
                        _ => match self.gen_set_update(&place, &v, rhs, &t, env) {
                            Some(code) => out.push_str(&code),
                            None => {
                                let c = self.gen_as(rhs, env, &t)?;
                                writeln!(out, "{place} = {c};").unwrap();
                            }
                        },
                    }
                    env2.primed.insert(v, (place, t));
                    return self.gen_action(rest, &env2, out);
                }
            }
            Bin(BOp::In, lhs, s) => {
                if let Some(v) = self.target(lhs, env) {
                    let t = self.var_ty(&v);
                    if self.infer.is_some() {
                        match self.iter_of(s, env) {
                            Ok((_, et)) => self.record(&v, et),
                            Err(e) => {
                                self.infer_errs.entry(v.clone()).or_insert(e);
                            }
                        }
                        let mut env2 = env.clone();
                        env2.primed.insert(v, ("__inferred".into(), t));
                        return self.gen_action(rest, &env2, out);
                    }
                    // x \in "Reals" (Real): TLC cannot enumerate a string
                    if let Some(Value::Atom(a)) = self.try_const(s, env) {
                        if !self.atoms.is_model(a) {
                            let when = if env.init { "initial" } else { "next" };
                            let msg = with_at(&format!("In computing {when} states, the right side of \\IN is not enumerable."), &err_at(s));
                            writeln!(out, "eval_error({msg:?}.into());").unwrap();
                            return Ok(());
                        }
                    }
                    let (it, et, ix) = self.iter_of_indexed(s, env)?;
                    let x = self.fresh("x");
                    let p = self.fresh(&format!("p_{v}_"));
                    // When iterating by index, decode back to the value
                    let val = match ix {
                        Some(_) => format!("dec_{}({x})", self.ty_id(&et)?),
                        None => x.clone(),
                    };
                    let c = self.coerce(val, &et, &t)?;
                    writeln!(out, "for {x} in {it} {{ let {p}: {} = {c};", t.repr()).unwrap();
                    let mut env2 = self.renew_work(env, out);
                    let w = self.work_var(&mut env2, out);
                    writeln!(out, "{w}.v_{v} = {p};").unwrap();
                    let place = format!("{w}.v_{v}");
                    env2.primed.insert(v, (place, t));
                    self.gen_action(rest, &env2, out)?;
                    out.push_str("}\n");
                    return Ok(());
                }
            }
            Un(UOp::Unchanged, x) => {
                let mut names = vec![];
                Self::unchanged_vars(x, &mut names)?;
                let mut env2 = env.clone();
                let mut guards = vec![];
                for v in names {
                    if !self.is_var(&v) {
                        return Err(format!("UNCHANGED of non-variable `{v}`"));
                    }
                    if let Some((p, _)) = env2.primed.get(&v) {
                        guards.push(format!("{p} == s.v_{v}"));
                    } else {
                        let t = self.var_ty(&v);
                        // The state under construction is a copy of *s, so nothing needs writing
                        let p = match &env2.work {
                            Some(w) => format!("{w}.v_{v}"),
                            None => format!("s.v_{v}"),
                        };
                        env2.primed.insert(v.clone(), (p, t));
                    }
                }
                if guards.is_empty() {
                    return self.gen_action(rest, &env2, out);
                }
                writeln!(out, "if {} {{", guards.join(" && ")).unwrap();
                self.gen_action(rest, &env2, out)?;
                out.push_str("}\n");
                return Ok(());
            }
            _ => {}
        }
        // Anything else is evaluated as a condition: as in TLC, reading a primed variable the action
        // has not determined yet is an error when evaluated
        if let (Some(Value::Bool(b)), made) = self.try_const_made(h, env) {
            // What TLC makes and warns about each time it evaluates it
            let notes = self.fold_notes(&made);
            out.push_str(&notes);
            return if b { self.gen_action(rest, env, out) } else { Ok(()) };
        }
        let c = match self.gen_as(h, env, &Ty::Bool) {
            Err(_) if self.infer.is_some() => "true".into(),
            r => r.map_err(|m| format!("{m}\n  in: {}", short(h)))?,
        };
        writeln!(out, "if {c} {{").unwrap();
        self.gen_action(rest, env, out)?;
        out.push_str("}\n");
        Ok(())
    }

    /// While computing whether an action is enabled, TLC binds a primed variable by its name in a
    /// partial state (`TLCStateFun`) and reads it from there. A variable of an instantiated module
    /// that the INSTANCE substitutes (see ast::SUBVAR) is bound the same way, as if it were a
    /// variable of its own: `x' = e` and `x' \in S` bind it when it is not bound yet, UNCHANGED x
    /// binds it to what x stands for, and `x'` elsewhere reads it (failing when it is not bound),
    /// never the substitution (measured on TLC 2.19, `tests/tlc/EnSubst*`). The binding does not
    /// assign any variable of the state. Returns None for a conjunct that binds nothing.
    fn gen_phantom(&mut self, h: &Expr, rest: &[Expr], env: &Env, out: &mut String) -> Option<R<()>> {
        use Expr::*;
        let unbound = |e: &Expr| match e.strip() {
            Prime(x) => crate::ast::subvar_of(x).map(|(n, _)| n.to_string()).filter(|n| !env.locals.contains_key(&phantom(n))),
            _ => None,
        };
        match h.strip() {
            Bin(BOp::Eq, lhs, rhs) => {
                let n = unbound(lhs)?;
                Some((|| {
                    let (c, t) = self.gen(rhs, env, None)?;
                    let x = self.fresh("ph");
                    writeln!(out, "{{ let {x} = {c};").unwrap();
                    let mut env2 = env.clone();
                    env2.bind(&phantom(&n), x, t);
                    self.gen_action(rest, &env2, out)?;
                    out.push_str("}\n");
                    Ok(())
                })())
            }
            Bin(BOp::In, lhs, s) => {
                let n = unbound(lhs)?;
                Some((|| {
                    let (it, et, ix) = self.iter_of_indexed(s, env)?;
                    let x = self.fresh("ph");
                    let val = match ix {
                        Some(_) => format!("dec_{}({x})", self.ty_id(&et)?),
                        None => x.clone(),
                    };
                    let y = self.fresh("ph");
                    writeln!(out, "for {x} in {it} {{ let {y} = {val};").unwrap();
                    let mut env2 = self.renew_work(env, out);
                    env2.bind(&phantom(&n), y, et);
                    self.gen_action(rest, &env2, out)?;
                    out.push_str("}\n");
                    Ok(())
                })())
            }
            Un(UOp::Unchanged, x) => {
                let mut leaves = vec![];
                Self::unchanged_leaves(x, &mut leaves);
                if !leaves.iter().any(|l| crate::ast::subvar_of(l).is_some()) {
                    return None;
                }
                let parts: Vec<Expr> = leaves
                    .into_iter()
                    .map(|l| match l.strip() {
                        Ident(n, _) if self.is_var(n) && crate::ast::subvar_of(&l).is_none() => Un(UOp::Unchanged, l.clone().b()),
                        _ => Bin(BOp::Eq, Prime(l.clone().b()).b(), l.b()),
                    })
                    .collect();
                let work: Vec<Expr> = parts.into_iter().chain(rest.iter().cloned()).collect();
                Some(self.gen_action(&work, env, out))
            }
            _ => None,
        }
    }

    /// `\A x \in S : B` that assigns variables, with S from the state. TLC evaluates it as the
    /// conjunction of B over the elements of S in order: an element can assign the variables not
    /// assigned yet, and once B only reads what is assigned, it is a test for the remaining
    /// elements. Over the empty set it is TRUE. Several bound variables nest, the first varying
    /// fastest.
    fn gen_forall(&mut self, bs: &[(String, Expr)], body: &Expr, rest: &[Expr], env: &Env, out: &mut String) -> R<()> {
        let (x, s) = bs.last().unwrap();
        let inner = if bs.len() > 1 { Expr::Quant(false, bs[..bs.len() - 1].to_vec(), body.clone().b()) } else { body.clone() };
        let (it, et, ix) = match self.iter_of_indexed(s, env) {
            Ok(x) => x,
            Err(_) if self.infer.is_some() => (String::new(), Ty::Enum(vec![]), None),
            Err(e) => return Err(e),
        };
        let els = self.fresh("els");
        let val = match ix {
            Some(_) => format!("dec_{}(__e)", self.ty_id(&et)?),
            None => "__e".into(),
        };
        writeln!(out, "let {els}: Vec<{}> = {it}.map(|__e| {val}).collect();", et.repr()).unwrap();
        let mut env2 = env.clone();
        let key = self.fresh("#els");
        env2.bind(&key, els, et);
        let first = Expr::Call(FORALL_REST.into(), vec![Expr::Ident(key, NOPOS), Expr::Ident(x.clone(), NOPOS), inner, Expr::Num(0), s.clone()]);
        let work: Vec<Expr> = std::iter::once(first).chain(rest.iter().cloned()).collect();
        self.gen_action(&work, &env2, out)
    }

    /// A recursive operator that assigns variables, called in an action with arguments from the
    /// state: a Rust function evaluates its body as an action and returns each state it builds,
    /// with the variables assigned by then (TLC evaluates the call as the body with the arguments
    /// bound, so the steps and their number are the same). The rest of the action continues from
    /// each, per set of assigned variables.
    fn gen_rec_action(&mut self, i: usize, args: &[Expr], rest: &[Expr], env: &Env, out: &mut String) -> R<()> {
        let rd = crate::expand::rec_def(i);
        if self.infer.is_some() {
            // Inferring types: the body a few levels deep shows what the call assigns
            if self.unroll >= 4 {
                return self.gen_action(rest, env, out);
            }
            let mut b = rd.body.clone();
            let mut env2 = env.clone();
            for (p, a) in rd.params.iter().zip(args) {
                let (c, t) = self.gen(a, env, None).unwrap_or((String::new(), Ty::Enum(vec![])));
                let y = self.fresh(&format!("{p}_r"));
                env2.bind(&y, c, t);
                b = rename_ident(&b, p, &y);
            }
            self.unroll += 1;
            let r = self.gen_action(&[b].into_iter().chain(rest.iter().cloned()).collect::<Vec<_>>(), &env2, out);
            self.unroll -= 1;
            return r;
        }
        let mut codes = vec![];
        let mut tys = vec![];
        for a in args {
            // Integers unbounded, as for `rec_fn`: one function serves n, n - 1, ...
            let (c, t) = self.gen(a, env, None)?;
            let w = unbounded_ints(&t);
            codes.push(self.coerce(c, &t, &w)?);
            tys.push(w);
        }
        let free = self.rec_free(&rd);
        for x in &free {
            let (c, t) = env.locals.get(x).cloned().ok_or(format!("recursive operator `{}` reads `{x}`, which is not bound where it is called", rd.name))?;
            codes.push(c);
            tys.push(t);
        }
        let mask_in = self.assigned_id(env);
        let (name, masks) = self.rec_action_fn(i, &rd, &free, &tys, mask_in, env.init)?;
        // In Init the state under construction holds what is assigned so far, which is all the
        // function reads of the variables
        let mut env1 = env.clone();
        let w0 = if env.init { self.work_var(&mut env1, out) } else { env.work.clone().unwrap_or("*s".into()) };
        let s0 = if env.init { format!("&{w0}") } else { "s".into() };
        let (w, m) = (self.fresh("w"), self.fresh("m"));
        writeln!(out, "for (mut {w}, {m}) in {name}({s0}, {w0}, {}) {{ match {m} {{", codes.join(", ")).unwrap();
        for mask in masks {
            writeln!(out, "{mask}u32 => {{").unwrap();
            let mut env2 = env.clone();
            env2.work = Some(w.clone());
            env2.primed = HashMap::new();
            for &k in &self.assigned_sets[mask as usize] {
                let (v, t) = self.vars[k].clone();
                env2.primed.insert(v.clone(), (format!("{w}.v_{v}"), t));
            }
            self.gen_action(rest, &env2, out)?;
            out.push_str("}\n");
        }
        out.push_str("_ => {} } }\n");
        Ok(())
    }

    /// The function of `gen_rec_action` for the recursive operator `i` with arguments of types
    /// `tys` (its parameters, then the identifiers `free` bound at the call site), called with the
    /// variables in `mask_in` assigned: its name and the sets of variables assigned when it
    /// returns. A call of itself inside uses the sets found so far, so the body is generated again
    /// until they settle.
    /// A recursive operator for the elements of `\A x \in S : B` from the k-th on (in the order
    /// the quantifier takes them), called as `F(S, k)`: IF k > Cardinality(S) THEN TRUE ELSE B with
    /// x the k-th element /\ F(S, k + 1). An action calling it with arguments from the state is a
    /// function that returns the states B builds (`gen_rec_action`), so the size of the generated
    /// code does not grow with the number of elements
    fn forall_rec(&mut self, x: &str, b: &Expr) -> usize {
        use Expr::*;
        let key = format!("{x}|{b:?}");
        if let Some(&id) = self.forall_recs.get(&key) {
            return id;
        }
        let n = self.forall_recs.len();
        let (sp, kp) = (format!("#forall_s{n}"), format!("#forall_k{n}"));
        let rd = |body| crate::expand::RecDef { name: "\\A".into(), params: vec![sp.clone(), kp.clone()], body };
        let id = crate::expand::add_rec_def(rd(Bool(true)));
        let elem = Call(FORALL_NTH.into(), vec![Ident(sp.clone(), NOPOS), Ident(kp.clone(), NOPOS)]);
        let next = RecCall(id, vec![Ident(sp.clone(), NOPOS), Bin(BOp::Add, Ident(kp.clone(), NOPOS).b(), Num(1).b())]);
        let more = And(vec![replace_expr(b, &Ident(x.to_string(), NOPOS), &elem), next]);
        let done = Bin(BOp::Gt, Ident(kp.clone(), NOPOS).b(), Call("Cardinality".into(), vec![Ident(sp.clone(), NOPOS)]).b());
        crate::expand::set_rec_def(id, rd(If(done.b(), Bool(true).b(), more.b())));
        self.forall_recs.insert(key, id);
        id
    }

    /// The number of the set of variables `env` has assigned (see `assigned_sets`)
    fn assigned_id(&mut self, env: &Env) -> u32 {
        let set: Vec<usize> = self.vars.iter().enumerate().filter(|(_, (v, _))| env.primed.contains_key(v)).map(|(k, _)| k).collect();
        match self.assigned_sets.iter().position(|m| *m == set) {
            Some(i) => i as u32,
            None => {
                self.assigned_sets.push(set);
                (self.assigned_sets.len() - 1) as u32
            }
        }
    }

    fn rec_action_fn(&mut self, i: usize, rd: &crate::expand::RecDef, free: &[String], tys: &[Ty], mask_in: u32, init: bool) -> R<(String, BTreeSet<u32>)> {
        let key = format!("{i}|{tys:?}|{mask_in}|{init}");
        if let Some((n, ms, done)) = self.ract.get(&key) {
            if *done || self.ract_progress.contains(&key) {
                return Ok((n.clone(), ms.clone()));
            }
        } else {
            if self.ract.keys().filter(|k| k.starts_with(&format!("{i}|"))).count() >= 16 {
                return Err(format!("recursive operator `{}`: the types of its arguments keep changing between calls", rd.name));
            }
            let n = format!("ract_{}", self.ract.len());
            self.ract.insert(key.clone(), (n, BTreeSet::new(), false));
        }
        let name = self.ract[&key].0.clone();
        let names: Vec<&String> = rd.params.iter().chain(free).collect();
        let mut env = Env::default();
        let mut sig = String::from("s: &State, mut __w: State, ");
        for (k, (x, t)) in names.iter().zip(tys).enumerate() {
            env.locals.insert(x.to_string(), (format!("a{k}"), t.clone()));
            write!(sig, "a{k}: {}, ", t.repr()).unwrap();
        }
        for &k in &self.assigned_sets[mask_in as usize] {
            let (v, t) = &self.vars[k];
            env.primed.insert(v.clone(), (format!("__w.v_{v}"), t.clone()));
        }
        env.init = init;
        env.work = Some("__w".into());
        env.sink = Some(key.clone());
        loop {
            let before = self.ract[&key].1.clone();
            let mut body = String::new();
            self.ract_progress.push(key.clone());
            let r = self.gen_action(&[rd.body.clone()], &env, &mut body);
            self.ract_progress.pop();
            r?;
            let f = format!(
                "#[allow(unused_mut, unused_variables)]\nfn {name}({sig}) -> Vec<(State, u32)> {{ rec_enter({:?}); let mut __res: Vec<(State, u32)> = Vec::new(); {{ {body} }} rec_leave(); __res }}\n",
                rd.name
            );
            self.rec_code.insert(name.clone(), f);
            let after = self.ract[&key].1.clone();
            if after == before {
                if self.ract_progress.is_empty() {
                    self.ract.get_mut(&key).unwrap().2 = true;
                }
                return Ok((name, after));
            }
        }
    }

    fn record(&mut self, v: &str, t: Ty) {
        let m = self.infer.as_mut().unwrap();
        let cur = m.remove(v).unwrap_or(Ty::Enum(vec![]));
        let j = join(&cur, &t).unwrap_or(t);
        m.insert(v.to_string(), j);
    }

    /// The assignment target (x' in Next, x in Init), if it is not yet assigned
    fn target(&self, e: &Expr, env: &Env) -> Option<String> {
        let n = match (e.strip(), env.init) {
            // Bound by its name while computing ENABLED (see gen_phantom)
            (Expr::Prime(x), false) if env.phantom && crate::ast::subvar_of(x).is_some() => return None,
            (Expr::Prime(x), false) => match x.strip() {
                Expr::Ident(n, _) => n.clone(),
                _ => return None,
            },
            (Expr::Ident(n, _), true) => n.clone(),
            _ => return None,
        };
        (self.is_var(&n) && !env.primed.contains_key(&n)).then_some(n)
    }

    /// Whether the recursive operator `i` may assign a variable here: it reads a variable the
    /// action has not determined (primed, or in Init unprimed)
    fn rec_assigns(&self, i: usize, env: &Env) -> bool {
        match self.rec_reads(i) {
            Ok((reads, primes, _)) => {
                let open = |v: &String| !env.primed.contains_key(v);
                if env.init { reads.iter().any(open) } else { primes.iter().any(open) }
            }
            Err(_) => false,
        }
    }

    fn only_reads_assigned(&self, e: &Expr, env: &Env) -> bool {
        match e {
            // A primed constant is the constant
            Expr::Prime(p) => match p.strip() {
                Expr::Ident(n, _) if self.is_var(n) => env.primed.contains_key(n),
                p => self.only_reads_assigned(p, env),
            },
            // UNCHANGED e reads e' (every variable in e primed)
            Expr::Un(UOp::Unchanged, v) => !v.any(&|x| matches!(x, Expr::Ident(n, _) if self.is_var(n) && !env.primed.contains_key(n))),
            // ENABLED A reads no primed variable of the step around it
            Expr::Un(UOp::Enabled, _) => true,
            e => e.children().into_iter().all(|c| self.only_reads_assigned(c, env)),
        }
    }

    /// The components of UNCHANGED e: the elements of (nested) tuples
    fn unchanged_leaves(e: &Expr, out: &mut Vec<Expr>) {
        match e.strip() {
            Expr::Tuple(xs) => xs.iter().for_each(|x| Self::unchanged_leaves(x, out)),
            _ => out.push(e.clone()),
        }
    }

    fn unchanged_vars(e: &Expr, out: &mut Vec<String>) -> R<()> {
        match e.strip() {
            Expr::Ident(n, _) => out.push(n.clone()),
            Expr::Tuple(xs) => {
                for x in xs {
                    Self::unchanged_vars(x, out)?;
                }
            }
            e => return Err(format!("UNCHANGED of {}", short(e))),
        }
        Ok(())
    }

    /// Statements that turn `place`, which holds the value of the sparse set variable `v`, into
    /// `e`, if `e` only adds elements to `v` and removes elements from it (`(v \ a) \cup b`).
    /// Building the new set elsewhere would copy the whole array out and back in.
    fn gen_set_update(&mut self, place: &str, v: &str, e: &Expr, st: &Ty, env: &Env) -> Option<String> {
        use Expr::*;
        if env.init || !is_sparse(st) {
            return None;
        }
        match e.strip() {
            Ident(n, _) if n == v => Some(String::new()),
            Bin(op @ (BOp::Cup | BOp::SetMinus), a, b) => {
                let base = self.gen_set_update(place, v, a, st, env)?;
                let method = if *op == BOp::Cup { "insert" } else { "remove" };
                Some(base + &self.gen_set_change(place, method, b, st, env)?)
            }
            _ => None,
        }
    }

    /// Statements that call `method` (insert or remove) on `place` for each element of the set `e`.
    /// None if an element may not fit the element type of `st`: coercing it would drop a field,
    /// and it could then equal an element it differs from.
    fn gen_set_change(&mut self, place: &str, method: &str, e: &Expr, st: &Ty, env: &Env) -> Option<String> {
        use Expr::*;
        let fits = |want: &Ty, got: &Ty| join(want, got).ok().as_ref() == Some(want);
        match e.strip() {
            SetLit(xs) => {
                let el = Self::elem_of(st);
                let mut code = String::new();
                for x in xs {
                    let (c, t) = self.gen(x, env, Some(&el)).ok()?;
                    if !fits(&el, &t) {
                        return None;
                    }
                    writeln!(code, "{place}.{method}({});", self.coerce(c, &t, &el).ok()?).unwrap();
                }
                Some(code)
            }
            If(c, x, y) => {
                let c = self.gen_as(c, env, &Ty::Bool).ok()?;
                let x = self.gen_set_change(place, method, x, st, env)?;
                let y = self.gen_set_change(place, method, y, st, env)?;
                Some(format!("if {c} {{\n{x}}} else {{\n{y}}}\n"))
            }
            _ => {
                let (c, t) = self.gen(e, env, Some(st)).ok()?;
                if !fits(st, &t) {
                    return None;
                }
                let c = self.coerce(c, &t, st).ok()?;
                let x = self.fresh("x");
                Some(format!("for {x} in ({c}).iter() {{ {place}.{method}({x}); }}\n"))
            }
        }
    }

    /// Applies EXCEPT updates directly to `place`; `@` refers to the original value at `place`.
    fn gen_except_into(
        &mut self,
        place: &str,
        ups: &[(Vec<Path>, Expr)],
        ft: &Ty,
        env: &Env,
        warn_at: Option<String>,
        out: &mut String,
    ) -> R<()> {
        // TLC's warning for an argument or field the value does not have (see `Except` in `gen`)
        let warn = match &warn_at {
            Some(at) => format!(" else {{ except_warning({at:?}); }}"),
            None => String::new(),
        };
        for (path, val) in ups {
            let (path, val) = self.split_dynamic_index(ft, path, val, env, warn_at.as_deref());
            let val = &val;
            let path = &self.resolve_path(ft, &path, env)?;
            let mut p = place.to_string();
            let mut cur = ft.clone();
            let mut conds = vec![];
            let mut at_name = None;
            for step in path {
                match (step, &cur) {
                    // Name of this EXCEPT's @, attached during expansion
                    (Path::Field(k), _) if k.starts_with('@') => at_name = Some(k.clone()),
                    (Path::Idx(i), Ty::Seq(e)) => {
                        let (ic, _) = self.gen_int(i, env)?;
                        let iv = self.fresh("i");
                        writeln!(out, "let {iv}: i64 = {ic};").unwrap();
                        conds.push(format!("{iv} >= 1 && {iv} <= ({p}).len as i64"));
                        p = format!("{p}.items[({iv} - 1) as usize]");
                        cur = e.as_ref().clone();
                    }
                    (Path::Idx(i), Ty::Fun(d, c)) => {
                        let known = match i.strip() {
                            Expr::Ident(n, _) => env.idx.get(n).filter(|(t, _)| *t == **d).map(|(_, v)| v.clone()),
                            _ => None,
                        };
                        match known {
                            Some(iv) => p = format!("{p}[{iv} as usize]"),
                            None => {
                                let did = self.ty_id(d)?;
                                let ic = self.gen_as(i, env, d)?;
                                let iv = self.fresh("i");
                                // An index outside the domain is a no-op (as in TLC)
                                writeln!(out, "let {iv} = enc_{did}({ic});").unwrap();
                                conds.push(format!("{iv} != u64::MAX"));
                                p = format!("{p}[{iv} as usize]");
                            }
                        }
                        cur = c.as_ref().clone();
                    }
                    // A function over part of a type: a key outside its domain leaves it
                    // unchanged, as in TLC (as in the EXCEPT that builds a new value)
                    (Path::Idx(i), Ty::PFun(d, c)) => {
                        let ic = self.gen_as(i, env, d)?;
                        let iv = self.fresh("i");
                        if is_sparse_fun(&cur) {
                            writeln!(out, "let {iv} = {ic};").unwrap();
                            conds.push(format!("({p}).find(&{iv}).is_ok()"));
                            p = format!("{p}.items[({p}).find(&{iv}).unwrap()].1");
                        } else {
                            let did = self.ty_id(d)?;
                            writeln!(out, "let {iv} = enc_{did}({ic});").unwrap();
                            conds.push(format!("{iv} != u64::MAX && {p}[{iv} as usize].0"));
                            p = format!("{p}[{iv} as usize].1");
                        }
                        cur = c.as_ref().clone();
                    }
                    (Path::Field(k), Ty::Rec(fs)) => {
                        let i = fs.iter().position(|(n, _)| n == k).ok_or(format!("no field {k}"))?;
                        match &fs[i].1 {
                            // EXCEPT on an absent field is a no-op
                            Ty::Opt(t) => {
                                let fp = rec_field(fs.len(), i);
                                conds.push(format!("{p}{fp}.0"));
                                p = format!("{p}{fp}.1");
                                cur = t.as_ref().clone();
                            }
                            t => {
                                p = format!("{p}{}", rec_field(fs.len(), i));
                                cur = t.clone();
                            }
                        }
                    }
                    _ => return Err("EXCEPT path does not match the value's type".into()),
                }
            }
            let at = self.fresh("at");
            let mut env2 = env.clone();
            env2.locals.insert("@".into(), (at.clone(), cur.clone()));
            if let Some(n) = at_name {
                env2.locals.insert(n, (at.clone(), cur.clone()));
            }
            let vc = self.gen_as(val, &env2, &cur)?;
            // Skip reading the original value unless @ is used
            let read_at = if vc.contains(&at) { format!("let {at} = {p}; ") } else { String::new() };
            if conds.is_empty() {
                writeln!(out, "{read_at}{p} = {vc};").unwrap();
            } else {
                writeln!(out, "if {} {{ {read_at}{p} = {vc}; }}{warn}", conds.join(" && ")).unwrap();
            }
        }
        Ok(())
    }

    /// Renews the state under construction on entering a branch or loop. If it has already been
    /// written to, copies its current value into a fresh variable so inner writes do not leak out.
    fn renew_work(&mut self, env: &Env, out: &mut String) -> Env {
        let mut env2 = env.clone();
        let Some(old) = env.work.clone() else { return env2 };
        let w = self.fresh("w");
        writeln!(out, "let mut {w} = {old};").unwrap();
        env2.work = Some(w.clone());
        // Repoint the slots of already-assigned variables to the new copy
        for (v, slot) in env2.primed.iter_mut() {
            if slot.0 == format!("{old}.v_{v}") {
                slot.0 = format!("{w}.v_{v}");
            }
        }
        env2
    }

    /// Creates the state under construction from `*s` on first use only
    fn work_var(&mut self, env: &mut Env, out: &mut String) -> String {
        if let Some(w) = &env.work {
            return w.clone();
        }
        let w = self.fresh("w");
        if env.init {
            // An initial state has no predecessor, so start from default values
            let fields: Vec<String> =
                self.vars.iter().map(|(v, t)| format!("v_{v}: {}", Self::default_code(t))).collect();
            writeln!(out, "let mut {w} = State {{ {} }};", fields.join(", ")).unwrap();
        } else {
            writeln!(out, "let mut {w} = *s;").unwrap();
        }
        env.work = Some(w.clone());
        w
    }

    fn emit_state(&mut self, env: &Env, out: &mut String) -> R<()> {
        if let Some(key) = env.sink.clone() {
            let mask = self.assigned_id(env);
            self.ract.get_mut(&key).unwrap().1.insert(mask);
            writeln!(out, "__res.push(({}, {mask}u32));", env.work.as_ref().unwrap()).unwrap();
            return Ok(());
        }
        if let Some(exit) = &env.en_exit {
            // Enabled: TLC stops at the first successor, so what the rest would raise is not reached
            writeln!(out, "break '{exit} true;").unwrap();
            return Ok(());
        }
        let mut unassigned: Vec<&str> =
            self.vars.iter().map(|(v, _)| v.as_str()).filter(|v| !env.partial && !env.primed.contains_key(*v)).collect();
        if !unassigned.is_empty() {
            // Fail only if this branch is reached. TLC shows the state with those variables as
            // null, and names them in the order of their names (not the order it prints them in:
            // tests/tlc/VarOrder-Partial)
            let st = match &env.work {
                Some(w) => w.clone(),
                None => {
                    let fields: Vec<String> = self
                        .vars
                        .iter()
                        .map(|(v, t)| {
                            let val = env.primed.get(v).map_or_else(|| Self::default_code(t), |p| p.0.clone());
                            format!("v_{v}: {val}")
                        })
                        .collect();
                    format!("State {{ {} }}", fields.join(", "))
                }
            };
            unassigned.sort_unstable();
            let names: Vec<String> = unassigned.iter().map(|v| format!("{v:?}")).collect();
            if env.init {
                writeln!(out, "incomplete_init({st}, &[{}]);", names.join(", ")).unwrap();
            } else {
                writeln!(out, "incomplete_succ({st}, {}, &[{}]);", env.label.unwrap_or(1), names.join(", ")).unwrap();
            }
            return Ok(());
        }
        // All assignments are already in the state under construction, so emit it as is
        let st = match &env.work {
            Some(w) => w.clone(),
            None => {
                let fields: Vec<String> = self
                    .vars
                    .iter()
                    .map(|(v, _)| format!("v_{v}: {}", env.primed.get(v).map_or(format!("s.v_{v}"), |p| p.0.clone())))
                    .collect();
                format!("State {{ {} }}", fields.join(", "))
            }
        };
        if env.init {
            writeln!(out, "out.push({st});").unwrap();
        } else {
            writeln!(out, "out.push(({st}, {}));", env.label.unwrap_or(1)).unwrap();
        }
        // For the order of printed lines and of strings made (a no-op in a checker that follows
        // neither)
        writeln!(out, "mark_push();").unwrap();
        Ok(())
    }

    /// Environment for expressions over a transition (s, t): x' is t.v_x
    pub fn env_step(&self, mut env: Env) -> Env {
        for (v, t) in &self.vars {
            env.primed.insert(v.clone(), (format!("t.v_{v}"), t.clone()));
        }
        env
    }

    /// Environment for computing whether an action is enabled (for fairness)
    pub fn env_enabled(mut env: Env) -> Env {
        env.enabled = true;
        env
    }

    /// Environment for whether `<<A>>_v` is enabled, for WF_v(A) / SF_v(A): as TLC computes
    /// ENABLED, a successor may leave variables undetermined (reading one fails)
    pub fn env_fair(&mut self, env: Env, action: &Expr) -> Env {
        let mut env = Self::env_enabled(env);
        env.en_exit = Some(self.fresh("en"));
        env.partial = true;
        env.phantom = matches!(action, Expr::Label(n, ..) if n == crate::ast::ENINST);
        env
    }

    pub fn env_init() -> Env {
        Env { init: true, ..Default::default() }
    }

    pub fn env_next() -> Env {
        Env { split: true, ..Default::default() }
    }

    /// The next-state relation split into actions as TLC splits it (`Tool.getActions`, measured
    /// on TLC 2.19): through `\/`, `\E` over sets that do not depend on the state, labels, and
    /// calls of definitions whose arguments do not depend on the state, except a definition of an
    /// INSTANCE with substitutions, which stays whole. Where splitting stops is an action, named
    /// in a trace by the innermost definition called (`Action` if none) and the position of the
    /// innermost part with a POS label, as `Name line L, col C to line L2, col C2 of module M`.
    /// Returns false for `\/`, `\E` and recursive calls that gen_action goes on splitting.
    fn gen_split(&mut self, h: &Expr, rest: &[Expr], env: &Env, out: &mut String) -> R<bool> {
        use Expr::*;
        let with = |x: &Expr| -> Vec<Expr> { std::iter::once(x.clone()).chain(rest.iter().cloned()).collect() };
        let open = env.primed.len() < self.vars.len();
        let mut env2 = env.clone();
        match h {
            Label(n, _, b) if pos_of(n).is_some() => {
                env2.apos = pos_of(n).map(|p| p.to_string());
                self.gen_action(&with(b), &env2, out)?;
                return Ok(true);
            }
            Label(_, _, b) if h.is_user_label() => {
                self.gen_action(&with(b), env, out)?;
                return Ok(true);
            }
            // An AT label (see ast::AT) changes nothing in how TLC splits
            Label(n, _, b) if err_pos_of(n).is_some() => {
                if matches!(b.strip(), Case(..)) {
                    self.case_at = err_pos_of(n).map(|p| p.to_string());
                }
                self.gen_action(&with(b), env, out)?;
                return Ok(true);
            }
            Label(n, args, b) if !n.starts_with('#') && n != "<<>>_" && !self.whole_instance(n) => {
                env2.aname = Some(self.action_name(n));
                // Called with an argument from the state: the call is the action (named by the
                // definition called, at the position of the call)
                if !args.iter().any(|a| self.mentions_state(a)) {
                    self.gen_action(&with(b), &env2, out)?;
                    return Ok(true);
                }
            }
            Or(_) if open => return Ok(false),
            Quant(true, bs, _) if open && !bs.iter().any(|(_, s)| self.mentions_state(s)) => return Ok(false),
            RecCall(i, args) => {
                let state = args.iter().any(|a| self.mentions_state(a));
                if !state && open && self.rec_assigns(*i, env) && args.iter().all(|a| self.try_const(a, env).is_some()) {
                    return Ok(false);
                }
                let rd = crate::expand::rec_def(*i);
                env2.aname = Some(self.action_name(&rd.name));
                // Arguments bound by a split \E are constants to TLC but not here: TLC would
                // split the body further, which is not followed
                if !state {
                    if let Some(p) = self.def_pos.get(&rd.name) {
                        env2.apos = Some(p.clone());
                    }
                }
            }
            _ => {}
        }
        let name = env2.aname.as_deref().unwrap_or("Action");
        let label = match &env2.apos {
            Some(p) => format!("{name} {p}"),
            None => name.to_string(),
        };
        env2.label = Some(self.label_id(&label));
        self.actions += 1;
        writeln!(out, "mark_action();").unwrap();
        env2.split = false;
        self.gen_action(&with(&strip_pos(h)), &env2, out)?;
        Ok(true)
    }

    /// Whether `e` depends on the state (has level 1 or more for SANY)
    fn mentions_state(&self, e: &Expr) -> bool {
        e.any(&|x| {
            matches!(x, Expr::Ident(n, _) if self.is_var(n) || self.bound_mentions_state(n))
                || matches!(x, Expr::Prime(_) | Expr::Un(UOp::Unchanged | UOp::Enabled, _) | Expr::BoxAction(..))
        })
    }

    /// Whether the expression a BIND label binds to the name n depends on the state
    fn bound_mentions_state(&self, n: &str) -> bool {
        if let Some(&b) = self.bstate.borrow().get(n) {
            return b;
        }
        let Some(x) = crate::value::bound_expr(n) else { return false };
        let b = self.mentions_state(&x);
        self.bstate.borrow_mut().insert(n.to_string(), b);
        b
    }

    /// The names a BIND label binds (`Expander::expand_def_code`), in an expression: TLC evaluates
    /// a LET definition or an argument where it is first used and keeps the value for the rest of
    /// the evaluation of the LET or the call (measured, `tests/tlc/LazyLet`). Each name becomes a
    /// Rust `OnceCell` and a closure computing its value on first use. A name is written out where
    /// it is used instead (as all were before) when its value is constant (folded there), when TLC
    /// keeps its value unevaluated (`lazy_value`: a function constructor applied only where it is
    /// applied, a set it does not enumerate), in Init when it reads variables while some are still
    /// unassigned (the closure would hold the state being built), and when its value cannot be
    /// generated on its own (a set only tested for membership). Returns the code declaring the
    /// names, the environment with them, and the body with the names written out replaced
    fn gen_bind(&mut self, pairs: &[Expr], body: &Expr, env: &Env) -> R<(String, Env, Expr)> {
        let mut env2 = env.clone();
        let mut pairs: Vec<(String, Expr)> = pairs
            .chunks(2)
            .map(|p| match p {
                [Expr::Ident(n, _), x] => (n.clone(), x.clone()),
                _ => unreachable!(),
            })
            .collect();
        let mut body = body.clone();
        let mut lets = String::new();
        for k in 0..pairs.len() {
            let (n, x) = pairs[k].clone();
            let all_assigned = env.primed.len() == self.vars.len();
            // A constant whose computation TLC warns about (an EXCEPT) is computed where first used
            // too, so that it warns once for the evaluation, as TLC does (`tests/tlc/ExceptFold-Arg`)
            let warns = || !self.try_const_made(&x, &env2).1.warns.is_empty();
            // A tuple of variables is written out too: a use reads one of them (see `App`), and
            // a cell would copy every one at its first use
            let vars = matches!(unlabel(&x), Expr::Tuple(es) if self.var_tuple(es, &env2));
            let cell = (!self.is_const(&x, &env2) || warns()) && !x.is_action() && !lazy_value(&x) && !vars && !(env.init && !all_assigned && self.mentions_state(&x));
            if cell {
                if let Ok((c, t)) = self.gen(&x, &env2, None) {
                    let id = self.fresh("b");
                    write!(lets, "let {id} = std::cell::OnceCell::new(); let {id}f = || -> {} {{ {c} }}; ", t.repr()).unwrap();
                    // Every value type is Copy: read through the reference, so that a use that
                    // only reads a part (a field, an iteration) does not copy the whole value
                    env2.bind(&n, format!("(*{id}.get_or_init(&{id}f))"), t);
                    continue;
                }
            }
            for p in &mut pairs[k + 1..] {
                p.1 = crate::expand::subst_ident(&p.1, &n, &x);
            }
            body = crate::expand::subst_ident(&body, &n, &x);
        }
        Ok((lets, env2, body))
    }

    /// Whether every element is a variable, primed or not, whose value `env` has
    fn var_tuple(&self, es: &[Expr], env: &Env) -> bool {
        !es.is_empty()
            && es.iter().all(|e| match unlabel(e) {
                Expr::Ident(n, _) => self.is_var(n) && !env.locals.contains_key(n) && !(env.init && !env.primed.contains_key(n)),
                Expr::Prime(v) => matches!(v.as_ref(), Expr::Ident(n, _) if self.is_var(n) && env.primed.contains_key(n)),
                _ => false,
            })
    }

    /// Whether `n` is the hidden definition of an INSTANCE with substitutions, which TLC does not
    /// split (a SubstInNode)
    fn whole_instance(&self, n: &str) -> bool {
        self.inst_prefixes.iter().any(|(p, _, subs)| *subs > 0 && n.starts_with(p.as_str()))
    }

    /// The name TLC gives the definition called `n`
    fn action_name(&self, n: &str) -> String {
        for (p, shown, _) in &self.inst_prefixes {
            if let Some(op) = n.strip_prefix(p.as_str()) {
                return format!("{shown}{op}");
            }
        }
        n.to_string()
    }

    // ---------------------------------------------------------------- Helpers

    pub fn helpers(&mut self) -> R<String> {
        let mut s = String::new();
        // TLC's order of sets: by size, then by their elements in order
        s += "fn tlc_set_cmp(a: u128, b: u128) -> std::cmp::Ordering { a.count_ones().cmp(&b.count_ones()).then_with(|| { let d = a ^ b; if d == 0 { std::cmp::Ordering::Equal } else if a & d & d.wrapping_neg() != 0 { std::cmp::Ordering::Less } else { std::cmp::Ordering::Greater } }) }\n";
        if self.need_subsets {
            // The subsets of a bitmask set in TLC's order: by size, then by their elements in order
            // (the lowest element where two subsets differ belongs to the earlier one)
            s += "fn subsets_tlc(m: u128) -> Vec<u128> { if m.count_ones() > 20 { eval_error(format!(\"SUBSET of a set of {} elements is too large to enumerate\", m.count_ones())) } \
                  let mut v = vec![]; let mut sub = m; loop { v.push(sub); if sub == 0 { break; } sub = (sub - 1) & m; } \
                  v.sort_by(|a, b| a.count_ones().cmp(&b.count_ones()).then_with(|| { let d = a ^ b; if d == 0 { std::cmp::Ordering::Equal } else if a & d & d.wrapping_neg() != 0 { std::cmp::Ordering::Less } else { std::cmp::Ordering::Greater } })); v }\n";
        }
        // fmt is needed for every type reachable from the variables' types, so register those first
        for (_, t) in self.vars.clone() {
            self.ty_id(&t)?;
        }
        let mut i = 0;
        while i < self.tys.len() {
            let t = self.tys[i].clone();
            let r = t.repr();
            if let Some(n) = t.size() {
                // enc / dec / bit / idx
                let enc_body = match &t {
                    Ty::Bool => "v as u64".to_string(),
                    Ty::Int(lo, hi) => format!("if v >= {lo} && v <= {hi} {{ (v as i128 - {lo} as i128) as u64 }} else {{ u64::MAX }}"),
                    Ty::Enum(d) => {
                        let arms: String = d.iter().enumerate().map(|(p, a)| format!("{a} => {p}, ")).collect();
                        format!("match v {{ {arms}_ => u64::MAX }}")
                    }
                    Ty::IntAtom(lo, hi, d) => {
                        // Model values first, then the integers
                        let k = d.len();
                        let arms: String = d.iter().enumerate().map(|(p, a)| format!("{a} => {p}, ")).collect();
                        format!(
                            "if v >= {lo} && v <= {hi} {{ (v as i128 - {lo} as i128) as u64 + {k} }} else {{ match (v as i128 - i64::MIN as i128) as u64 {{ {arms}_ => u64::MAX }} }}"
                        )
                    }
                    Ty::Rec(fs) => {
                        let mut b = String::from("let mut acc: u64 = 0; ");
                        for (k, (_, ft)) in fs.iter().enumerate() {
                            let fid = self.ty_id(ft)?;
                            write!(
                                b,
                                "let e = enc_{fid}(v{}); if e == u64::MAX {{ return u64::MAX; }} acc = acc * {} + e; ",
                                rec_field(fs.len(), k),
                                ft.size().unwrap()
                            )
                            .unwrap();
                        }
                        b + "acc"
                    }
                    Ty::Opt(inner) => {
                        let iid = self.ty_id(inner)?;
                        format!("if v.0 {{ let e = enc_{iid}(v.1); if e == u64::MAX {{ u64::MAX }} else {{ e + 1 }} }} else {{ 0 }}")
                    }
                    _ => unreachable!(),
                };
                let dec_body = match &t {
                    Ty::Bool => "i == 1".to_string(),
                    Ty::Int(lo, _) => format!("({lo} as i128 + i as i128) as i64"),
                    Ty::Enum(d) => {
                        let list: Vec<String> = d.iter().map(|a| format!("{a}u16")).collect();
                        format!("const T: [u16; {}] = [{}]; T[i as usize]", d.len(), list.join(", "))
                    }
                    Ty::IntAtom(lo, _, d) => {
                        let k = d.len();
                        let list: Vec<String> = d.iter().map(|a| format!("{a}u16")).collect();
                        format!(
                            "if i >= {k} {{ ({lo} as i128 + (i - {k}) as i128) as i64 }} else {{ const T: [u16; {k}] = [{}]; i64::MIN + T[i as usize] as i64 }}",
                            list.join(", ")
                        )
                    }
                    Ty::Rec(fs) => {
                        let mut b = String::from("let mut i = i; ");
                        let mut parts = vec![];
                        for (k, (_, ft)) in fs.iter().enumerate().rev() {
                            let fid = self.ty_id(ft)?;
                            let sz = ft.size().unwrap();
                            write!(b, "let f{k} = dec_{fid}(i % {sz}); i /= {sz}; ").unwrap();
                            parts.push(k);
                        }
                        parts.reverse();
                        b + &rec_build(&parts.iter().map(|k| format!("f{k}")).collect::<Vec<_>>())
                    }
                    Ty::Opt(inner) => {
                        let iid = self.ty_id(inner)?;
                        format!("if i == 0 {{ {} }} else {{ (true, dec_{iid}(i - 1)) }}", Self::default_code(&t))
                    }
                    _ => unreachable!(),
                };
                // Records of different fields: numbered in TLC's order (see Ty::tlc_perm)
                let (enc_body, dec_body) = match t.tlc_perm() {
                    Some(perm) => {
                        let mut inv = vec![0u32; perm.len()];
                        for (k, &r) in perm.iter().enumerate() {
                            inv[r as usize] = k as u32;
                        }
                        let list = |v: &[u32]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
                        (
                            format!(
                                "const P: [u32; {n}] = [{}]; let m = (|| -> u64 {{ {enc_body} }})(); if m == u64::MAX {{ m }} else {{ P[m as usize] as u64 }}",
                                list(&perm)
                            ),
                            format!("const Q: [u32; {n}] = [{}]; let i = Q[i as usize] as u64; {dec_body}", list(&inv)),
                        )
                    }
                    None => (enc_body, dec_body),
                };
                writeln!(s, "#[inline] fn enc_{i}(v: {r}) -> u64 {{ {enc_body} }}").unwrap();
                writeln!(s, "#[inline] fn dec_{i}(i: u64) -> {r} {{ {dec_body} }}").unwrap();
                writeln!(
                    s,
                    "#[inline] fn bit_{i}(v: {r}) -> u128 {{ let e = enc_{i}(v); if e >= 128 {{ type_error(\"set element\", &fmt_{i}(&v)) }} 1u128 << e }}"
                )
                .unwrap();
                writeln!(
                    s,
                    "#[inline] fn idx_{i}(v: {r}) -> usize {{ let e = enc_{i}(v); if e == u64::MAX {{ type_error(\"function argument\", &fmt_{i}(&v)) }} e as usize }}"
                )
                .unwrap();
                let _ = n;
            }
            // fmt
            let string_keys = |d: &Ty| -> Option<Vec<String>> {
                match d {
                    Ty::Enum(ids) if !ids.is_empty() && ids.iter().all(|&a| !self.atoms.is_model(a)) => Some(ids.iter().map(|&a| self.atoms.name(a)).collect()),
                    _ => None,
                }
            };
            let all_field_names = |d: &Ty| string_keys(d).is_some_and(|ks| ks.iter().all(|k| crate::compile::field_name(k)));
            let fmt_body = match &t {
                // A function over strings prints as a record (<< >> when empty, as TLC spells an
                // empty function), when they are all field names (see `compile::field_name`); a
                // partial one or a bag decides by the strings it holds
                Ty::Fun(d, _) | Ty::PFun(d, _) | Ty::Bag(d) if string_keys(d).is_some() && (all_field_names(d) || !matches!(t, Ty::Fun(..))) => {
                    let keys = string_keys(d).unwrap();
                    let names: Vec<String> = keys.iter().map(|n| format!("{n:?}")).collect();
                    let entry = match &t {
                        Ty::Fun(_, c) => format!("Some(fmt_{}(x))", self.ty_id(c)?),
                        Ty::PFun(_, c) => format!("if x.0 {{ Some(fmt_{}(&x.1)) }} else {{ None }}", self.ty_id(c)?),
                        _ => "if *x > 0 { Some(x.to_string()) } else { None }".into(),
                    };
                    if all_field_names(d) {
                        format!(
                            "const K: [&str; {}] = [{}]; let ps: Vec<String> = v.iter().enumerate().filter_map(|(i, x)| {{ let e: Option<String> = {entry}; e.map(|e| format!(\"{{}} |-> {{}}\", K[i], e)) }}).collect(); \
                             if ps.is_empty() {{ return \"<< >>\".into(); }} format!(\"[{{}}]\", ps.join(\", \"))",
                            names.len(),
                            names.join(", ")
                        )
                    } else {
                        let fields: Vec<String> = keys.iter().map(|k| crate::compile::field_name(k).to_string()).collect();
                        format!(
                            "const K: [&str; {n}] = [{}]; const F: [bool; {n}] = [{}]; let ps: Vec<(usize, String)> = v.iter().enumerate().filter_map(|(i, x)| {{ let e: Option<String> = {entry}; e.map(|e| (i, e)) }}).collect(); \
                             if ps.is_empty() {{ return \"<< >>\".into(); }} \
                             if ps.iter().all(|(i, _)| F[*i]) {{ return format!(\"[{{}}]\", ps.iter().map(|(i, e)| format!(\"{{}} |-> {{}}\", K[*i], e)).collect::<Vec<_>>().join(\", \")); }} \
                             format!(\"({{}})\", ps.iter().map(|(i, e)| format!(\"{{:?}} :> {{}}\", K[*i], e)).collect::<Vec<_>>().join(\" @@ \"))",
                            names.join(", "),
                            fields.join(", "),
                            n = names.len()
                        )
                    }
                }
                // A sparse function or bag, entry by entry in TLC's order of keys: << >> when empty
                // (TLC's spelling for an empty function), a tuple over 1..n
                Ty::PFun(..) | Ty::Bag(_) if is_sparse_fun(&t) => {
                    let (kt, vt) = fun_kv(&t);
                    let (kid, vid) = (self.ty_id(&kt)?, self.ty_id(&vt)?);
                    let it = self.fun_iter("v", &t, true)?;
                    let ints = matches!(kt, Ty::Int(..));
                    format!(
                        "let ks: Vec<(String, String)> = {it}.map(|(k, x)| (fmt_{kid}(&k), fmt_{vid}(&x))).collect(); \
                         if ks.is_empty() {{ return \"<< >>\".into(); }} \
                         if {ints} && ks.iter().enumerate().all(|(j, (k, _))| *k == (j + 1).to_string()) {{ \
                         return format!(\"<<{{}}>>\", ks.iter().map(|(_, x)| x.clone()).collect::<Vec<_>>().join(\", \")); }} \
                         format!(\"({{}})\", ks.iter().map(|(k, x)| format!(\"{{}} :> {{}}\", k, x)).collect::<Vec<_>>().join(\" @@ \"))"
                    )
                }
                // A bag prints as the function it is: << >> when empty (TLC's spelling for an empty
                // function), a tuple over 1..n
                Ty::PFun(d, c) => {
                    let (did, cid) = (self.ty_id(d)?, self.ty_id(c)?);
                    let ints = matches!(d.as_ref(), Ty::Int(..));
                    format!(
                        "let ks: Vec<(u64, String)> = v.iter().enumerate().filter(|(_, x)| x.0).map(|(i, x)| (i as u64, fmt_{cid}(&x.1))).collect(); \
                         if ks.is_empty() {{ return \"<< >>\".into(); }} \
                         if {ints} && ks.iter().enumerate().all(|(j, (i, _))| fmt_{did}(&dec_{did}(*i)) == (j + 1).to_string()) {{ \
                         return format!(\"<<{{}}>>\", ks.iter().map(|(_, c)| c.clone()).collect::<Vec<_>>().join(\", \")); }} \
                         format!(\"({{}})\", ks.iter().map(|(i, c)| format!(\"{{}} :> {{}}\", fmt_{did}(&dec_{did}(*i)), c)).collect::<Vec<_>>().join(\" @@ \"))"
                    )
                }
                Ty::Bag(e) => {
                    let eid = self.ty_id(e)?;
                    let ints = matches!(e.as_ref(), Ty::Int(..));
                    format!(
                        "let ks: Vec<(u64, i64)> = v.iter().enumerate().filter(|(_, &c)| c > 0).map(|(i, &c)| (i as u64, c)).collect(); \
                         if ks.is_empty() {{ return \"<< >>\".into(); }} \
                         if {ints} && ks.iter().enumerate().all(|(j, &(i, _))| fmt_{eid}(&dec_{eid}(i)) == (j + 1).to_string()) {{ \
                         return format!(\"<<{{}}>>\", ks.iter().map(|&(_, c)| c.to_string()).collect::<Vec<_>>().join(\", \")); }} \
                         format!(\"({{}})\", ks.iter().map(|&(i, c)| format!(\"{{}} :> {{}}\", fmt_{eid}(&dec_{eid}(i)), c)).collect::<Vec<_>>().join(\" @@ \"))"
                    )
                }
                Ty::Bool => "if *v { \"TRUE\".into() } else { \"FALSE\".into() }".to_string(),
                Ty::Int(..) => "v.to_string()".into(),
                Ty::Enum(_) => "ATOMS[*v as usize].to_string()".into(),
                Ty::IntAtom(..) => "if *v < i64::MIN + 65536 { ATOMS[(*v - i64::MIN) as usize].to_string() } else { v.to_string() }".into(),
                // The empty tuple (as TLC prints it)
                Ty::Rec(fs) if fs.is_empty() => "\"<< >>\".to_string()".into(),
                Ty::Rec(fs) if fs.iter().all(|(n, _)| n.starts_with('#')) => {
                    // Tuple
                    let mut parts = vec![];
                    for (k, (_, ft)) in fs.iter().enumerate() {
                        let fid = self.ty_id(ft)?;
                        parts.push(format!("fmt_{fid}(&v{})", rec_field(fs.len(), k)));
                    }
                    format!("format!(\"<<{{}}>>\", [{}].join(\", \"))", parts.join(", "))
                }
                Ty::Rec(fs) => {
                    let mut b = String::from("let mut ps: Vec<String> = vec![]; ");
                    for (k, (name, ft)) in fs.iter().enumerate() {
                        let fp = rec_field(fs.len(), k);
                        if name == crate::types::ATOM_FIELD || name == crate::types::VAL_FIELD {
                            // A model value, or a value of another kind (see types::ATOM_FIELD,
                            // VAL_FIELD)
                            let Ty::Opt(inner) = ft else { unreachable!() };
                            let fid = self.ty_id(inner)?;
                            write!(b, "if v{fp}.0 {{ return fmt_{fid}(&v{fp}.1); }} ").unwrap();
                            continue;
                        }
                        match ft {
                            Ty::Opt(inner) => {
                                let fid = self.ty_id(inner)?;
                                write!(b, "if v{fp}.0 {{ ps.push(format!(\"{name} |-> {{}}\", fmt_{fid}(&v{fp}.1))); }} ").unwrap();
                            }
                            ft => {
                                let fid = self.ty_id(ft)?;
                                write!(b, "ps.push(format!(\"{name} |-> {{}}\", fmt_{fid}(&v{fp}))); ").unwrap();
                            }
                        }
                    }
                    b + "format!(\"[{}]\", ps.join(\", \"))"
                }
                Ty::Opt(inner) => {
                    let fid = self.ty_id(inner)?;
                    format!("if v.0 {{ fmt_{fid}(&v.1) }} else {{ \"<none>\".into() }}")
                }
                // The function over the empty set (TLC's spelling for an empty function)
                Ty::Fun(d, _) if d.size() == Some(0) => "\"<< >>\".to_string()".into(),
                Ty::Fun(d, c) => {
                    let (did, cid) = (self.ty_id(d)?, self.ty_id(c)?);
                    if let Ty::Int(1, _) = d.as_ref() {
                        format!("format!(\"<<{{}}>>\", v.iter().map(|x| fmt_{cid}(x)).collect::<Vec<_>>().join(\", \"))")
                    } else {
                        format!(
                            "format!(\"({{}})\", v.iter().enumerate().map(|(i, x)| format!(\"{{}} :> {{}}\", fmt_{did}(&dec_{did}(i as u64)), fmt_{cid}(x))).collect::<Vec<_>>().join(\" @@ \"))"
                        )
                    }
                }
                Ty::Seq(e) => {
                    let eid = self.ty_id(e)?;
                    format!("format!(\"<<{{}}>>\", v.iter().map(|x| fmt_{eid}(&x)).collect::<Vec<_>>().join(\", \"))")
                }
                Ty::Set(e) if is_sparse(&t) => {
                    let eid = self.ty_id(e)?;
                    let it = self.s_iter("*v", &t)?;
                    format!("format!(\"{{{{{{}}}}}}\", {it}.map(|x| fmt_{eid}(&x)).collect::<Vec<_>>().join(\", \"))")
                }
                Ty::Set(e) => {
                    let eid = self.ty_id(e)?;
                    format!("format!(\"{{{{{{}}}}}}\", bits(*v).map(|i| fmt_{eid}(&dec_{eid}(i))).collect::<Vec<_>>().join(\", \"))")
                }
            };
            writeln!(s, "fn fmt_{i}(v: &{r}) -> String {{ {fmt_body} }}").unwrap();
            i += 1;
        }
        for (a, b) in self.convs.clone() {
            let (Ty::Set(ea), Ty::Set(eb)) = (&self.tys[a], &self.tys[b]) else { unreachable!() };
            let (ia, ib) = (self.ty_ids[&**ea], self.ty_ids[&**eb]);
            writeln!(
                s,
                "fn conv_{a}_{b}(x: u128) -> u128 {{ let mut o = 0u128; for i in bits(x) {{ o |= bit_{ib}(dec_{ia}(i)); }} o }}"
            )
            .unwrap();
        }
        Ok(s)
    }

    // ---------------------------------------------------------------- Bit packing

    fn bits_for(n: u64) -> u32 {
        if n <= 1 {
            0
        } else {
            64 - (n - 1).leading_zeros()
        }
    }

    /// Statement writing `bits` bits at constant offset `at` (spanning up to 3 words); the value
    /// is treated as u128.
    fn put_at(v: &str, bits: u32, at: u32) -> String {
        let (i, sh) = ((at / 64) as usize, at % 64);
        let mut s = format!("{{ let __v = {v} as u128; w[{i}] |= (__v << {sh}) as u64; ");
        let mut covered = 64 - sh;
        let mut word = i + 1;
        while covered < bits {
            write!(s, "w[{word}] |= (__v >> {}) as u64; ", covered).unwrap();
            covered += 64;
            word += 1;
        }
        s + "}; "
    }

    /// Expression reading `bits` bits at constant offset `at` (as u128)
    fn get_at(bits: u32, at: u32) -> String {
        let (i, sh) = ((at / 64) as usize, at % 64);
        let mut parts = vec![format!("((w[{i}] as u128) >> {sh})")];
        let mut covered = 64 - sh;
        let mut word = i + 1;
        while covered < bits {
            parts.push(format!("((w[{word}] as u128) << {covered})"));
            covered += 64;
            word += 1;
        }
        let mask = if bits >= 128 { "u128::MAX".to_string() } else { format!("((1u128 << {bits}) - 1)") };
        format!("(({}) & {mask})", parts.join(" | "))
    }

    /// Code that writes a state into the bit string. When `at` is Some the offset is a constant,
    /// so shift amounts are baked in. After the first value whose size is only known at runtime
    /// (a sparse set), `at` becomes None and the code falls back to threading the offset.
    fn pack_value(&mut self, c: &str, t: &Ty, out: &mut String, at: &mut Option<u32>) -> R<u32> {
        if is_sparse_fun(t) {
            return self.pack_value(c, &fun_pairs(t), out, at);
        }
        if let Ty::Bag(e) = t {
            return self.pack_value(c, &bag_fun(e), out, at);
        }
        if let Ty::PFun(d, cd) = t {
            return self.pack_value(c, &pfun_repr(d, cd), out, at);
        }
        if let Some(n) = t.size() {
            let id = self.ty_id(t)?;
            let b = Self::bits_for(n);
            let e = self.fresh("e");
            write!(out, "let {e} = enc_{id}({c}); if {e} == u64::MAX {{ return None; }} ").unwrap();
            if b > 0 {
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(&e, b, *o));
                        *o += b;
                    }
                    None => write!(out, "put(&mut w, &mut p, {e} as u128, {b}); ").unwrap(),
                }
            }
            return Ok(b);
        }
        Ok(match t {
            Ty::Seq(e) => {
                // The length, followed by that many elements, as for a sparse set
                let lb = Self::bits_for(self.qcap as u64 + 1);
                let (k, n) = (self.fresh("k"), self.fresh("n"));
                if let Some(o) = at {
                    write!(out, "let mut p = {o}u32; ").unwrap();
                }
                *at = None;
                write!(out, "let {n} = ({c}).len as usize; put(&mut w, &mut p, {n} as u128, {lb}); for {k} in 0..{n} {{ ").unwrap();
                let b = self.pack_value(&format!("({c}).items[{k}]"), e, out, &mut None)?;
                out.push_str("} ");
                lb + b * self.qcap as u32
            }
            Ty::Set(e) if is_sparse(t) => {
                // The count, followed by that many elements (the rest stay 0). The offset is only
                // known at runtime from here on, so thread it
                let cap = crate::types::set_cap(t, self.scap);
                let lb = Self::bits_for(cap as u64 + 1);
                let k = self.fresh("k");
                let n = self.fresh("n");
                if let Some(o) = at {
                    write!(out, "let mut p = {o}u32; ").unwrap();
                }
                *at = None;
                write!(out, "let {n} = ({c}).len as usize; put(&mut w, &mut p, {n} as u128, {lb}); for {k} in 0..{n} {{ ").unwrap();
                let b = self.pack_value(&format!("({c}).items[{k}]"), e, out, &mut None)?;
                out.push_str("} ");
                lb + b * cap as u32
            }
            Ty::Set(e) => {
                let n = e.size().unwrap() as u32;
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(c, n, *o));
                        *o += n;
                    }
                    None => write!(out, "put(&mut w, &mut p, {c}, {n}); ").unwrap(),
                }
                n
            }
            Ty::Opt(inner) => {
                match at {
                    Some(o) => {
                        out.push_str(&Self::put_at(&format!("({c}).0 as u128"), 1, *o));
                        *o += 1;
                    }
                    None => write!(out, "put(&mut w, &mut p, ({c}).0 as u128, 1); ").unwrap(),
                }
                1 + self.pack_value(&format!("({c}).1"), inner, out, at)?
            }
            Ty::Fun(d, cod) => {
                let n = d.size().unwrap();
                if at.is_some() {
                    // The size is known, so unroll at generation time
                    let mut total = 0;
                    for k in 0..n {
                        total += self.pack_value(&format!("{c}[{k}]"), cod, out, at)?;
                    }
                    return Ok(total);
                }
                let k = self.fresh("k");
                write!(out, "for {k} in 0..{n} {{ ").unwrap();
                let b = self.pack_value(&format!("{c}[{k}]"), cod, out, &mut None)?;
                out.push_str("} ");
                b * n as u32
            }
            Ty::Rec(fs) => {
                let mut total = 0;
                for (i, (_, ft)) in fs.iter().enumerate() {
                    total += self.pack_value(&format!("{c}{}", rec_field(fs.len(), i)), ft, out, at)?;
                }
                total
            }
            _ => unreachable!(),
        })
    }

    fn unpack_value(&mut self, t: &Ty, at: &mut Option<u32>) -> R<String> {
        if is_sparse_fun(t) {
            return self.unpack_value(&fun_pairs(t), at);
        }
        if let Ty::Bag(e) = t {
            return self.unpack_value(&bag_fun(e), at);
        }
        if let Ty::PFun(d, cd) = t {
            return self.unpack_value(&pfun_repr(d, cd), at);
        }
        if let Some(n) = t.size() {
            let id = self.ty_id(t)?;
            let b = Self::bits_for(n);
            if b == 0 {
                return Ok(format!("dec_{id}(0)"));
            }
            return Ok(match at {
                Some(o) => {
                    let e = Self::get_at(b, *o);
                    *o += b;
                    format!("dec_{id}({e} as u64)")
                }
                None => format!("dec_{id}(get(w, &mut p, {b}) as u64)"),
            });
        }
        Ok(match t {
            Ty::Seq(e) => {
                let lb = Self::bits_for(self.qcap as u64 + 1);
                let pre = match at {
                    Some(o) => format!("p = {o}u32; "),
                    None => String::new(),
                };
                *at = None;
                let inner = self.unpack_value(e, &mut None)?;
                format!(
                    "{{ {pre}let n = get(w, &mut p, {lb}) as usize; let mut ss = {}; for k in 0..n {{ ss.items[k] = {inner}; }} ss.len = n as u16; ss }}",
                    Self::default_code(t)
                )
            }
            Ty::Set(e) if is_sparse(t) => {
                let lb = Self::bits_for(crate::types::set_cap(t, self.scap) as u64 + 1);
                // Thread the offset from here on, assigning to the outer p (a fresh `let` inside
                // the block would reset the offset to 0 on leaving it, so later fields would be
                // read from the start)
                let pre = match at {
                    Some(o) => format!("p = {o}u32; "),
                    None => String::new(),
                };
                *at = None;
                let inner = self.unpack_value(e, &mut None)?;
                format!(
                    "{{ {pre}let n = get(w, &mut p, {lb}) as usize; let mut ss = {}; for k in 0..n {{ ss.items[k] = {inner}; }} ss.len = n as u16; ss }}",
                    Self::default_code(t)
                )
            }
            Ty::Set(e) => {
                let n = e.size().unwrap() as u32;
                match at {
                    Some(o) => {
                        let e = Self::get_at(n, *o);
                        *o += n;
                        e
                    }
                    None => format!("get(w, &mut p, {n})"),
                }
            }
            Ty::Opt(inner) => {
                let flag = match at {
                    Some(o) => {
                        let e = Self::get_at(1, *o);
                        *o += 1;
                        format!("{e} == 1")
                    }
                    None => "get(w, &mut p, 1) == 1".into(),
                };
                format!("({flag}, {})", self.unpack_value(inner, at)?)
            }
            Ty::Fun(d, cod) => {
                let n = d.size().unwrap();
                if at.is_some() {
                    let mut parts = vec![];
                    for _ in 0..n {
                        parts.push(self.unpack_value(cod, at)?);
                    }
                    return Ok(format!("[{}]", parts.join(", ")));
                }
                format!("std::array::from_fn(|_| {})", self.unpack_value(cod, &mut None)?)
            }
            Ty::Rec(fs) => {
                let mut parts = vec![];
                for (_, ft) in fs {
                    parts.push(self.unpack_value(ft, at)?);
                }
                rec_build(&parts)
            }
            _ => unreachable!(),
        })
    }

    /// pack / unpack and the word count
    pub fn gen_pack(&mut self) -> R<String> {
        let mut body = String::new();
        let mut total = 0;
        let mut at = Some(0u32);
        for (v, t) in self.vars.clone() {
            total += self.pack_value(&format!("s.v_{v}"), &t, &mut body, &mut at)?;
        }
        // If the offset stayed constant, p is unused; omit it to avoid an unused-variable warning
        let pack_p = if at.is_some() { "" } else { "let mut p = 0u32; " };
        let words = total.div_ceil(64).max(1);
        let mut at = Some(0u32);
        let mut un = String::from("State { ");
        for (v, t) in self.vars.clone() {
            write!(un, "v_{v}: {}, ", self.unpack_value(&t, &mut at)?).unwrap();
        }
        un += "}";
        let unpack_p = if at.is_some() { "" } else { "let mut p = 0u32; " };
        Ok(format!(
            "// {total} bits per state\nconst WORDS: usize = {words};\ntype Packed = [u64; WORDS];\n\
             fn pack(s: &State) -> Option<Packed> {{ let mut w: Packed = [0; WORDS]; {pack_p}{body}Some(w) }}\n\
             fn unpack(w: &Packed) -> State {{ {unpack_p}{un} }}\n"
        ))
    }

    // ---------------------------------------------------------------- VIEW and SYMMETRY

    /// Function that packs the deduplication key (the VIEW value if there is one, otherwise the
    /// state) into a bit string
    pub fn gen_key(&mut self, view: Option<&Expr>) -> R<String> {
        let Some(view) = view else {
            return Ok("const HAS_VIEW: bool = false;\ntype Key = Packed;\nfn key_of(s: &State) -> Option<Key> { pack(s) }\n".into());
        };
        let (vc, vt) = self.gen(view, &Gen::env_next(), None).map_err(|e| format!("VIEW: {e}"))?;
        let mut body = String::new();
        let mut at = Some(0u32);
        let bits = self.pack_value("(*__v)", &vt, &mut body, &mut at)?;
        let vp = if at.is_some() { "" } else { "let mut p = 0u32; " };
        let words = bits.div_ceil(64).max(1);
        Ok(format!(
            "const HAS_VIEW: bool = true;\nconst VWORDS: usize = {words};\ntype Key = [u64; VWORDS];\n\
             fn key_of(s: &State) -> Option<Key> {{ let __v: &{} = &{{ {vc} }}; let mut w: Key = [0; VWORDS]; {vp}{body}Some(w) }}\n",
            vt.repr()
        ))
    }

    /// Expression applying the model-value permutation pm to value c of type t
    fn perm_code(&mut self, c: &str, t: &Ty) -> R<String> {
        if is_sparse_fun(t) {
            return self.perm_code(c, &fun_pairs(t));
        }
        if let Ty::Bag(e) = t {
            return self.perm_code(c, &bag_fun(e));
        }
        if let Ty::PFun(d, cd) = t {
            return self.perm_code(c, &pfun_repr(d, cd));
        }
        Ok(match t {
            Ty::Bag(_) | Ty::PFun(..) => unreachable!(),
            Ty::Bool | Ty::Int(..) => c.to_string(),
            Ty::Enum(_) => format!("pm[({c}) as usize]"),
            Ty::IntAtom(..) => {
                let x = self.fresh("x");
                format!("{{ let {x} = {c}; if {x} < i64::MIN + 65536 {{ i64::MIN + pm[({x} - i64::MIN) as usize] as i64 }} else {{ {x} }} }}")
            }
            Ty::Rec(fs) => {
                let r = self.fresh("r");
                let mut parts = vec![];
                for (i, (_, ft)) in fs.iter().enumerate() {
                    parts.push(self.perm_code(&format!("{r}{}", rec_field(fs.len(), i)), ft)?);
                }
                format!("{{ let {r} = &({c}); {} }}", rec_build(&parts))
            }
            Ty::Opt(inner) => {
                let o = self.fresh("o");
                format!("{{ let {o} = &({c}); ({o}.0, {}) }}", self.perm_code(&format!("{o}.1"), inner)?)
            }
            Ty::Fun(d, cod) => {
                let did = self.ty_id(d)?;
                let (f, o, i) = (self.fresh("f"), self.fresh("o"), self.fresh("i"));
                let k = self.perm_code(&format!("dec_{did}({i} as u64)"), d)?;
                let v = self.perm_code(&format!("{f}[{i}]"), cod)?;
                format!("{{ let {f} = &({c}); let mut {o} = *{f}; for {i} in 0..{} {{ {o}[idx_{did}({k})] = {v}; }} {o} }}", d.size().unwrap())
            }
            Ty::Seq(e) => {
                let (acc, i) = (self.fresh("acc"), self.fresh("i"));
                let py = self.perm_code(&format!("{acc}.items[{i}]"), e)?;
                format!("{{ let mut {acc} = {c}; for {i} in 0..{acc}.len as usize {{ {acc}.items[{i}] = {py}; }} {acc} }}")
            }
            // A permutation is a bijection, so permuting the elements of a sorted array in place
            // leaves them distinct and one sort restores the order.
            Ty::Set(e) if is_sparse(t) => {
                let (acc, i, y) = (self.fresh("acc"), self.fresh("i"), self.fresh("y"));
                let py = self.perm_code(&format!("{acc}.items[{i}]"), e)?;
                format!(
                    "{{ let mut {acc} = {c}; for {i} in 0..{acc}.len as usize {{ let {y} = {py}; {acc}.items[{i}] = {y}; }} \
                     {acc}.items[..{acc}.len as usize].sort_unstable(); {acc} }}"
                )
            }
            Ty::Set(e) => {
                let x = self.fresh("x");
                let acc = self.fresh("acc");
                let it = self.s_iter(c, t)?;
                let px = self.perm_code(&x, e)?;
                let add = self.s_add(&acc, &px, t)?;
                let empty = self.s_empty(t)?;
                format!("{{ let mut {acc} = {empty}; for {x} in {it} {{ {add} }} {acc} }}")
            }
        })
    }

    /// Permutation tables and perm_state. Each entry of `perms` maps atom -> atom.
    pub fn gen_perms(&mut self, perms: &[Vec<u16>]) -> R<String> {
        let mut s = String::new();
        let tables: Vec<String> = perms
            .iter()
            .map(|p| format!("&[{}]", p.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")))
            .collect();
        writeln!(s, "static PERMS: &[&[u16]] = &[{}];", tables.join(", ")).unwrap();
        let mut fields = vec![];
        for (v, t) in self.vars.clone() {
            fields.push(format!("v_{v}: {}", self.perm_code(&format!("s.v_{v}"), &t)?));
        }
        writeln!(s, "fn perm_state(s: &State, pm: &[u16]) -> State {{ State {{ {} }} }}", fields.join(", ")).unwrap();
        // TLC's order of states: the variables in the order it prints them, each in its order of
        // values (with a VIEW, the smallest permuted state is the one whose view is taken)
        let mut cmp = String::from("std::cmp::Ordering::Equal");
        for v in self.print_order.clone().iter().rev() {
            let t = self.vars.iter().find(|(n, _)| n == v).map(|(_, t)| t.clone()).ok_or("a variable without a type")?;
            let c = self.tlc_cmp(&t, &format!("(&a.v_{v})"), &format!("(&b.v_{v})"))?;
            cmp = format!("{c}.then_with(|| {cmp})");
        }
        writeln!(s, "fn tlc_state_cmp(a: &State, b: &State) -> std::cmp::Ordering {{ {cmp} }}").unwrap();
        Ok(s)
    }

    pub fn atoms_table(&self) -> String {
        let names: Vec<String> = (0..self.atoms.len()).map(|i| format!("{:?}", self.atoms.show(i as u32))).collect();
        let strs: Vec<String> = (0..self.atoms.len()).map(|i| (!self.atoms.is_model(i as u32)).to_string()).collect();
        format!(
            "static ATOMS: [&str; {}] = [{}];\nstatic IS_STR: [bool; {}] = [{}];\n\
             // Equality of integers-or-atoms (an atom is i64::MIN + its id). TLC stops when it compares a string with an integer\n\
             fn mixed_eq(a: i64, b: i64) -> bool {{ let (ai, bi) = (a >= i64::MIN + 65536, b >= i64::MIN + 65536); \
             if ai != bi {{ let at = if ai {{ b }} else {{ a }}; let n = if ai {{ a }} else {{ b }}; if IS_STR[(at - i64::MIN) as usize] {{ \
             eval_error(format!(\"Attempted to check equality of integer {{}} with non-integer:\\n{{}}\", n, ATOMS[(at - i64::MIN) as usize])) }} }} a == b }}\n\
             // The same, worded by the value on the left (`Gen::str_int_eq`)\n\
             fn str_int_eq(a: i64, b: i64) -> bool {{ let (ai, bi) = (a >= i64::MIN + 65536, b >= i64::MIN + 65536); \
             if ai && !bi && IS_STR[(b - i64::MIN) as usize] {{ eval_error(format!(\"Attempted to check equality of integer {{}} with non-integer:\\n{{}}\", a, ATOMS[(b - i64::MIN) as usize])) }} \
             if bi && !ai && IS_STR[(a - i64::MIN) as usize] {{ eval_error(format!(\"Attempted to check equality of string {{}} with non-string:\\n{{}}\", ATOMS[(a - i64::MIN) as usize], b)) }} a == b }}\n",
            names.len(),
            names.join(", "),
            strs.len(),
            strs.join(", ")
        )
    }
}

/// How a comparison involving tuples turns out in TLC (see `Gen::tuple_cmp`)
#[derive(Clone, PartialEq)]
enum Cmp {
    /// Compare the values
    Normal,
    /// Never equal
    Unequal,
    /// TLC stops with this error when it evaluates the comparison
    Fails(String),
}

/// The sequence type of the generated checker, pasted in with the runtime. Errors of the operators
/// TLC implements as built-ins (Head, Tail, SubSeq) use `arith_error`, for TLC's exit code. Unused slots hold the
/// default value, so derived equality and hashing see only the elements; it orders as TLC orders
/// tuples, by length and then element by element.
pub const SQ_RUNTIME: &str = r#"
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Sq<T: Copy + Ord + ConstDefault, const N: usize> {
    len: u16,
    items: [T; N],
}
impl<T: Copy + Ord + ConstDefault, const N: usize> ConstDefault for Sq<T, N> {
    const DEFAULT: Self = Sq { len: 0, items: [T::DEFAULT; N] };
}
impl<T: Copy + Ord + ConstDefault, const N: usize> Ord for Sq<T, N> {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.len.cmp(&o.len).then_with(|| self.slice().cmp(o.slice()))
    }
}
impl<T: Copy + Ord + ConstDefault, const N: usize> PartialOrd for Sq<T, N> {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
#[cold]
fn seq_too_long(n: usize) -> ! {
    capacity_exceeded(CAP_SEQ, format!("a sequence grew beyond {n} elements; raise the bound with `Len(x) <= N` in TypeOK or a CONSTRAINT, or with -seqcap"))
}
impl<T: Copy + Ord + ConstDefault, const N: usize> Sq<T, N> {
    fn new() -> Self {
        Self::DEFAULT
    }
    fn slice(&self) -> &[T] {
        &self.items[..self.len as usize]
    }
    fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.slice().iter().copied()
    }
    fn from_slice(xs: &[T]) -> Self {
        let mut s = Self::new();
        for &x in xs {
            s.push(x);
        }
        s
    }
    fn push(&mut self, x: T) {
        if self.len as usize == N {
            seq_too_long(N)
        }
        self.items[self.len as usize] = x;
        self.len += 1;
    }
    fn at(&self, i: i64) -> T {
        if i < 1 || i > self.len as i64 {
            eval_error(format!("Attempted to apply a sequence of length {} to the index {}", self.len, i))
        }
        self.items[(i - 1) as usize]
    }
    fn head(&self) -> T {
        if self.len == 0 {
            arith_error("Attempted to apply Head to the empty sequence.".into())
        }
        self.items[0]
    }
    fn tail(&self) -> Self {
        if self.len == 0 {
            arith_error("Attempted to apply Tail to the empty sequence.".into())
        }
        Self::from_slice(&self.slice()[1..])
    }
    fn concat(&self, o: &Self) -> Self {
        let mut s = *self;
        for x in o.iter() {
            s.push(x);
        }
        s
    }
    fn sub(&self, m: i64, n: i64) -> Self {
        if m > n {
            return Self::new();
        }
        if m < 1 || m > self.len as i64 {
            arith_error("The second argument of SubSeq must be in the domain of its first argument.".into())
        }
        if n > self.len as i64 {
            arith_error("The third argument of SubSeq must be in the domain of its first argument.".into())
        }
        Self::from_slice(&self.slice()[(m - 1) as usize..n as usize])
    }
}
"#;

/// The domain and codomain types of a function value that @@ can join (None if not a function)
/// Constant sets of more elements than this that the checker iterates over are enumerated by it
/// instead of written out (see `Gen::big_set_iter`). A smaller set stays written out, so that the
/// code generated for it does not change; with 0 here, the checkers of every configuration of
/// examples/ and tests/tlc/ and of the corpus but GameOfLife enumerated the same elements in the
/// same order as written out (measured by comparing the two at run time)
const BIG_SET: usize = 1024;

/// A constant set of more elements than this, written out, is a table: a static where the
/// elements are constant expressions (`const_lit`)
const LIT_TABLE: usize = 64;

/// Whether `Gen::lit` writes the values of type t as constant expressions: not those holding a
/// sequence or a set held as an array, which it builds by calls
fn const_lit(t: &Ty) -> bool {
    match t {
        Ty::Bool | Ty::Int(..) | Ty::IntAtom(..) | Ty::Enum(_) => true,
        Ty::Rec(fs) => fs.iter().all(|(_, f)| const_lit(f)),
        Ty::Opt(e) | Ty::Fun(_, e) => const_lit(e),
        Ty::PFun(_, c) => !is_sparse_fun(t) && const_lit(c),
        Ty::Bag(_) => !is_sparse_fun(t),
        Ty::Set(_) => !is_sparse(t),
        Ty::Seq(_) => false,
    }
}

/// A constant set by its parts, enumerated by the checker (see `Gen::big_set_iter`). Its elements
/// come in the order of the set's value: functions, tuples and records compare their values one
/// by one (the first varies slowest), sets of the same size their elements in order
enum BigSet {
    /// A set written out: its elements, in order
    Lit(Vec<Value>),
    /// `[D -> R]`: D's elements in order, and R
    Fun(Vec<Value>, Box<BigSet>),
    /// `S1 \X ... \X Sn`
    Prod(Vec<BigSet>),
    /// `[f1 : S1, ...]`, the fields in TLC's order
    Rec(Vec<(String, BigSet)>),
    /// `SUBSET S`: S's elements in order (enumerated by `subsets_tlc`)
    Subset(Vec<Value>),
}

impl BigSet {
    fn size(&self) -> f64 {
        match self {
            BigSet::Lit(v) => v.len() as f64,
            BigSet::Fun(d, r) => r.size().powi(d.len() as i32),
            BigSet::Prod(ps) => ps.iter().map(|p| p.size()).product(),
            BigSet::Rec(fs) => fs.iter().map(|(_, p)| p.size()).product(),
            BigSet::Subset(s) => 2f64.powi(s.len() as i32),
        }
    }

    /// Elements whose types join to the type `ty_of_value` gives the elements of the whole set
    fn reps(&self) -> Vec<Value> {
        // Element i takes the i-th representative of each part (none is empty)
        let diag = |parts: Vec<Vec<Value>>| -> Vec<Vec<Value>> {
            let k = parts.iter().map(|p| p.len()).max().unwrap_or(0);
            (0..k).map(|i| parts.iter().map(|p| p[i % p.len()].clone()).collect()).collect()
        };
        match self {
            BigSet::Lit(v) => v.clone(),
            BigSet::Fun(d, r) => r.reps().into_iter().map(|x| fun_value(d.iter().map(|k| (k.clone(), x.clone())).collect())).collect(),
            BigSet::Prod(ps) => diag(ps.iter().map(|p| p.reps()).collect()).into_iter().map(Value::Tuple).collect(),
            BigSet::Rec(fs) => diag(fs.iter().map(|(_, p)| p.reps()).collect())
                .into_iter()
                .map(|xs| Value::Rec(fs.iter().map(|(k, _)| k.clone()).zip(xs).collect()))
                .collect(),
            BigSet::Subset(s) => vec![Value::Set(BTreeSet::new()), Value::Set(s.iter().cloned().collect())],
        }
    }

    /// The type of the elements
    fn ty(&self) -> R<Ty> {
        match ty_of_value(&Value::Set(self.reps().into_iter().collect()))? {
            Ty::Set(t) => Ok(*t),
            _ => unreachable!(),
        }
    }
}

fn pfun_parts(t: &Ty) -> Option<(Ty, Ty)> {
    match t {
        Ty::PFun(d, c) | Ty::Fun(d, c) => Some((d.as_ref().clone(), c.as_ref().clone())),
        Ty::Rec(fs) if fs.is_empty() => Some((Ty::Enum(vec![]), Ty::Enum(vec![]))),
        _ => None,
    }
}

/// How TLC prints function `f` (possibly after EXCEPT, which changes nothing in it) when it cannot
/// enumerate its domain: `[x \in Nat |-> <expression line 5, col 26 to line 5, col 30 of module
/// M>]`, with the bound variables as SANY groups them (only the first name of `a, c \in S`), each
/// group's domain as TLC prints its value (`part`, None when it is not supported), and the body's
/// position, or a number as written. Measured on TLC 2.19 (`tests/tlc/LazyFunText*`). None when f
/// is not a function constructor
pub fn lazy_fun_string(f: &Expr, part: &mut dyn FnMut(&Expr) -> Option<String>) -> Option<String> {
    let mut e = f;
    let (shape, inner) = loop {
        match e {
            Expr::Label(n, _, b) => match n.strip_prefix(crate::ast::FN) {
                Some(shape) => break (shape, b.as_ref()),
                None => e = b,
            },
            Expr::Except(b, _) => e = b,
            _ => return None,
        }
    };
    let Expr::FunCons(_, dom, _) = inner.strip() else { return None };
    let (bounds, body) = shape.split_once('\u{1}')?;
    let mut out = String::new();
    let mut rest = bounds;
    while let Some((pre, after)) = rest.split_once('\u{2}') {
        let (k, after) = after.split_once('\u{3}')?;
        out += pre;
        let d = match (k, dom.strip()) {
            ("*", _) => dom.as_ref(),
            (k, Expr::Call(x, parts)) if x == "\\X" => parts.get(k.parse::<usize>().ok()?)?,
            _ => return None,
        };
        out += &part(d)?;
        rest = after;
    }
    out += rest;
    Some(format!("[{out} |-> <expression {body}>]"))
}

/// `[x \in S |-> ...]` for messages, with the bound variable's name as written
fn lazy_fun_text(x: &str, s: &Expr) -> String {
    let x = x.split("__").next().unwrap_or(x);
    let s = match s.strip() {
        Expr::Ident(n, _) => n.clone(),
        s => short(s),
    };
    format!("[{x} \\in {s} |-> ...]")
}

/// The key and value types of a function over part of a type or of a bag (a count of 1 or more)
fn fun_kv(t: &Ty) -> (Ty, Ty) {
    match t {
        Ty::PFun(d, c) => (d.as_ref().clone(), c.as_ref().clone()),
        Ty::Bag(e) => (e.as_ref().clone(), Ty::Int(1, BIG)),
        _ => unreachable!(),
    }
}

/// The type a function over part of a type is stored as: an optional value per element
fn pfun_repr(d: &Ty, c: &Ty) -> Ty {
    Ty::Fun(d.clone().into(), Ty::Opt(c.clone().into()).into())
}

/// The function type a bag is stored as: element -> count (0 when absent)
fn bag_fun(e: &Ty) -> Ty {
    Ty::Fun(e.clone().into(), Ty::Int(0, BIG).into())
}

/// Whether the Rust order of values of type `t` differs from TLC's: a set held as a bitmask compares
/// as a number in Rust, but by size and then elements in TLC
fn needs_tlc_order(t: &Ty) -> bool {
    match t {
        Ty::Bag(_) | Ty::PFun(..) => true,
        Ty::Set(e) => !is_sparse(t) || needs_tlc_order(e),
        // Records of different fields: TLC compares the number of fields first
        Ty::Rec(fs) if !is_tuple_fields(fs) && fs.iter().any(|(_, t)| matches!(t, Ty::Opt(_))) => true,
        Ty::Rec(fs) => fs.iter().any(|(_, t)| needs_tlc_order(t)),
        Ty::Fun(_, c) | Ty::Seq(c) => needs_tlc_order(c),
        _ => false,
    }
}

/// A pair of fields of a record type inside t that the spec writes in the order opposite to TLC's
fn disordered_ty(t: &Ty) -> Option<(String, String)> {
    match t {
        Ty::Rec(fs) => {
            let names: Vec<&str> = fs.iter().map(|(k, _)| k.as_str()).collect();
            crate::types::disordered_fields(&names).or_else(|| fs.iter().find_map(|(_, t)| disordered_ty(t)))
        }
        Ty::Set(e) | Ty::Seq(e) | Ty::Opt(e) | Ty::Bag(e) => disordered_ty(e),
        Ty::Fun(d, c) | Ty::PFun(d, c) => disordered_ty(d).or_else(|| disordered_ty(c)),
        _ => None,
    }
}

/// The conjunct standing for the elements after the first in `Gen::gen_forall`
const FORALL_REST: &str = "#forall-rest";
/// `#forall-nth(S, k)`: the k-th element of S in the order `\A` takes them (see `Gen::forall_rec`)
const FORALL_NTH: &str = "#forall-nth";

/// A boolean expression that stops with an evaluation error when it is evaluated (TLC stops only
/// when it evaluates the comparison, so a branch never taken must not be an error)
/// The position of the AT label among the labels around e, if any (see ast::AT)
fn err_at(e: &Expr) -> Option<String> {
    let mut x = e;
    while let Expr::Label(n, _, b) = x {
        if let Some(p) = err_pos_of(n) {
            return Some(p.to_string());
        }
        x = b;
    }
    None
}

/// TLC's message followed by the position it gives, when known
pub fn with_at(msg: &str, at: &Option<String>) -> String {
    match at {
        Some(p) => format!("{msg}\n{p}"),
        None => msg.to_string(),
    }
}

/// TLC's error for an identifier it cannot evaluate (a variable not assigned yet), with the
/// position of the identifier when it is known
fn undefined_ident(n: &str, at: &Pos) -> String {
    let msg = format!("In evaluation, the identifier {n} is either undefined or not an operator.");
    if at.known() { format!("{msg}\n{}", at.text()) } else { msg }
}

fn eval_error_bool(msg: &str) -> String {
    // TLC's own evaluation errors (for a failed arithmetic operation) are raised as such
    let f = if msg.starts_with(crate::value::DIV_ZERO) || msg.starts_with(crate::value::MOD_NONPOS) { "arith_error" } else { "eval_error" };
    format!("{{ let __b: bool = {f}({msg:?}.to_string()); __b }}")
}

/// `t` with every integer range outside sets made unbounded
fn unbounded_ints(t: &Ty) -> Ty {
    match t {
        Ty::Int(..) => Ty::Int(-BIG, BIG),
        Ty::IntAtom(_, _, a) => Ty::IntAtom(-BIG, BIG, a.clone()),
        Ty::Rec(fs) => Ty::Rec(fs.iter().map(|(n, t)| (n.clone(), unbounded_ints(t))).collect()),
        Ty::Opt(x) => Ty::Opt(unbounded_ints(x).into()),
        Ty::Fun(d, c) => Ty::Fun(d.clone(), unbounded_ints(c).into()),
        t => t.clone(),
    }
}

impl Env {
    pub fn bind(&mut self, name: &str, code: String, t: Ty) {
        self.locals.insert(name.to_string(), (code, t));
    }
}

/// The body of a BIND label with the pairs `pairs`, with the names written out
fn unbind(pairs: &[Expr], body: &Expr) -> Expr {
    let mut body = body.clone();
    for p in pairs.chunks(2).rev() {
        if let [Expr::Ident(n, _), x] = p {
            body = crate::expand::subst_ident(&body, n, x);
        }
    }
    body
}

/// e without the labels around it other than BIND labels (call sites, positions)
fn unlabel(e: &Expr) -> &Expr {
    match e {
        Expr::Label(n, _, b) if !is_bind(n) => unlabel(b),
        e => e,
    }
}

/// Whether TLC keeps the value of e unevaluated, so that only the parts used are computed: a
/// function constructor (applied where it is applied), or a set it does not enumerate to test
/// membership (a range, SUBSET, UNION, a set of functions, records, sequences or tuples)
fn lazy_value(e: &Expr) -> bool {
    use Expr::*;
    match e {
        Label(_, _, b) => lazy_value(b),
        If(_, a, b) => lazy_value(a) || lazy_value(b),
        Case(arms, o) => arms.iter().any(|(_, v)| lazy_value(v)) || o.as_ref().is_some_and(|o| lazy_value(o)),
        FunCons(..) | FunSet(..) | RecSet(..) | Un(UOp::Subset | UOp::Union, _) | Bin(BOp::Range, ..) => true,
        Call(f, _) => f == "Seq" || f == "\\X",
        _ => false,
    }
}

/// e with the identifier `from` (a bound variable, named uniquely by expansion) renamed to `to`
fn rename_ident(e: &Expr, from: &str, to: &str) -> Expr {
    match e {
        Expr::Ident(n, _) if n == from => Expr::Ident(to.to_string(), NOPOS),
        _ => map_children(e, &|c| rename_ident(c, from, to)),
    }
}

/// e with every occurrence of the expression `from` replaced by `to`
fn replace_expr(e: &Expr, from: &Expr, to: &Expr) -> Expr {
    if e.strip() == from.strip() {
        return to.clone();
    }
    map_children(e, &|c| replace_expr(c, from, to))
}

/// Rebuilds e with each child replaced by f(child), preserving its structure
pub fn map_children(e: &Expr, f: &dyn Fn(&Expr) -> Expr) -> Expr {
    use Expr::*;
    let m = |x: &Expr| f(x);
    let mb = |x: &Expr| f(x).b();
    match e {
        Num(_) | Str(_) | Bool(_) | Ident(_, _) | At => e.clone(),
        Call(n, a) => Call(n.clone(), a.iter().map(m).collect()),
        Prime(x) => Prime(mb(x)),
        Un(o, x) => Un(*o, mb(x)),
        Bin(o, a, b) => Bin(*o, mb(a), mb(b)),
        And(xs) => And(xs.iter().map(m).collect()),
        Or(xs) => Or(xs.iter().map(m).collect()),
        If(a, b, c) => If(mb(a), mb(b), mb(c)),
        Case(arms, o) => Case(arms.iter().map(|(p, v)| (m(p), m(v))).collect(), o.as_ref().map(|x| mb(x))),
        Quant(q, bs, b) => Quant(*q, bs.iter().map(|(x, s)| (x.clone(), m(s))).collect(), mb(b)),
        Choose(x, s, p) => Choose(x.clone(), mb(s), mb(p)),
        SetLit(xs) => SetLit(xs.iter().map(m).collect()),
        SetFilter(x, s, p) => SetFilter(x.clone(), mb(s), mb(p)),
        SetMap(g, bs) => SetMap(mb(g), bs.iter().map(|(x, s)| (x.clone(), m(s))).collect()),
        FunCons(x, s, b) => FunCons(x.clone(), mb(s), mb(b)),
        FunSet(a, b) => FunSet(mb(a), mb(b)),
        RecLit(fs) => RecLit(fs.iter().map(|(k, v)| (k.clone(), m(v))).collect()),
        RecSet(fs) => RecSet(fs.iter().map(|(k, v)| (k.clone(), m(v))).collect()),
        App(a, b) => App(mb(a), mb(b)),
        Field(r, k) => Field(mb(r), k.clone()),
        Except(g, ups) => Except(
            mb(g),
            ups.iter()
                .map(|(path, v)| {
                    let path = path
                        .iter()
                        .map(|p| match p {
                            Path::Idx(i) => Path::Idx(m(i)),
                            Path::Field(k) => Path::Field(k.clone()),
                        })
                        .collect();
                    (path, m(v))
                })
                .collect(),
        ),
        Tuple(xs) => Tuple(xs.iter().map(m).collect()),
        Let(ds, b) => Let(ds.clone(), mb(b)),
        BoxAction(a, b) => BoxAction(mb(a), mb(b)),
        Fair(w, a, b) => Fair(*w, mb(a), mb(b)),
        Label(n, a, b) => Label(n.clone(), a.iter().map(m).collect(), mb(b)),
        Lambda(ps, b) => Lambda(ps.clone(), mb(b)),
        RecCall(i, a) => RecCall(*i, a.iter().map(m).collect()),
    }
}

pub fn short(e: &Expr) -> String {
    // Without the positions of names (see `Pos`)
    let s = format!("{e:?}").replace("\", _)", "\")");
    if s.len() > 200 {
        format!("{}…", &s[..s.char_indices().nth(200).map(|x| x.0).unwrap_or(s.len())])
    } else {
        s
    }
}
