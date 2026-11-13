//! Inlines all operator definitions. Bound variables are renamed to avoid capture.
//! Call sites are kept as `Expr::Label` (for trace output and fairness matching).

use crate::ast::*;
use crate::lexer::{R, SANY};
use std::collections::HashMap;

#[derive(Clone, Default)]
struct Env {
    subst: HashMap<String, Expr>,
    locals: HashMap<String, (Def, Env)>,
    /// LET definitions known only for the positional names of their subexpressions (`Op!1`):
    /// those bound to a name (their uses read `subst`), and those `check_subexprs` meets. Shared,
    /// since each holds the environment before it
    lets: HashMap<String, (Def, std::rc::Rc<Env>)>,
}

/// A recursive operator, expanded once with its parameters as fresh bound variables. Its calls
/// stay `Expr::RecCall`s, evaluated by the constant evaluator or compiled into a Rust function.
#[derive(Clone, Debug)]
pub struct RecDef {
    pub name: String,
    pub params: Vec<String>,
    pub body: Expr,
}

thread_local! {
    static REC_DEFS: std::cell::RefCell<Vec<RecDef>> = const { std::cell::RefCell::new(vec![]) };
}

pub fn rec_def(i: usize) -> RecDef {
    REC_DEFS.with(|r| r.borrow()[i].clone())
}

/// Adds a recursive definition that code generation makes (see `Gen::forall_rec`), and returns
/// its index
pub fn add_rec_def(d: RecDef) -> usize {
    REC_DEFS.with(|r| {
        let mut r = r.borrow_mut();
        r.push(d);
        r.len() - 1
    })
}

pub fn set_rec_def(i: usize, d: RecDef) {
    REC_DEFS.with(|r| r.borrow_mut()[i] = d);
}

pub struct Expander<'a> {
    defs: HashMap<&'a str, &'a Def>,
    fresh: usize,
    depth: usize,
    recursive: Vec<String>,
    /// Definitions being expanded (by their unique name), innermost last
    stack: Vec<String>,
    /// Unique name of a recursive definition -> its index in REC_DEFS
    rec_ids: HashMap<String, usize>,
    /// Keep the POS labels (see `ast::POS`), for the next-state relation; otherwise they are
    /// dropped
    pub keep_pos: bool,
    /// Bind arguments and LET definitions to names: for the constant evaluator
    /// (`expand_def_bound`, BIND_CONST) or for code generation (`expand_def_code`, BIND_CODE)
    bind: u8,
    /// The counter for fresh names while binding, apart from `fresh`, so that the names of what is
    /// expanded for code generation stay as they are
    bind_fresh: usize,
    variables: std::collections::HashSet<String>,
}

impl<'a> Expander<'a> {
    pub fn new(m: &'a Module) -> Self {
        REC_DEFS.with(|r| r.borrow_mut().clear());
        crate::value::clear_bound();
        Expander {
            defs: m.defs.iter().map(|d| (d.name.as_str(), d)).collect(),
            fresh: 0,
            depth: 0,
            recursive: m.recursive.clone(),
            stack: vec![],
            rec_ids: HashMap::new(),
            keep_pos: false,
            bind: 0,
            bind_fresh: 1 << 40,
            variables: m.variables.iter().cloned().collect(),
        }
    }

    /// Like `expand_def`, for the constant evaluator only: an argument of a call that is of
    /// constant level and not a name or literal, and a LET definition without arguments, are
    /// expanded once and bound to a name, which the body refers to (`ast::BIND`). Writing them out
    /// at each use repeats them in the expansion, and the evaluator would evaluate each copy, which
    /// multiplies at each level of definitions that pass a value on (a fold whose accumulator a
    /// definition uses several times: HTML's `HTMLFill`, the corpus's `BlockDagTest`)
    pub fn expand_def_bound(&mut self, name: &str) -> R<Expr> {
        self.bound(|s| s.expand_def(name))
    }

    /// `expand_top` with bindings, as `expand_def_bound`
    pub fn expand_top_bound(&mut self, e: &Expr) -> R<Expr> {
        self.bound(|s| s.expand_top(e))
    }

    fn bound<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = (self.bind, self.fresh);
        self.bind = BIND_CONST;
        self.fresh = self.bind_fresh;
        let r = f(self);
        self.bind_fresh = self.fresh;
        (self.bind, self.fresh) = saved;
        r
    }

    /// Like `expand_def`, for code generation: an argument of a call that is not a name or
    /// literal and reads no primed variable, and a LET definition without arguments, are expanded
    /// once and bound to a name (`ast::BIND`), which code generation evaluates where it is first
    /// used and keeps for the evaluation of the body, as TLC does (`Gen::gen_bind`)
    /// `action` tells whether TLC evaluates the definition as an action (Init and Next), see
    /// `float_binds`
    pub fn expand_def_code(&mut self, name: &str, action: bool) -> R<Expr> {
        self.code_bound(action, |s| s.expand_def(name))
    }

    /// `expand_top` with bindings for code generation, as `expand_def_code`
    pub fn expand_top_code(&mut self, e: &Expr, action: bool) -> R<Expr> {
        self.code_bound(action, |s| s.expand_top(e))
    }

    fn code_bound(&mut self, action: bool, f: impl FnOnce(&mut Self) -> R<Expr>) -> R<Expr> {
        let saved = self.bind;
        self.bind = BIND_CODE;
        let first = REC_DEFS.with(|r| r.borrow().len());
        let r = f(self);
        self.bind = saved;
        // The recursive definitions expanded with bindings for code generation are kept apart
        // (see `call`), so all of them were made by this call
        let last = REC_DEFS.with(|r| r.borrow().len());
        for i in first..last {
            let mut d = rec_def(i);
            d.body = float_binds(&d.body, false);
            set_rec_def(i, d);
        }
        Ok(float_binds(&r?, action))
    }

    /// Whether the expanded argument `a` is bound to a name while binding: not a name or literal
    /// (those cost nothing to write out). For the constant evaluator, of constant level, so that
    /// only the constant evaluator meets the name (a variable, prime or temporal operator stays
    /// written out, for the checks of levels and of what is constant); for code generation, of
    /// state level (what TLC evaluates in the state at hand, not in the step)
    fn bindable(&self, a: &Expr) -> bool {
        self.bind != 0
            && !matches!(a, Expr::Num(_) | Expr::Str(_) | Expr::Bool(_) | Expr::Ident(..))
            && !a.any(&|x| match x {
                Expr::Ident(v, _) => self.bind == BIND_CONST && self.variables.contains(v),
                Expr::Prime(_) | Expr::Un(UOp::Unchanged | UOp::Enabled | UOp::Always | UOp::Eventually, _) => true,
                Expr::BoxAction(..) | Expr::Fair(..) | Expr::Bin(BOp::LeadsTo, ..) | Expr::Lambda(..) | Expr::At => true,
                Expr::Label(n, ..) => n.starts_with(SUBVAR) || n == ENINST,
                x => x.is_unchecked_temporal(),
            })
    }

    pub fn has_def(&self, n: &str) -> bool {
        self.defs.contains_key(n)
    }

    pub fn def(&self, n: &str) -> Option<&'a Def> {
        self.defs.get(n).copied()
    }

    /// Returns the expanded body of a definition by name
    pub fn expand_def(&mut self, name: &str) -> R<Expr> {
        let d = self.defs.get(name).ok_or(format!("no definition named `{name}`"))?;
        if !d.params.is_empty() {
            return Err(format!("`{name}` takes arguments"));
        }
        let body = self.expand(&d.body, &Env::default())?;
        Ok(Expr::Label(name.into(), vec![], body.b()))
    }

    pub fn expand_top(&mut self, e: &Expr) -> R<Expr> {
        self.expand(e, &Env::default())
    }

    fn bind(&mut self, x: &str, env: &mut Env) -> String {
        self.fresh += 1;
        let n = format!("{x}__{}", self.fresh);
        env.subst.insert(x.to_string(), Expr::Ident(n.clone(), NOPOS));
        n
    }

    /// Expands a call of `d` (defined in `env`) with the unexpanded arguments `raw`, written in
    /// `caller`. An operator parameter `F(_)` is bound to the operator passed for it (a name or a
    /// LAMBDA), together with the environment it was written in.
    fn call(&mut self, name: &str, d: &Def, mut env: Env, raw: &[Expr], caller: &Env) -> R<Expr> {
        if d.params.len() != raw.len() {
            return Err(format!("`{name}` expects {} arguments, got {}", d.params.len(), raw.len()));
        }
        // A RECURSIVE operator called again while its body is being expanded: keep the call
        if self.recursive.iter().any(|r| r == name) && self.stack.contains(&d.name) {
            // Operator arguments are bound in the definition, which is expanded once for each
            // combination of operators passed to it
            // Expanded with bindings, the definition is another one
            let mut key = match self.bind {
                BIND_CONST => format!("{}{BIND}", d.name),
                BIND_CODE => format!("{}{BIND}code", d.name),
                _ => d.name.clone(),
            };
            let mut args = vec![];
            for (i, (p, a)) in d.params.iter().zip(raw).enumerate() {
                if d.arity.get(i).copied().unwrap_or(0) > 0 {
                    let op = self.op_arg(name, p, d.arity[i], a, caller)?;
                    key = format!("{key}|{}", op.0.name);
                    env.subst.remove(p);
                    env.locals.insert(p.clone(), op);
                } else {
                    args.push(self.expand(a, caller)?);
                }
            }
            let id = self.rec_id(name, &key, d, &env)?;
            return Ok(Expr::RecCall(id, args));
        }
        let mut args = vec![];
        let mut binds = vec![];
        for (i, (p, a)) in d.params.iter().zip(raw).enumerate() {
            let arity = d.arity.get(i).copied().unwrap_or(0);
            if arity > 0 {
                let op = self.op_arg(name, p, arity, a, caller)?;
                env.subst.remove(p);
                env.locals.insert(p.clone(), op);
                args.push(Expr::Ident(p.clone(), NOPOS));
            } else {
                if matches!(a, Expr::Lambda(..)) {
                    return Err(format!("`{name}`: LAMBDA passed for `{p}`, which is not an operator parameter"));
                }
                let a = self.expand(a, caller)?;
                if self.bindable(&a) {
                    let n = self.bind(p, &mut env);
                    // For code generation the call site keeps the names the argument reads from
                    // outside, which tell whether it depends on the state, to name actions
                    // (`Gen::gen_split`). Not the argument written out: it holds the call sites
                    // of the calls in it, each with its own argument, so it would double at each
                    // call that passes the value on (`tests/tlc/ArgShare`)
                    args.push(if self.bind == BIND_CODE { Expr::Tuple(free_idents(&a)) } else { Expr::Ident(n.clone(), NOPOS) });
                    binds.extend([Expr::Ident(n, NOPOS), a]);
                } else {
                    env.subst.insert(p.clone(), a.clone());
                    args.push(a);
                }
            }
        }
        self.depth += 1;
        if self.depth > 200 {
            return Err(format!("`{name}`: recursive operator definitions are not supported"));
        }
        self.stack.push(d.name.clone());
        let body = self.expand(&d.body, &env);
        self.stack.pop();
        self.depth -= 1;
        Ok(Expr::Label(name.into(), args, with_binds(binds, body?).b()))
    }

    /// Whether `n` names a recursive function definition (not shadowed by a bound variable)
    fn rec_fun_app(&self, n: &str, env: &Env) -> bool {
        if env.subst.contains_key(n) {
            return false;
        }
        let app = format!("{n}#app");
        env.locals.contains_key(&app) || (!env.locals.contains_key(n) && self.defs.contains_key(app.as_str()))
    }

    /// The index of the recursive definition `d` (in the environment `env`), expanding it with
    /// fresh parameters the first time
    fn rec_id(&mut self, name: &str, key: &str, d: &Def, env: &Env) -> R<usize> {
        if let Some(&i) = self.rec_ids.get(key) {
            return Ok(i);
        }
        // Operators that change on every recursive call expand without end, each expansion inside
        // the one before; separate calls (each LAMBDA is a new operator) do not nest
        if self.stack.iter().filter(|s| **s == d.name).count() >= 16 {
            return Err(format!("`{name}`: the operators passed to it keep changing between recursive calls"));
        }
        let i = REC_DEFS.with(|r| {
            let mut r = r.borrow_mut();
            r.push(RecDef { name: name.to_string(), params: vec![], body: Expr::Bool(true) });
            r.len() - 1
        });
        self.rec_ids.insert(key.to_string(), i);
        let mut env = env.clone();
        let params: Vec<String> = d
            .params
            .iter()
            .enumerate()
            .filter(|(i, _)| d.arity.get(*i).copied().unwrap_or(0) == 0)
            .map(|(_, p)| self.bind(p, &mut env))
            .collect();
        self.stack.push(d.name.clone());
        // Shared by every use of the operator, so without positions
        let keep = std::mem::replace(&mut self.keep_pos, false);
        let body = self.expand(&d.body, &env);
        self.keep_pos = keep;
        self.stack.pop();
        let body = body?;
        REC_DEFS.with(|r| r.borrow_mut()[i] = RecDef { name: name.to_string(), params, body });
        Ok(i)
    }

    /// The operator passed for the operator parameter `p` of `name`: a LAMBDA, or the name of an
    /// operator visible in the caller (a definition, a LET definition, or an operator parameter)
    fn op_arg(&mut self, name: &str, p: &str, arity: usize, a: &Expr, caller: &Env) -> R<(Def, Env)> {
        let (d, env) = match a.strip() {
            Expr::Lambda(ps, body) => {
                self.fresh += 1;
                let d = Def {
                    name: format!("LAMBDA#{}", self.fresh),
                    params: ps.clone(),
                    arity: vec![0; ps.len()],
                    body: body.as_ref().clone(),
                };
                (d, caller.clone())
            }
            Expr::Ident(g, _) => match caller.locals.get(g) {
                Some((d, e)) => (d.clone(), e.clone()),
                None => match self.defs.get(g.as_str()) {
                    Some(d) => ((*d).clone(), Env::default()),
                    // A built-in infix operator, as in SortSeq(s, <)
                    None if crate::parser::is_infix_name(g) => {
                        let ps = vec!["#lhs".to_string(), "#rhs".to_string()];
                        let body = crate::parser::bin_expr(g, Expr::Ident(ps[0].clone(), NOPOS), Expr::Ident(ps[1].clone(), NOPOS));
                        (Def { name: format!("{g}#op"), params: ps, arity: vec![0, 0], body }, Env::default())
                    }
                    None => return Err(format!("`{name}`: `{g}` passed for the operator parameter `{p}` is not an operator")),
                },
            },
            _ => return Err(format!("`{name}`: the operator parameter `{p}` needs an operator name or a LAMBDA")),
        };
        if d.params.len() != arity {
            return Err(format!("`{name}`: `{p}` takes {arity} arguments, but the operator passed takes {}", d.params.len()));
        }
        Ok((d, env))
    }

    fn binders(&mut self, bs: &[(String, Expr)], env: &Env) -> R<(Vec<(String, Expr)>, Env)> {
        let mut inner = env.clone();
        let mut out = vec![];
        for (x, s) in bs {
            let s = self.expand(s, env)?;
            let n = self.bind(x, &mut inner);
            out.push((n, s));
        }
        Ok((out, inner))
    }

    fn expand(&mut self, e: &Expr, env: &Env) -> R<Expr> {
        use Expr::*;
        let ex = |s: &mut Self, x: &Expr| s.expand(x, env);
        Ok(match e {
            Num(_) | Str(_) | Bool(_) | At => e.clone(),
            Ident(n, at) => {
                if let Some(v) = env.subst.get(n) {
                    match v {
                        // A bound variable renamed: still written here
                        Ident(m, p) if !p.known() => Ident(m.clone(), *at),
                        // A substituted variable of an instance, written here
                        Label(l, a, b) if l.starts_with(SUBVAR) && !l.contains(SUBVAR_AT) && at.known() => {
                            Label(format!("{l}{SUBVAR_AT}{}", at.text()), a.clone(), b.clone())
                        }
                        v => v.clone(),
                    }
                } else if let Some((d, denv)) = env.locals.get(n) {
                    let (d, denv) = (d.clone(), with_self(n, &d, denv.clone()));
                    self.call(n, &d, denv, &[], env)?
                } else if let Some(d) = self.defs.get(n.as_str()).copied() {
                    self.call(n, d, Env::default(), &[], env)?
                } else if n.contains('!') && self.label_path(n, env).is_some() {
                    self.subexpr("", e, &[], env)?
                } else {
                    e.clone()
                }
            }
            Call(n, parts) if n.starts_with(crate::parser::SUBEXPR) => self.subexpr(n, &parts[0], &parts[1..], env)?,
            Call(n, args) if n.contains('!') && !env.locals.contains_key(n) && !self.defs.contains_key(n.as_str()) && self.label_path(n, env).is_some() => {
                self.subexpr("", e, &[], env)?
            }
            Call(n, args) => {
                if let Some((d, denv)) = env.locals.get(n) {
                    let (d, denv) = (d.clone(), with_self(n, &d, denv.clone()));
                    self.call(n, &d, denv, args, env)?
                } else if let Some(d) = self.defs.get(n.as_str()).copied() {
                    self.call(n, d, Env::default(), args, env)?
                } else if let Some((k, arity)) = builtin_op_param(n, args.len()) {
                    // A built-in with an operator parameter (SelectSeq(s, Test(_)), SortSeq(s,
                    // Op(_, _)), BagOfAll(F(_), B)): the operator becomes a LAMBDA over fresh names
                    let mut out = vec![];
                    for (i, a) in args.iter().enumerate() {
                        if i != k {
                            out.push(ex(self, a)?);
                            continue;
                        }
                        let (d, denv) = self.op_arg(n, "the operator argument", arity, a, env)?;
                        let mut denv = with_self(&d.name, &d, denv);
                        let xs: Vec<String> = d.params.iter().map(|p| self.bind(p, &mut denv)).collect();
                        self.stack.push(d.name.clone());
                        let body = self.expand(&d.body, &denv);
                        self.stack.pop();
                        out.push(Lambda(xs, body?.b()));
                    }
                    Call(n.clone(), out)
                } else {
                    Call(n.clone(), args.iter().map(|a| ex(self, a)).collect::<R<_>>()?)
                }
            }
            Lambda(..) => return Err("LAMBDA is only supported as the argument of an operator parameter".into()),
            RecCall(i, args) => RecCall(*i, args.iter().map(|a| ex(self, a)).collect::<R<_>>()?),
            Prime(x) => Prime(ex(self, x)?.b()),
            Un(op, x) => Un(*op, ex(self, x)?.b()),
            Bin(op, a, b) => {
                let (a2, b2) = (ex(self, a)?, ex(self, b)?);
                // TLC cannot enumerate a string in `x' \in S` and gives the position of the whole
                // expression, whose end is that of S's name, lost here when S names a definition
                let b2 = match (op, a.as_ref(), b.as_ref()) {
                    (BOp::In, Prime(x), Ident(_, sat)) if sat.known() && matches!(b2.strip(), Str(_)) => match x.as_ref() {
                        Ident(_, xat) if xat.known() && xat.module == sat.module => {
                            let whole = Pos { end_line: sat.end_line, end_col: sat.end_col, ..*xat };
                            at_err(&whole.text(), b2)
                        }
                        _ => b2,
                    },
                    _ => b2,
                };
                Bin(*op, a2.b(), b2.b())
            }
            And(xs) => And(xs.iter().map(|x| ex(self, x)).collect::<R<_>>()?),
            Or(xs) => Or(xs.iter().map(|x| ex(self, x)).collect::<R<_>>()?),
            If(c, a, b) => If(ex(self, c)?.b(), ex(self, a)?.b(), ex(self, b)?.b()),
            Case(arms, o) => Case(
                arms.iter().map(|(p, v)| Ok((ex(self, p)?, ex(self, v)?))).collect::<R<_>>()?,
                match o {
                    Some(o) => Some(ex(self, o)?.b()),
                    None => None,
                },
            ),
            Quant(q, bs, body) => {
                let (bs, inner) = self.binders(bs, env)?;
                Quant(*q, bs, self.expand(body, &inner)?.b())
            }
            SetMap(f, bs) => {
                let (bs, inner) = self.binders(bs, env)?;
                SetMap(self.expand(f, &inner)?.b(), bs)
            }
            Choose(x, s, p) | SetFilter(x, s, p) | FunCons(x, s, p) => {
                let s2 = ex(self, s)?;
                let mut inner = env.clone();
                let n = self.bind(x, &mut inner);
                let p2 = self.expand(p, &inner)?;
                match e {
                    Choose(..) => Choose(n, s2.b(), p2.b()),
                    SetFilter(..) => SetFilter(n, s2.b(), p2.b()),
                    _ => FunCons(n, s2.b(), p2.b()),
                }
            }
            SetLit(xs) => SetLit(xs.iter().map(|x| ex(self, x)).collect::<R<_>>()?),
            Tuple(xs) => Tuple(xs.iter().map(|x| ex(self, x)).collect::<R<_>>()?),
            FunSet(a, b) => FunSet(ex(self, a)?.b(), ex(self, b)?.b()),
            RecLit(fs) => RecLit(fs.iter().map(|(k, v)| Ok((k.clone(), ex(self, v)?))).collect::<R<_>>()?),
            RecSet(fs) => RecSet(fs.iter().map(|(k, v)| Ok((k.clone(), ex(self, v)?))).collect::<R<_>>()?),
            // f[a] for a recursive function definition calls the operator it was turned into, so
            // only the entries needed are evaluated (TLC evaluates such a function lazily too)
            App(f, x) if matches!(f.as_ref(), Ident(n, _) if self.rec_fun_app(n, env)) => {
                let Ident(n, _) = f.as_ref() else { unreachable!() };
                self.expand(&Call(format!("{n}#app"), vec![x.as_ref().clone()]), env)?
            }
            App(f, x) => App(ex(self, f)?.b(), ex(self, x)?.b()),
            Field(r, k) => Field(ex(self, r)?.b(), k.clone()),
            Except(f, ups) => {
                let mut f2 = ex(self, f)?;
                // A name replaced by what it stands for: keep where it is written (see EXCEPT_AT)
                if let Ident(_, at) = f.as_ref() {
                    if at.known() && !matches!(f2, Ident(..)) {
                        f2 = except_at(&at.text(), f2);
                    }
                }
                let mut out = vec![];
                for (path, v) in ups {
                    let mut path2: Vec<Path> = path
                        .iter()
                        .map(|p| match p {
                            Path::Idx(i) => Ok(Path::Idx(ex(self, i)?)),
                            Path::Field(k) => Ok(Path::Field(k.clone())),
                        })
                        .collect::<R<_>>()?;
                    // Give this EXCEPT's @ a unique name before expanding, so that an outer @
                    // passed in an argument isn't captured by an EXCEPT in the operator body (@
                    // becomes an expanded identifier).
                    self.fresh += 1;
                    let at = format!("@{}", self.fresh);
                    let v2 = self.expand(&replace_at(v, &at), env)?;
                    path2.push(Path::Field(at));
                    out.push((path2, v2));
                }
                Except(f2.b(), out)
            }
            Let(defs, body) => {
                let mut inner = env.clone();
                let mut binds = vec![];
                for d in defs {
                    let snapshot = inner.clone();
                    inner.subst.remove(&d.name);
                    // A unique name tells apart same-named LET definitions on the expansion stack
                    self.fresh += 1;
                    let unique = Def { name: format!("{}#let{}", d.name, self.fresh), ..d.clone() };
                    // While binding, a definition without arguments is expanded here, once, as a
                    // use would expand it (not a function `f[x \in S]`, whose applications call
                    // `f#app`); one that does not expand is left to its uses, as otherwise
                    let app = format!("{}#app", d.name);
                    if self.bind != 0 && d.params.is_empty() && !defs.iter().any(|x| x.name == app) {
                        let denv = with_self(&d.name, &unique, snapshot.clone());
                        let (depth, stack, rec_ids) = (self.depth, self.stack.len(), self.rec_ids.clone());
                        match self.call(&d.name, &unique, denv, &[], &inner) {
                            Ok(b) if self.bindable(&b) => {
                                let n = self.bind(&d.name, &mut inner);
                                inner.locals.remove(&d.name);
                                // A positional name `M!1` still finds the definition (`tests/tlc/SubLet`)
                                inner.lets.insert(d.name.clone(), (unique.clone(), std::rc::Rc::new(snapshot)));
                                binds.extend([Expr::Ident(n, NOPOS), b]);
                                continue;
                            }
                            Ok(_) => {}
                            // Nothing of the attempt is kept: a recursive definition whose
                            // expansion failed is expanded again where it is used
                            Err(_) => (self.depth, self.rec_ids) = (depth, rec_ids),
                        }
                        self.stack.truncate(stack);
                    }
                    inner.locals.insert(d.name.clone(), (unique, snapshot));
                }
                with_binds(binds, self.expand(body, &inner)?)
            }
            BoxAction(a, v) => BoxAction(ex(self, a)?.b(), ex(self, v)?.b()),
            Fair(w, v, a) => Fair(*w, ex(self, v)?.b(), ex(self, a)?.b()),
            // `a /\ b` written infix (see INFIX_JUNCTION): flattened as the parser otherwise does
            Label(n, _, b) if n == crate::parser::INFIX_JUNCTION => {
                let (And(xs) | Or(xs)) = b.as_ref() else { unreachable!() };
                let (a, c) = (ex(self, &xs[0])?, ex(self, &xs[1])?);
                match (b.as_ref(), a) {
                    (And(_), And(mut v)) => {
                        v.push(c);
                        And(v)
                    }
                    (Or(_), Or(mut v)) => {
                        v.push(c);
                        Or(v)
                    }
                    (And(_), a) => And(vec![a, c]),
                    (_, a) => Or(vec![a, c]),
                }
            }
            Label(n, _, b) if pos_of(n).is_some() => {
                if self.keep_pos {
                    Label(n.clone(), vec![], ex(self, b)?.b())
                } else {
                    ex(self, b)?
                }
            }
            Label(n, args, b) => Label(n.clone(), args.clone(), ex(self, b)?.b()),
        })
    }

    /// For a name `Op!l1!l2` that is not a definition: the longest prefix that is an operator, and
    /// the labels after it
    fn label_path(&self, n: &str, env: &Env) -> Option<(String, Vec<String>)> {
        let parts: Vec<&str> = n.split('!').collect();
        (1..parts.len()).rev().find_map(|i| {
            let op = parts[..i].join("!");
            (env.locals.contains_key(&op) || env.lets.contains_key(&op) || self.defs.contains_key(op.as_str()))
                .then(|| (op, parts[i..].iter().map(|l| l.to_string()).collect()))
        })
    }

    /// A subexpression of an operator's definition, named by labels (`Op!lab`, `Op(a)!lab(b)`) or
    /// by position (`Op!1!2`, `Op!<<`, `Op!>>`, `Op!:`, `Op!(e)` for the body of a quantifier
    /// with its bound variables set to e, and labels after these), as SANY names them. It is
    /// expanded as a definition whose parameters are those of Op, followed by the bound variables
    /// and label parameters set along the way.
    fn subexpr(&mut self, call: &str, base: &Expr, sels: &[Expr], env: &Env) -> R<Expr> {
        let (name, sub, denv, args) = self.subexpr_def(call, base, sels, env)?;
        self.call(&name, &sub, denv, &args, env)
    }

    /// The errors SANY reports for the subexpression names in e (SANY checks every definition,
    /// used or not): those of a name whose operator is a definition of the module
    pub fn check_subexprs(&self, e: &Expr) -> R<()> {
        self.check_subexprs_in(e, &Env::default())
    }

    /// `check_subexprs` with the LET definitions in scope in `env`
    fn check_subexprs_in(&self, e: &Expr, env: &Env) -> R<()> {
        if let Expr::Let(defs, body) = e {
            let mut inner = env.clone();
            for d in defs {
                self.check_subexprs_in(&d.body, &inner)?;
                let before = std::rc::Rc::new(inner.clone());
                inner.lets.insert(d.name.clone(), (d.clone(), before));
            }
            return self.check_subexprs_in(body, &inner);
        }
        let r = match e {
            Expr::Call(n, parts) if n.starts_with(crate::parser::SUBEXPR) => Some(self.subexpr_def(n, &parts[0], &parts[1..], env)),
            // `Op!lab`
            Expr::Ident(n, _) | Expr::Call(n, _) if n.contains('!') && !self.defs.contains_key(n.as_str()) && self.label_path(n, env).is_some() => {
                Some(self.subexpr_def("", e, &[], env))
            }
            _ => None,
        };
        if let Some(Err(m)) = r {
            if m.starts_with(SANY) {
                return Err(m);
            }
        }
        e.children().into_iter().try_for_each(|c| self.check_subexprs_in(c, env))
    }

    /// The definition a subexpression name stands for (see `subexpr`; `call` is the name of the
    /// SUBEXPR call, with the positions of the selectors): the name, the definition, its
    /// environment and the arguments
    fn subexpr_def(&self, call: &str, base: &Expr, sels: &[Expr], env: &Env) -> R<(String, Def, Env, Vec<Expr>)> {
        use Expr::*;
        let (name, mut args) = match base {
            Ident(n, _) => (n.clone(), vec![]),
            Call(n, a) => (n.clone(), a.clone()),
            _ => return Err("a subexpression name must start with an operator".into()),
        };
        // Labels written as part of the name (`Op!lab`) come first
        let (op, labels) = if env.locals.contains_key(&name) || env.lets.contains_key(&name) || self.defs.contains_key(name.as_str()) {
            (name.clone(), vec![])
        } else {
            self.label_path(&name, env).ok_or(format!("unknown operator `{name}`"))?
        };
        let (d, denv) = match (env.locals.get(&op), env.lets.get(&op)) {
            (Some((d, denv)), _) => (d.clone(), with_self(&op, d, denv.clone())),
            (None, Some((d, denv))) => (d.clone(), with_self(&op, d, (**denv).clone())),
            (None, None) => ((*self.defs[op.as_str()]).clone(), Env::default()),
        };
        if args.len() < d.params.len() {
            return Err(format!("`{name}`: `{op}` expects {} arguments", d.params.len()));
        }
        let mut extra = args.split_off(d.params.len());
        extra.reverse();
        let sel_at = crate::parser::subexpr_at(call);
        let mut steps: Vec<(Expr, &str)> = labels
            .into_iter()
            .map(|l| (Call(format!("#label{l}"), vec![]), ""))
            .chain(sels.iter().cloned().enumerate().map(|(k, s)| (s, sel_at.get(k).copied().unwrap_or(""))))
            .collect();
        let mut params = d.params.clone();
        let mut arity = d.arity.clone();
        let mut lets: Vec<Vec<Def>> = vec![];
        let mut cur = d.body.clone();
        steps.reverse();
        while let Some((sel, sel_at)) = steps.pop() {
            match sel {
                Num(_) | Ident(_, _) => {
                    let k = match &sel {
                        Num(k) => *k as usize,
                        Ident(c, _) if c == "<<" => 1,
                        Ident(c, _) if c == ">>" => 2,
                        Ident(c, _) if c == ":" => {
                            let Let(defs, body) = strip_labels(&cur).clone() else {
                                return Err(format!("{SANY}`{name}`: `!:` names the body of a LET"));
                            };
                            lets.push(defs);
                            cur = *body;
                            continue;
                        }
                        _ => return Err(format!("`{name}`: the selector `!@` is not supported")),
                    };
                    if let Case(arms, other) = strip_labels(&cur) {
                        // !i!j: the condition (j = 1) or the value (j = 2) of the i-th arm
                        let Some((Num(j), _)) = steps.pop() else { return Err(crate::sany::report_one(sel_at, "Subexpression of CASE must have form !i!j.")) };
                        let arm = match arms.get(k - 1) {
                            Some((p, v)) => [p.clone(), v.clone()],
                            None if k == arms.len() + 1 && other.is_some() => [Bool(true), other.as_ref().unwrap().as_ref().clone()],
                            None => return Err(format!("{SANY}`{name}`: CASE has no arm {k}")),
                        };
                        cur = arm.get(j as usize - 1).cloned().ok_or(format!("{SANY}`{name}`: no subexpression {k}!{j} of CASE"))?;
                        continue;
                    }
                    if let Let(defs, body) = strip_labels(&cur).clone() {
                        if k != 1 {
                            return Err(format!("{SANY}`{name}`: a LET has one subexpression, its body"));
                        }
                        lets.push(defs);
                        cur = *body;
                        continue;
                    }
                    let parts = operands(&cur).ok_or(format!("`{name}`: cannot name a subexpression of {}", crate::codegen::short(&cur)))?;
                    cur = parts.get(k.wrapping_sub(1)).cloned().ok_or_else(|| crate::sany::report_one(sel_at, &format!("Nonexistent operand specified by `argument selector {k}'.")))?;
                }
                // !(e, ...): the body of a quantifier (CHOOSE, set or function constructor) with its
                // bound variables set to e, ...
                Tuple(vals) => {
                    let (xs, body) = match strip_labels(&cur) {
                        Quant(_, bs, body) => (bs.iter().map(|(x, _)| x.clone()).collect::<Vec<_>>(), body.as_ref().clone()),
                        SetMap(body, bs) => (bs.iter().map(|(x, _)| x.clone()).collect(), body.as_ref().clone()),
                        Choose(x, _, p) | SetFilter(x, _, p) | FunCons(x, _, p) => (vec![x.clone()], p.as_ref().clone()),
                        e => return Err(format!("`{name}`: `!(...)` needs a quantifier, not {}", crate::codegen::short(e))),
                    };
                    if xs.len() != vals.len() {
                        return Err(format!("{SANY}`{name}`: {} values for {} bound variables", vals.len(), xs.len()));
                    }
                    arity.extend(xs.iter().map(|_| 0));
                    params.extend(xs);
                    args.extend(vals);
                    cur = body;
                }
                Call(l, largs) if l.starts_with("#label") => {
                    let l = &l["#label".len()..];
                    let mut scope = vec![];
                    let mut lets2 = vec![];
                    let Some((ps, body)) = find_label(&cur, l, &mut scope, &mut lets2) else {
                        return Err(format!("{SANY}`{name}`: no label `{l}`"));
                    };
                    if let Some(x) = scope.iter().find(|x| !ps.contains(x)) {
                        return Err(format!("{SANY}`{name}`: label `{l}` is in the scope of `{x}`, which it does not take as a parameter"));
                    }
                    let largs = if largs.is_empty() && !ps.is_empty() {
                        // Arguments written after the name `Op!lab(a)` were joined with Op's
                        let n = ps.len().min(extra.len());
                        (0..n).map(|_| extra.pop().unwrap()).collect()
                    } else {
                        largs
                    };
                    if largs.len() != ps.len() {
                        return Err(format!("{SANY}`{name}`: label `{l}` takes {} arguments", ps.len()));
                    }
                    lets.extend(lets2);
                    arity.extend(ps.iter().map(|_| 0));
                    params.extend(ps);
                    args.extend(largs);
                    cur = body;
                }
                _ => unreachable!(),
            }
        }
        if !extra.is_empty() {
            return Err(format!("{SANY}`{name}`: too many arguments"));
        }
        for defs in lets.into_iter().rev() {
            cur = Let(defs, cur.b());
        }
        let sub = Def { name: format!("{}#sub", d.name), params, arity, body: cur };
        Ok((name, sub, denv, args))
    }
}

/// e without the labels around it (written ones and POS labels)
fn strip_labels(e: &Expr) -> &Expr {
    match e {
        Expr::Label(n, _, b) if n.ends_with("::") || pos_of(n).is_some() || err_pos_of(n).is_some() || n.starts_with(crate::ast::FN) => strip_labels(b),
        e => e,
    }
}

/// The operands of e, numbered from 1 by positional subexpression names
fn operands(e: &Expr) -> Option<Vec<Expr>> {
    use Expr::*;
    Some(match strip_labels(e) {
        Label(_, _, b) => match b.as_ref() {
            And(v) | Or(v) => v.clone(),
            _ => return None,
        },
        And(v) | Or(v) | Tuple(v) | SetLit(v) => v.clone(),
        Call(n, a) if !n.starts_with('#') => a.clone(),
        Bin(_, a, b) | App(a, b) | FunSet(a, b) | BoxAction(a, b) => vec![*a.clone(), *b.clone()],
        Un(_, x) | Prime(x) | Field(x, _) => vec![*x.clone()],
        If(c, a, b) => vec![*c.clone(), *a.clone(), *b.clone()],
        Quant(_, bs, _) | SetMap(_, bs) => bs.iter().map(|(_, s)| s.clone()).collect(),
        Choose(_, s, _) | SetFilter(_, s, _) | FunCons(_, s, _) => vec![*s.clone()],
        RecLit(fs) | RecSet(fs) => fs.iter().map(|(_, v)| v.clone()).collect(),
        _ => return None,
    })
}

/// The label `l` in e (not inside another label): its parameters and body. `scope` collects the
/// bound variables around it and `lets` the LET definitions it is in.
fn find_label(e: &Expr, l: &str, scope: &mut Vec<String>, lets: &mut Vec<Vec<Def>>) -> Option<(Vec<String>, Expr)> {
    use Expr::*;
    if let Label(n, _, b) = e {
        if let Some(head) = n.strip_suffix("::") {
            let (ln, ps) = match head.split_once('(') {
                Some((ln, ps)) => (ln, ps.trim_end_matches(')').split(',').map(|p| p.to_string()).collect()),
                None => (head, vec![]),
            };
            return (ln == l).then(|| (ps, b.as_ref().clone()));
        }
    }
    let (binders, sets, bodies): (Vec<String>, Vec<&Expr>, Vec<&Expr>) = match e {
        Quant(_, bs, body) | SetMap(body, bs) => (bs.iter().map(|(x, _)| x.clone()).collect(), bs.iter().map(|(_, s)| s).collect(), vec![body]),
        Choose(x, s, p) | SetFilter(x, s, p) | FunCons(x, s, p) => (vec![x.clone()], vec![s], vec![p]),
        Let(defs, body) => {
            lets.push(defs.clone());
            let r = find_label(body, l, scope, lets);
            if r.is_none() {
                lets.pop();
            }
            return r;
        }
        e => (vec![], e.children(), vec![]),
    };
    for s in sets {
        if let Some(r) = find_label(s, l, scope, lets) {
            return Some(r);
        }
    }
    let n = scope.len();
    scope.extend(binders);
    for b in bodies {
        if let Some(r) = find_label(b, l, scope, lets) {
            return Some(r);
        }
    }
    scope.truncate(n);
    None
}

/// For a built-in operator taking an operator argument: its position and number of arguments
pub(crate) fn builtin_op_param(name: &str, args: usize) -> Option<(usize, usize)> {
    match (name, args) {
        ("SelectSeq", 2) => Some((1, 1)),
        ("SortSeq", 2) => Some((1, 2)),
        ("BagOfAll", 2) => Some((0, 1)),
        _ => None,
    }
}

const BIND_CONST: u8 = 1;
const BIND_CODE: u8 = 2;

/// The identifiers e reads from outside it, each once, in the order first read
fn free_idents(e: &Expr) -> Vec<Expr> {
    fn walk(e: &Expr, bound: &mut Vec<String>, out: &mut Vec<Expr>) {
        use Expr::*;
        let n = bound.len();
        match e {
            Ident(x, _) => {
                if !bound.contains(x) && !out.iter().any(|o| matches!(o, Ident(y, _) if y == x)) {
                    out.push(e.clone());
                }
            }
            // A BIND label binds its names in the expressions after them and in its body
            Label(l, a, b) if is_bind(l) => {
                for p in a.chunks(2) {
                    if let [Ident(x, _), v] = p {
                        walk(v, bound, out);
                        bound.push(x.clone());
                    }
                }
                walk(b, bound, out);
            }
            _ => {
                match e {
                    Quant(_, bs, _) | SetMap(_, bs) => bound.extend(bs.iter().map(|(x, _)| x.clone())),
                    Choose(x, ..) | SetFilter(x, ..) | FunCons(x, ..) => bound.push(x.clone()),
                    Lambda(ps, _) => bound.extend(ps.iter().cloned()),
                    Let(ds, _) => bound.extend(ds.iter().flat_map(|d| std::iter::once(&d.name).chain(&d.params).cloned())),
                    Except(_, ups) => bound.extend(ups.iter().flat_map(|(p, _)| {
                        p.iter().filter_map(|s| match s {
                            Path::Field(k) if k.starts_with('@') => Some(k.clone()),
                            _ => None,
                        })
                    })),
                    _ => {}
                }
                for c in e.children() {
                    walk(c, bound, out);
                }
            }
        }
        bound.truncate(n);
    }
    let mut out = vec![];
    walk(e, &mut vec![], &mut out);
    out
}

/// `body` under a BIND label for the names and expressions in `binds`, if any

fn with_binds(binds: Vec<Expr>, body: Expr) -> Expr {
    if binds.is_empty() { body } else { Expr::Label(BIND.into(), binds, body.b()) }
}

/// The environment of the LET definition `d` named `n`, with `d` itself in it, so that a LET
/// RECURSIVE definition can call itself
fn with_self(n: &str, d: &Def, mut denv: Env) -> Env {
    if d.name.contains("#let") && !denv.locals.contains_key(n) {
        let inner = denv.clone();
        denv.locals.insert(n.to_string(), (d.clone(), inner));
    }
    denv
}

/// e with the BIND labels made for code generation moved up to where code generation evaluates
/// their names. TLC evaluates a LET definition or an argument where it is first used, and keeps
/// the value for the rest of the evaluation of the LET or the call when it evaluates an
/// expression; when it computes the successors of an action (Init and Next, while some variable
/// is still unassigned) it evaluates one again at each use (measured, `tests/tlc/LazyAction`).
/// So where TLC goes through an action (`action`: a conjunction, disjunction, `\E`, IF, CASE, a
/// call), a label stays where it is and is renamed BIND_ACT; inside an expression, it moves up
/// past every part evaluated once (an operator applied, a set or tuple built, IF, ...), and not
/// past one evaluated per value of a bound variable (a quantifier, CHOOSE, a set or function
/// constructor, the values of an EXCEPT), nor past a prime, ENABLED or a temporal operator.
/// The names are evaluated where they are first used, so moving a label changes nothing that is
/// evaluated. Then a name not used is dropped, and one used once, not in a part evaluated per
/// value of a bound variable, is written out where it is used
pub fn float_binds(e: &Expr, action: bool) -> Expr {
    use Expr::*;
    if action {
        let act = |x: &Expr| float_binds(x, true);
        let val = |x: &Expr| float_binds(x, false);
        return match e {
            Label(n, pairs, body) if n == BIND => {
                let pairs: Vec<Expr> = pairs.iter().enumerate().map(|(i, x)| if i % 2 == 0 { x.clone() } else { val(x) }).collect();
                match with_binds_code(pairs.chunks(2).map(|p| p.to_vec()).collect(), act(body)) {
                    Label(n, pairs, body) if n == BIND => Label(BIND_ACT.into(), pairs, body),
                    e => e,
                }
            }
            And(xs) => And(xs.iter().map(act).collect()),
            Or(xs) => Or(xs.iter().map(act).collect()),
            Quant(q, bs, b) => Quant(*q, bs.iter().map(|(x, s)| (x.clone(), val(s))).collect(), act(b).b()),
            If(c, a, b) => If(val(c).b(), act(a).b(), act(b).b()),
            Case(arms, o) => Case(arms.iter().map(|(p, v)| (val(p), act(v))).collect(), o.as_ref().map(|x| act(x).b())),
            Label(n, a, b) => Label(n.clone(), a.clone(), act(b).b()),
            Un(UOp::Enabled, _) => crate::codegen::map_children(e, &act),
            e => val(e),
        };
    }
    let (pairs, e) = float(e);
    with_binds_code(pairs.chunks(2).map(|p| p.to_vec()).collect(), e)
}

fn float(e: &Expr) -> (Vec<Expr>, Expr) {
    use Expr::*;
    let out = std::cell::RefCell::new(vec![]);
    let fl = |x: &Expr| {
        let (p, x) = float(x);
        out.borrow_mut().extend(p);
        x
    };
    let root = |x: &Expr| float_binds(x, false);
    let e2 = match e {
        Label(n, pairs, body) if n == BIND => {
            let mut all: Vec<Expr> = pairs.iter().enumerate().map(|(i, x)| if i % 2 == 0 { x.clone() } else { root(x) }).collect();
            let b = fl(body);
            all.extend(out.into_inner());
            return (all, b);
        }
        Num(_) | Str(_) | Bool(_) | Ident(..) | At => return (vec![], e.clone()),
        Un(UOp::Enabled, _) => return (vec![], crate::codegen::map_children(e, &|x| float_binds(x, true))),
        Prime(_) | Un(UOp::Unchanged | UOp::Always | UOp::Eventually, _) | BoxAction(..) | Fair(..) | Lambda(..) | Let(..) | Bin(BOp::LeadsTo, ..) => {
            return (vec![], crate::codegen::map_children(e, &root));
        }
        _ if e.is_action() => return (vec![], crate::codegen::map_children(e, &root)),
        Quant(q, bs, b) => Quant(*q, bs.iter().map(|(x, s)| (x.clone(), fl(s))).collect(), root(b).b()),
        SetMap(f, bs) => {
            let bs = bs.iter().map(|(x, s)| (x.clone(), fl(s))).collect();
            SetMap(root(f).b(), bs)
        }
        Choose(x, s, p) => Choose(x.clone(), fl(s).b(), root(p).b()),
        SetFilter(x, s, p) => SetFilter(x.clone(), fl(s).b(), root(p).b()),
        FunCons(x, s, p) => FunCons(x.clone(), fl(s).b(), root(p).b()),
        Except(f, ups) => {
            let ups = ups
                .iter()
                .map(|(path, v)| {
                    let path = path
                        .iter()
                        .map(|p| match p {
                            Path::Idx(i) => Path::Idx(root(i)),
                            Path::Field(k) => Path::Field(k.clone()),
                        })
                        .collect();
                    (path, root(v))
                })
                .collect();
            Except(fl(f).b(), ups)
        }
        // The arguments of a call site are only a trace
        Label(n, a, b) => Label(n.clone(), a.clone(), fl(b).b()),
        _ => crate::codegen::map_children(e, &fl),
    };
    (out.into_inner(), e2)
}

/// `body` under a BIND label for the pairs of names and expressions in `pairs`, without the
/// names not used, and with a name used once (not in a part evaluated per value of a bound
/// variable) written out where it is used
fn with_binds_code(pairs: Vec<Vec<Expr>>, mut body: Expr) -> Expr {
    let mut pairs: Vec<(String, Expr)> = pairs
        .iter()
        .map(|p| match p.as_slice() {
            [Expr::Ident(n, _), x] => (n.clone(), x.clone()),
            _ => unreachable!(),
        })
        .collect();
    let mut k = 0;
    while k < pairs.len() {
        let n = pairs[k].0.clone();
        let (mut count, mut under) = (0, false);
        for (_, x) in &pairs[k + 1..] {
            uses(x, &n, false, &mut count, &mut under);
        }
        uses(&body, &n, false, &mut count, &mut under);
        if count == 0 {
            pairs.remove(k);
        } else if count == 1 && !under {
            let (_, x) = pairs.remove(k);
            for p in &mut pairs[k..] {
                p.1 = subst_ident(&p.1, &n, &x);
            }
            body = subst_ident(&body, &n, &x);
        } else {
            k += 1;
        }
    }
    with_binds(pairs.into_iter().flat_map(|(n, x)| [Expr::Ident(n, NOPOS), x]).collect(), body)
}

/// Counts the uses of the name n in e, noting whether one is in a part evaluated per value of a
/// bound variable
fn uses(e: &Expr, n: &str, under: bool, count: &mut usize, flag: &mut bool) {
    use Expr::*;
    match e {
        Ident(m, _) if m == n => {
            *count += 1;
            *flag |= under;
        }
        Quant(_, bs, b) => {
            bs.iter().for_each(|(_, s)| uses(s, n, under, count, flag));
            uses(b, n, true, count, flag);
        }
        SetMap(f, bs) => {
            bs.iter().for_each(|(_, s)| uses(s, n, under, count, flag));
            uses(f, n, true, count, flag);
        }
        Choose(_, s, p) | SetFilter(_, s, p) | FunCons(_, s, p) => {
            uses(s, n, under, count, flag);
            uses(p, n, true, count, flag);
        }
        Lambda(_, b) => uses(b, n, true, count, flag),
        Except(f, ups) => {
            uses(f, n, under, count, flag);
            for c in Except(Bool(true).b(), ups.clone()).children().into_iter().skip(1) {
                uses(c, n, true, count, flag);
            }
        }
        // A recursive operator's body is evaluated per call, and reads the names bound outside
        // it from there (`Gen::rec_free`)
        RecCall(i, args) => {
            args.iter().for_each(|a| uses(a, n, under, count, flag));
            if rec_reads(*i, n, &mut std::collections::HashSet::new()) {
                *count += 2;
                *flag = true;
            }
        }
        e => e.children().into_iter().for_each(|c| uses(c, n, under, count, flag)),
    }
}

/// Whether the body of the recursive definition i, or of one it calls, reads the name n
fn rec_reads(i: usize, n: &str, seen: &mut std::collections::HashSet<usize>) -> bool {
    if !seen.insert(i) {
        return false;
    }
    let body = rec_def(i).body;
    body.any(&|e| matches!(e, Expr::Ident(m, _) if m == n)) || {
        let calls = std::cell::RefCell::new(vec![]);
        body.any(&|e| {
            if let Expr::RecCall(j, _) = e {
                calls.borrow_mut().push(*j);
            }
            false
        });
        calls.into_inner().into_iter().any(|j| rec_reads(j, n, seen))

    }
}

/// e with the identifier n replaced by x (names are unique after expansion, so nothing is

/// captured)
pub fn subst_ident(e: &Expr, n: &str, x: &Expr) -> Expr {
    match e {
        Expr::Ident(m, _) if m == n => x.clone(),
        // The value an EXCEPT changes, replaced by what it stands for: keep where it is written,
        // for TLC's warning (see EXCEPT_AT)
        Expr::Except(f, _) if matches!(f.as_ref(), Expr::Ident(m, at) if m == n && at.known()) && !matches!(x, Expr::Ident(..)) => {
            let Expr::Ident(_, at) = f.as_ref() else { unreachable!() };
            match crate::codegen::map_children(e, &|c| subst_ident(c, n, x)) {
                Expr::Except(f2, ups) => Expr::Except(except_at(&at.text(), *f2).b(), ups),
                e2 => e2,
            }
        }
        _ => crate::codegen::map_children(e, &|c| subst_ident(c, n, x)),
    }
}

/// Replaces @ in e (except inside the values of nested EXCEPTs) with the identifier name

fn replace_at(e: &Expr, name: &str) -> Expr {
    match e {
        Expr::At => Expr::Ident(name.to_string(), NOPOS),
        Expr::Except(f, ups) => Expr::Except(
            replace_at(f, name).b(),
            ups.iter()
                .map(|(path, v)| {
                    let path = path
                        .iter()
                        .map(|p| match p {
                            Path::Idx(i) => Path::Idx(replace_at(i, name)),
                            Path::Field(k) => Path::Field(k.clone()),
                        })
                        .collect();
                    (path, v.clone())
                })
                .collect(),
        ),
        _ => crate::codegen::map_children(e, &|c| replace_at(c, name)),
    }
}
