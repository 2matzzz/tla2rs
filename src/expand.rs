//! Inlines all operator definitions. Bound variables are renamed to avoid capture.
//! Call sites are kept as `Expr::Label` (for trace output and fairness matching).

use crate::ast::*;
use crate::lexer::R;
use std::collections::HashMap;

#[derive(Clone, Default)]
struct Env {
    subst: HashMap<String, Expr>,
    locals: HashMap<String, (Def, Env)>,
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

pub struct Expander<'a> {
    defs: HashMap<&'a str, &'a Def>,
    fresh: usize,
    depth: usize,
    recursive: Vec<String>,
    /// Definitions being expanded (by their unique name), innermost last
    stack: Vec<String>,
    /// Unique name of a recursive definition -> its index in REC_DEFS
    rec_ids: HashMap<String, usize>,
}

impl<'a> Expander<'a> {
    pub fn new(m: &'a Module) -> Self {
        REC_DEFS.with(|r| r.borrow_mut().clear());
        Expander {
            defs: m.defs.iter().map(|d| (d.name.as_str(), d)).collect(),
            fresh: 0,
            depth: 0,
            recursive: m.recursive.clone(),
            stack: vec![],
            rec_ids: HashMap::new(),
        }
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

    /// Expands a definition with parameters, renaming the formals to fresh names
    pub fn expand_params(&mut self, name: &str) -> R<(Vec<String>, Expr)> {
        let d = self.defs.get(name).copied().ok_or(format!("no definition named `{name}`"))?;
        let mut env = Env::default();
        let mut names = vec![];
        for p in &d.params {
            names.push(self.bind(p, &mut env));
        }
        let body = self.expand(&d.body, &env)?;
        Ok((names, Expr::Label(name.into(), vec![], body.b())))
    }

    pub fn expand_top(&mut self, e: &Expr) -> R<Expr> {
        self.expand(e, &Env::default())
    }

    fn bind(&mut self, x: &str, env: &mut Env) -> String {
        self.fresh += 1;
        let n = format!("{x}__{}", self.fresh);
        env.subst.insert(x.to_string(), Expr::Ident(n.clone()));
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
            if d.arity.iter().any(|&a| a > 0) {
                return Err(format!("`{name}`: recursive operators with operator parameters are not supported"));
            }
            let id = self.rec_id(name, d, &env)?;
            let args = raw.iter().map(|a| self.expand(a, caller)).collect::<R<_>>()?;
            return Ok(Expr::RecCall(id, args));
        }
        let mut args = vec![];
        for (i, (p, a)) in d.params.iter().zip(raw).enumerate() {
            let arity = d.arity.get(i).copied().unwrap_or(0);
            if arity > 0 {
                let op = self.op_arg(name, p, arity, a, caller)?;
                env.subst.remove(p);
                env.locals.insert(p.clone(), op);
                args.push(Expr::Ident(p.clone()));
            } else {
                if matches!(a, Expr::Lambda(..)) {
                    return Err(format!("`{name}`: LAMBDA passed for `{p}`, which is not an operator parameter"));
                }
                let a = self.expand(a, caller)?;
                env.subst.insert(p.clone(), a.clone());
                args.push(a);
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
        Ok(Expr::Label(name.into(), args, body?.b()))
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
    fn rec_id(&mut self, name: &str, d: &Def, env: &Env) -> R<usize> {
        if let Some(&i) = self.rec_ids.get(&d.name) {
            return Ok(i);
        }
        let i = REC_DEFS.with(|r| {
            let mut r = r.borrow_mut();
            r.push(RecDef { name: name.to_string(), params: vec![], body: Expr::Bool(true) });
            r.len() - 1
        });
        self.rec_ids.insert(d.name.clone(), i);
        let mut env = env.clone();
        let params: Vec<String> = d.params.iter().map(|p| self.bind(p, &mut env)).collect();
        self.stack.push(d.name.clone());
        let body = self.expand(&d.body, &env);
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
            Expr::Ident(g) => match caller.locals.get(g) {
                Some((d, e)) => (d.clone(), e.clone()),
                None => match self.defs.get(g.as_str()) {
                    Some(d) => ((*d).clone(), Env::default()),
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
            Ident(n) => {
                if let Some(v) = env.subst.get(n) {
                    v.clone()
                } else if let Some((d, denv)) = env.locals.get(n) {
                    let (d, denv) = (d.clone(), with_self(n, &d, denv.clone()));
                    self.call(n, &d, denv, &[], env)?
                } else if let Some(d) = self.defs.get(n.as_str()).copied() {
                    self.call(n, d, Env::default(), &[], env)?
                } else {
                    e.clone()
                }
            }
            Call(n, args) => {
                if let Some((d, denv)) = env.locals.get(n) {
                    let (d, denv) = (d.clone(), with_self(n, &d, denv.clone()));
                    self.call(n, &d, denv, args, env)?
                } else if let Some(d) = self.defs.get(n.as_str()).copied() {
                    self.call(n, d, Env::default(), args, env)?
                } else {
                    Call(n.clone(), args.iter().map(|a| ex(self, a)).collect::<R<_>>()?)
                }
            }
            Lambda(..) => return Err("LAMBDA is only supported as the argument of an operator parameter".into()),
            RecCall(i, args) => RecCall(*i, args.iter().map(|a| ex(self, a)).collect::<R<_>>()?),
            Prime(x) => Prime(ex(self, x)?.b()),
            Un(op, x) => Un(*op, ex(self, x)?.b()),
            Bin(op, a, b) => Bin(*op, ex(self, a)?.b(), ex(self, b)?.b()),
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
            App(f, x) if matches!(f.as_ref(), Ident(n) if self.rec_fun_app(n, env)) => {
                let Ident(n) = f.as_ref() else { unreachable!() };
                self.expand(&Call(format!("{n}#app"), vec![x.as_ref().clone()]), env)?
            }
            App(f, x) => App(ex(self, f)?.b(), ex(self, x)?.b()),
            Field(r, k) => Field(ex(self, r)?.b(), k.clone()),
            Except(f, ups) => {
                let f2 = ex(self, f)?;
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
                for d in defs {
                    let snapshot = inner.clone();
                    inner.subst.remove(&d.name);
                    // A unique name tells apart same-named LET definitions on the expansion stack
                    self.fresh += 1;
                    let unique = Def { name: format!("{}#let{}", d.name, self.fresh), ..d.clone() };
                    inner.locals.insert(d.name.clone(), (unique, snapshot));
                }
                self.expand(body, &inner)?
            }
            BoxAction(a, v) => BoxAction(ex(self, a)?.b(), ex(self, v)?.b()),
            Fair(w, v, a) => Fair(*w, ex(self, v)?.b(), ex(self, a)?.b()),
            Label(n, args, b) => Label(n.clone(), args.clone(), ex(self, b)?.b()),
        })
    }
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

/// Replaces @ in e (except inside the values of nested EXCEPTs) with the identifier name
fn replace_at(e: &Expr, name: &str) -> Expr {
    match e {
        Expr::At => Expr::Ident(name.to_string()),
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
