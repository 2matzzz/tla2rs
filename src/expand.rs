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

pub struct Expander<'a> {
    defs: HashMap<&'a str, &'a Def>,
    fresh: usize,
    depth: usize,
}

impl<'a> Expander<'a> {
    pub fn new(m: &'a Module) -> Self {
        Expander { defs: m.defs.iter().map(|d| (d.name.as_str(), d)).collect(), fresh: 0, depth: 0 }
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

    fn call(&mut self, name: &str, d: &Def, mut env: Env, args: Vec<Expr>) -> R<Expr> {
        if d.params.len() != args.len() {
            return Err(format!("`{name}` expects {} arguments, got {}", d.params.len(), args.len()));
        }
        for (p, a) in d.params.iter().zip(args.iter()) {
            env.subst.insert(p.clone(), a.clone());
        }
        self.depth += 1;
        if self.depth > 200 {
            return Err(format!("`{name}`: recursive operator definitions are not supported"));
        }
        let body = self.expand(&d.body, &env);
        self.depth -= 1;
        Ok(Expr::Label(name.into(), args, body?.b()))
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
                    let (d, denv) = (d.clone(), denv.clone());
                    self.call(n, &d, denv, vec![])?
                } else if let Some(d) = self.defs.get(n.as_str()).copied() {
                    self.call(n, d, Env::default(), vec![])?
                } else {
                    e.clone()
                }
            }
            Call(n, args) => {
                let args: Vec<Expr> = args.iter().map(|a| ex(self, a)).collect::<R<_>>()?;
                if let Some((d, denv)) = env.locals.get(n) {
                    let (d, denv) = (d.clone(), denv.clone());
                    self.call(n, &d, denv, args)?
                } else if let Some(d) = self.defs.get(n.as_str()).copied() {
                    self.call(n, d, Env::default(), args)?
                } else {
                    Call(n.clone(), args)
                }
            }
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
                    inner.locals.insert(d.name.clone(), (d.clone(), snapshot));
                }
                self.expand(body, &inner)?
            }
            BoxAction(a, v) => BoxAction(ex(self, a)?.b(), ex(self, v)?.b()),
            Fair(w, v, a) => Fair(*w, ex(self, v)?.b(), ex(self, a)?.b()),
            Label(n, args, b) => Label(n.clone(), args.clone(), ex(self, b)?.b()),
        })
    }
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
