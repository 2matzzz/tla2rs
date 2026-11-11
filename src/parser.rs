//! Parser for a subset of TLA+. Precedences follow the TLA+ table closely; `/\` and `\/` bullet
//! lists are delimited by column.

use crate::ast::*;
use crate::lexer::{lex, Tok, Token, R};

static EOF: Tok = Tok::Eof;

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// Bullet-list columns. An expression ends at a line-leading token at or left of this column;
    /// None means inside brackets.
    limits: Vec<Option<usize>>,
    /// Names declared RECURSIVE, and the operators recursive function definitions become
    recursive: Vec<String>,
    /// Count of `<<x, y>> \in S` bound variables, for fresh names
    tuple_binders: usize,
}

const KEYWORDS: &[&str] = &[
    "THEN", "ELSE", "OTHER", "IN", "EXCEPT", "LET", "IF", "CASE", "CHOOSE", "MODULE", "EXTENDS",
    "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES", "ASSUME", "THEOREM", "LOCAL",
];

/// Number of characters a token spans in the source (to report ASSUME positions the way TLC does)
fn tok_width(t: &Tok) -> usize {
    match t {
        Tok::Ident(s) | Tok::Sym(s) => s.chars().count(),
        Tok::Str(s) => s.chars().count() + 2,
        Tok::Num(n) => n.to_string().len(),
        _ => 1,
    }
}

pub fn parse_module(src: &str) -> R<Module> {
    let mut p = Parser { toks: lex(src)?, pos: 0, limits: vec![], recursive: vec![], tuple_binders: 0 };
    p.module()
}

/// Infix operators without a built-in meaning, which a spec may define (`a ++ b == ...`), with
/// their precedence (the lower end of the range in the TLA+ table). `:>` and `@@` are defined by
/// the TLC module.
const USER_INFIX: &[(&str, u8)] = &[
    ("@@", 6), (":>", 7), ("<:", 7), ("\\prec", 5), ("\\succ", 5), ("\\preceq", 5), ("\\succeq", 5),
    ("\\sim", 5), ("\\simeq", 5), ("\\approx", 5), ("\\cong", 5), ("\\asymp", 5), ("\\doteq", 5),
    ("\\propto", 5), ("\\sqsubseteq", 5), ("\\sqsupseteq", 5), ("\\uplus", 9), ("\\sqcap", 9),
    ("\\sqcup", 9), ("##", 9), ("$$", 9), ("\\wr", 9), ("\\oplus", 10), ("++", 10), ("%%", 10),
    ("\\ominus", 11), ("\\otimes", 13), ("\\oslash", 13), ("\\odot", 13), ("**", 13), ("//", 13),
    ("&&", 13), ("\\star", 13), ("\\bullet", 13), ("||", 13), ("^^", 14),
];

fn user_infix(t: &Tok) -> Option<(u8, &'static str)> {
    let Tok::Sym(s) = t else { return None };
    USER_INFIX.iter().find(|(n, _)| n == s).map(|(n, p)| (*p, *n))
}

fn infix(t: &Tok) -> Option<(u8, bool, &'static str)> {
    if let Some((p, n)) = user_infix(t) {
        return Some((p, false, n));
    }
    let Tok::Sym(s) = t else { return None };
    // (precedence, right-associative, normalized name)
    Some(match s.as_str() {
        "=>" => (1, true, "=>"),
        "<=>" => (2, false, "<=>"),
        "~>" => (2, false, "~>"),
        "\\/" => (3, false, "\\/"),
        "/\\" => (3, false, "/\\"),
        "=" => (5, false, "="),
        "#" | "/=" => (5, false, "#"),
        "<" => (5, false, "<"),
        ">" => (5, false, ">"),
        "<=" | "=<" => (5, false, "<="),
        ">=" => (5, false, ">="),
        "\\in" => (5, false, "\\in"),
        "\\notin" => (5, false, "\\notin"),
        "\\subseteq" => (5, false, "\\subseteq"),
        "\\cup" => (8, false, "\\cup"),
        "\\cap" => (8, false, "\\cap"),
        "\\" => (8, false, "\\"),
        ".." => (9, false, ".."),
        // Cartesian product (10-13 in TLA+). `A \X B \X C` is one 3-ary product; see `expr`
        "\\X" => (10, false, "\\X"),
        "+" => (10, false, "+"),
        "-" => (10, false, "-"),
        "*" => (13, false, "*"),
        // Sequence concatenation, parsed only to reject it with a clear message
        "\\o" | "\\circ" => (13, false, "\\o"),
        "\\div" => (13, false, "\\div"),
        // In TLA+, % is 10-11 (looser than * and \div, and looser than unary -)
        "%" => (11, false, "%"),
        "^" => (14, true, "^"),
        _ => return None,
    })
}

fn bin(op: &str, a: Expr, b: Expr) -> Expr {
    let o = match op {
        "=>" => BOp::Implies,
        "<=>" => BOp::Equiv,
        "~>" => BOp::LeadsTo,
        "\\/" => {
            return match a {
                Expr::Or(mut v) => {
                    v.push(b);
                    Expr::Or(v)
                }
                a => Expr::Or(vec![a, b]),
            }
        }
        "/\\" => {
            return match a {
                Expr::And(mut v) => {
                    v.push(b);
                    Expr::And(v)
                }
                a => Expr::And(vec![a, b]),
            }
        }
        "=" => BOp::Eq,
        "#" => BOp::Neq,
        "<" => BOp::Lt,
        ">" => BOp::Gt,
        "<=" => BOp::Le,
        ">=" => BOp::Ge,
        "\\in" => BOp::In,
        "\\notin" => BOp::NotIn,
        "\\subseteq" => BOp::Subseteq,
        "\\cup" => BOp::Cup,
        "\\cap" => BOp::Cap,
        "\\" => BOp::SetMinus,
        ".." => BOp::Range,
        "+" => BOp::Add,
        "-" => BOp::Sub,
        "*" => BOp::Mul,
        "\\div" => BOp::Div,
        "%" => BOp::Mod,
        "\\o" => return Expr::Call("\\o".into(), vec![a, b]),
        "^" => return Expr::Call("^".into(), vec![a, b]),
        o if USER_INFIX.iter().any(|(n, _)| *n == o) => return Expr::Call(o.into(), vec![a, b]),
        _ => unreachable!(),
    };
    Expr::Bin(o, a.b(), b.b())
}

/// e with every application `f[a]` replaced by the call `app(a)`
fn calls_for_apps(e: &Expr, f: &str, app: &str) -> Expr {
    match e {
        Expr::App(g, a) if matches!(g.as_ref(), Expr::Ident(n) if n == f) => {
            Expr::Call(app.to_string(), vec![calls_for_apps(a, f, app)])
        }
        _ => crate::codegen::map_children(e, &|c| calls_for_apps(c, f, app)),
    }
}

/// `[x \in S |-> e]`, and for several bound variables `[x \in S, y \in T |-> e]`, a function on
/// tuples: `[t \in S \X T |-> LET x == t[1] y == t[2] IN e]`
fn fun_cons(bs: Vec<(String, Expr)>, body: Expr) -> Expr {
    if bs.len() == 1 {
        let (x, s) = bs.into_iter().next().unwrap();
        return Expr::FunCons(x, s.b(), body.b());
    }
    // `#` cannot start a TLA+ identifier, so this name cannot capture one of the spec's
    let t = "#args".to_string();
    let defs = bs
        .iter()
        .enumerate()
        .map(|(i, (x, _))| Def {
            name: x.clone(),
            params: vec![],
            arity: vec![],
            body: Expr::App(Expr::Ident(t.clone()).b(), Expr::Num(i as i64 + 1).b()),
        })
        .collect();
    let dom = Expr::Call("\\X".into(), bs.into_iter().map(|(_, s)| s).collect());
    Expr::FunCons(t, dom.b(), Expr::Let(defs, body.b()).b())
}

impl Parser {
    fn raw(&self) -> &Token {
        &self.toks[self.pos]
    }
    fn hidden(&self, t: &Token) -> bool {
        matches!(self.limits.last(), Some(Some(l)) if t.first && t.col <= *l)
    }
    fn peek(&self) -> &Tok {
        let t = self.raw();
        if self.hidden(t) {
            &EOF
        } else {
            &t.tok
        }
    }
    fn peek2(&self) -> &Tok {
        &self.toks[(self.pos + 1).min(self.toks.len() - 1)].tok
    }
    fn is(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Sym(x) if x == s)
    }
    fn is_kw(&self, s: &str) -> bool {
        matches!(self.peek(), Tok::Ident(x) if x == s)
    }
    fn err<T>(&self, msg: &str) -> R<T> {
        let t = self.raw();
        Err(format!("line {}:{}: {msg} (at {:?})", t.line, t.col + 1, t.tok))
    }
    fn expect(&mut self, s: &str) -> R<()> {
        if self.is(s) {
            self.pos += 1;
            Ok(())
        } else {
            self.err(&format!("expected `{s}`"))
        }
    }
    fn expect_kw(&mut self, s: &str) -> R<()> {
        if self.is_kw(s) {
            self.pos += 1;
            Ok(())
        } else {
            self.err(&format!("expected `{s}`"))
        }
    }
    fn ident(&mut self) -> R<String> {
        match self.peek().clone() {
            Tok::Ident(s) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("expected identifier"),
        }
    }
    fn nested<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.limits.push(None);
        let r = f(self);
        self.limits.pop();
        r
    }

    fn module(&mut self) -> R<Module> {
        let mut m = Module::default();
        while !matches!(self.raw().tok, Tok::Ident(ref s) if s == "MODULE") {
            if self.raw().tok == Tok::Eof {
                return self.err("no MODULE header");
            }
            self.pos += 1;
        }
        self.pos += 1;
        m.name = self.ident()?;
        loop {
            match self.raw().tok.clone() {
                Tok::Eof => break,
                Tok::Sym(s) if s == "====" => break,
                Tok::Sym(s) if s == "----" => self.pos += 1,
                Tok::Ident(k) if k == "EXTENDS" => {
                    self.pos += 1;
                    m.extends = self.ident_list()?;
                }
                Tok::Ident(k) if k == "CONSTANT" || k == "CONSTANTS" => {
                    self.pos += 1;
                    for (c, n) in self.ident_list_arity()? {
                        if n > 0 {
                            m.op_constants.push((c.clone(), n));
                        }
                        m.constants.push(c);
                    }
                }
                Tok::Ident(k) if k == "VARIABLE" || k == "VARIABLES" => {
                    self.pos += 1;
                    m.variables.extend(self.ident_list()?);
                }
                // TLC checks ASSUME and ASSUMPTION, and skips THEOREM and AXIOM
                Tok::Ident(k) if k == "ASSUME" || k == "ASSUMPTION" => {
                    self.pos += 1;
                    let start = self.pos;
                    let expr = self.expr(0)?;
                    let (a, b) = (&self.toks[start], &self.toks[self.pos - 1]);
                    let span = (a.line, a.col + 1, b.line, b.col + tok_width(&b.tok));
                    m.assumes.push(Assume { module: m.name.clone(), expr, span });
                }
                Tok::Ident(k) if k == "THEOREM" || k == "AXIOM" => {
                    self.pos += 1;
                    self.expr(0)?;
                }
                Tok::Ident(k) if k == "LOCAL" => self.pos += 1,
                Tok::Ident(k) if k == "RECURSIVE" => {
                    self.pos += 1;
                    for (n, _) in self.ident_list_arity()? {
                        self.recursive.push(n);
                    }
                }
                Tok::Ident(_) => {
                    let d = self.def()?;
                    m.defs.extend(d);
                }
                _ => return self.err("unexpected token at module level"),
            }
        }
        m.recursive = std::mem::take(&mut self.recursive);
        Ok(m)
    }

    /// Names with optional parameter lists `F(_, _)`, and the number of parameters of each
    fn ident_list_arity(&mut self) -> R<Vec<(String, usize)>> {
        let mut v = vec![];
        loop {
            let name = self.ident()?;
            let mut n = 0;
            if self.is("(") {
                self.pos += 1;
                loop {
                    match self.peek() {
                        Tok::Ident(u) if u == "_" => self.pos += 1,
                        _ => return self.err("expected `_` in the parameters of a CONSTANT"),
                    }
                    n += 1;
                    if self.is(",") {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                self.expect(")")?;
            }
            v.push((name, n));
            if self.is(",") {
                self.pos += 1;
            } else {
                return Ok(v);
            }
        }
    }

    fn ident_list(&mut self) -> R<Vec<String>> {
        let mut v = vec![self.ident()?];
        // For CONSTANT F(_, _), skip the parameter list
        if self.is("(") {
            while !self.is(")") {
                self.pos += 1;
            }
            self.pos += 1;
        }
        while self.is(",") {
            self.pos += 1;
            v.push(self.ident()?);
            if self.is("(") {
                while !self.is(")") {
                    self.pos += 1;
                }
                self.pos += 1;
            }
        }
        Ok(v)
    }

    fn def(&mut self) -> R<Vec<Def>> {
        let name = self.ident()?;
        // An infix operator definition `a ++ b == e`
        if let Some((_, op)) = user_infix(self.peek()) {
            self.pos += 1;
            let b = self.ident()?;
            self.expect("==")?;
            let body = self.expr(0)?;
            return Ok(vec![Def { name: op.to_string(), params: vec![name, b], arity: vec![0, 0], body }]);
        }
        let mut params = vec![];
        let mut arity = vec![];
        if self.is("(") {
            self.pos += 1;
            loop {
                params.push(self.ident()?);
                // An operator parameter F(_, _)
                let mut n = 0;
                if self.is("(") {
                    self.pos += 1;
                    loop {
                        match self.peek() {
                            Tok::Ident(u) if u == "_" => self.pos += 1,
                            _ => return self.err("expected `_` in an operator parameter"),
                        }
                        n += 1;
                        if self.is(",") {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                    self.expect(")")?;
                }
                arity.push(n);
                if self.is(",") {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            self.expect(")")?;
        }
        if self.is("[") && params.is_empty() {
            // f[x \in S] == e is f == [x \in S |-> e]
            let at = self.pos;
            self.pos += 1;
            let bs = self.nested(|p| p.binders())?;
            self.expect("]")?;
            self.expect("==")?;
            let body = self.expr(0)?;
            let _ = at;
            if body.any(&|e| matches!(e, Expr::Ident(n) | Expr::Call(n, _) if *n == name)) {
                return Ok(self.rec_fun(name, bs, body));
            }
            return Ok(vec![Def { name, params, arity, body: fun_cons(bs, body) }]);
        }
        self.expect("==")?;
        let body = self.expr(0)?;
        Ok(vec![Def { name, params, arity, body }])
    }

    /// A recursive function definition `f[x \in S] == e` becomes the recursive operator
    /// `f#app(x) == IF x \in S THEN e ELSE <error>`, with each `f[a]` in e a call `f#app(a)`, and
    /// `f == [x \in S |-> f#app(x)]` for the function as a whole
    fn rec_fun(&mut self, name: String, bs: Vec<(String, Expr)>, body: Expr) -> Vec<Def> {
        let app = format!("{name}#app");
        self.recursive.push(app.clone());
        let body = calls_for_apps(&body, &name, &app);
        let (x, dom, inner) = if bs.len() == 1 {
            let (x, s) = bs.into_iter().next().unwrap();
            (x, s, body)
        } else {
            match fun_cons(bs, body) {
                Expr::FunCons(t, d, b) => (t, *d, *b),
                _ => unreachable!(),
            }
        };
        // Applying f outside its domain is an error, as in TLC (CHOOSE from the empty set fails)
        let outside = Expr::Choose("#none".into(), Expr::SetLit(vec![]).b(), Expr::Bool(true).b());
        let guarded = Expr::If(Expr::Bin(BOp::In, Expr::Ident(x.clone()).b(), dom.clone().b()).b(), inner.b(), outside.b());
        let whole = Expr::FunCons(x.clone(), dom.b(), Expr::Call(app.clone(), vec![Expr::Ident(x.clone())]).b());
        vec![
            Def { name: app, params: vec![x], arity: vec![0], body: guarded },
            Def { name, params: vec![], arity: vec![], body: whole },
        ]
    }

    pub fn expr(&mut self, min: u8) -> R<Expr> {
        let mut lhs = self.prefix()?;
        loop {
            let Some((prec, right, op)) = infix(self.peek()) else { break };
            if prec < min {
                break;
            }
            self.pos += 1;
            if op == "\\X" {
                // A \X B \X C is the set of triples, not of pairs whose first element is a pair
                let mut parts = vec![lhs, self.expr(prec + 1)?];
                while self.is("\\X") {
                    self.pos += 1;
                    parts.push(self.expr(prec + 1)?);
                }
                lhs = Expr::Call("\\X".into(), parts);
                continue;
            }
            let rhs = self.expr(if right { prec } else { prec + 1 })?;
            lhs = bin(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn bullets(&mut self, sym: &str) -> R<Expr> {
        let col = self.raw().col;
        let mut items = vec![];
        loop {
            self.pos += 1; // the bullet symbol
            self.limits.push(Some(col));
            let e = self.expr(0);
            self.limits.pop();
            items.push(e?);
            let t = self.raw();
            let same = matches!(&t.tok, Tok::Sym(s) if s == sym) && t.col == col && !self.hidden(t);
            if !same {
                break;
            }
        }
        Ok(if items.len() == 1 {
            items.pop().unwrap()
        } else if sym == "/\\" {
            Expr::And(items)
        } else {
            Expr::Or(items)
        })
    }

    fn binders(&mut self) -> R<Vec<(String, Expr)>> {
        let (bs, lets) = self.binders_pat()?;
        if !lets.is_empty() {
            return self.err("a tuple of bound variables `<<x, y>> \\in S` is only supported after \\E, \\A, and in {e : ...}");
        }
        Ok(bs)
    }

    /// Bound variables `x, y \in S, <<a, b>> \in T`. A tuple of variables binds a fresh variable t
    /// and returns the definitions `a == t[1]`, `b == t[2]` to wrap the body in.
    fn binders_pat(&mut self) -> R<(Vec<(String, Expr)>, Vec<Def>)> {
        let mut out = vec![];
        let mut lets = vec![];
        loop {
            if self.is("<<") {
                self.pos += 1;
                let mut names = vec![self.ident()?];
                while self.is(",") {
                    self.pos += 1;
                    names.push(self.ident()?);
                }
                self.expect(">>")?;
                self.expect("\\in")?;
                let s = self.expr(4)?;
                self.tuple_binders += 1;
                let t = format!("#tup{}", self.tuple_binders);
                for (i, n) in names.into_iter().enumerate() {
                    let body = Expr::App(Expr::Ident(t.clone()).b(), Expr::Num(i as i64 + 1).b());
                    lets.push(Def { name: n, params: vec![], arity: vec![], body });
                }
                out.push((t, s));
                if self.is(",") {
                    self.pos += 1;
                    continue;
                }
                break;
            }
            let mut names = vec![self.ident()?];
            while self.is(",") {
                self.pos += 1;
                names.push(self.ident()?);
            }
            self.expect("\\in")?;
            let s = self.expr(4)?; // stops at `,` and `:`; only binds tighter than \in
            for n in names {
                out.push((n, s.clone()));
            }
            if self.is(",") {
                self.pos += 1;
            } else {
                break;
            }
        }
        Ok((out, lets))
    }

    fn prefix(&mut self) -> R<Expr> {
        let t = self.peek().clone();
        match &t {
            Tok::Sym(s) if s == "/\\" || s == "\\/" => self.bullets(&s.clone()),
            Tok::Sym(s) if s == "~" => {
                self.pos += 1;
                Ok(Expr::Un(UOp::Not, self.expr(4)?.b()))
            }
            Tok::Sym(s) if s == "-" => {
                self.pos += 1;
                Ok(Expr::Un(UOp::Neg, self.expr(12)?.b()))
            }
            Tok::Sym(s) if s == "[]" => {
                self.pos += 1;
                Ok(Expr::Un(UOp::Always, self.expr(4)?.b()))
            }
            Tok::Sym(s) if s == "<>" => {
                self.pos += 1;
                Ok(Expr::Un(UOp::Eventually, self.expr(4)?.b()))
            }
            Tok::Sym(s) if s == "\\E" || s == "\\A" => {
                let ex = s == "\\E";
                self.pos += 1;
                let (bs, lets) = self.binders_pat()?;
                self.expect(":")?;
                let body = self.expr(0)?;
                let body = if lets.is_empty() { body } else { Expr::Let(lets, body.b()) };
                Ok(Expr::Quant(ex, bs, body.b()))
            }
            Tok::Ident(k) => match k.as_str() {
                "SUBSET" | "UNION" | "DOMAIN" => {
                    self.pos += 1;
                    let op = match k.as_str() {
                        "SUBSET" => UOp::Subset,
                        "UNION" => UOp::Union,
                        _ => UOp::Domain,
                    };
                    Ok(Expr::Un(op, self.expr(9)?.b()))
                }
                "UNCHANGED" | "ENABLED" => {
                    self.pos += 1;
                    let op = if k == "UNCHANGED" { UOp::Unchanged } else { UOp::Enabled };
                    Ok(Expr::Un(op, self.expr(15)?.b()))
                }
                "IF" => {
                    self.pos += 1;
                    let c = self.expr(0)?;
                    self.expect_kw("THEN")?;
                    let a = self.expr(0)?;
                    self.expect_kw("ELSE")?;
                    let b = self.expr(0)?;
                    Ok(Expr::If(c.b(), a.b(), b.b()))
                }
                "CASE" => {
                    self.pos += 1;
                    let mut arms = vec![];
                    let mut other = None;
                    loop {
                        if self.is_kw("OTHER") {
                            self.pos += 1;
                            self.expect("->")?;
                            other = Some(self.expr(0)?.b());
                            break;
                        }
                        let p = self.expr(0)?;
                        self.expect("->")?;
                        let e = self.expr(0)?;
                        arms.push((p, e));
                        if self.is("[]") {
                            self.pos += 1;
                        } else {
                            break;
                        }
                    }
                    Ok(Expr::Case(arms, other))
                }
                "LET" => {
                    self.pos += 1;
                    let mut defs = vec![];
                    while !self.is_kw("IN") {
                        if self.is_kw("RECURSIVE") {
                            self.pos += 1;
                            for (n, _) in self.ident_list_arity()? {
                                self.recursive.push(n);
                            }
                            continue;
                        }
                        defs.extend(self.def()?);
                    }
                    self.pos += 1;
                    let body = self.expr(0)?;
                    Ok(Expr::Let(defs, body.b()))
                }
                "LAMBDA" => {
                    self.pos += 1;
                    let mut ps = vec![self.ident()?];
                    while self.is(",") {
                        self.pos += 1;
                        ps.push(self.ident()?);
                    }
                    self.expect(":")?;
                    let body = self.expr(0)?;
                    Ok(Expr::Lambda(ps, body.b()))
                }
                "CHOOSE" => {
                    self.pos += 1;
                    let x = self.ident()?;
                    self.expect("\\in")?;
                    let s = self.expr(4)?;
                    self.expect(":")?;
                    let p = self.expr(0)?;
                    Ok(Expr::Choose(x, s.b(), p.b()))
                }
                _ => self.postfix(),
            },
            _ => self.postfix(),
        }
    }

    fn postfix(&mut self) -> R<Expr> {
        let mut e = self.primary()?;
        loop {
            if self.is("'") {
                self.pos += 1;
                e = Expr::Prime(e.b());
            } else if self.is("[") {
                self.pos += 1;
                let args = self.nested(|p| p.comma_list("]"))?;
                let arg = if args.len() == 1 { args.into_iter().next().unwrap() } else { Expr::Tuple(args) };
                e = Expr::App(e.b(), arg.b());
            } else if self.is(".") {
                self.pos += 1;
                let f = self.ident()?;
                e = Expr::Field(e.b(), f);
            } else {
                break;
            }
        }
        Ok(e)
    }

    /// Comma-separated items up to and including `close`.
    fn comma_list(&mut self, close: &str) -> R<Vec<Expr>> {
        let mut v = vec![];
        if self.is(close) {
            self.pos += 1;
            return Ok(v);
        }
        loop {
            v.push(self.expr(0)?);
            if self.is(",") {
                self.pos += 1;
            } else {
                self.expect(close)?;
                return Ok(v);
            }
        }
    }

    fn primary(&mut self) -> R<Expr> {
        let t = self.peek().clone();
        match t {
            Tok::Num(n) => {
                self.pos += 1;
                Ok(Expr::Num(n))
            }
            Tok::Str(s) => {
                self.pos += 1;
                Ok(Expr::Str(s))
            }
            Tok::Ident(s) => {
                if KEYWORDS.contains(&s.as_str()) {
                    return self.err("unexpected keyword");
                }
                self.pos += 1;
                if s == "TRUE" || s == "FALSE" {
                    return Ok(Expr::Bool(s == "TRUE"));
                }
                if (s == "WF_" || s == "SF_") && self.is("<<") {
                    // WF_<<x, y>>(A)
                    let sub = self.primary()?;
                    self.expect("(")?;
                    let a = self.nested(|p| p.expr(0))?;
                    self.expect(")")?;
                    return Ok(Expr::Fair(s == "WF_", sub.b(), a.b()));
                }
                if (s.starts_with("WF_") || s.starts_with("SF_")) && self.is("(") {
                    self.pos += 1;
                    let a = self.nested(|p| p.expr(0))?;
                    self.expect(")")?;
                    return Ok(Expr::Fair(s.starts_with("WF_"), Expr::Ident(s[3..].into()).b(), a.b()));
                }
                if self.is("(") {
                    self.pos += 1;
                    let args = self.nested(|p| p.comma_list(")"))?;
                    return Ok(Expr::Call(s, args));
                }
                Ok(Expr::Ident(s))
            }
            Tok::Sym(s) => match s.as_str() {
                "(" => {
                    self.pos += 1;
                    let e = self.nested(|p| p.expr(0))?;
                    self.expect(")")?;
                    Ok(e)
                }
                "<<" => {
                    self.pos += 1;
                    let v = self.nested(|p| p.comma_list(">>"))?;
                    Ok(Expr::Tuple(v))
                }
                "{" => {
                    self.pos += 1;
                    self.nested(|p| p.braces())
                }
                "[" => {
                    self.pos += 1;
                    self.nested(|p| p.brackets())
                }
                "@" => {
                    self.pos += 1;
                    Ok(Expr::At)
                }
                _ => self.err("unexpected symbol"),
            },
            Tok::Eof => self.err("unexpected end of expression"),
        }
    }

    fn braces(&mut self) -> R<Expr> {
        if self.is("}") {
            self.pos += 1;
            return Ok(Expr::SetLit(vec![]));
        }
        // {x \in S : P} only when it starts with `identifier \in`; a parenthesized (y \in T) is a
        // map expression
        let filter_shape = matches!(self.peek(), Tok::Ident(_)) && matches!(self.peek2(), Tok::Sym(s) if s == "\\in");
        let first = self.expr(0)?;
        if self.is(":") {
            self.pos += 1;
            if let (true, Expr::Bin(BOp::In, x, s)) = (filter_shape, &first) {
                if let Expr::Ident(x) = x.as_ref() {
                    let p = self.expr(0)?;
                    self.expect("}")?;
                    return Ok(Expr::SetFilter(x.clone(), s.clone(), p.b()));
                }
            }
            let (bs, lets) = self.binders_pat()?;
            self.expect("}")?;
            let first = if lets.is_empty() { first } else { Expr::Let(lets, first.b()) };
            return Ok(Expr::SetMap(first.b(), bs));
        }
        let mut v = vec![first];
        while self.is(",") {
            self.pos += 1;
            v.push(self.expr(0)?);
        }
        self.expect("}")?;
        Ok(Expr::SetLit(v))
    }

    fn brackets(&mut self) -> R<Expr> {
        // [a |-> e, ...] and [a : S, ...]
        if let Tok::Ident(_) = self.peek() {
            let sep = match self.peek2() {
                Tok::Sym(s) if s == "|->" => Some(true),
                Tok::Sym(s) if s == ":" => Some(false),
                _ => None,
            };
            if let Some(lit) = sep {
                let mut fs = vec![];
                loop {
                    let f = self.ident()?;
                    self.pos += 1;
                    fs.push((f, self.expr(0)?));
                    if self.is(",") {
                        self.pos += 1;
                    } else {
                        break;
                    }
                }
                self.expect("]")?;
                return Ok(if lit { Expr::RecLit(fs) } else { Expr::RecSet(fs) });
            }
        }
        let start = self.pos;
        let e = self.expr(0)?;
        if self.is(",") && matches!(&e, Expr::Ident(_) | Expr::Bin(BOp::In, ..)) {
            // [x \in S, y \in T |-> e] or [x, y \in S |-> e]
            self.pos = start;
            let bs = self.binders()?;
            self.expect("|->")?;
            let body = self.expr(0)?;
            self.expect("]")?;
            return Ok(fun_cons(bs, body));
        }
        if self.is_kw("EXCEPT") {
            self.pos += 1;
            let mut ups = vec![];
            loop {
                self.expect("!")?;
                let mut path = vec![];
                loop {
                    if self.is("[") {
                        self.pos += 1;
                        // ![a, b] is ![<<a, b>>]
                        let mut ix = self.comma_list("]")?;
                        let i = if ix.len() == 1 { ix.pop().unwrap() } else { Expr::Tuple(ix) };
                        path.push(Path::Idx(i));
                    } else if self.is(".") {
                        self.pos += 1;
                        path.push(Path::Field(self.ident()?));
                    } else {
                        break;
                    }
                }
                self.expect("=")?;
                ups.push((path, self.expr(0)?));
                if self.is(",") {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            self.expect("]")?;
            return Ok(Expr::Except(e.b(), ups));
        }
        if self.is("->") {
            self.pos += 1;
            let r = self.expr(0)?;
            self.expect("]")?;
            return Ok(Expr::FunSet(e.b(), r.b()));
        }
        if self.is("|->") {
            if let Expr::Bin(BOp::In, x, s) = &e {
                if let Expr::Ident(x) = x.as_ref() {
                    self.pos += 1;
                    let body = self.expr(0)?;
                    self.expect("]")?;
                    return Ok(Expr::FunCons(x.clone(), s.clone(), body.b()));
                }
            }
            return self.err("unsupported function constructor");
        }
        self.expect("]")?;
        // [A]_v
        if let Tok::Ident(sub) = &self.raw().tok {
            if let Some(v) = sub.strip_prefix('_') {
                let v = v.to_string();
                self.pos += 1;
                let sub = if v.is_empty() { self.primary()? } else { Expr::Ident(v) };
                return Ok(Expr::BoxAction(e.b(), sub.b()));
            }
        }
        self.err("unsupported bracket expression")
    }
}
