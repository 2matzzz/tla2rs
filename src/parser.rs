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
    let mut p = Parser { toks: lex(src)?, pos: 0, limits: vec![] };
    p.module()
}

fn infix(t: &Tok) -> Option<(u8, bool, &'static str)> {
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
        "+" => (10, false, "+"),
        "-" => (10, false, "-"),
        "*" => (13, false, "*"),
        "\\div" => (13, false, "\\div"),
        // In TLA+, % is 10-11 (looser than * and \div, and looser than unary -)
        "%" => (11, false, "%"),
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
        _ => unreachable!(),
    };
    Expr::Bin(o, a.b(), b.b())
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
                    m.constants.extend(self.ident_list()?);
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
                Tok::Ident(_) => {
                    let d = self.def()?;
                    m.defs.push(d);
                }
                _ => return self.err("unexpected token at module level"),
            }
        }
        Ok(m)
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

    fn def(&mut self) -> R<Def> {
        let name = self.ident()?;
        let mut params = vec![];
        if self.is("(") {
            self.pos += 1;
            loop {
                params.push(self.ident()?);
                if self.is(",") {
                    self.pos += 1;
                } else {
                    break;
                }
            }
            self.expect(")")?;
        }
        if self.is("[") {
            return self.err("function definitions `f[x \\in S] == ...` are not supported yet");
        }
        self.expect("==")?;
        let body = self.expr(0)?;
        Ok(Def { name, params, body })
    }

    pub fn expr(&mut self, min: u8) -> R<Expr> {
        let mut lhs = self.prefix()?;
        loop {
            let Some((prec, right, op)) = infix(self.peek()) else { break };
            if prec < min {
                break;
            }
            self.pos += 1;
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
        let mut out = vec![];
        loop {
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
        Ok(out)
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
                let bs = self.binders()?;
                self.expect(":")?;
                let body = self.expr(0)?;
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
                        defs.push(self.def()?);
                    }
                    self.pos += 1;
                    let body = self.expr(0)?;
                    Ok(Expr::Let(defs, body.b()))
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
            let bs = self.binders()?;
            self.expect("}")?;
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
        let e = self.expr(0)?;
        if self.is_kw("EXCEPT") {
            self.pos += 1;
            let mut ups = vec![];
            loop {
                self.expect("!")?;
                let mut path = vec![];
                loop {
                    if self.is("[") {
                        self.pos += 1;
                        let i = self.expr(0)?;
                        self.expect("]")?;
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
            return self.err("unsupported function constructor (only [x \\in S |-> e])");
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
