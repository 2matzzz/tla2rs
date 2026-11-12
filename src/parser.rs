//! Parser for a subset of TLA+. Precedences follow the TLA+ table closely; `/\` and `\/` bullet
//! lists are delimited by column.

use crate::ast::*;
use crate::lexer::{lex_module, Tok, Token, R, SANY};

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
    /// Instances defined inside LET, made module-level (see `let_instance`)
    let_instances: Vec<Instance>,
    /// The name of the module being parsed (for POS labels)
    module: String,
    /// A prefix operator (`[]`, `<>`, ENABLED, UNCHANGED) whose operand is being parsed: SANY
    /// refuses a postfix operator on that operand (`[]x'`)
    postfix_guard: Option<&'static str>,
}

const KEYWORDS: &[&str] = &[
    "THEN", "ELSE", "OTHER", "IN", "EXCEPT", "LET", "IF", "CASE", "CHOOSE", "MODULE", "EXTENDS",
    "CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES", "ASSUME", "THEOREM", "LOCAL", "INSTANCE", "WITH",
];

/// Module-level statements that TLC parses and does not evaluate: theorems and the like, with their
/// proofs, and USE / HIDE
const PROOF_UNITS: &[&str] = &["THEOREM", "LEMMA", "PROPOSITION", "COROLLARY", "AXIOM", "USE", "HIDE"];

/// Tokens that can start a line of a proof at the left margin
const PROOF_LINE_STARTS: &[&str] = &["PROOF", "BY", "OBVIOUS", "OMITTED", "QED", "USE", "HIDE", "DEF", "DEFS"];

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
    let toks = lex_module(src)?;
    // Positional subexpression names (`Op!1`, `Op!<<`, `Op!(e)`) need infix /\ and \/ as SANY
    // reads them: binary and left-associative. Only then are they kept so (see INFIX_JUNCTION)
    let positional = toks.windows(2).any(|w| matches!(&w[0].tok, Tok::Sym(b) if b == "!") && is_selector(&w[1].tok));
    NEST_JUNCTIONS.with(|n| n.set(positional));
    let mut p = Parser { toks, pos: 0, limits: vec![], recursive: vec![], tuple_binders: 0, let_instances: vec![], module: String::new(), postfix_guard: None };
    let r = p.module();
    NEST_JUNCTIONS.with(|n| n.set(false));
    r
}

/// Whether a token after `!` starts a positional subexpression selector
fn is_selector(t: &Tok) -> bool {
    matches!(t, Tok::Num(_)) || matches!(t, Tok::Sym(c) if ["<<", ">>", ":", "(", "@"].contains(&c.as_str()))
}

thread_local! {
    static NEST_JUNCTIONS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The label around `a /\ b` (and `a \/ b`) written infix, in a module that names
/// subexpressions by position: the conjunction of the two, which expansion flattens as the parser
/// otherwise does (`a /\ b /\ c` is one conjunction of three)
pub const INFIX_JUNCTION: &str = "#infix";

/// The call a positional subexpression name becomes: the operator (Ident or Call) and then the
/// selectors: Num(n) for `!n`, Ident("<<" / ">>" / ":" / "@"), Tuple(args) for `!(args)`, and a
/// call of `#label<name>` for a label
pub const SUBEXPR: &str = "#subexpr";

/// Infix operators without a built-in meaning, which a spec may define (`a ++ b == ...`), with
/// their precedence (the lower end of the range in the TLA+ table). `:>` and `@@` are defined by
/// the TLC module.
const USER_INFIX: &[(&str, u8)] = &[
    ("@@", 6), (":>", 7), ("<:", 7), ("\\prec", 5), ("\\succ", 5), ("\\preceq", 5), ("\\succeq", 5),
    ("\\sim", 5), ("\\simeq", 5), ("\\approx", 5), ("\\cong", 5), ("\\asymp", 5), ("\\doteq", 5),
    ("\\propto", 5), ("\\sqsubseteq", 5), ("\\sqsupseteq", 5), ("\\uplus", 9), ("\\sqcap", 9),
    ("\\sqcup", 9), ("##", 9), ("$$", 9), ("\\wr", 9), ("\\oplus", 10), ("++", 10), ("%%", 10),
    ("\\ominus", 11), ("\\otimes", 13), ("\\oslash", 13), ("\\odot", 13), ("**", 13), ("//", 13),
    ("&&", 13), ("\\star", 13), ("\\bullet", 13), ("||", 13), ("^^", 14), ("--", 11), ("|-", 5),
    ("!!", 9), ("??", 9), ("\\bigcirc", 13), ("&", 13),
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
        "-+->" => (2, false, "-+->"),
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

/// The precedence range of an infix operator in the TLA+ table (by its normalized name) and
/// whether it associates to the left. SANY refuses two operators whose ranges overlap next to each
/// other without parentheses, unless they are the same operator and it associates.
fn sany_range(op: &str) -> Option<(u8, u8, bool)> {
    Some(match op {
        "=>" => (1, 1, false),
        "<=>" | "~>" | "-+->" => (2, 2, false),
        "\\/" | "/\\" => (3, 3, true),
        "=" | "#" | "<" | ">" | "<=" | ">=" | "\\in" | "\\notin" | "\\subseteq" | "|-" => (5, 5, false),
        "\\prec" | "\\succ" | "\\preceq" | "\\succeq" | "\\sim" | "\\simeq" | "\\approx" | "\\cong" | "\\asymp" => (5, 5, false),
        "\\doteq" | "\\propto" | "\\sqsubseteq" | "\\sqsupseteq" => (5, 5, false),
        "@@" => (6, 6, true),
        ":>" | "<:" => (7, 7, false),
        "\\cup" | "\\cap" => (8, 8, true),
        "\\" => (8, 8, false),
        ".." => (9, 9, false),
        "!!" => (9, 13, false),
        "??" | "##" | "$$" | "\\uplus" | "\\sqcap" | "\\sqcup" => (9, 13, true),
        "\\wr" => (9, 14, false),
        "\\X" => (10, 13, true),
        "+" | "++" | "\\oplus" => (10, 10, true),
        "%" => (10, 11, false),
        "%%" | "||" => (10, 11, true),
        "-" | "--" | "\\ominus" => (11, 11, true),
        "*" | "**" | "\\o" | "&&" | "&" | "\\otimes" | "\\odot" | "\\star" | "\\bullet" | "\\bigcirc" => (13, 13, true),
        "\\div" | "//" | "\\oslash" => (13, 13, false),
        "^" | "^^" => (14, 14, false),
        // Prefix operators, as SANY treats them (measured on SANY 2.19): unary minus, and the
        // temporal ones, ENABLED and UNCHANGED, as in the TLA+ table; SUBSET, UNION and DOMAIN
        // as if their range were 10-13 (`SUBSET a + b` is refused, `SUBSET 1..2` is
        // `(SUBSET 1)..2`, `SUBSET a \cup b` is `(SUBSET a) \cup b`)
        "-." => (12, 12, false),
        "[]" | "<>" | "ENABLED" | "UNCHANGED" => (4, 15, false),
        "SUBSET" | "UNION" | "DOMAIN" => (10, 13, false),
        _ => return None,
    })
}

/// Whether SANY refuses `a op1 b op2 c` without parentheses (see `sany_range`)
fn precedence_conflict(op1: &str, op2: &str) -> bool {
    match (sany_range(op1), sany_range(op2)) {
        (Some((l1, h1, assoc)), Some((l2, h2, _))) => l1 <= h2 && l2 <= h1 && !(op1 == op2 && assoc),
        _ => false,
    }
}

/// Whether `name` is an infix operator the parser knows (by its normalized name)
pub fn is_infix_name(name: &str) -> bool {
    infix(&Tok::Sym(name.to_string())).is_some_and(|(_, _, n)| n == name)
}

/// The name of the call an unbounded quantifier or CHOOSE becomes, followed by `\\E`, `\\A` or
/// `CHOOSE`, a space and its position
pub const UNBOUNDED: &str = "#unbounded";

/// TLC's error when it evaluates the unbounded quantifier or CHOOSE named `call` (see UNBOUNDED)
pub fn unbounded_error(call: &str) -> Option<String> {
    let (kind, at) = call.strip_prefix(UNBOUNDED)?.split_once(' ')?;
    Some(format!("TLC attempted to evaluate an unbounded {kind}.\nMake sure that the expression is of form {kind} x \\in S: P(x).\n{at}"))
}

/// `a op b` for an infix operator by its normalized name, as the parser builds it
pub fn bin_expr(op: &str, a: Expr, b: Expr) -> Expr {
    bin(op, a, b)
}

pub(crate) fn bin(op: &str, a: Expr, b: Expr) -> Expr {
    let o = match op {
        "=>" => BOp::Implies,
        "<=>" => BOp::Equiv,
        "~>" => BOp::LeadsTo,
        "\\/" | "/\\" if NEST_JUNCTIONS.with(|n| n.get()) => {
            let j = if op == "/\\" { Expr::And(vec![a, b]) } else { Expr::Or(vec![a, b]) };
            return Expr::Label(INFIX_JUNCTION.into(), vec![], j.b());
        }
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
        // TLC cannot check -+->, \EE or \AA: kept only to be refused where TLC refuses them
        "-+->" => return Expr::Call("-+->".into(), vec![a, b]),
        "^" => return Expr::Call("^".into(), vec![a, b]),
        o if USER_INFIX.iter().any(|(n, _)| *n == o) => return Expr::Call(o.into(), vec![a, b]),
        _ => unreachable!(),
    };
    Expr::Bin(o, a.b(), b.b())
}

/// The definitions `x1 == t[1]`, `x2 == t[2]`, ... binding the names of a tuple pattern
fn tuple_lets(t: &str, names: Vec<String>) -> Vec<Def> {
    names
        .into_iter()
        .enumerate()
        .map(|(i, n)| Def {
            name: n,
            params: vec![],
            arity: vec![],
            body: Expr::App(Expr::Ident(t.to_string()).b(), Expr::Num(i as i64 + 1).b()),
        })
        .collect()
}

/// The identifiers e mentions and does not bind itself, in order, without repeats
fn free_names(e: &Expr, out: &mut Vec<String>) {
    let mut bound = vec![];
    binder_names(e, &mut bound);
    let mut all = vec![];
    all_names(e, &mut all);
    for n in all {
        if !bound.contains(&n) && !out.contains(&n) {
            out.push(n);
        }
    }
}

fn all_names(e: &Expr, out: &mut Vec<String>) {
    if let Expr::Ident(n) = e {
        if !n.starts_with('@') {
            out.push(n.clone());
        }
    }
    for c in e.children() {
        all_names(c, out);
    }
}

fn binder_names(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Lambda(ps, _) => out.extend(ps.iter().cloned()),
        Expr::Quant(_, bs, _) | Expr::SetMap(_, bs) => out.extend(bs.iter().map(|(x, _)| x.clone())),
        Expr::Choose(x, ..) | Expr::SetFilter(x, ..) | Expr::FunCons(x, ..) => out.push(x.clone()),
        Expr::Let(defs, _) => out.extend(defs.iter().map(|d| d.name.clone())),
        _ => {}
    }
    for c in e.children() {
        binder_names(c, out);
    }
}

/// e with the references `N!Op` to a LET instance N renamed to the module-level instance, passing
/// the names it takes as its first arguments
fn rename_instance(e: &Expr, r: &(String, String, Vec<String>)) -> Expr {
    let (local, unique, names) = r;
    let prefix = format!("{local}!");
    let target = |n: &str| n.strip_prefix(&prefix).map(|op| format!("{unique}!{op}"));
    match e {
        Expr::Ident(n) | Expr::Call(n, _) if target(n).is_some() => {
            let mut args: Vec<Expr> = names.iter().map(|n| Expr::Ident(n.clone())).collect();
            if let Expr::Call(_, a) = e {
                args.extend(a.iter().map(|x| rename_instance(x, r)));
            }
            let name = target(match e {
                Expr::Ident(n) | Expr::Call(n, _) => n,
                _ => unreachable!(),
            })
            .unwrap();
            if args.is_empty() { Expr::Ident(name) } else { Expr::Call(name, args) }
        }
        _ => crate::codegen::map_children(e, &|c| rename_instance(c, r)),
    }
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
    /// The position of the tokens a..=b as TLC prints it: 1-based, the end column inclusive. SANY
    /// gives a parenthesized expression the position of what is inside the parentheses
    fn span_text(&self, mut a: usize, mut b: usize) -> String {
        let sym = |t: &Token, c: &str| matches!(&t.tok, Tok::Sym(x) if x == c);
        while a < b && sym(&self.toks[a], "(") && sym(&self.toks[b], ")") {
            // Only if these two parentheses match each other
            let mut depth = 0i32;
            let mut matched = true;
            for t in &self.toks[a..b] {
                if sym(t, "(") {
                    depth += 1;
                } else if sym(t, ")") {
                    depth -= 1;
                }
                if depth == 0 {
                    matched = false;
                    break;
                }
            }
            if !matched {
                break;
            }
            a += 1;
            b -= 1;
        }
        let (s, e) = (&self.toks[a], &self.toks[b]);
        format!("line {}, col {} to line {}, col {} of module {}", s.line, s.col + 1, e.line, e.end, self.module)
    }

    /// `e`, parsed from the token at `start` to the last one consumed, in a POS label
    fn at(&self, start: usize, e: Expr) -> Expr {
        if self.pos <= start {
            return e;
        }
        at_pos(&self.span_text(start, self.pos - 1), e)
    }

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
        let outer = std::mem::replace(&mut self.module, m.name.clone());
        loop {
            match self.raw().tok.clone() {
                Tok::Eof => break,
                Tok::Sym(s) if s == "====" => {
                    // Consumed, so that a nested module ends here and the enclosing one goes on
                    self.pos += 1;
                    break;
                }
                Tok::Sym(s) if s == "----" => self.pos += 1,
                Tok::Ident(k) if k == "MODULE" => {
                    let inner = self.module()?;
                    m.units.push(Unit::Nested(m.nested.len()));
                    m.nested.push(inner);
                }
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
                        m.units.push(Unit::Decl(c.clone()));
                        m.constants.push(c);
                    }
                }
                Tok::Ident(k) if k == "VARIABLE" || k == "VARIABLES" => {
                    self.pos += 1;
                    let vs = self.ident_list()?;
                    m.units.extend(vs.iter().map(|v| Unit::Decl(v.clone())));
                    m.variables.extend(vs);
                }
                // TLC checks ASSUME and ASSUMPTION, and skips THEOREM and AXIOM
                Tok::Ident(k) if k == "ASSUME" || k == "ASSUMPTION" => {
                    self.pos += 1;
                    // ASSUME Name == e also defines Name
                    let named = match (self.peek().clone(), self.peek2().clone()) {
                        (Tok::Ident(n), Tok::Sym(eq)) if eq == "==" => {
                            self.pos += 2;
                            Some(n)
                        }
                        _ => None,
                    };
                    let start = self.pos;
                    let expr = self.expr(0)?;
                    let (a, b) = (&self.toks[start], &self.toks[self.pos - 1]);
                    let span = (a.line, a.col + 1, b.line, b.col + tok_width(&b.tok));
                    if let Some(name) = named {
                        m.units.push(Unit::Def(m.defs.len(), false));
                        m.defs.push(Def { name, params: vec![], arity: vec![], body: expr.clone() });
                    } else {
                        m.units.push(Unit::Assume(m.assumes.len()));
                    }
                    m.assumes.push(Assume { module: m.name.clone(), expr, span });
                }
                Tok::Ident(k) if PROOF_UNITS.contains(&k.as_str()) => {
                    // THEOREM Name == e defines Name (TLC checks nothing of it)
                    if !matches!(k.as_str(), "USE" | "HIDE") {
                        let at = |p: &Self, k: usize| p.toks[(p.pos + k).min(p.toks.len() - 1)].tok.clone();
                        if let (Tok::Ident(n), Tok::Sym(eq)) = (at(self, 1), at(self, 2)) {
                            if eq == "==" {
                                m.units.push(Unit::Theorem(n.clone()));
                                let save = self.pos;
                                self.pos += 3;
                                if let Ok(e) = self.expr(0) {
                                    m.defs.push(Def { name: n, params: vec![], arity: vec![], body: e });
                                }
                                self.pos = save;
                            }
                        }
                    }
                    self.skip_proof_unit()
                }
                Tok::Ident(k) if k == "INSTANCE" => {
                    let start = self.pos;
                    self.pos += 1;
                    let mut inst = self.instance(None, vec![], vec![])?;
                    inst.at = self.span_text(start, self.pos - 1);
                    let local = start > 0 && matches!(&self.toks[start - 1].tok, Tok::Ident(l) if l == "LOCAL");
                    m.units.push(Unit::Inst(m.instances.len(), local));
                    m.instances.push(inst);
                }
                Tok::Ident(k) if k == "LOCAL" => {
                    self.pos += 1;
                    if let Tok::Ident(n) = &self.raw().tok {
                        if n != "INSTANCE" {
                            m.local_defs.push(n.clone());
                        }
                    }
                }
                Tok::Ident(k) if k == "RECURSIVE" => {
                    self.pos += 1;
                    for (n, _) in self.ident_list_arity()? {
                        m.units.push(Unit::Recursive(n.clone()));
                        self.recursive.push(n);
                    }
                }
                Tok::Ident(_) => {
                    let fun = matches!(self.peek2(), Tok::Sym(b) if b == "[");
                    let local = self.pos > 0 && matches!(&self.toks[self.pos - 1].tok, Tok::Ident(l) if l == "LOCAL");
                    match self.def()? {
                        Ok(d) => {
                            for d in d {
                                m.units.push(Unit::Def(m.defs.len(), fun));
                                m.defs.push(d);
                            }
                        }
                        Err(inst) => {
                            m.units.push(Unit::Inst(m.instances.len(), local));
                            m.instances.push(inst);
                        }
                    }
                }
                _ => return self.err("unexpected token at module level"),
            }
        }
        m.recursive = std::mem::take(&mut self.recursive);
        m.instances.append(&mut self.let_instances);
        self.module = outer;
        Ok(m)
    }

    /// Names with optional parameter lists `F(_, _)`, and the number of parameters of each
    fn ident_list_arity(&mut self) -> R<Vec<(String, usize)>> {
        let mut v = vec![];
        loop {
            // An infix operator constant `_ ** _`
            if matches!(self.peek(), Tok::Ident(u) if u == "_") {
                if let Some((_, _, op)) = infix(self.peek2()) {
                    if matches!(&self.toks[self.pos + 2].tok, Tok::Ident(u) if u == "_") {
                        self.pos += 3;
                        v.push((op.to_string(), 2));
                        if self.is(",") {
                            self.pos += 1;
                            continue;
                        }
                        return Ok(v);
                    }
                }
            }
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

    /// Skips a theorem-like statement and its proof: everything up to the next line that starts at
    /// or left of the statement's column, other than a proof step (`<1>...`) or a proof keyword
    fn skip_proof_unit(&mut self) {
        let col = self.raw().col;
        self.pos += 1;
        loop {
            let t = self.raw();
            match &t.tok {
                Tok::Eof => return,
                Tok::Sym(s) if s == "====" || s == "----" => return,
                _ => {}
            }
            if t.first && t.col <= col {
                let continues = match &t.tok {
                    Tok::Sym(s) => s == "<",
                    Tok::Ident(k) => PROOF_LINE_STARTS.contains(&k.as_str()),
                    _ => false,
                };
                if !continues {
                    return;
                }
            }
            self.pos += 1;
        }
    }

    /// The rest of an INSTANCE statement after the keyword: `M [WITH x <- e, ...]`
    fn instance(&mut self, name: Option<String>, params: Vec<String>, arity: Vec<usize>) -> R<Instance> {
        let module = self.ident()?;
        let mut subs = vec![];
        if self.is_kw("WITH") {
            self.pos += 1;
            loop {
                // A name, or an operator symbol (`** <- Mul`)
                let x = match self.peek().clone() {
                    Tok::Ident(x) => x,
                    t => match infix(&t) {
                        Some((_, _, op)) => op.to_string(),
                        None => return self.err("expected a name or an operator in a WITH substitution"),
                    },
                };
                self.pos += 1;
                self.expect("<-")?;
                // An operator symbol on the right (`** <- +`) stands for LAMBDA a, b : a + b
                let e = match infix(self.peek()) {
                    Some((_, _, op)) if matches!(self.peek2(), Tok::Sym(c) if c == ",") || matches!(self.peek2(), Tok::Eof) || self.toks[self.pos + 1].first => {
                        self.pos += 1;
                        let (a, b) = (Expr::Ident("#l".into()), Expr::Ident("#r".into()));
                        Expr::Lambda(vec!["#l".into(), "#r".into()], bin(op, a, b).b())
                    }
                    _ => self.expr(0)?,
                };
                subs.push((x, e));
                if self.is(",") {
                    self.pos += 1;
                } else {
                    break;
                }
            }
        }
        Ok(Instance { name, params, arity, module, subs, at: String::new() })
    }

    /// An instance defined inside LET becomes a module-level instance with a unique name that
    /// takes as parameters the names its substitutions mention (they may be bound around the
    /// LET); references `N!Op(args)` in the LET are rewritten to pass them
    fn let_instance(&mut self, inst: Instance) -> (String, String, Vec<String>) {
        let local = inst.name.clone().unwrap_or_default();
        let unique = format!("{local}#let{}", self.let_instances.len());
        let mut names: Vec<String> = vec![];
        for (_, e) in &inst.subs {
            free_names(e, &mut names);
        }
        names.retain(|n| !inst.params.contains(n));
        let mut params = names.clone();
        params.extend(inst.params.iter().cloned());
        let mut arity = vec![0; names.len()];
        arity.extend(inst.arity.iter().copied());
        self.let_instances.push(Instance { name: Some(unique.clone()), params, arity, module: inst.module, subs: inst.subs, at: inst.at });
        (local, unique, names)
    }

    /// A definition, or (as Err) a definition of an instance `N(p) == INSTANCE M ...`
    fn def(&mut self) -> R<Result<Vec<Def>, Instance>> {
        let def_start = self.pos;
        let name = self.ident()?;
        // A postfix operator definition `a ^+ == e`
        if let Some(op) = ["^+", "^*", "^#"].iter().find(|o| self.is(o)) {
            self.pos += 1;
            self.expect("==")?;
            let start = self.pos;
            let body = self.expr(0)?;
            let body = self.at(start, body);
            return Ok(Ok(vec![Def { name: op.to_string(), params: vec![name], arity: vec![0], body }]));
        }
        // An infix operator definition `a ++ b == e`
        if let Some((_, op)) = user_infix(self.peek()) {
            self.pos += 1;
            let b = self.ident()?;
            self.expect("==")?;
            let start = self.pos;
            let body = self.expr(0)?;
            let body = self.at(start, body);
            return Ok(Ok(vec![Def { name: op.to_string(), params: vec![name, b], arity: vec![0, 0], body }]));
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
            let (bs, lets) = self.nested(|p| p.binders_pat())?;
            self.expect("]")?;
            self.expect("==")?;
            let body = self.expr(0)?;
            let body = if lets.is_empty() { body } else { Expr::Let(lets, body.b()) };
            let _ = at;
            if body.any(&|e| matches!(e, Expr::Ident(n) | Expr::Call(n, _) if *n == name)) {
                return Ok(Ok(self.rec_fun(name, bs, body)));
            }
            return Ok(Ok(vec![Def { name, params, arity, body: fun_cons(bs, body) }]));
        }
        self.expect("==")?;
        if self.is_kw("INSTANCE") {
            self.pos += 1;
            let mut inst = self.instance(Some(name), params, arity)?;
            inst.at = self.span_text(def_start, self.pos - 1);
            return Ok(Err(inst));
        }
        let start = self.pos;
        let body = self.expr(0)?;
        let body = self.at(start, body);
        Ok(Ok(vec![Def { name, params, arity, body }]))
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
        self.expr_in(min, None)
    }

    /// An expression whose operators bind at least as tightly as `min`; `parent` is the infix
    /// operator it is the right operand of
    fn expr_in(&mut self, min: u8, parent: Option<&'static str>) -> R<Expr> {
        let lhs_start = self.pos;
        let mut lhs = self.prefix(parent)?;
        let mut prev: Option<&'static str> = None;
        // Whether lhs is a disjunction built in this loop (its operands are in POS labels)
        let mut chain_or = false;
        loop {
            let Some((prec, right, op)) = infix(self.peek()) else { break };
            if prec < min {
                break;
            }
            if let Some(other) = [prev, parent].into_iter().flatten().find(|o| precedence_conflict(o, op)) {
                return self.err(&format!("{SANY}Precedence conflict between ops {other} and {op}."));
            }
            prev = Some(op);
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
            if op == "\\/" && !chain_or {
                let end = self.pos - 1;
                let at = std::mem::replace(&mut self.pos, end);
                lhs = self.at(lhs_start, lhs);
                self.pos = at;
            }
            let rhs_start = self.pos;
            let rhs = self.expr_in(if right { prec } else { prec + 1 }, Some(op))?;
            let rhs = if op == "\\/" { self.at(rhs_start, rhs) } else { rhs };
            chain_or = op == "\\/";
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
            let start = self.pos;
            let e = self.expr(0);
            self.limits.pop();
            let e = e?;
            items.push(if sym == "\\/" { self.at(start, e) } else { e });
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

    /// At `<<x, y>> \in`, the names (consuming the pattern up to `\in` inclusive); otherwise None
    /// and nothing is consumed
    fn tuple_pattern(&mut self) -> Option<Vec<String>> {
        if !self.is("<<") {
            return None;
        }
        let mut i = self.pos + 1;
        let mut names = vec![];
        loop {
            let Tok::Ident(n) = &self.toks[i].tok else { return None };
            names.push(n.clone());
            i += 1;
            match &self.toks[i].tok {
                Tok::Sym(s) if s == "," => i += 1,
                Tok::Sym(s) if s == ">>" => break,
                _ => return None,
            }
        }
        if !matches!(&self.toks[i + 1].tok, Tok::Sym(s) if s == "\\in") {
            return None;
        }
        self.pos = i + 2;
        Some(names)
    }

    fn fresh_tuple_name(&mut self) -> String {
        self.tuple_binders += 1;
        format!("#tup{}", self.tuple_binders)
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

    /// At the bound variables of `\\E x, y : P` (or \\A, CHOOSE) without a set: the quantifier,
    /// as a call that stops with TLC's error when it is evaluated (TLC accepts it and fails only
    /// then). Otherwise None and nothing is consumed.
    fn unbounded(&mut self, kind: &str) -> R<Option<Expr>> {
        let mut i = self.pos;
        loop {
            if !matches!(&self.toks[i].tok, Tok::Ident(_)) {
                return Ok(None);
            }
            match &self.toks[i + 1].tok {
                Tok::Sym(c) if c == "," => i += 2,
                Tok::Sym(c) if c == ":" => break,
                _ => return Ok(None),
            }
        }
        // The position runs from the quantifier to the end of its body
        let start = self.pos - 1;
        self.pos = i + 2;
        self.expr(0)?;
        let at = self.span_text(start, self.pos - 1);
        Ok(Some(Expr::Call(format!("{UNBOUNDED}{kind} {at}"), vec![])))
    }

    /// The operand of the prefix operator `op` (by its name in `sany_range`), parsed at
    /// precedence `min`. SANY refuses an infix operator whose range overlaps op's right after it,
    /// inside the operand (`[]x = 1`, `ENABLED x' = 1`) or after it (`-a \X b`)
    fn prefix_operand(&mut self, op: &'static str, min: u8) -> R<Expr> {
        let e = self.expr_in(min, Some(op))?;
        if let Some((_, _, next)) = infix(self.peek()) {
            if precedence_conflict(op, next) {
                return self.err(&format!("{SANY}Precedence conflict between ops {op} and {next}."));
            }
        }
        Ok(e)
    }

    /// `parent` is the infix operator whose right operand this is
    fn prefix(&mut self, parent: Option<&'static str>) -> R<Expr> {
        let guard = self.postfix_guard.take();
        let t = self.peek().clone();
        match &t {
            Tok::Sym(s) if s == "/\\" || s == "\\/" => self.bullets(&s.clone()),
            Tok::Sym(s) if s == "~" => {
                self.pos += 1;
                Ok(Expr::Un(UOp::Not, self.expr(4)?.b()))
            }
            Tok::Sym(s) if s == "-" => {
                // SANY refuses unary minus as the operand of an operator that binds tighter
                // (`a * -b`, `a ^ -b`)
                if let Some(p) = parent.filter(|p| sany_range(p).is_some_and(|(lo, _, _)| lo > 12)) {
                    return self.err(&format!("{SANY}Precedence conflict between ops {p} and -."));
                }
                self.pos += 1;
                Ok(Expr::Un(UOp::Neg, self.prefix_operand("-.", 12)?.b()))
            }
            // In an AT label: TLC names a part of a property, such as `[]P` checked as an
            // invariant, by its position
            Tok::Sym(s) if s == "[]" => {
                let start = self.pos;
                self.pos += 1;
                self.postfix_guard = Some("[]");
                let e = Expr::Un(UOp::Always, self.prefix_operand("[]", 4)?.b());
                Ok(at_err(&self.span_text(start, self.pos - 1), e))
            }
            Tok::Sym(s) if s == "<>" => {
                self.pos += 1;
                self.postfix_guard = Some("<>");
                Ok(Expr::Un(UOp::Eventually, self.prefix_operand("<>", 4)?.b()))
            }
            // \EE x : e and \AA x : e (temporal quantifiers)
            Tok::Sym(s) if s == "\\EE" || s == "\\AA" => {
                self.pos += 1;
                loop {
                    self.ident()?;
                    if !self.is(",") {
                        break;
                    }
                    self.pos += 1;
                }
                self.expect(":")?;
                let body = self.expr(0)?;
                Ok(Expr::Call(s.clone(), vec![body]))
            }
            Tok::Sym(s) if s == "\\E" || s == "\\A" => {
                let ex = s == "\\E";
                self.pos += 1;
                if let Some(e) = self.unbounded(s)? {
                    return Ok(e);
                }
                let (bs, lets) = self.binders_pat()?;
                self.expect(":")?;
                let start = self.pos;
                let body = self.expr(0)?;
                let body = if ex { self.at(start, body) } else { body };
                let body = if lets.is_empty() { body } else { Expr::Let(lets, body.b()) };
                Ok(Expr::Quant(ex, bs, body.b()))
            }
            Tok::Ident(k) => match k.as_str() {
                "SUBSET" | "UNION" | "DOMAIN" => {
                    self.pos += 1;
                    let (op, name) = match k.as_str() {
                        "SUBSET" => (UOp::Subset, "SUBSET"),
                        "UNION" => (UOp::Union, "UNION"),
                        _ => (UOp::Domain, "DOMAIN"),
                    };
                    Ok(Expr::Un(op, self.prefix_operand(name, 14)?.b()))
                }
                "UNCHANGED" | "ENABLED" => {
                    self.pos += 1;
                    let (op, name) = if k == "UNCHANGED" { (UOp::Unchanged, "UNCHANGED") } else { (UOp::Enabled, "ENABLED") };
                    self.postfix_guard = Some(name);
                    Ok(Expr::Un(op, self.prefix_operand(name, 15)?.b()))
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
                    let start = self.pos;
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
                    Ok(at_err(&self.span_text(start, self.pos - 1), Expr::Case(arms, other)))
                }
                "LET" => {
                    self.pos += 1;
                    let mut defs = vec![];
                    let mut renames = vec![];
                    while !self.is_kw("IN") {
                        if self.is_kw("RECURSIVE") {
                            self.pos += 1;
                            for (n, _) in self.ident_list_arity()? {
                                self.recursive.push(n);
                            }
                            continue;
                        }
                        match self.def()? {
                            Ok(d) => defs.extend(d),
                            Err(inst) => renames.push(self.let_instance(inst)),
                        }
                    }
                    self.pos += 1;
                    let start = self.pos;
                    let body = self.expr(0)?;
                    let mut body = self.at(start, body);
                    for r in &renames {
                        body = rename_instance(&body, r);
                        for d in defs.iter_mut() {
                            d.body = rename_instance(&d.body, r);
                        }
                    }
                    if defs.is_empty() {
                        return Ok(body);
                    }
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
                    let start = self.pos;
                    self.pos += 1;
                    if let Some(e) = self.unbounded("CHOOSE")? {
                        return Ok(e);
                    }
                    // CHOOSE <<x, y>> \in S : P binds a fresh name to the tuple
                    let pat = self.tuple_pattern();
                    let x = match &pat {
                        Some(_) => self.fresh_tuple_name(),
                        None => {
                            let x = self.ident()?;
                            self.expect("\\in")?;
                            x
                        }
                    };
                    let s = self.expr(4)?;
                    self.expect(":")?;
                    let p = self.expr(0)?;
                    let p = match pat {
                        Some(names) => Expr::Let(tuple_lets(&x, names), p.b()),
                        None => p,
                    };
                    Ok(at_err(&self.span_text(start, self.pos - 1), Expr::Choose(x, s.b(), p.b())))
                }
                _ => {
                    self.postfix_guard = guard;
                    self.postfix()
                }
            },
            _ => {
                self.postfix_guard = guard;
                self.postfix()
            }
        }
    }

    fn postfix(&mut self) -> R<Expr> {
        let guard = self.postfix_guard.take();
        let mut e = self.primary()?;
        loop {
            if let (Some(p), Some(op)) = (guard, ["'", "^+", "^*", "^#"].iter().find(|o| self.is(o))) {
                return self.err(&format!("{SANY}Precedence conflict between ops {p} and {op}."));
            }
            // The postfix operators a spec may define (a ^+ == ...)
            if let Some(op) = ["^+", "^*", "^#"].iter().find(|o| self.is(o)) {
                self.pos += 1;
                e = Expr::Call(op.to_string(), vec![e]);
                continue;
            }
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
            // An infix operator passed as an operator argument, as in SortSeq(s, <)
            if let Some((_, _, name)) = infix(self.peek()) {
                if matches!(self.peek2(), Tok::Sym(s) if s == "," || s == close) {
                    self.pos += 1;
                    v.push(Expr::Ident(name.to_string()));
                    if self.is(",") {
                        self.pos += 1;
                        continue;
                    }
                    self.expect(close)?;
                    return Ok(v);
                }
            }
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
                // A label `l :: e` or `l(a, b) :: e`: kept as a Label named `l::`, which nothing
                // but liveness looks at (TLC cannot check a labeled temporal formula)
                // The label is in an AT label for its position, which TLC gives when it refuses it
                let id_tok = self.pos - 1;
                if self.is("::") {
                    self.pos += 1;
                    let start = self.pos;
                    let body = self.expr(0)?;
                    let body = self.at(start, body);
                    let l = Expr::Label(format!("{s}::"), vec![], body.b());
                    return Ok(at_err(&self.span_text(id_tok, self.pos - 1), l));
                }
                if self.is("(") {
                    let mut j = self.pos + 1;
                    while matches!(&self.toks[j].tok, Tok::Ident(_)) && matches!(&self.toks[j + 1].tok, Tok::Sym(c) if c == "," || c == ")") {
                        j += 2;
                        if matches!(&self.toks[j - 1].tok, Tok::Sym(c) if c == ")") {
                            break;
                        }
                    }
                    if j > self.pos + 1 && matches!(&self.toks[j - 1].tok, Tok::Sym(c) if c == ")") && matches!(&self.toks[j].tok, Tok::Sym(c) if c == "::") {
                        // The parameters are kept in the name, for naming the label with arguments
                        let ps: Vec<String> = self.toks[self.pos + 1..j]
                            .iter()
                            .filter_map(|t| match &t.tok {
                                Tok::Ident(x) => Some(x.clone()),
                                _ => None,
                            })
                            .collect();
                        self.pos = j + 1;
                        let start = self.pos;
                        let body = self.expr(0)?;
                        let body = self.at(start, body);
                        let l = Expr::Label(format!("{s}({})::", ps.join(",")), vec![], body.b());
                        return Ok(at_err(&self.span_text(id_tok, self.pos - 1), l));
                    }
                }
                let mut name = s;
                let mut args = vec![];
                let mut call = false;
                loop {
                    if self.is("(") {
                        self.pos += 1;
                        args.extend(self.nested(|p| p.comma_list(")"))?);
                        call = true;
                    }
                    // An operator of an instance: `N!Op`, `N(a)!Op(b)` (the arguments are joined)
                    match (self.peek(), self.peek2()) {
                        (Tok::Sym(b), Tok::Ident(op)) if b == "!" => {
                            name = format!("{name}!{op}");
                            self.pos += 2;
                        }
                        // An operator symbol of an instance: `N!+(a, b)`
                        (Tok::Sym(b), t) if b == "!" && infix(t).is_some() => {
                            let op = infix(t).unwrap().2;
                            name = format!("{name}!{op}");
                            self.pos += 2;
                        }
                        _ => break,
                    }
                }
                let base = if call || !args.is_empty() { Expr::Call(name, args) } else { Expr::Ident(name) };
                // RTnow(v) and RTBound(A, v, D, E) of RealTime are temporal formulas TLC refuses,
                // naming them by position
                if matches!(&base, Expr::Call(n, _) if n == "RTnow" || n == "RTBound") {
                    return Ok(at_err(&self.span_text(id_tok, self.pos - 1), base));
                }
                // A positional subexpression name: `Op!1!2`, `Op!<<`, `Op!(e)`, `Op!:`, also
                // followed by labels
                if !(self.is("!") && is_selector(self.peek2())) {
                    return Ok(base);
                }
                let mut parts = vec![base];
                while self.is("!") {
                    let next = self.peek2().clone();
                    self.pos += 2;
                    parts.push(match next {
                        Tok::Num(n) => Expr::Num(n),
                        Tok::Sym(c) if c == "(" => Expr::Tuple(self.nested(|p| p.comma_list(")"))?),
                        Tok::Sym(c) if ["<<", ">>", ":", "@"].contains(&c.as_str()) => Expr::Ident(c),
                        Tok::Ident(l) => {
                            let mut largs = vec![];
                            if self.is("(") {
                                self.pos += 1;
                                largs = self.nested(|p| p.comma_list(")"))?;
                            }
                            Expr::Call(format!("#label{l}"), largs)
                        }
                        _ => {
                            self.pos -= 2;
                            return self.err("expected a subexpression selector after `!`");
                        }
                    });
                }
                Ok(Expr::Call(SUBEXPR.into(), parts))
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
                    // <<A>>_v: an A step that changes v, written A /\ v' # v. The subscript follows
                    // `>>` without a space: `_v` lexes as one identifier, `_<<x, y>>` as `_` and a tuple
                    let close = &self.toks[self.pos - 1];
                    let (line, end) = (close.line, close.col + 2);
                    if let Tok::Ident(u) = &self.raw().tok {
                        if u.starts_with('_') && self.raw().line == line && self.raw().col == end {
                            let u = u.clone();
                            self.pos += 1;
                            let sub = if u == "_" { self.primary()? } else { Expr::Ident(u[1..].to_string()) };
                            let [a] = <[Expr; 1]>::try_from(v).map_err(|_| "<<...>>_v takes one action".to_string())?;
                            let same = Expr::Bin(BOp::Eq, Expr::Prime(sub.clone().b()).b(), sub.b());
                            // Marked, so that <>(<<A>>_v) can be told from <> of another action
                            let step = Expr::And(vec![a, Expr::Un(UOp::Not, same.b())]);
                            return Ok(Expr::Label("<<>>_".into(), vec![], step.b()));
                        }
                    }
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
        // {<<x, y>> \in S : P}
        let at = self.pos;
        if let Some(names) = self.tuple_pattern() {
            let s = self.expr(4)?;
            if self.is(":") {
                self.pos += 1;
                let t = self.fresh_tuple_name();
                let p = self.expr(0)?;
                self.expect("}")?;
                return Ok(Expr::SetFilter(t.clone(), s.b(), Expr::Let(tuple_lets(&t, names), p.b()).b()));
            }
            self.pos = at;
        }
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
        let e_end = self.pos;
        if self.is(",") && matches!(&e, Expr::Ident(_) | Expr::Bin(BOp::In, ..)) {
            // [x \in S, y \in T |-> e] or [x, y \in S |-> e]
            self.pos = start;
            // A tuple of bound variables `<<a, b>> \in S` among them names the components of
            // that argument
            let (bs, lets) = self.binders_pat()?;
            self.expect("|->")?;
            let body = self.expr(0)?;
            self.expect("]")?;
            let body = if lets.is_empty() { body } else { Expr::Let(lets, body.b()) };
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
                // [<<x, y>> \in S |-> e]
                if let Expr::Tuple(xs) = x.as_ref() {
                    if let Some(names) = xs.iter().map(|x| if let Expr::Ident(n) = x { Some(n.clone()) } else { None }).collect::<Option<Vec<_>>>() {
                        self.pos += 1;
                        let body = self.expr(0)?;
                        self.expect("]")?;
                        let t = self.fresh_tuple_name();
                        return Ok(Expr::FunCons(t.clone(), s.clone(), Expr::Let(tuple_lets(&t, names), body.b()).b()));
                    }
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
                let e = at_pos(&self.span_text(start, e_end - 1), e);
                return Ok(Expr::BoxAction(e.b(), sub.b()));
            }
        }
        self.err("unsupported bracket expression")
    }
}
