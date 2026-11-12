//! TLC's check that a PlusCal algorithm and its TLA+ translation have not changed since the
//! translator wrote them.
//!
//! The translator writes two checksums in the line that opens the translation:
//! `\* BEGIN TRANSLATION (chksum(pcal) = "..." /\ chksum(tla) = "...")`. When SANY parses the root
//! module and each module it EXTENDS, TLC computes both again and prints a warning when one
//! differs (measured on TLC 2.19, `tests/tlc/PcalSum*`; see "PlusCal checksums" in CLAUDE.md):
//!
//! - the TLA+ checksum is the CRC-32 of the lines between `BEGIN TRANSLATION` and `END
//!   TRANSLATION`, joined without line breaks, as written
//! - the PlusCal checksum is the CRC-32 of the algorithm's syntax tree as TLC's PlusCal translator
//!   prints it, after it has parsed the algorithm, split it into labeled steps and expanded those
//!   steps into assignments to `pc` (which changes parts of the tree it prints). Line breaks inside
//!   an expression are part of that text, spaces and comments are not
//!
//! The tree is rebuilt here for the algorithms in the subset tla2rs reads (P-syntax and C-syntax,
//! one process or several, the statements other than procedure calls, returns and macros, every
//! statement that needs a label having one). For anything else the PlusCal checksum is not
//! computed and no warning is printed, with a note on stderr.
//!
//! What the translator prints, and how it expands the steps, was learned from TLC's output and
//! from its published sources (the tlaplus/tlaplus repository, MIT licence); the code here is
//! written for tla2rs.

/// CRC-32 (IEEE), as java.util.zip.CRC32
fn crc32(data: &[u8]) -> u32 {
    let mut c = !0u32;
    for &b in data {
        c ^= b as u32;
        for _ in 0..8 {
            c = if c & 1 != 0 { (c >> 1) ^ 0xEDB8_8320 } else { c >> 1 };
        }
    }
    !c
}

/// A checksum as TLC writes it: lowercase hexadecimal without leading zeros
fn hex(c: u32) -> String {
    format!("{c:x}")
}

/// The warnings TLC prints, in its order, for the module `root` (its text) and the modules it
/// extends from files in `dir`; and notes for the modules whose PlusCal checksum tla2rs cannot
/// compute
pub fn warnings(root: &str, dir: &std::path::Path) -> (Vec<String>, Vec<String>) {
    let (mut out, mut notes) = (vec![], vec![]);
    // TLC checks the root module, then each module reached through EXTENDS (also from a module
    // reached through INSTANCE), in the order SANY loads them
    let mut queue: std::collections::VecDeque<(String, bool)> = std::collections::VecDeque::new();
    let mut seen: Vec<String> = vec![];
    let mut first = Some(root.to_string());
    let mut check_next = true;
    loop {
        let src = match first.take() {
            Some(s) => s,
            None => {
                let Some((name, check)) = queue.pop_front() else { break };
                check_next = check;
                match std::fs::read(dir.join(format!("{name}.tla"))) {
                    Ok(b) => String::from_utf8_lossy(&b).into_owned(),
                    Err(_) => continue,
                }
            }
        };
        let Ok(m) = crate::parser::parse_module(&src) else { continue };
        if seen.contains(&m.name) {
            continue;
        }
        seen.push(m.name.clone());
        if check_next {
            match check(&src) {
                Check::Same => {}
                Check::Warn(w) => out.push(w.replace("{}", &m.name)),
                Check::Unknown(why) => notes.push(format!(
                    "the PlusCal checksum of module {} is not checked: {why}; TLC may warn that the algorithm changed",
                    m.name
                )),
            }
        }
        for e in &m.extends {
            queue.push_back((e.clone(), true));
        }
        for i in &m.instances {
            queue.push_back((i.module.clone(), false));
        }
    }
    (out, notes)
}

enum Check {
    Same,
    /// The warning, with `{}` for the module's name
    Warn(String),
    Unknown(String),
}

/// The lines of a file as Java's BufferedReader reads them (split at \n, \r\n or \r)
fn java_lines(src: &str) -> Vec<String> {
    let mut v = vec![];
    let mut cur = String::new();
    let mut it = src.chars().peekable();
    while let Some(c) = it.next() {
        match c {
            '\n' => v.push(std::mem::take(&mut cur)),
            '\r' => {
                if it.peek() == Some(&'\n') {
                    it.next();
                }
                v.push(std::mem::take(&mut cur));
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        v.push(cur);
    }
    v
}

/// The lines of the first module in src, from its first line to its closing line (as SANY locates
/// them), as written and with tabs expanded to multiples of 8 and a space added to each (as TLC's
/// translator reads them)
fn module_lines(src: &str) -> Option<(Vec<String>, Vec<String>)> {
    let all = java_lines(src);
    let begin = all.iter().position(|l| is_module_start(l))?;
    let end = all[begin..].iter().position(|l| l.starts_with("====")).map(|i| begin + i).unwrap_or(all.len() - 1);
    let lines: Vec<String> = all[begin..=end].to_vec();
    let detab = lines
        .iter()
        .map(|l| {
            let mut s = String::new();
            for c in l.chars() {
                if c == '\t' {
                    let n = 8 - s.chars().count() % 8;
                    s.extend(std::iter::repeat_n(' ', n));
                } else {
                    s.push(c);
                }
            }
            s.push(' ');
            s
        })
        .collect();
    Some((lines, detab))
}

/// Where the algorithm starts: the line, the column after `--algorithm` or `--fair` (in
/// characters), and whether it is `--fair`
fn find_algorithm(detab: &[String]) -> Option<(usize, usize, bool)> {
    for (i, l) in detab.iter().enumerate() {
        // TLC stops at a line of `=` only, which a line with its added space never is
        if let Some(c) = l.find("--algorithm") {
            return Some((i, l[..c].chars().count() + "--algorithm".len(), false));
        }
        if let Some(c) = l.find("--fair") {
            return Some((i, l[..c].chars().count() + "--fair".len(), true));
        }
    }
    None
}

fn check(src: &str) -> Check {
    let Some((lines, detab)) = module_lines(src) else { return Check::Same };
    if !lines.iter().any(|l| l.find("algorithm").is_some_and(|i| i > 0)) {
        return Check::Same;
    }
    let alg = find_algorithm(&detab);
    let Some(tl) = token_pair(&detab, 0, "BEGIN", "TRANSLATION") else { return Check::Same };
    let Some(etl) = token_pair(&detab, tl + 1, "END", "TRANSLATION") else { return Check::Same };
    let Some((alg_line, alg_col, fair)) = alg else { return Check::Same };
    let Some((pcal_sum, tla_sum)) = checksums(&detab[tl]) else { return Check::Same };
    let tla_diff = tla_sum.is_some_and(|s| {
        let text: String = lines[tl + 1..etl].concat();
        s != hex(crc32(text.as_bytes()))
    });
    let pcal_diff = match pcal_sum {
        None => false,
        Some(s) => {
            if detab.iter().any(|l| has_options(l)) {
                return Check::Unknown("the module has a PlusCal options line".into());
            }
            match tree_text(detab.clone(), alg_line, alg_col, fair) {
                Ok(t) => s != hex(crc32(t.as_bytes())),
                Err(why) => return Check::Unknown(why),
            }
        }
    };
    match (pcal_diff, tla_diff) {
        (true, true) => Check::Warn(
            "!! WARNING: The PlusCal algorithm and its TLA+ translation in module {} filename since the last translation."
                .into(),
        ),
        (false, true) => Check::Warn("!! WARNING: The TLA+ translation in module {} has changed since its last translation.".into()),
        (true, false) => Check::Warn("!! WARNING: The PlusCal algorithm in module {} has changed since its last translation.".into()),
        (false, false) => Check::Same,
    }
}

/// `----...` (at least four) then spaces and `MODULE`
fn is_module_start(l: &str) -> bool {
    let t = l.trim_start();
    let d = t.len() - t.trim_start_matches('-').len();
    d >= 4 && t[d..].trim_start().starts_with("MODULE")
}

/// The first line at or after `from` where `a` is followed by spaces and then `b`, both at their
/// first occurrence on the line
fn token_pair(lines: &[String], from: usize, a: &str, b: &str) -> Option<usize> {
    (from..lines.len()).find(|&i| {
        let l = &lines[i];
        let Some(c) = l.find(a) else { return false };
        let mut n = c + a.len();
        while l.as_bytes().get(n) == Some(&b' ') {
            n += 1;
        }
        n < l.len() && l.find(b) == Some(n)
    })
}

/// A line naming PlusCal options (`PlusCal options (...)`), which change how TLC parses the
/// algorithm; such modules are left alone
fn has_options(l: &str) -> bool {
    l.match_indices("PlusCal").any(|(i, _)| {
        let r = l[i + 7..].trim_start();
        r.starts_with("options") && !r[7..].starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_')
    })
}

/// The checksums in the line that opens the translation (None for `\in STRING`), or None when the
/// line does not have them, following TLC's pattern
fn checksums(line: &str) -> Option<(Option<String>, Option<String>)> {
    let ws = |s: &str| s.trim_start_matches([' ', '\t', '\n', '\u{b}', '\u{c}', '\r']).len();
    for (i, _) in line.match_indices("\\* BEGIN TRANSLATION") {
        let s = &line[i + "\\* BEGIN TRANSLATION".len()..];
        let r = &s[s.len() - ws(s)..];
        if r.len() == s.len() {
            continue;
        }
        let Some(r) = r.strip_prefix('(') else { continue };
        let r = &r[r.len() - ws(r)..];
        let Some((pcal, r)) = sum_clause(r, true) else { continue };
        let r = &r[r.len() - ws(r)..];
        let Some(r) = r.strip_prefix("/\\") else { continue };
        let r = &r[r.len() - ws(r)..];
        let Some((tla, r)) = sum_clause(r, false) else { continue };
        let r = &r[r.len() - ws(r)..];
        if r.starts_with(')') {
            return Some((pcal, tla));
        }
    }
    None
}

/// `chksum(pcal) = "hex"` or `chksum(pcal) \in STRING` (also `checksum`, `plusc al`, case-insensitive
/// in the name), and what follows
fn sum_clause(r: &str, pcal: bool) -> Option<(Option<String>, &str)> {
    let lower = r.to_ascii_lowercase();
    let mut n = 0;
    let eat = |n: &mut usize, s: &str| -> bool {
        if lower[*n..].starts_with(s) {
            *n += s.len();
            true
        } else {
            false
        }
    };
    if !eat(&mut n, "ch") {
        return None;
    }
    eat(&mut n, "ec");
    if !eat(&mut n, "ksum(") {
        return None;
    }
    if pcal {
        if !eat(&mut n, "p") {
            return None;
        }
        eat(&mut n, "lus");
        if !eat(&mut n, "cal)") {
            return None;
        }
    } else {
        if !eat(&mut n, "tla") {
            return None;
        }
        eat(&mut n, "+");
        if !eat(&mut n, ")") {
            return None;
        }
    }
    let r = r[n..].trim_start_matches([' ', '\t', '\n', '\u{b}', '\u{c}', '\r']);
    if let Some(r) = r.strip_prefix('=') {
        let r = r.trim_start_matches([' ', '\t', '\n', '\u{b}', '\u{c}', '\r']);
        let r = r.strip_prefix('"')?;
        let h = r.len() - r.trim_start_matches(|c: char| c.is_ascii_hexdigit()).len();
        let rest = r[h..].strip_prefix('"')?;
        return Some((Some(r[..h].to_string()), rest));
    }
    let r = r.strip_prefix("\\in")?;
    let r = r.trim_start_matches([' ', '\t', '\n', '\u{b}', '\u{c}', '\r']);
    Some((None, r.strip_prefix("STRING")?))
}

// ---------------------------------------------------------------------------------------------
// The algorithm's syntax tree

/// A token of an expression; `string` for a string literal (its text without the quotes)
#[derive(Clone, Debug)]
struct Tok {
    s: String,
    string: bool,
}

/// An expression: its tokens, line by line (lines without tokens kept between the first and the
/// last)
type Expr = Vec<Vec<Tok>>;

#[derive(Clone, Debug)]
struct Labeled {
    label: String,
    stmts: Vec<Stmt>,
}

#[derive(Clone, Debug)]
struct Clause {
    unlab: Vec<Stmt>,
    lab: Vec<Labeled>,
}

#[derive(Clone, Debug)]
enum Kind {
    LabelIf { test: Expr, unlab_then: Vec<Stmt>, lab_then: Vec<Labeled>, unlab_else: Vec<Stmt>, lab_else: Vec<Labeled> },
    If { test: Expr, then: Vec<Stmt>, els: Vec<Stmt> },
    LabelEither(Vec<Clause>),
    Either(Vec<Vec<Stmt>>),
    While { test: Expr, unlab: Vec<Stmt>, lab: Vec<Labeled> },
    With { var: String, eq: bool, exp: Expr, body: Vec<Stmt> },
    /// (variable, subscript, right-hand side) for each `||`-separated assignment
    Assign(Vec<(String, Expr, Expr)>),
    When(Expr),
    Print(Expr),
    Assert(Expr),
    Skip,
    Goto(String),
}

#[derive(Clone, Debug)]
struct Stmt {
    lbl: String,
    k: Kind,
}

struct VarDecl {
    var: String,
    eq: bool,
    val: Expr,
}

struct Process {
    name: String,
    fairness: &'static str,
    eq: bool,
    id: Expr,
    decls: Vec<VarDecl>,
    plus: Vec<String>,
    minus: Vec<String>,
    body: Vec<Labeled>,
}

// ---------------------------------------------------------------------------------------------
// Tokens

/// TLA+ operator symbols as TLC's PlusCal tokenizer knows them (those not made of letters)
const SYMBOLS: &[&str] = &[
    ">>_", "]_", "(", "[", "{", "<<", ")", "}", "]", ">>", "~", "<>", "'", "^+", "^*", "^#", "=>", "<=>", "~>", "-+->", "\\",
    "/\\", "\\/", "-", "+", "*", "/", "^", "|", "||", "&", "&&", "++", "--", "**", "//", "^^", "|-", "|=", "-|", "=|", "<:",
    ":>", ":=", "::=", "(+)", "(-)", "(.)", "(/)", "(\\X)", "=", "#", "/=", "<", ">", "=<", "<=", ">=", ":", "->", "|->", "<-",
    "==", "[]", "..", "...", "$", "$$", "?", "??", "%", "%%", "##", "@@", "!!", "!", ";", ",", ".", "-.", "@",
];

/// Operators written as a backslash and letters
const BS_SYMBOLS: &[&str] = &[
    "A", "forall", "E", "exists", "AA", "EE", "lnot", "neg", "cdot", "equiv", "subseteq", "subset", "supset", "supseteq", "ll",
    "gg", "cap", "intersect", "cup", "union", "land", "lor", "X", "oplus", "ominus", "odot", "oslash", "otimes", "uplus",
    "sqcap", "sqcup", "div", "star", "o", "circ", "bigcirc", "bullet", "in", "notin", "prec", "succ", "preceq", "succeq",
    "sim", "simeq", "approx", "doteq", "asymp", "sqsubset", "sqsupset", "sqsubseteq", "sqsupseteq", "propto", "times", "leq",
    "geq", "mod", "wr", "cong",
];

fn is_symbol(s: &str) -> bool {
    SYMBOLS.contains(&s) || s.strip_prefix('\\').is_some_and(|r| BS_SYMBOLS.contains(&r))
}

fn is_symbol_prefix(s: &str) -> bool {
    SYMBOLS.iter().any(|x| x.starts_with(s)) || s.strip_prefix('\\').is_some_and(|r| BS_SYMBOLS.iter().any(|x| x.starts_with(r)))
}

fn is_letter(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

/// A token of the algorithm's text, with its line
#[derive(Clone, Debug)]
struct LexTok {
    s: String,
    string: bool,
    line: usize,
}

/// Reads tokens from the text after `--algorithm` on demand, as TLC's tokenizer does (the text
/// beyond the algorithm may not be PlusCal, so it is never read ahead)
struct Lexer {
    chars: Vec<Vec<char>>,
    line: usize,
    col: usize,
    buf: Vec<LexTok>,
}

impl Lexer {
    fn peek_char(&self) -> Option<char> {
        let l = self.chars.get(self.line)?;
        Some(if self.col < l.len() { l[self.col] } else { '\n' })
    }

    fn bump(&mut self) {
        if self.col < self.chars[self.line].len() {
            self.col += 1;
        } else {
            self.line += 1;
            self.col = 0;
        }
    }

    fn char_at(&self, off: usize) -> Option<char> {
        let l = self.chars.get(self.line)?;
        let i = self.col + off;
        if i < l.len() {
            Some(l[i])
        } else if i == l.len() {
            Some('\n')
        } else {
            None
        }
    }

    fn next_raw(&mut self) -> Result<Option<LexTok>, String> {
        loop {
            let Some(c) = self.peek_char() else { return Ok(None) };
            if c == ' ' || c == '\n' {
                self.bump();
                continue;
            }
            // Comments are gone before the end of the algorithm; skip any after it
            if c == '\\' && self.char_at(1) == Some('*') {
                self.col = self.chars[self.line].len();
                continue;
            }
            if c == '(' && self.char_at(1) == Some('*') {
                let mut depth = 0;
                loop {
                    let Some(c) = self.peek_char() else { return Ok(None) };
                    if c == '(' && self.char_at(1) == Some('*') {
                        depth += 1;
                        self.bump();
                    } else if c == '*' && self.char_at(1) == Some(')') {
                        depth -= 1;
                        self.bump();
                        if depth == 0 {
                            self.bump();
                            break;
                        }
                    }
                    self.bump();
                }
                continue;
            }
            let line = self.line;
            let l = &self.chars[self.line];
            let start = self.col;
            let take = |n: usize| l[start..start + n].iter().collect::<String>();
            let len_while = |from: usize, f: &dyn Fn(char) -> bool| {
                let mut n = from;
                while start + n < l.len() && f(l[start + n]) {
                    n += 1;
                }
                n
            };
            let (s, string, n) = if is_letter(c) {
                // WF_ and SF_ end at their underscore
                let n = len_while(0, &|c| is_letter(c) || c.is_ascii_digit());
                let n = if n > 3 && (take(3) == "WF_" || take(3) == "SF_") { 3 } else { n };
                (take(n), false, n)
            } else if c.is_ascii_digit() {
                let n = len_while(0, &|c| c.is_ascii_digit());
                let n = if start + n < l.len() && is_letter(l[start + n]) { len_while(n, &|c| is_letter(c) || c.is_ascii_digit()) } else { n };
                (take(n), false, n)
            } else if c == '"' {
                let mut n = 1;
                loop {
                    let Some(&d) = l.get(start + n) else { return Err("an unterminated string".into()) };
                    if d == '\\' {
                        n += 2;
                    } else if d == '"' {
                        break;
                    } else {
                        n += 1;
                    }
                }
                let body: String = l[start + 1..start + n].iter().collect();
                (body, true, n + 1)
            } else if c == '\\' && matches!(self.char_at(1), Some('b' | 'B' | 'o' | 'O' | 'h' | 'H')) && self.char_at(2).is_some_and(|d| d.is_ascii_digit()) {
                let n = len_while(2, &|c| c.is_ascii_digit());
                (take(n), false, n)
            } else if c == '\\' && self.char_at(1).is_some_and(|d| d.is_ascii_alphabetic()) {
                let n = len_while(1, &|c| c.is_ascii_alphabetic());
                let s = take(n);
                if !is_symbol(&s) {
                    return Err(format!("an unknown operator {s}"));
                }
                (s, false, n)
            } else if c == '-' && take_n(l, start, 4) == "----" {
                return Err("a line of dashes".into());
            } else if c == '=' && take_n(l, start, 4) == "====" {
                return Err("a line of `=`".into());
            } else {
                // The longest symbol, as the tokenizer extends a symbol while it is a prefix of one
                let mut n = 0;
                while start + n < l.len() && is_symbol_prefix(&take(n + 1)) {
                    n += 1;
                }
                while n > 0 && !is_symbol(&take(n)) {
                    n -= 1;
                }
                if n == 0 {
                    return Err(format!("an unexpected character `{c}`"));
                }
                (take(n), false, n)
            };
            self.col += n;
            return Ok(Some(LexTok { s, string, line }));
        }
    }

    fn peek(&mut self, k: usize) -> Result<Option<&LexTok>, String> {
        while self.buf.len() <= k {
            match self.next_raw()? {
                Some(t) => self.buf.push(t),
                None => return Ok(None),
            }
        }
        Ok(self.buf.get(k))
    }

    fn next(&mut self) -> Result<LexTok, String> {
        self.peek(0)?;
        if self.buf.is_empty() {
            return Err("the algorithm ends early".into());
        }
        Ok(self.buf.remove(0))
    }
}

fn take_n(l: &[char], start: usize, n: usize) -> String {
    l[start..(start + n).min(l.len())].iter().collect()
}

/// Comments in the algorithm become spaces, from (line, col) to the `*)` that closes the comment
/// holding the algorithm
fn uncomment(lines: &mut [String], line0: usize, col0: usize) -> Result<(), String> {
    let mut depth = 0;
    for (li, line) in lines.iter_mut().enumerate().skip(line0) {
        let old: Vec<char> = line.chars().collect();
        let mut col = if li == line0 { col0 } else { 0 };
        let mut out: String = if li == line0 { old[..col].iter().collect() } else { String::new() };
        let mut in_string = false;
        let mut done = false;
        while col < old.len() {
            let c = old[col];
            let next = old.get(col + 1).copied();
            if c == '(' && !in_string && next == Some('*') {
                depth += 1;
                out.push_str("  ");
                col += 2;
                continue;
            }
            if c == '*' && !in_string && next == Some(')') {
                if depth == 0 {
                    out.push_str("*)");
                    col += 2;
                    done = true;
                    break;
                }
                depth -= 1;
                out.push_str("  ");
                col += 2;
                continue;
            }
            if depth == 0 {
                if in_string {
                    if c == '"' {
                        in_string = false;
                    } else if c == '\\' && next.is_some() {
                        out.push(c);
                        out.push(next.unwrap());
                        col += 2;
                        continue;
                    }
                    out.push(c);
                } else if c == '\\' && next == Some('*') {
                    out.push(' ');
                    col = old.len();
                    continue;
                } else {
                    if c == '"' {
                        in_string = true;
                    }
                    out.push(c);
                }
            } else {
                out.push(' ');
            }
            col += 1;
        }
        if in_string {
            return Err("an unterminated string".into());
        }
        if done {
            out.extend(&old[col..]);
            *line = out;
            return Ok(());
        }
        *line = out;
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// Parsing

/// The words that end an expression in PlusCal
const DELIMITERS: &[&str] = &[
    ";", "do", "then", ":=", "begin", "variable", "variables", "||", "end", "else", "elsif", "if", "either", "or", "while",
    "with", "call", "return", "goto", "print", "assert", "skip", "procedure", "define", "process", "fair",
];

struct Parser {
    lx: Lexer,
    c_syntax: bool,
    plus: Vec<String>,
    minus: Vec<String>,
    goto_used: bool,
    goto_done: bool,
    omit_pc: bool,
}

type R<T> = Result<T, String>;

impl Parser {
    fn peek(&mut self, k: usize) -> R<String> {
        Ok(self.lx.peek(k)?.map(|t| t.s.clone()).unwrap_or_default())
    }

    fn tok(&mut self) -> R<String> {
        Ok(self.lx.next()?.s)
    }

    fn must(&mut self, s: &str) -> R<()> {
        let t = self.tok()?;
        if t != s {
            return Err(format!("expected `{s}`, found `{t}`"));
        }
        Ok(())
    }

    /// TLC's GobbleThis: a `;` may be left out before the words that end a statement
    fn gobble(&mut self, s: &str) -> R<()> {
        if s == ";" {
            let n = self.peek(0)?;
            if ["end", "begin", "else", "elsif", "or", "do", "macro", "procedure", "process", "fair", "define", "}", "{"].contains(&n.as_str()) {
                return Ok(());
            }
        }
        self.must(s)
    }

    fn comma_or_semi(&mut self) -> R<()> {
        if self.peek(0)? == "," {
            self.must(",")
        } else {
            self.gobble(";")
        }
    }

    fn eq_or_in(&mut self) -> R<bool> {
        match self.tok()?.as_str() {
            "=" => Ok(true),
            "\\in" => Ok(false),
            t => Err(format!("expected `=` or `\\in`, found `{t}`")),
        }
    }

    /// An expression: the tokens up to the word or unmatched bracket or comma that ends it
    fn expr(&mut self) -> R<Expr> {
        let mut toks: Vec<LexTok> = vec![];
        let mut depth = 0i32;
        let mut quant = false;
        let mut prev = " ".to_string();
        loop {
            let Some(t) = self.lx.peek(0)? else { break };
            let t = t.clone();
            if !t.string {
                let ident = t.s.starts_with(is_letter);
                let delim = DELIMITERS.contains(&t.s.as_str()) && !(ident && [".", "[", ","].contains(&prev.as_str()));
                let closer = ((t.s == "," && !quant) || t.s == ")" || t.s == "}") && depth == 0;
                if delim || closer {
                    if depth != 0 {
                        return Err("an expression with an unmatched bracket".into());
                    }
                    if quant {
                        return Err("a quantifier without `:`".into());
                    }
                    break;
                }
                if ["(", "[", "{", "<<"].contains(&t.s.as_str()) {
                    depth += 1;
                }
                if [")", "}", "]", ">>", ">>_", "]_"].contains(&t.s.as_str()) {
                    depth -= 1;
                    if depth < 0 {
                        return Err("an unmatched closing bracket".into());
                    }
                }
                if (t.s == "\\A" || t.s == "\\E") && depth == 0 {
                    quant = true;
                }
                if quant && t.s == ":" && depth == 0 {
                    quant = false;
                }
                prev = t.s.clone();
            } else {
                prev = " ".into();
            }
            self.lx.next()?;
            toks.push(t);
        }
        let mut e: Expr = vec![];
        if let Some(first) = toks.first().map(|t| t.line) {
            let last = toks.last().unwrap().line;
            e = vec![vec![]; last - first + 1];
            for t in toks {
                e[t.line - first].push(Tok { s: t.s, string: t.string });
            }
        }
        Ok(e)
    }

    fn label(&mut self) -> R<String> {
        let t = self.peek(0)?;
        const NOT: &[&str] = &[
            "while", "if", "assert", "print", "else", "elsif", "either", "or", "end", "with", "when", "await", "skip", "call",
            "return", "goto",
        ];
        if NOT.contains(&t.as_str()) || self.peek(1)? != ":" {
            return Ok(String::new());
        }
        let l = self.tok()?;
        if l == "Done" || l == "Error" {
            return Err(format!("the label {l}"));
        }
        self.must(":")?;
        if self.peek(0)? == "+" {
            self.must("+")?;
            self.plus.push(l.clone());
            self.omit_pc = false;
        } else if self.peek(0)? == "-" {
            self.must("-")?;
            self.minus.push(l.clone());
            self.omit_pc = false;
        }
        Ok(l)
    }

    fn stmt_seq(&mut self) -> R<Vec<Stmt>> {
        let mut out = vec![];
        loop {
            let t = self.peek(0)?;
            if t.is_empty() {
                return Err("the algorithm ends early".into());
            }
            if (!self.c_syntax && ["end", "else", "elsif", "or"].contains(&t.as_str())) || (self.c_syntax && t == "}") {
                break;
            }
            let l = self.label()?;
            if self.c_syntax && self.peek(0)? == "{" {
                out.extend(self.c_block(l)?);
            } else {
                let mut s = self.stmt()?;
                s.lbl = l;
                out.push(s);
            }
        }
        if self.c_syntax && out.is_empty() {
            return Err("an empty statement list".into());
        }
        Ok(out)
    }

    fn c_block(&mut self, l: String) -> R<Vec<Stmt>> {
        self.must("{")?;
        let mut s = self.stmt_seq()?;
        self.gobble("}")?;
        self.gobble(";")?;
        if !l.is_empty() {
            if !s[0].lbl.is_empty() {
                return Err("a statement labeled twice".into());
            }
            s[0].lbl = l;
        }
        Ok(s)
    }

    fn c_stmt(&mut self) -> R<Vec<Stmt>> {
        let l = self.label()?;
        if self.peek(0)? == "{" {
            return self.c_block(l);
        }
        let mut s = self.stmt()?;
        s.lbl = l;
        Ok(vec![s])
    }

    fn stmt(&mut self) -> R<Stmt> {
        let t = self.peek(0)?;
        let k = match t.as_str() {
            "if" => self.if_stmt(0)?,
            "either" => self.either()?,
            "with" => self.with(0)?,
            "when" | "await" => {
                self.tok()?;
                let e = self.expr()?;
                if e.is_empty() {
                    return Err("an empty expression".into());
                }
                self.gobble(";")?;
                Kind::When(e)
            }
            "print" | "assert" => {
                self.tok()?;
                let e = self.expr()?;
                if e.is_empty() {
                    return Err("an empty expression".into());
                }
                self.gobble(";")?;
                if t == "print" {
                    Kind::Print(e)
                } else {
                    Kind::Assert(e)
                }
            }
            "skip" => {
                self.tok()?;
                self.gobble(";")?;
                Kind::Skip
            }
            "goto" => {
                self.tok()?;
                let to = self.tok()?;
                self.goto_used = true;
                if to == "Done" {
                    self.goto_done = true;
                }
                self.gobble(";")?;
                Kind::Goto(to)
            }
            "while" => self.while_stmt()?,
            "call" | "return" => return Err("a procedure call or return".into()),
            _ => {
                if self.peek(1)? == "(" {
                    return Err("a macro call".into());
                }
                let mut ass = vec![self.single_assign()?];
                while self.peek(0)? == "||" {
                    self.tok()?;
                    ass.push(self.single_assign()?);
                }
                self.gobble(";")?;
                Kind::Assign(ass)
            }
        };
        Ok(Stmt { lbl: String::new(), k })
    }

    fn single_assign(&mut self) -> R<(String, Expr, Expr)> {
        let var = self.tok()?;
        let sub = self.expr()?;
        self.gobble(":=")?;
        let rhs = self.expr()?;
        if rhs.is_empty() {
            return Err("an empty right-hand side".into());
        }
        Ok((var, sub, rhs))
    }

    fn while_stmt(&mut self) -> R<Kind> {
        self.must("while")?;
        if self.c_syntax {
            self.gobble("(")?;
        }
        let test = self.expr()?;
        if self.c_syntax {
            self.gobble(")")?;
        }
        if test.is_empty() {
            return Err("an empty while test".into());
        }
        let unlab = if !self.c_syntax {
            self.gobble("do")?;
            let s = self.stmt_seq()?;
            self.gobble("end")?;
            self.gobble("while")?;
            self.gobble(";")?;
            s
        } else {
            self.c_stmt()?
        };
        if unlab.is_empty() {
            return Err("a while without a body".into());
        }
        Ok(Kind::While { test, unlab, lab: vec![] })
    }

    fn if_stmt(&mut self, depth: usize) -> R<Kind> {
        self.must(if depth == 0 { "if" } else { "elsif" })?;
        if self.c_syntax {
            self.gobble("(")?;
        }
        let test = self.expr()?;
        if self.c_syntax {
            self.gobble(")")?;
        }
        if test.is_empty() {
            return Err("an empty if test".into());
        }
        let unlab_then;
        let unlab_else;
        if !self.c_syntax {
            self.gobble("then")?;
            unlab_then = self.stmt_seq()?;
            let n = self.peek(0)?;
            unlab_else = match n.as_str() {
                "else" => {
                    self.must("else")?;
                    self.stmt_seq()?
                }
                "elsif" => vec![Stmt { lbl: String::new(), k: self.if_stmt(depth + 1)? }],
                "end" => vec![],
                _ => return Err(format!("expected else, elsif or end, found `{n}`")),
            };
            if depth == 0 {
                self.gobble("end")?;
                self.gobble("if")?;
                self.gobble(";")?;
            }
        } else {
            unlab_then = self.c_stmt()?;
            unlab_else = if self.peek(0)? == "else" {
                self.must("else")?;
                self.c_stmt()?
            } else {
                vec![]
            };
        }
        Ok(Kind::LabelIf { test, unlab_then, lab_then: vec![], unlab_else, lab_else: vec![] })
    }

    fn either(&mut self) -> R<Kind> {
        self.must("either")?;
        let mut clauses = vec![];
        loop {
            let unlab = if !self.c_syntax { self.stmt_seq()? } else { self.c_stmt()? };
            if unlab.is_empty() {
                return Err("an empty or clause".into());
            }
            clauses.push(Clause { unlab, lab: vec![] });
            if self.peek(0)? == "or" {
                self.must("or")?;
            } else {
                break;
            }
        }
        if !self.c_syntax {
            self.must("end")?;
            self.gobble("either")?;
            self.gobble(";")?;
        }
        if clauses.len() < 2 {
            return Err("an either without or".into());
        }
        Ok(Kind::LabelEither(clauses))
    }

    fn with(&mut self, depth: usize) -> R<Kind> {
        if depth == 0 {
            self.gobble("with")?;
            if self.c_syntax {
                self.gobble("(")?;
            }
        }
        let var = self.tok()?;
        let eq = self.eq_or_in()?;
        let exp = self.expr()?;
        if !self.c_syntax || self.peek(0)? != ")" {
            self.comma_or_semi()?;
        }
        if exp.is_empty() {
            return Err("an empty with expression".into());
        }
        let body = if !self.c_syntax && self.peek(0)? == "do" {
            self.gobble("do")?;
            let s = self.stmt_seq()?;
            self.gobble("end")?;
            self.gobble("with")?;
            self.gobble(";")?;
            s
        } else if self.c_syntax && self.peek(0)? == ")" {
            self.must(")")?;
            self.c_stmt()?
        } else {
            vec![Stmt { lbl: String::new(), k: self.with(depth + 1)? }]
        };
        if body.is_empty() {
            return Err("a with without a body".into());
        }
        Ok(Kind::With { var, eq, exp, body })
    }

    fn var_decls(&mut self) -> R<Vec<VarDecl>> {
        let t = self.tok()?;
        if t != "variables" && t != "variable" {
            return Err(format!("expected variables, found `{t}`"));
        }
        let mut out = vec![];
        while !["begin", "{", "procedure", "process", "fair", "define", "macro"].contains(&self.peek(0)?.as_str()) {
            let var = self.tok()?;
            let n = self.peek(0)?;
            // A variable declared without a value starts as `defaultInitValue`
            let (mut eq, mut val) = (true, vec![vec![Tok { s: "defaultInitValue".into(), string: false }]]);
            if n == "=" || n == "\\in" {
                eq = self.eq_or_in()?;
                val = self.expr()?;
                if val.is_empty() {
                    return Err("a missing expression".into());
                }
            }
            self.comma_or_semi()?;
            out.push(VarDecl { var, eq, val });
        }
        Ok(out)
    }

    fn process(&mut self, fairness: &'static str) -> R<Process> {
        self.must("process")?;
        if self.c_syntax {
            self.gobble("(")?;
        }
        let name = self.tok()?;
        let eq = self.eq_or_in()?;
        let id = self.expr()?;
        self.plus.clear();
        self.minus.clear();
        if self.c_syntax {
            self.gobble(")")?;
        }
        if id.is_empty() {
            return Err("an empty process id".into());
        }
        let decls = if ["begin", "{"].contains(&self.peek(0)?.as_str()) { vec![] } else { self.var_decls()? };
        if self.c_syntax {
            self.gobble("{")?;
        } else {
            self.gobble("begin")?;
        }
        let body = self.stmt_seq()?;
        if self.c_syntax {
            self.gobble("}")?;
        } else {
            self.gobble("end")?;
            self.gobble("process")?;
        }
        if self.peek(0)? == ";" {
            self.tok()?;
        }
        let body = make_labeled(body)?;
        Ok(Process { name, fairness, eq, id, decls, plus: self.plus.clone(), minus: self.minus.clone(), body })
    }
}

// ---------------------------------------------------------------------------------------------
// Labeled steps

/// A statement sequence, each label starting a step, as labeled statements
fn make_labeled(seq: Vec<Stmt>) -> R<Vec<Labeled>> {
    if seq.first().is_some_and(|s| s.lbl.is_empty()) {
        return Err("a statement that needs a label has none (TLC would add labels)".into());
    }
    let mut v = inner_make_labeled(seq);
    for l in &mut v {
        classify_seq(&mut l.stmts)?;
    }
    Ok(v)
}

fn inner_make_labeled(seq: Vec<Stmt>) -> Vec<Labeled> {
    let mut out: Vec<Labeled> = vec![];
    for s in seq {
        if !s.lbl.is_empty() || out.is_empty() {
            out.push(Labeled { label: s.lbl.clone(), stmts: vec![] });
        }
        out.last_mut().unwrap().stmts.push(s);
    }
    for l in &mut out {
        fix_seq(&mut l.stmts);
    }
    out
}

/// The unlabeled statements at the start of v, and the rest as labeled statements
fn split_labeled(v: Vec<Stmt>) -> (Vec<Stmt>, Vec<Labeled>) {
    let n = v.iter().position(|s| !s.lbl.is_empty()).unwrap_or(v.len());
    let mut unlab = v;
    let rest = unlab.split_off(n);
    fix_seq(&mut unlab);
    (unlab, inner_make_labeled(rest))
}

fn fix_seq(seq: &mut [Stmt]) {
    for s in seq {
        match &mut s.k {
            Kind::LabelIf { unlab_then, lab_then, unlab_else, lab_else, .. } => {
                (*unlab_then, *lab_then) = split_labeled(std::mem::take(unlab_then));
                (*unlab_else, *lab_else) = split_labeled(std::mem::take(unlab_else));
            }
            Kind::LabelEither(clauses) => {
                for c in clauses {
                    (c.unlab, c.lab) = split_labeled(std::mem::take(&mut c.unlab));
                }
            }
            Kind::While { unlab, lab, .. } => {
                (*unlab, *lab) = split_labeled(std::mem::take(unlab));
            }
            _ => {}
        }
    }
}

/// TLC's ClassifyStmtSeq: an if or either without labels inside becomes a plain one. Returns 2
/// when the last statement has a label inside, 1 when it ends in a goto
fn classify_seq(seq: &mut [Stmt]) -> R<u8> {
    let mut result = 0;
    let n = seq.len();
    for (i, s) in seq.iter_mut().enumerate() {
        match &mut s.k {
            Kind::LabelIf { test, unlab_then, lab_then, unlab_else, lab_else } => {
                let tc = classify_seq(unlab_then)?;
                for l in lab_then.iter_mut() {
                    classify_seq(&mut l.stmts)?;
                }
                let ec = classify_seq(unlab_else)?;
                for l in lab_else.iter_mut() {
                    classify_seq(&mut l.stmts)?;
                }
                result = if !lab_then.is_empty() || !lab_else.is_empty() || tc == 2 || ec == 2 {
                    2
                } else if tc + ec > 0 {
                    1
                } else {
                    0
                };
                if result < 2 {
                    s.k = Kind::If { test: std::mem::take(test), then: std::mem::take(unlab_then), els: std::mem::take(unlab_else) };
                }
            }
            Kind::LabelEither(clauses) => {
                let mut c = 0;
                for cl in clauses.iter_mut() {
                    c = c.max(classify_seq(&mut cl.unlab)?);
                    if !cl.lab.is_empty() {
                        c = 2;
                        for l in cl.lab.iter_mut() {
                            classify_seq(&mut l.stmts)?;
                        }
                    }
                }
                result = c;
                if result < 2 {
                    s.k = Kind::Either(clauses.iter_mut().map(|c| std::mem::take(&mut c.unlab)).collect());
                }
            }
            Kind::With { body, .. } => {
                result = classify_seq(body)?;
                if result == 2 {
                    return Err("a with statement with a label inside".into());
                }
            }
            Kind::While { unlab, lab, .. } => {
                classify_seq(unlab)?;
                for l in lab.iter_mut() {
                    classify_seq(&mut l.stmts)?;
                }
            }
            Kind::Goto(_) => result = 1,
            _ => {}
        }
        if result > 0 && i + 1 < n {
            return Err("a statement that needs a label has none".into());
        }
    }
    Ok(result)
}

/// TLC's check of a process body (or the algorithm's) for whether the translation can do
/// without `pc`
fn check_body(body: &[Labeled], omit_pc: &mut bool) {
    if body.is_empty() {
        return;
    }
    if body.len() > 1 {
        *omit_pc = false;
        return;
    }
    let stmts = &body[0].stmts;
    if stmts.is_empty() {
        return;
    }
    let Kind::While { test, unlab, lab } = &stmts[0].k else {
        *omit_pc = false;
        return;
    };
    if stmts.len() > 1 || !(test.len() == 1 && test[0].len() == 1 && test[0][0].s == "TRUE") {
        *omit_pc = false;
        return;
    }
    if !lab.is_empty() || unlab.iter().any(|s| matches!(s.k, Kind::LabelIf { .. } | Kind::LabelEither(_))) {
        *omit_pc = false;
    }
}

/// The labels of a body, also those inside its statements
fn labels(body: &[Labeled], out: &mut Vec<String>) {
    fn stmts(v: &[Stmt], out: &mut Vec<String>) {
        for s in v {
            match &s.k {
                Kind::LabelIf { unlab_then, lab_then, unlab_else, lab_else, .. } => {
                    stmts(unlab_then, out);
                    labels(lab_then, out);
                    stmts(unlab_else, out);
                    labels(lab_else, out);
                }
                Kind::LabelEither(cs) => {
                    for c in cs {
                        stmts(&c.unlab, out);
                        labels(&c.lab, out);
                    }
                }
                Kind::While { unlab, lab, .. } => {
                    stmts(unlab, out);
                    labels(lab, out);
                }
                _ => {}
            }
        }
    }
    for l in body {
        out.push(l.label.clone());
        stmts(&l.stmts, out);
    }
}

/// Whether two of the algorithm's names are equal (variables, processes, labels), which the
/// translator resolves by renaming one, and tla2rs does not follow
fn has_clash(names: &[String]) -> bool {
    let mut v: Vec<&String> = names.iter().collect();
    v.sort();
    v.windows(2).any(|w| w[0] == w[1])
}

// ---------------------------------------------------------------------------------------------
// Expanding the steps
//
// TLC builds the expanded steps as a new tree, but on the way it changes parts of the tree it
// parsed, which is the tree it prints: the statement lists it does not copy get `pc := "..."`
// appended, and a last `goto`, labeled if or labeled either in them is replaced. The lists of a
// labeled statement, and the body of a while at its start, are copied first, so only what they
// hold changes. `own` says whether the list itself changes.

fn update_pc(next: &str) -> Stmt {
    Stmt { lbl: String::new(), k: Kind::Assign(vec![("pc".into(), vec![], vec![vec![Tok { s: next.into(), string: true }]])]) }
}

/// Expands the last statement of `stmts`; whether control still has to go to `next`
fn explode_last(stmts: &mut Vec<Stmt>, next: &str, own: bool, omit_pc: bool) -> bool {
    let mut needs = true;
    if let Some(last) = stmts.last_mut() {
        let mut replace = None;
        needs = false;
        match &mut last.k {
            Kind::LabelIf { test, unlab_then, lab_then, unlab_else, lab_else } => {
                let nt = lab_then.first().map(|l| l.label.clone()).unwrap_or(next.into());
                let ne = lab_else.first().map(|l| l.label.clone()).unwrap_or(next.into());
                let then = explode_last_goto(unlab_then, &nt, true, omit_pc);
                let els = explode_last_goto(unlab_else, &ne, true, omit_pc);
                explode_seq(lab_then, next, omit_pc);
                explode_seq(lab_else, next, omit_pc);
                replace = Some(Kind::If { test: test.clone(), then, els });
            }
            Kind::LabelEither(clauses) => {
                let mut ors = vec![];
                for c in clauses.iter_mut() {
                    let n = c.lab.first().map(|l| l.label.clone()).unwrap_or(next.into());
                    ors.push(explode_last_goto(&mut c.unlab, &n, true, omit_pc));
                    explode_seq(&mut c.lab, next, omit_pc);
                }
                replace = Some(Kind::Either(ors));
            }
            Kind::Goto(to) => replace = Some(update_pc(to).k),
            Kind::If { then, els, .. } => {
                let t = explode_last(then, next, true, omit_pc);
                let e = explode_last(els, next, true, omit_pc);
                if !omit_pc {
                    needs = t && e;
                    if !needs {
                        if t {
                            then.push(update_pc(next));
                        }
                        if e {
                            els.push(update_pc(next));
                        }
                    }
                }
            }
            Kind::Either(ors) => {
                needs = true;
                let v: Vec<bool> = ors.iter_mut().map(|o| explode_last(o, next, true, omit_pc)).collect();
                needs = needs && v.iter().all(|&b| b);
                if !omit_pc && !needs {
                    for (o, &b) in ors.iter_mut().zip(&v) {
                        if b {
                            o.push(update_pc(next));
                        }
                    }
                }
            }
            Kind::With { body, .. } => needs = explode_last(body, next, true, omit_pc),
            _ => needs = true,
        }
        if let Some(k) = replace {
            if own {
                last.k = k;
            }
        }
    }
    needs && !omit_pc
}

/// As explode_last, then adds `pc := next` if control still has to go there, and returns the
/// expanded list. TLC expands an empty list into a new one, so the `pc` it adds there does not
/// show in the tree it prints
fn explode_last_goto(stmts: &mut Vec<Stmt>, next: &str, own: bool, omit_pc: bool) -> Vec<Stmt> {
    let empty = stmts.is_empty();
    if !explode_last(stmts, next, own, omit_pc) {
        return stmts.clone();
    }
    if own && !empty {
        stmts.push(update_pc(next));
        return stmts.clone();
    }
    let mut v = stmts.clone();
    v.push(update_pc(next));
    v
}

fn explode_labeled(l: &mut Labeled, next: &str, omit_pc: bool) {
    let label = l.label.clone();
    if let Some(Stmt { k: Kind::While { unlab, lab, .. }, .. }) = l.stmts.first_mut() {
        let first = lab.first().map(|x| x.label.clone()).unwrap_or(label.clone());
        explode_last(unlab, &first, false, omit_pc);
        let n = lab.len();
        for i in 0..n {
            let nl = if i + 1 < n { lab[i + 1].label.clone() } else { label.clone() };
            explode_labeled(&mut lab[i], &nl, omit_pc);
        }
        let mut rest = l.stmts.split_off(1);
        explode_last(&mut rest, next, false, omit_pc);
        l.stmts.extend(rest);
        return;
    }
    explode_last(&mut l.stmts, next, false, omit_pc);
}

fn explode_seq(seq: &mut [Labeled], next: &str, omit_pc: bool) {
    let n = seq.len();
    for i in 0..n {
        let nl = if i + 1 < n { seq[i + 1].label.clone() } else { next.to_string() };
        explode_labeled(&mut seq[i], &nl, omit_pc);
    }
}

// ---------------------------------------------------------------------------------------------
// Printing, as the translator prints its tree: each field is indented by the width of the text
// before it, whatever the actual column

struct Printer {
    out: String,
    stack: Vec<usize>,
}

impl Printer {
    fn s(&mut self, s: &str) {
        self.out.push_str(s);
    }
    fn indent(&mut self, s: &str) {
        let top = *self.stack.last().unwrap();
        self.stack.push(top + s.chars().count());
        self.out.push_str(s);
    }
    fn end(&mut self) {
        self.stack.pop();
    }
    fn nl(&mut self) {
        let n = *self.stack.last().unwrap();
        self.out.push('\n');
        self.out.extend(std::iter::repeat_n(' ', n));
    }
    fn expr(&mut self, e: &Expr) {
        self.s("<< ");
        let mut nonempty = false;
        for (i, line) in e.iter().enumerate() {
            if i > 0 {
                self.s("\n");
            }
            for t in line {
                if nonempty {
                    self.s(", ");
                }
                nonempty = true;
                if t.string {
                    self.s(&format!("\"\\\"\", \"{}\", \"\\\"\"", t.s));
                } else if t.s.starts_with('\\') {
                    self.s(&format!("\"\\{}\"", t.s));
                } else if t.s == "/\\" {
                    self.s("\"/\\\\\"");
                } else {
                    self.s(&format!("\"{}\"", t.s));
                }
            }
        }
        self.s(" >>");
    }
    fn seq<T>(&mut self, v: &[T], f: fn(&mut Printer, &T)) {
        self.indent("<<");
        for (i, x) in v.iter().enumerate() {
            if i > 0 {
                self.s(", ");
                self.nl();
            }
            f(self, x);
        }
        self.s(">>");
        self.end();
    }
    fn quoted(&mut self, v: &[String]) {
        self.indent("<<");
        self.s(&v.iter().map(|x| format!("\"{x}\"")).collect::<Vec<_>>().join(", "));
        self.s(">>");
        self.end();
    }
    fn eq_in(&mut self, eq: bool) {
        self.s(if eq { "\"=\"" } else { "\"\\\\in\"" });
    }
    fn field_seq<T>(&mut self, name: &str, v: &[T], f: fn(&mut Printer, &T), close: &str) {
        self.indent(name);
        self.seq(v, f);
        self.s(close);
        self.end();
    }
    fn var_decl(&mut self, d: &VarDecl) {
        self.indent("");
        self.s(&format!("[var |-> \"{}\", eqOrIn |-> ", d.var));
        self.eq_in(d.eq);
        self.s(", val |-> ");
        self.expr(&d.val);
        self.s("]");
        self.end();
    }
    fn labeled(&mut self, l: &Labeled) {
        self.indent("");
        self.s(&format!("[label |-> \"{}\",", l.label));
        self.nl();
        self.field_seq(" stmts |-> ", &l.stmts, Printer::stmt, "]");
        self.end();
    }
    fn clause(&mut self, c: &Clause) {
        self.indent("");
        self.field_seq("[unlabOr |-> ", &c.unlab, Printer::stmt, ",");
        self.nl();
        self.field_seq(" labOr   |-> ", &c.lab, Printer::labeled, "]");
        self.nl();
        self.end();
    }
    fn stmt(&mut self, s: &Stmt) {
        match &s.k {
            Kind::Skip => return self.s("[type |-> \"skip\"]"),
            Kind::Goto(to) => return self.s(&format!("[type |-> \"goto\",  to |-> \"{to}\"]")),
            _ => {}
        }
        self.indent("");
        match &s.k {
            Kind::While { test, unlab, lab } => {
                self.s("[type    |-> \"while\", ");
                self.nl();
                self.s(" test    |-> ");
                self.expr(test);
                self.s(",");
                self.nl();
                self.field_seq(" labDo   |-> ", lab, Printer::labeled, ",");
                self.nl();
                self.field_seq(" unlabDo |-> ", unlab, Printer::stmt, "]");
            }
            Kind::Assign(ass) => {
                self.s("[type |-> \"assignment\",");
                self.nl();
                self.field_seq(" ass  |-> ", ass, Printer::single_assign, "]");
            }
            Kind::If { test, then, els } => {
                self.s("[type    |-> \"if\", ");
                self.nl();
                self.s(" test    |-> ");
                self.expr(test);
                self.s(",");
                self.nl();
                self.field_seq(" then |-> ", then, Printer::stmt, ",");
                self.nl();
                self.field_seq(" else |-> ", els, Printer::stmt, "]");
            }
            Kind::Either(ors) => {
                self.s("[type |-> \"either\", ");
                self.nl();
                self.indent(" ors  |-> ");
                self.indent("<< ");
                for (i, o) in ors.iter().enumerate() {
                    if i > 0 {
                        self.s(", ");
                        self.nl();
                    }
                    self.seq(o, Printer::stmt);
                }
                self.s(" >>");
                self.end();
                self.s("]");
                self.end();
            }
            Kind::With { var, eq, exp, body } => {
                self.s("[type   |-> \"with\", ");
                self.nl();
                self.s(&format!(" var    |-> \"{var}\","));
                self.nl();
                self.s(" eqOrIn |-> ");
                self.eq_in(*eq);
                self.s(",");
                self.nl();
                self.s(" exp    |-> ");
                self.expr(exp);
                self.s(",");
                self.nl();
                self.field_seq(" do     |-> ", body, Printer::stmt, "]");
            }
            Kind::When(e) | Kind::Print(e) | Kind::Assert(e) => {
                let t = match &s.k {
                    Kind::When(_) => "when",
                    Kind::Print(_) => "print",
                    _ => "assert",
                };
                self.s(&format!("[type |-> \"{t}\", "));
                self.nl();
                self.s(" exp |-> ");
                self.expr(e);
                self.s("]");
            }
            Kind::LabelIf { test, unlab_then, lab_then, unlab_else, lab_else } => {
                self.s("[type      |-> \"labelIf\",");
                self.nl();
                self.s(" test      |-> ");
                self.expr(test);
                self.s(",");
                self.nl();
                self.field_seq(" unlabThen |-> ", unlab_then, Printer::stmt, ",");
                self.nl();
                self.field_seq(" labThen   |-> ", lab_then, Printer::labeled, ",");
                self.nl();
                self.field_seq(" unlabElse |-> ", unlab_else, Printer::stmt, ",");
                self.nl();
                self.field_seq(" labElse   |-> ", lab_else, Printer::labeled, "]");
                self.nl();
            }
            Kind::LabelEither(clauses) => {
                self.s("[type    |-> \"labelEither\",");
                self.nl();
                self.field_seq(" clauses |-> ", clauses, Printer::clause, "]");
                self.nl();
            }
            Kind::Skip | Kind::Goto(_) => unreachable!(),
        }
        self.end();
    }
    fn single_assign(&mut self, a: &(String, Expr, Expr)) {
        self.indent("");
        self.s(&format!("[lhs |-> [var |-> \"{}\", sub |-> ", a.0));
        self.expr(&a.1);
        self.s("],");
        self.nl();
        self.s(" rhs |-> ");
        self.expr(&a.2);
        self.s("]");
        self.end();
    }
    fn process(&mut self, p: &Process) {
        self.indent("");
        self.s(&format!("[name   |-> \"{}\",", p.name));
        self.nl();
        self.s(&format!(" fairness |-> \"{}\", minusLabels |-> ", p.fairness));
        self.quoted(&p.minus);
        self.s(", plusLabels |->");
        self.quoted(&p.plus);
        self.s(", proceduresCalled |->");
        self.quoted(&[]);
        self.s(",");
        self.nl();
        self.s(" eqOrIn |-> ");
        self.eq_in(p.eq);
        self.s(",");
        self.nl();
        self.s(" id     |-> ");
        self.expr(&p.id);
        self.s(",");
        self.nl();
        self.field_seq(" decls  |-> ", &p.decls, Printer::var_decl, ",");
        self.nl();
        self.field_seq(" body   |-> ", &p.body, Printer::labeled, "]");
        self.end();
    }
}

/// The text TLC hashes for the algorithm that starts at (line, col) of the module's lines
fn tree_text(mut lines: Vec<String>, line: usize, col: usize, fair: bool) -> R<String> {
    uncomment(&mut lines, line, col)?;
    let chars: Vec<Vec<char>> = lines.iter().map(|l| l.chars().collect()).collect();
    let lx = Lexer { chars, line, col, buf: vec![] };
    let mut p = Parser { lx, c_syntax: false, plus: vec![], minus: vec![], goto_used: false, goto_done: false, omit_pc: true };
    // `--fair algorithm` makes every process weakly fair unless it says otherwise
    let default_fairness = if fair {
        p.must("algorithm")?;
        "wf"
    } else {
        "unfair"
    };
    let name = p.tok()?;
    if p.peek(0)? == "{" {
        p.c_syntax = true;
        p.must("{")?;
    }
    let decls = if ["variable", "variables"].contains(&p.peek(0)?.as_str()) { p.var_decls()? } else { vec![] };
    let mut defs = vec![];
    if p.peek(0)? == "define" {
        p.must("define")?;
        if p.c_syntax {
            p.gobble("{")?;
        }
        defs = p.expr()?;
        if p.c_syntax {
            p.gobble("}")?;
        } else {
            p.gobble("end")?;
            p.gobble("define")?;
        }
        p.gobble(";")?;
    }
    if ["macro", "procedure"].contains(&p.peek(0)?.as_str()) {
        return Err("a macro or procedure".into());
    }
    let mut pr = Printer { out: String::new(), stack: vec![0] };
    let multi = p.peek(0)? == "process" || (p.peek(0)? == "fair" && (p.peek(1)? == "process" || (p.peek(1)? == "+" && p.peek(2)? == "process")));
    if multi {
        let mut procs = vec![];
        while ["fair", "process"].contains(&p.peek(0)?.as_str()) {
            let mut fairness = default_fairness;
            if p.peek(0)? == "fair" {
                p.must("fair")?;
                fairness = "wf";
                if p.peek(0)? == "+" {
                    p.must("+")?;
                    fairness = "sf";
                }
            }
            procs.push(p.process(fairness)?);
        }
        if p.c_syntax {
            p.gobble("}")?;
        } else {
            p.gobble("end")?;
            p.gobble("algorithm")?;
        }
        let mut names: Vec<String> = decls.iter().map(|d| d.var.clone()).collect();
        for pr in &procs {
            names.push(pr.name.clone());
            names.extend(pr.decls.iter().map(|d| d.var.clone()));
            labels(&pr.body, &mut names);
        }
        if has_clash(&names) {
            return Err("two of its names are equal, and TLC's translator renames one".into());
        }
        let mut omit_pc = p.omit_pc;
        for pr in &procs {
            check_body(&pr.body, &mut omit_pc);
        }
        if p.goto_done || p.goto_used {
            omit_pc = false;
        }
        for pr in &mut procs {
            explode_seq(&mut pr.body, "Done", omit_pc);
        }
        pr.indent("");
        pr.s("[type    |-> \"multiprocess\", ");
        pr.nl();
        pr.s(&format!(" name  |-> \"{name}\", "));
        pr.nl();
        pr.field_seq(" decls |-> ", &decls, Printer::var_decl, ",");
        pr.nl();
        pr.indent(" defs  |-> ");
        pr.expr(&defs);
        pr.s(",");
        pr.end();
        pr.nl();
        pr.field_seq(" prcds |-> ", &[] as &[Labeled], Printer::labeled, ",");
        pr.nl();
        pr.field_seq(" procs |-> ", &procs, Printer::process, "]");
        pr.end();
    } else {
        if p.c_syntax {
            p.gobble("{")?;
        } else {
            p.gobble("begin")?;
        }
        let body = p.stmt_seq()?;
        if p.c_syntax {
            p.gobble("}")?;
            p.gobble("}")?;
        } else {
            p.gobble("end")?;
            p.gobble("algorithm")?;
        }
        let mut body = make_labeled(body)?;
        let mut names: Vec<String> = decls.iter().map(|d| d.var.clone()).collect();
        labels(&body, &mut names);
        if has_clash(&names) {
            return Err("two of its names are equal, and TLC's translator renames one".into());
        }
        let mut omit_pc = p.omit_pc;
        if p.goto_used {
            omit_pc = false;
        }
        if p.goto_done {
            omit_pc = false;
        } else {
            check_body(&body, &mut omit_pc);
        }
        explode_seq(&mut body, "Done", omit_pc);
        pr.indent("");
        pr.s("[type     |-> \"uniprocess\", ");
        pr.nl();
        pr.s(&format!(" name  |-> \"{name}\", "));
        pr.nl();
        pr.field_seq(" decls  |-> ", &decls, Printer::var_decl, ",");
        pr.nl();
        pr.indent(" defs   |-> ");
        pr.expr(&defs);
        pr.s(",");
        pr.end();
        pr.nl();
        pr.field_seq(" prcds  |-> ", &[] as &[Labeled], Printer::labeled, ",");
        pr.nl();
        pr.field_seq(" body  |-> ", &body, Printer::labeled, "]");
        pr.end();
    }
    Ok(pr.out)
}

/// `tla2rs --pcal-text FILE`: the text TLC hashes for the PlusCal algorithm in FILE
pub fn main(path: &str) -> i32 {
    let Ok(src) = std::fs::read(path) else {
        eprintln!("cannot read {path}");
        return 2;
    };
    let src = String::from_utf8_lossy(&src);
    let Some((_, detab)) = module_lines(&src) else {
        eprintln!("no module in {path}");
        return 1;
    };
    let Some((line, col, fair)) = find_algorithm(&detab) else {
        eprintln!("no algorithm in {path}");
        return 1;
    };
    match tree_text(detab, line, col, fair) {
        Ok(t) => {
            println!("{t}");
            println!("CRC {}", hex(crc32(t.as_bytes())));
            0
        }
        Err(e) => {
            eprintln!("not computed: {e}");
            1
        }
    }
}
