//! Lexer for TLA+. Tokens carry column numbers, since `/\` and `\/` bullet lists are delimited by
//! column.

pub type R<T> = Result<T, String>;

/// The start of an error that SANY reports too (TLC then stops with exit 150, before checking)
pub const SANY: &str = "SANY: ";

/// After SANY: an error that stops SANY while it parses a module (a lexical or parse error), with
/// the module's name on the rest of the line and SANY's report on the lines after it
pub const SANY_ABORT: &str = "abort ";

/// A string as Java escapes it when SANY shows what it read (`"` as `\"`, `\` as `\\`)
pub fn java_escape(s: &str) -> String {
    let mut o = String::new();
    for c in s.chars() {
        match c {
            '\\' => o.push_str("\\\\"),
            '"' => o.push_str("\\\""),
            '\'' => o.push_str("\\'"),
            '\n' => o.push_str("\\n"),
            '\t' => o.push_str("\\t"),
            '\r' => o.push_str("\\r"),
            '\x0c' => o.push_str("\\f"),
            c => o.push(c),
        }
    }
    o
}


#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Num(i64),
    Str(String),
    Sym(String),
    Eof,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub line: usize,
    pub col: usize,
    /// Whether this is the first token on its line
    pub first: bool,
    /// The column just after the token (tokens do not span lines)
    pub end: usize,
    /// A number as written (`007`, `\b11`), which TLC prints for a function's body
    pub raw: Option<String>,
}

const SYMS: &[&str] = &[
    "!!", "??", "<=>", "|->", "~>", "==", "=>", "=<", "<=", ">=", "/=", "/\\", "\\/", "->", "<-", "<<", ">>", "<>",
    "[]", "..", "::", "^+", "^*", "^#", "--", "|-", "@@", ":>", "<:", "++", "**", "//", "^^", "%%", "##", "&&", "||", "$$", "(", ")", "[", "]", "{", "}", ",", ":", "'", ".", "=", "#", "<", ">", "+",
    "-", "*", "%", "!", "@", "~", "^", "|", "&", "$",
];

fn normalize_backslash(word: &str) -> String {
    match word {
        "union" => "\\cup".into(),
        "intersect" => "\\cap".into(),
        "land" => "/\\".into(),
        "lor" => "\\/".into(),
        "lnot" | "neg" => "~".into(),
        "leq" => "<=".into(),
        "geq" => ">=".into(),
        "equiv" => "<=>".into(),
        "times" => "\\X".into(),
        w => format!("\\{w}"),
    }
}

pub fn lex(src: &str) -> R<Vec<Token>> {
    lex_from(src, false)
}

/// Lexes a module: as in TLC, anything before the `---- MODULE` line and after the module's
/// closing `====` is ignored (it need not even be valid TLA+ text).
pub fn lex_module(src: &str) -> R<Vec<Token>> {
    lex_from(src, true)
}

/// The position of the first `----` run followed by `MODULE`
fn module_start(cs: &[char]) -> Option<usize> {
    let mut i = 0;
    while i + 4 <= cs.len() {
        if cs[i..i + 4].iter().all(|&c| c == '-') {
            let mut j = i;
            while j < cs.len() && cs[j] == '-' {
                j += 1;
            }
            while j < cs.len() && cs[j].is_whitespace() {
                j += 1;
            }
            if cs[j..].starts_with(&['M', 'O', 'D', 'U', 'L', 'E']) {
                return Some(i);
            }
            i = j.max(i + 1);
        } else {
            i += 1;
        }
    }
    None
}

#[allow(unused_assignments)]
fn lex_from(src: &str, module: bool) -> R<Vec<Token>> {
    let cs: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let (mut i, mut line, mut col) = (0usize, 1usize, 0usize);
    let mut line_has_tok = false;
    let mut depth = 0i32;
    if module {
        // Skip to the header, keeping line numbers
        let start = module_start(&cs).unwrap_or(0);
        while i < start {
            if cs[i] == '\n' {
                line += 1;
                col = 0;
            } else {
                col += 1;
            }
            i += 1;
        }
    }
    macro_rules! adv {
        () => {{
            if cs[i] == '\n' {
                line += 1;
                col = 0;
                line_has_tok = false;
            } else {
                col += 1;
            }
            i += 1;
        }};
    }
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            adv!();
            continue;
        }
        // Comments
        if c == '\\' && cs.get(i + 1) == Some(&'*') {
            while i < cs.len() && cs[i] != '\n' {
                adv!();
            }
            continue;
        }
        if c == '(' && cs.get(i + 1) == Some(&'*') {
            let mut depth = 0;
            loop {
                if i >= cs.len() {
                    return Err(format!("line {line}: unterminated comment"));
                }
                if cs[i] == '(' && cs.get(i + 1) == Some(&'*') {
                    depth += 1;
                    adv!();
                    adv!();
                } else if cs[i] == '*' && cs.get(i + 1) == Some(&')') {
                    depth -= 1;
                    adv!();
                    adv!();
                    if depth == 0 {
                        break;
                    }
                } else {
                    adv!();
                }
            }
            continue;
        }
        let (tl, tc, first, start) = (line, col, !line_has_tok, i);
        let tok = if c == '-' && cs[i..].iter().take(4).all(|&x| x == '-') && cs.len() - i >= 4 {
            while i < cs.len() && cs[i] == '-' {
                adv!();
            }
            Tok::Sym("----".into())
        } else if c == '=' && cs.len() - i >= 4 && cs[i..i + 4].iter().all(|&x| x == '=') {
            while i < cs.len() && cs[i] == '=' {
                adv!();
            }
            Tok::Sym("====".into())
        } else if c == '"' {
            let i0 = i;
            adv!();
            let mut s = String::new();
            while i < cs.len() && cs[i] != '"' {
                if cs[i] == '\\' && i + 1 < cs.len() {
                    adv!();
                    s.push(match cs[i] {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        'f' => '\x0c',
                        x @ ('\\' | '"') => x,
                        // As SANY reports it: the character, its code, and the string read up to it
                        x => {
                            let read: String = cs[i0..i].iter().collect();
                            return Err(format!(
                                "{SANY}{SANY_ABORT}{}\nLexical error at line {line}, column {}.  Encountered: \"{x}\" ({}), after : \"{}\"",
                                module_name(&cs.iter().collect::<String>()),
                                col + 1,
                                x as u32,
                                java_escape(&read)
                            ));
                        }
                    });
                } else {
                    s.push(cs[i]);
                }
                adv!();
            }
            if i >= cs.len() {
                return Err(format!("line {tl}: unterminated string"));
            }
            adv!();
            Tok::Str(s)
        } else if c.is_ascii_digit() && !ident_ahead(&cs, i) {
            let mut n: i64 = 0;
            while i < cs.len() && cs[i].is_ascii_digit() {
                n = n * 10 + cs[i].to_digit(10).unwrap() as i64;
                adv!();
            }
            Tok::Num(n)
        } else if c.is_ascii_alphanumeric() || c == '_' {
            let mut s = String::new();
            while i < cs.len() && (cs[i].is_ascii_alphanumeric() || cs[i] == '_') {
                s.push(cs[i]);
                adv!();
            }
            Tok::Ident(s)
        } else if c == '\\' {
            if cs.get(i + 1) == Some(&'/') {
                adv!();
                adv!();
                Tok::Sym("\\/".into())
            } else if cs.get(i + 1).is_some_and(|x| x.is_ascii_alphabetic()) {
                adv!();
                let mut w = String::new();
                while i < cs.len() && cs[i].is_ascii_alphanumeric() {
                    w.push(cs[i]);
                    adv!();
                }
                // \b101, \o17, \hFF: numbers in base 2, 8 and 16
                let radix = match w.chars().next() {
                    Some('b' | 'B') => 2,
                    Some('o' | 'O') => 8,
                    Some('h' | 'H') => 16,
                    _ => 0,
                };
                let digits = &w[1..];
                if radix > 0 && !digits.is_empty() && digits.chars().all(|d| d.is_digit(radix)) {
                    Tok::Num(i64::from_str_radix(digits, radix).map_err(|e| format!("line {tl}: {e}"))?)
                } else {
                    Tok::Sym(normalize_backslash(&w))
                }
            } else {
                adv!();
                Tok::Sym("\\".into())
            }
        } else {
            // -+-> (TLA+'s "while" operator), the only symbol of four characters
            if cs[i..].starts_with(&['-', '+', '-', '>']) {
                for _ in 0..4 {
                    adv!();
                }
                out.push(Token { tok: Tok::Sym("-+->".into()), line: tl, col: tc, first, end: col, raw: None });
                line_has_tok = true;
                continue;
            }
            let rest: String = cs[i..(i + 3).min(cs.len())].iter().collect();
            // (+) and (-) spell \oplus and \ominus (the bag union and difference of Bags)
            if rest == "(+)" || rest == "(-)" {
                for _ in 0..3 {
                    adv!();
                }
                let name = if rest == "(+)" { "\\oplus" } else { "\\ominus" };
                out.push(Token { tok: Tok::Sym(name.into()), line: tl, col: tc, first, end: col, raw: None });
                line_has_tok = true;
                continue;
            }
            let Some(sym) = SYMS.iter().find(|s| rest.starts_with(**s)) else {
                return Err(format!("line {line}:{col}: unexpected character {c:?}"));
            };
            for _ in 0..sym.chars().count() {
                adv!();
            }
            Tok::Sym(sym.to_string())
        };
        // A module ends at its `====`; a module nested in it (`---- MODULE M ----`) ends at its own
        if module && tok == Tok::Ident("MODULE".into()) {
            depth += 1;
        }
        if module && tok == Tok::Sym("====".into()) {
            depth -= 1;
        }
        let end = module && tok == Tok::Sym("====".into()) && depth <= 0;
        let raw = matches!(tok, Tok::Num(_)).then(|| cs[start..i].iter().collect());
        out.push(Token { tok, line: tl, col: tc, first, end: col, raw });
        line_has_tok = true;
        if end {
            break;
        }
    }
    out.push(Token { tok: Tok::Eof, line, col: 0, first: true, end: 0, raw: None });
    Ok(out)
}

/// Whether this is an identifier starting with a digit, like `1a`
fn ident_ahead(cs: &[char], mut i: usize) -> bool {
    while i < cs.len() && cs[i].is_ascii_digit() {
        i += 1;
    }
    i < cs.len() && (cs[i].is_ascii_alphabetic() || cs[i] == '_')
}

/// The name of the first module in a source (after `MODULE`), for SANY's reports
pub fn module_name(text: &str) -> String {
    text.split_once("MODULE")
        .map(|(_, r)| r.trim_start().chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect())
        .unwrap_or_default()
}
