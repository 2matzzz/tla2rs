//! Lexer for TLA+. Tokens carry column numbers, since `/\` and `\/` bullet lists are delimited by
//! column.

pub type R<T> = Result<T, String>;


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
}

const SYMS: &[&str] = &[
    "<=>", "|->", "~>", "==", "=>", "=<", "<=", ">=", "/=", "/\\", "\\/", "->", "<-", "<<", ">>", "<>",
    "[]", "..", "::", "@@", ":>", "<:", "++", "**", "//", "^^", "%%", "##", "&&", "||", "$$", "(", ")", "[", "]", "{", "}", ",", ":", "'", ".", "=", "#", "<", ">", "+",
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
        let (tl, tc, first) = (line, col, !line_has_tok);
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
            adv!();
            let mut s = String::new();
            while i < cs.len() && cs[i] != '"' {
                if cs[i] == '\\' && i + 1 < cs.len() {
                    adv!();
                    s.push(match cs[i] {
                        'n' => '\n',
                        't' => '\t',
                        x => x,
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
                Tok::Sym(normalize_backslash(&w))
            } else {
                adv!();
                Tok::Sym("\\".into())
            }
        } else {
            let rest: String = cs[i..(i + 3).min(cs.len())].iter().collect();
            let Some(sym) = SYMS.iter().find(|s| rest.starts_with(**s)) else {
                return Err(format!("line {line}:{col}: unexpected character {c:?}"));
            };
            for _ in 0..sym.chars().count() {
                adv!();
            }
            Tok::Sym(sym.to_string())
        };
        let end = module && tok == Tok::Sym("====".into());
        out.push(Token { tok, line: tl, col: tc, first });
        line_has_tok = true;
        if end {
            break;
        }
    }
    out.push(Token { tok: Tok::Eof, line, col: 0, first: true });
    Ok(out)
}

/// Whether this is an identifier starting with a digit, like `1a`
fn ident_ahead(cs: &[char], mut i: usize) -> bool {
    while i < cs.len() && cs[i].is_ascii_digit() {
        i += 1;
    }
    i < cs.len() && (cs[i].is_ascii_alphabetic() || cs[i] == '_')
}
