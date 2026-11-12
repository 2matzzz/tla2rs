// TLC's pretty printer for values, used by the compiler (Print and PrintT evaluated when TLC
// starts) and pasted into every generated checker (`runtime::PPR`). No inner doc comments here:
// the text is also part of the generated main.rs.

/// TLC's pretty printer (`tlc2.pprint`, called by `Values.ppr` with width 80 on each variable's
/// value when it prints a state). It parses the value's text and breaks it over lines when it is
/// wider than 80 columns; if the text does not parse (TLC's parser does not know escaped quotes in
/// strings or `_` in names), it is printed as is. Ported as written, quirks included.
pub fn ppr(s: &str) -> String {
    let c: Vec<char> = s.chars().collect();
    match pp_parse(&c, 0) {
        Some(n) if n.last + 1 >= c.len() => pp_format(&c, &n, 80, 0, "").unwrap_or_else(|| s.to_string()),
        _ => s.to_string(),
    }
}

/// A node of TLC's parse tree of a value: its kind (Node.CONSTANT .. Node.SUBSET), the first and
/// last character, and its children (the elements, or the two halves of a pair)
struct PNode {
    kind: u8,
    first: usize,
    last: usize,
    kids: Vec<PNode>,
}

const PP_CONST: u8 = 1;
const PP_SET: u8 = 2;
const PP_SEQ: u8 = 3;
const PP_REC: u8 = 4;
const PP_FUN: u8 = 6;
const PP_SUBSET: u8 = 8;

fn pp_ws(c: char) -> bool {
    // Character.isWhitespace
    matches!(c, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | '\u{1c}'..='\u{1f}')
}

fn pp_digit(c: char) -> bool {
    c.is_ascii_digit() || (!c.is_ascii() && c.is_numeric())
}

fn pp_alnum(c: char) -> bool {
    c.is_ascii_alphanumeric() || (!c.is_ascii() && c.is_alphanumeric())
}

fn pp_skip(c: &[char], mut i: usize) -> Option<usize> {
    while pp_ws(*c.get(i)?) {
        i += 1;
    }
    Some(i)
}

fn pp_at(c: &[char], i: usize, w: &str) -> bool {
    w.chars().enumerate().all(|(k, x)| c.get(i + k) == Some(&x))
}

fn pp_parse(c: &[char], i: usize) -> Option<PNode> {
    if i >= c.len() {
        return None;
    }
    let i = pp_skip(c, i)?;
    match c[i] {
        '{' => pp_list(c, i, PP_SET, 1, '}', false),
        '<' => pp_list(c, i, PP_SEQ, 2, '>', false),
        '[' => pp_list(c, i, PP_REC, 1, ']', true),
        '(' => pp_list(c, i, PP_FUN, 1, ')', true),
        _ if pp_at(c, i, "SUBSET") => {
            let e = pp_parse(c, pp_skip(c, i + 6)?)?;
            Some(PNode { kind: PP_SUBSET, first: i, last: e.last, kids: vec![e] })
        }
        _ => pp_constant(c, i),
    }
}

/// A set, sequence, record or function: elements (pairs for the last two) up to the closing
/// character, separated by "," ("@@" between the pairs of a function)
fn pp_list(c: &[char], i: usize, kind: u8, open: usize, close: char, pairs: bool) -> Option<PNode> {
    let mut last = pp_skip(c, i + open)?;
    let mut kids = vec![];
    while *c.get(last)? != close {
        let e = if pairs { pp_pair(c, last, if kind == PP_REC { "|->" } else { ":>" })? } else { pp_parse(c, last)? };
        last = pp_skip(c, e.last + 1)?;
        if kind == PP_FUN {
            if pp_at(c, last, "@@") {
                last += 2;
            }
        } else if c[last] == ',' {
            last += 1;
        }
        last = pp_skip(c, last)?;
        kids.push(e);
    }
    if kind == PP_SEQ {
        last += 1;
    }
    Some(PNode { kind, first: i, last, kids })
}

fn pp_pair(c: &[char], i: usize, div: &str) -> Option<PNode> {
    let a = pp_parse(c, i)?;
    let mut last = pp_skip(c, a.last + 1)?;
    if !pp_at(c, last, div) {
        return None;
    }
    last = pp_skip(c, last + div.len())?;
    let b = pp_parse(c, last)?;
    Some(PNode { kind: 0, first: i, last: b.last, kids: vec![a, b] })
}

fn pp_constant(c: &[char], i: usize) -> Option<PNode> {
    let first = pp_skip(c, i)?;
    let k = |last| Some(PNode { kind: PP_CONST, first, last, kids: vec![] });
    let mut last = first;
    if c[first] == '"' {
        loop {
            last += 1;
            if *c.get(last)? == '"' {
                return k(last);
            }
        }
    }
    if pp_digit(c[last]) {
        // An interval i..j
        let mut j = i;
        while j < c.len() && pp_digit(c[j]) {
            j += 1;
        }
        if pp_at(c, j, "..") && c.get(j + 2).is_some_and(|&x| pp_digit(x)) {
            j += 2;
            while j < c.len() && pp_digit(c[j]) {
                j += 1;
            }
            return Some(PNode { kind: PP_CONST, first: i, last: j - 1, kids: vec![] });
        }
    }
    if c[last] == '-' {
        last += 1;
        while pp_digit(*c.get(last)?) {
            last += 1;
            if last == c.len() {
                break;
            }
        }
        return k(last - 1);
    }
    if pp_alnum(c[last]) {
        while pp_alnum(c[last]) {
            last += 1;
            if last == c.len() {
                break;
            }
        }
        return k(last - 1);
    }
    None
}

fn pp_text(c: &[char], n: &PNode) -> String {
    c[n.first..=n.last].iter().collect()
}

fn pp_len(n: &PNode) -> i64 {
    (n.last - n.first + 1) as i64
}

fn pp_format(c: &[char], n: &PNode, cw: i64, tw: i64, pad: &str) -> Option<String> {
    if pp_len(n) <= cw - tw {
        return Some(pp_text(c, n));
    }
    match n.kind {
        PP_CONST => Some(pp_text(c, n)),
        PP_SET => pp_simple(c, n, cw, tw, pad, "{ ", " }", "  "),
        PP_SEQ => pp_simple(c, n, cw, tw, pad, "<< ", " >>", "   "),
        PP_SUBSET => pp_simple(c, n, cw, tw, pad, "SUBSET ", " ", " "),
        PP_FUN => pp_pairs(c, n, cw, tw, pad, ["( ", " )", "  ", " @@", " :>", "    "]),
        PP_REC => pp_pairs(c, n, cw, tw, pad, ["[ ", " ]", "  ", ",", " |->", "    "]),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn pp_simple(c: &[char], n: &PNode, cw: i64, tw: i64, pad: &str, open: &str, close: &str, opad: &str) -> Option<String> {
    let cw = cw - open.len().max(opad.len()) as i64;
    let (tw, lp) = (tw + close.len() as i64, format!("{pad}{opad}"));
    let mut o = String::from(open);
    for (k, e) in n.kids.iter().enumerate() {
        if k + 1 < n.kids.len() {
            o += &pp_format(c, e, cw, 1, &lp)?;
            o += ",\n";
            o += &lp;
        } else {
            o += &pp_format(c, e, cw, tw, &lp)?;
        }
    }
    o += close;
    Some(o)
}

/// A record or function: [open, close, pad, sep, div, divpad]
fn pp_pairs(c: &[char], n: &PNode, cw: i64, tw: i64, pad: &str, d: [&str; 6]) -> Option<String> {
    let [open, close, opad, sep, div, divpad] = d;
    let cw = cw - open.len().max(opad.len()) as i64;
    let (tw, lp) = (tw + close.len() as i64, format!("{pad}{opad}"));
    let (sl, dl, dpl) = (sep.len() as i64, div.len() as i64, divpad.len() as i64);
    let lpd = format!("{lp}{divpad}");
    let mut o = String::from(open);
    for (k, p) in n.kids.iter().enumerate() {
        let (a, v) = (&p.kids[0], &p.kids[1]);
        let more = k + 1 < n.kids.len();
        // The last pair leaves room for the closing delimiter; the others for the separator
        let (fits, vtw, end) = if more {
            (pp_len(a) + dl + 1 + pp_len(v) + sl <= cw, sl, format!("{sep}\n{lp}"))
        } else {
            (pp_len(a) + dl + 1 + pp_len(v) <= cw - tw, tw, String::new())
        };
        if fits {
            o += &format!("{}{div} {}{end}", pp_text(c, a), pp_text(c, v));
            continue;
        }
        if pp_len(a) + dl <= cw {
            o += &pp_text(c, a);
        } else {
            o += &pp_format(c, a, cw, tw + dl, &lp)?;
        }
        o += &format!("{div}\n{lpd}{}{end}", pp_format(c, v, cw - dpl, vtw, &lpd)?);
    }
    o += close;
    Some(o)
}
