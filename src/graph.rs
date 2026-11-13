//! Reduces a state graph written by TLC (`-dump dot FILE`) or by a generated checker
//! (`-dumpgraph FILE`) to a form that depends on neither node ids nor the order of the file: the
//! sorted set of state texts and the sorted set of edges between them.
//!
//! - A node's label is the state as TLC prints it, its variables in TLC's order, which a checker
//!   follows (see `sany::var_order`)
//! - Initial states (filled nodes) are marked
//! - Edges are deduplicated (TLC writes one per successor generated, so a successor generated
//!   twice is written twice), and the stuttering edges TLC adds for liveness checking (dashed) are
//!   left out: they are not transitions of the next-state relation
//!
//! `tla2rs --graph FILE` prints `states N <sha256>` and `edges M <sha256>`; `--graph-text FILE`
//! prints the canonical form itself, one state or edge per line, for diffing.

use std::collections::{BTreeSet, HashMap};

pub struct Canon {
    /// False if the file does not end the graph: TLC leaves it so when it stops while computing
    /// the initial states or before (what it buffered is lost)
    pub complete: bool,
    /// (state text with "\" and newlines escaped, initial?), sorted by text
    pub states: Vec<(String, bool)>,
    /// (source, target) as indexes into `states`, sorted and unique
    pub edges: Vec<(usize, usize)>,
}

fn unescape(s: &str) -> String {
    let mut o = String::with_capacity(s.len());
    let mut it = s.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            o.push(c);
            continue;
        }
        match it.next() {
            Some('n') => o.push('\n'),
            Some(x) => o.push(x),
            None => o.push('\\'),
        }
    }
    o
}

/// The canonical text of a state: its `/\ var = value` conjuncts (each with its continuation
/// lines) in the order printed, on one line with "\" and newlines escaped
fn canon_state(label: &str) -> String {
    canon_state_text(&unescape(label))
}

/// `canon_state` of a state as printed (not escaped)
pub fn canon_state_text(text: &str) -> String {
    let mut parts: Vec<String> = vec![];
    for line in text.split('\n') {
        match parts.last_mut() {
            Some(p) if !line.starts_with("/\\ ") => {
                p.push('\n');
                p.push_str(line);
            }
            _ => parts.push(line.to_string()),
        }
    }
    let parts: Vec<String> = parts.iter().map(|p| intervals(p)).collect();
    empty_seqs(&parts.join("\n")).replace('\\', "\\\\").replace('\n', "\\n")
}

/// TLC prints a set in the form it holds it, so a set built as `1..3` prints as `1..3` until an
/// operation enumerates it, while a checker prints `{1, 2, 3}`. Both are the same value, so an
/// interval outside strings becomes the set it denotes, in a conjunct printed on one line whose
/// value still fits in TLC's 80 columns after that (TLC's pretty printer would leave it on one
/// line). A conjunct that does not qualify is kept as printed, and then differs.
fn intervals(part: &str) -> String {
    if part.contains('\n') || !part.contains("..") {
        return part.to_string();
    }
    let c: Vec<char> = part.chars().collect();
    let mut o = String::with_capacity(part.len());
    let (mut i, mut in_str) = (0, false);
    let num = |j: usize| -> Option<(i64, usize)> {
        let mut k = j;
        if k < c.len() && c[k] == '-' {
            k += 1;
        }
        let d = k;
        while k < c.len() && c[k].is_ascii_digit() {
            k += 1;
        }
        if k == d {
            return None;
        }
        c[j..k].iter().collect::<String>().parse().ok().map(|v| (v, k))
    };
    while i < c.len() {
        if in_str {
            if c[i] == '\\' && i + 1 < c.len() {
                o.push(c[i]);
                i += 1;
            } else if c[i] == '"' {
                in_str = false;
            }
            o.push(c[i]);
            i += 1;
            continue;
        }
        if c[i] == '"' {
            in_str = true;
            o.push(c[i]);
            i += 1;
            continue;
        }
        let starts = i == 0 || !(c[i - 1].is_alphanumeric() || c[i - 1] == '_' || c[i - 1] == '.');
        if starts {
            if let Some((a, j)) = num(i) {
                if c[j..].starts_with(&['.', '.']) {
                    if let Some((b, k)) = num(j + 2) {
                        if k == c.len() || !(c[k].is_alphanumeric() || c[k] == '_' || c[k] == '.') {
                            if b.saturating_sub(a) > 40 {
                                return part.to_string();
                            }
                            let elems: Vec<String> = (a..=b).map(|v| v.to_string()).collect();
                            o.push('{');
                            o.push_str(&elems.join(", "));
                            o.push('}');
                            i = k;
                            continue;
                        }
                    }
                }
                // A number that does not start an interval: copy it whole
                o.extend(&c[i..j]);
                i = j;
                continue;
            }
        }
        o.push(c[i]);
        i += 1;
    }
    let value = |t: &str| t.split_once(" = ").map(|(_, v)| v.chars().count()).unwrap_or(0);
    if value(&o) > 80 {
        return part.to_string();
    }
    o
}

/// TLC prints the empty function as `<<>>` when it is held as a function and `<< >>` when it is
/// held as a tuple, depending on the expression that built it. Both are the same value, so `<<>>`
/// outside strings becomes `<< >>`.
fn empty_seqs(text: &str) -> String {
    let c: Vec<char> = text.chars().collect();
    let mut o = String::with_capacity(text.len());
    let (mut i, mut in_str) = (0, false);
    while i < c.len() {
        if in_str {
            if c[i] == '\\' && i + 1 < c.len() {
                o.push(c[i]);
                i += 1;
            } else if c[i] == '"' {
                in_str = false;
            }
        } else if c[i] == '"' {
            in_str = true;
        } else if c[i..].starts_with(&['<', '<', '>', '>']) {
            o.push_str("<< >>");
            i += 4;
            continue;
        }
        o.push(c[i]);
        i += 1;
    }
    o
}

pub fn canon(dot: &str) -> Result<Canon, String> {
    let mut label: HashMap<&str, (String, bool)> = HashMap::new();
    let mut edges: Vec<(&str, &str)> = vec![];
    let complete = dot.lines().rev().find(|l| !l.trim().is_empty()).is_some_and(|l| l.trim() == "}");
    // TLC stopped before ending the file: it is not compared, and its last line can be cut off anywhere
    if !complete {
        return Ok(Canon { complete, states: vec![], edges: vec![] });
    }
    for (no, line) in dot.lines().enumerate() {
        let Some((id, rest)) = line.split_once(' ') else { continue };
        if let Some(r) = rest.strip_prefix("-> ") {
            if r.contains("style=\"dashed\"") {
                continue;
            }
            let to = r.split([' ', ';']).next().unwrap_or("");
            edges.push((id, to));
        } else if let Some(r) = rest.strip_prefix("[label=\"") {
            let (text, init) = if let Some(t) = r.strip_suffix("\",style = filled]") {
                (t, true)
            } else if let Some(t) = r.strip_suffix("\"];").or_else(|| r.strip_suffix("\"]")) {
                (t, false)
            } else {
                return Err(format!("line {}: unexpected node: {line}", no + 1));
            };
            let c = (canon_state(text), init);
            if let Some(old) = label.insert(id, c.clone()) {
                if old != c {
                    return Err(format!("line {}: node {id} has two labels", no + 1));
                }
            }
        }
    }
    let texts: BTreeSet<&(String, bool)> = label.values().collect();
    let mut states: Vec<(String, bool)> = vec![];
    for (t, init) in texts {
        // The same state written under two ids: one entry, initial if either is
        match states.last_mut() {
            Some(last) if last.0 == *t => last.1 |= *init,
            _ => states.push((t.clone(), *init)),
        }
    }
    let index: HashMap<&str, usize> = states.iter().enumerate().map(|(i, (t, _))| (t.as_str(), i)).collect();
    let at = |id: &str| -> Result<usize, String> {
        let (t, _) = label.get(id).ok_or_else(|| format!("edge to or from node {id}, which has no label"))?;
        Ok(index[t.as_str()])
    };
    let mut es = BTreeSet::new();
    for (a, b) in edges {
        es.insert((at(a)?, at(b)?));
    }
    Ok(Canon { complete, states, edges: es.into_iter().collect() })
}

impl Canon {
    pub fn state_lines(&self) -> String {
        let mut o = String::new();
        for (t, init) in &self.states {
            o += if *init { "init " } else { "state " };
            o += t;
            o.push('\n');
        }
        o
    }

    pub fn edge_lines(&self) -> String {
        let mut o = String::new();
        for (a, b) in &self.edges {
            o += &format!("{a} {b}\n");
        }
        o
    }

    /// The edges with the states' texts, for reading
    pub fn edge_text(&self) -> String {
        let mut o = String::new();
        for (a, b) in &self.edges {
            o += &format!("{} -> {}\n", self.states[*a].0, self.states[*b].0);
        }
        o
    }
}

/// SHA-256 (FIPS 180-4), hex
pub fn sha256(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
        0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
        0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
        0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] =
        [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    let mut msg = data.to_vec();
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&((data.len() as u64) * 8).to_be_bytes());
    for block in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes(block[i * 4..i * 4 + 4].try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        let mut v = h;
        for i in 0..64 {
            let s1 = v[4].rotate_right(6) ^ v[4].rotate_right(11) ^ v[4].rotate_right(25);
            let ch = (v[4] & v[5]) ^ (!v[4] & v[6]);
            let t1 = v[7].wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
            let s0 = v[0].rotate_right(2) ^ v[0].rotate_right(13) ^ v[0].rotate_right(22);
            let maj = (v[0] & v[1]) ^ (v[0] & v[2]) ^ (v[1] & v[2]);
            let t2 = s0.wrapping_add(maj);
            v = [t1.wrapping_add(t2), v[0], v[1], v[2], v[3].wrapping_add(t1), v[4], v[5], v[6]];
        }
        for i in 0..8 {
            h[i] = h[i].wrapping_add(v[i]);
        }
    }
    h.iter().map(|x| format!("{x:08x}")).collect()
}

/// `tla2rs --graph FILE` / `--graph-text FILE`. A missing file is an empty graph (the run stopped
/// before exploring anything).
pub fn main(mode: &str, path: &str) -> i32 {
    let dot = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => String::new(),
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return 2;
        }
    };
    let c = match canon(&dot) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{path}: {e}");
            return 1;
        }
    };
    if !c.complete && !dot.is_empty() {
        println!("states incomplete");
        println!("edges incomplete");
    } else if mode == "--graph-text" {
        print!("{}{}", c.state_lines(), c.edge_text());
    } else {
        println!("states {} {}", c.states.len(), sha256(c.state_lines().as_bytes()));
        println!("edges {} {}", c.edges.len(), sha256(c.edge_lines().as_bytes()));
    }
    0
}

