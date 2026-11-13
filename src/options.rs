//! Reductions for configurations that pass one of TLC's options to both TLC and tla2rs, where the
//! usual ones (`graph.rs`, `trace.rs`) do not apply.
//!
//! A file written by TLC's `-dump` option (or by a checker given the same option) is reduced to a
//! canonical text and its hash:
//!
//! - `-dump FILE` lists the distinct states in the order found (`State N:` and the state, then an
//!   empty line). The canonical text keeps that order (with one worker it is TLC's breadth-first
//!   order), one state per line in the canonical form of a state (as in `graph.rs`)
//! - `-dump dot,actionlabels FILE` writes the state graph with each edge labelled with its action.
//!   The canonical text is the sorted set of states and of labelled edges between their texts,
//!   which depends on neither node ids nor the order of the file (stuttering edges left out, as in
//!   `graph.rs`)
//! - `-dump dot,colorize FILE` gives each edge the color of its action, and the file a legend that
//!   lists the actions with their colors. The canonical text keeps the edges' colors, says that
//!   the file names the color scheme, and lists the legend in the order of the file (TLC's order)
//!
//! `tla2rs --dump FILE` prints `dump N <sha256>` (N lines); `--dump-text FILE` prints the text.
//!
//! With `-view`, TLC prints the view of each state of a behavior and no empty line after it, so a
//! state ends at the next step or at a line of TLC's or the checker's own (an error, the counts,
//! the statistics). `tla2rs --trace-view FILE` prints `trace N <sha256>` as `--trace` does, and
//! `--trace-view-text FILE` the canonical form.

use crate::graph::{canon_state_text, sha256};
use std::collections::{BTreeSet, HashMap};

fn states(text: &str) -> Vec<String> {
    let mut out: Vec<String> = vec![];
    let mut cur: Option<(String, Vec<&str>)> = None;
    for l in text.lines() {
        if l.starts_with("State ") && l.ends_with(':') {
            if let Some((h, s)) = cur.take() {
                out.push(format!("{h} {}", canon_state_text(&s.join("\n"))));
            }
            cur = Some((l.to_string(), vec![]));
        } else if let Some((_, s)) = cur.as_mut().filter(|_| !l.is_empty()) {
            s.push(l);
        }
    }
    if let Some((h, s)) = cur {
        out.push(format!("{h} {}", canon_state_text(&s.join("\n"))));
    }
    out
}

fn unescape(s: &str) -> String {
    let mut o = String::with_capacity(s.len());
    let mut it = s.chars();
    while let Some(c) = it.next() {
        match (c, c == '\\') {
            (_, false) => o.push(c),
            _ => match it.next() {
                Some('n') => o.push('\n'),
                Some(x) => o.push(x),
                None => o.push('\\'),
            },
        }
    }
    o
}

fn dot(text: &str) -> Result<Vec<String>, String> {
    let mut label: HashMap<&str, String> = HashMap::new();
    let mut edges: Vec<(&str, &str, &str)> = vec![];
    let mut out = BTreeSet::new();
    let mut legend = 0;
    for line in text.lines() {
        if line == "edge [colorscheme=\"paired12\"]" {
            out.insert("colorscheme paired12".to_string());
            continue;
        }
        let Some((id, rest)) = line.split_once(' ') else { continue };
        // An entry of the legend: `Name [label="Name",fillcolor=N]`
        if let Some((name, color)) = rest.strip_prefix("[label=\"").and_then(|r| r.strip_suffix(']')).and_then(|r| r.split_once("\",fillcolor=")) {
            legend += 1;
            out.insert(format!("legend {legend:05} {id} {name} {color}"));
            continue;
        }
        if let Some(r) = rest.strip_prefix("-> ") {
            if r.contains("style=\"dashed\"") {
                continue;
            }
            let (to, attrs) = r.split_once(' ').unwrap_or((r.trim_end_matches(';'), ""));
            edges.push((id, to.trim_end_matches(';'), attrs.trim_end_matches(';')));
        } else if let Some(r) = rest.strip_prefix("[label=\"") {
            let (t, init) = match r.strip_suffix("\",style = filled]") {
                Some(t) => (t, true),
                None => (r.strip_suffix("\"];").or_else(|| r.strip_suffix("\"]")).ok_or_else(|| format!("unexpected node: {line}"))?, false),
            };
            let c = canon_state_text(&unescape(t));
            out.insert(format!("{} {c}", if init { "init" } else { "state" }));
            label.insert(id, c);
        }
    }
    for (a, b, attrs) in edges {
        let at = |id: &str| label.get(id).cloned().ok_or_else(|| format!("edge to or from node {id}, which has no label"));
        out.insert(format!("edge {} -> {} {attrs}", at(a)?, at(b)?));
    }
    Ok(out.into_iter().collect())
}

fn is_step(l: &str) -> bool {
    let after_no = |s: &str| s.trim_start_matches(|c: char| c.is_ascii_digit()).starts_with(": ");
    l.strip_prefix("State ").is_some_and(after_no) || l.strip_prefix("Back to state ").is_some_and(after_no)
}

/// A line that ends a view printed in a behavior: TLC's and the checker's own
fn ends_view(l: &str) -> bool {
    const P: &[&str] = &[
        "Error:",
        "Model checking completed.",
        "The depth of ",
        "The average outdegree ",
        "Finished in ",
        "Progress(",
        "Checking temporal properties",
        "Finished checking temporal",
        "Checked temporal properties",
        "  ",
    ];
    let counts = l.split_once(" states generated, ").is_some_and(|(n, _)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit() || c == ','));
    l.is_empty() || counts || P.iter().any(|p| l.starts_with(p))
}

/// `tla2rs --trace-view FILE` / `--trace-view-text FILE`
pub fn trace_view(mode: &str, path: &str) -> i32 {
    let text = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return 2;
        }
    };
    let mut o = String::new();
    let mut n = 0;
    let mut in_state = false;
    for l in text.lines() {
        if is_step(l) {
            if in_state {
                o.push('\n');
            }
            o += l;
            o.push('\n');
            n += l.starts_with("State ") as usize;
            in_state = true;
        } else if in_state && ends_view(l) {
            o.push('\n');
            in_state = false;
        } else if in_state {
            o += l;
            o += "\\n";
        }
    }
    if in_state {
        o.push('\n');
    }
    if mode == "--trace-view-text" {
        print!("{o}");
    } else if n == 0 {
        println!("trace 0");
    } else {
        println!("trace {n} {}", sha256(o.as_bytes()));
    }
    0
}

/// `tla2rs --dump FILE` / `--dump-text FILE`
pub fn main(mode: &str, path: &str) -> i32 {
    let text = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return 2;
        }
    };
    let lines = if text.starts_with("strict digraph") {
        match dot(&text) {
            Ok(l) => l,
            Err(e) => {
                eprintln!("{path}: {e}");
                return 2;
            }
        }
    } else {
        states(&text)
    };
    let body: String = lines.iter().map(|l| format!("{l}\n")).collect();
    if mode == "--dump-text" {
        print!("{body}");
    } else {
        println!("dump {} {}", lines.len(), sha256(body.as_bytes()));
    }
    0
}
