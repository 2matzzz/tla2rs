//! Reduces what TLC or a generated checker prints, other than its progress, statistics and
//! counterexample, to a canonical text and its hash: the error and warning messages and the lines
//! the spec prints (Print, PrintT), in the order they appear.
//!
//! Left out, line by line (see "Messages and printed lines" in CLAUDE.md):
//! - TLC's banner (version, fingerprint seed, process id), the modules it parses (with temporary
//!   paths), its progress and statistics (counts, depth, outdegree, fingerprint collision estimates,
//!   times), and the equivalent lines of a checker. The verdict and counts are compared on their own
//! - A counterexample: each `State N:` / `Back to state N:` line with the state after it, up to an
//!   empty line (compared by `trace.rs`)
//! - TLC's list of the nested expressions it was evaluating when an error occurred (`Error: The
//!   error occurred when TLC was evaluating the nested ...`, then numbered positions or `The error
//!   call stack is empty.`, up to an empty line), and its `Fingerprint Stack Trace:` with the
//!   numbered positions after it. Both are deterministic, but they are TLC's evaluation stack, which
//!   a checker that inlines every definition does not have
//! - The parser's stack (`Residual stack trace follows:` and the `... starting at line L, column C.`
//!   lines after it) and the Java exception SANY stops with (`tla2sany.semantic.AbortException`)
//! - Empty lines
//!
//! Rewritten:
//! - Where TLC reports an error through a Java exception, `The exception was a <class>` is dropped,
//!   and the message on the next line loses its leading `: ` and a Java class name before it
//!   (`tlc2.tool.EvalException: `, `util.Assert$TLCRuntimeException: `), which say how TLC passed the
//!   error on, not what it is
//! - A state printed after a message without a `State N:` line (`... is violated by the initial
//!   state:`, `While working on the initial state:`) becomes one line in the canonical form of a
//!   state (its variables sorted, as in `graph.rs`)
//!
//! The error lines are the lines of the canonical text that start with `Error:`, except TLC's
//! `Error: TLC was unable to fingerprint.`, a second error TLC reports after some failures while
//! it prints the behavior. A configuration whose full text cannot match compares these only.
//!
//! `tla2rs --messages FILE` prints `messages N <sha256>` and `errors M <sha256>` (N and M lines, or
//! `messages 0` / `errors 0`); `--messages-text FILE` prints the canonical text.

use crate::graph::{canon_state_text, sha256};

/// TLC's and a checker's lines that are not messages (progress, statistics, banner)
fn is_progress(l: &str) -> bool {
    const PREFIXES: &[&str] = &[
        "TLC2 Version ",
        "Running breadth-first search Model-Checking ",
        "Parsing file ",
        "Semantic processing of module ",
        "Starting... (",
        "Computing initial states...",
        "Finished computing initial states: ",
        "Progress(",
        "Model checking completed. No error has been found.",
        "  Estimates of the probability that TLC did not check all reachable states",
        "  because two distinct states had the same fingerprint:",
        "  calculated (optimistic):",
        "  based on the actual fingerprints:",
        "The depth of the complete state graph search is ",
        "The average outdegree of the complete state graph is ",
        "Finished in ",
        "Implied-temporal checking--satisfiability problem has ",
        "Checking temporal properties for the ",
        "Finished checking temporal properties in ",
        // A checker's
        "Temporal properties hold (",
        "Checked temporal properties in ",
        "  Estimate of the probability that a state was skipped ",
        "  The queue spilled ",
    ];
    if PREFIXES.iter().any(|p| l.starts_with(p)) {
        return true;
    }
    let digits = |s: &str| !s.is_empty() && s.chars().all(|c| c.is_ascii_digit() || c == ',');
    // `N states generated, M distinct states found, K states left on queue.`
    if let Some((n, _)) = l.split_once(" states generated, ") {
        return digits(n);
    }
    // `Computed N initial states...`
    if let Some(r) = l.strip_prefix("Computed ") {
        return r.split_once(' ').is_some_and(|(n, r)| digits(n) && r.starts_with("initial state"));
    }
    // `Checking N branches of temporal properties for the ...`
    if let Some(r) = l.strip_prefix("Checking ") {
        return r.split_once(' ').is_some_and(|(n, r)| digits(n) && r.starts_with("branches of temporal properties"));
    }
    false
}

/// `0) line L, col C to line L2, col C2 of module M`
fn is_fp_frame(l: &str) -> bool {
    l.split_once(") line ").is_some_and(|(n, _)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
}

fn is_trace_header(l: &str) -> bool {
    let after_no = |s: &str| s.trim_start_matches(|c: char| c.is_ascii_digit()).starts_with(": ");
    l.strip_prefix("State ").is_some_and(after_no) || l.strip_prefix("Back to state ").is_some_and(after_no)
}

/// `tlc2.tool.EvalException: msg` -> `msg`: a Java class name (dotted, its last part capitalized,
/// optionally with `$Inner`) followed by `: `
fn strip_java_class(l: &str) -> &str {
    let Some((name, rest)) = l.split_once(": ") else { return l };
    let parts: Vec<&str> = name.split('.').collect();
    let ident = |s: &str| !s.is_empty() && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$');
    let is_class = parts.len() >= 2
        && parts.iter().all(|p| ident(p))
        && parts.last().unwrap().starts_with(|c: char| c.is_ascii_uppercase())
        && parts[..parts.len() - 1].iter().all(|p| p.starts_with(|c: char| c.is_ascii_lowercase()));
    if is_class { rest } else { l }
}

/// The canonical text: the lines kept, in order
pub fn canon(out: &str) -> Vec<String> {
    let lines: Vec<&str> = out.lines().collect();
    let mut kept = vec![];
    let mut i = 0;
    while i < lines.len() {
        let l = lines[i];
        i += 1;
        if is_trace_header(l) {
            while i < lines.len() && !lines[i].is_empty() {
                i += 1;
            }
            continue;
        }
        if l == "Error: The error occurred when TLC was evaluating the nested" {
            if lines.get(i) == Some(&"expressions at the following positions:") {
                i += 1;
            }
            while i < lines.len() && !lines[i].is_empty() {
                i += 1;
            }
            continue;
        }
        // TLC's stack of the expressions it was fingerprinting: as the nested expressions above
        if l == "Fingerprint Stack Trace:" {
            while i < lines.len() && (lines[i].is_empty() || is_fp_frame(lines[i])) {
                i += 1;
            }
            continue;
        }
        // A state printed after the message, without a `State N:` line: kept as one line, in the
        // canonical form of a state
        if l.ends_with("by the initial state:") || l == "While working on the initial state:" {
            let mut st = vec![];
            while i < lines.len() && !lines[i].is_empty() {
                st.push(lines[i]);
                i += 1;
            }
            kept.push(l.to_string());
            kept.push(canon_state_text(&st.join("\n")));
            continue;
        }
        if l == "Residual stack trace follows:" {
            while i < lines.len() && lines[i].contains(" starting at line ") {
                i += 1;
            }
            continue;
        }
        if l == "tla2sany.semantic.AbortException" {
            continue;
        }
        if let Some(_class) = l.strip_prefix("The exception was a ") {
            if let Some(m) = lines.get(i).and_then(|n| n.strip_prefix(": ")) {
                kept.push(strip_java_class(m).to_string());
                i += 1;
            }
            continue;
        }
        if l.trim().is_empty() || is_progress(l) {
            continue;
        }
        kept.push(l.to_string());
    }
    kept
}

/// The error lines of the canonical text (see the module comment)
pub fn errors(kept: &[String]) -> Vec<String> {
    kept.iter().filter(|l| l.starts_with("Error:") && *l != "Error: TLC was unable to fingerprint.").cloned().collect()
}

fn hashed(name: &str, lines: &[String]) -> String {
    if lines.is_empty() {
        return format!("{name} 0");
    }
    let text: String = lines.iter().map(|l| format!("{l}\n")).collect();
    format!("{name} {} {}", lines.len(), sha256(text.as_bytes()))
}

/// `tla2rs --messages FILE` / `--messages-text FILE`
pub fn main(mode: &str, path: &str) -> i32 {
    let out = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return 2;
        }
    };
    let kept = canon(&out);
    if mode == "--messages-text" {
        kept.iter().for_each(|l| println!("{l}"));
    } else {
        println!("{}", hashed("messages", &kept));
        println!("{}", hashed("errors", &errors(&kept)));
    }
    0
}
