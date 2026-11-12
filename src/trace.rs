//! Reduces the counterexample in the output of TLC or of a generated checker to a canonical form
//! and its hash, so that two counterexamples can be compared as a whole.
//!
//! A counterexample is a list of steps. Each starts with a line `State N: <Action line L, col C to
//! line L2, col C2 of module M>` (`<Initial predicate>` for the first), `State N: Stuttering` or
//! `Back to state N: <...>`, followed by the state as TLC prints it, up to an empty line. The state
//! is reduced as in a state graph (`graph::canon_state_text`: its variables in the order printed,
//! `<<>>` read as `<< >>`).
//!
//! `tla2rs --trace FILE` prints `trace N <sha256>` (N is the number of `State N:` lines) or
//! `trace 0`; `--trace-text FILE` prints the canonical form, two lines per step, for diffing.

use crate::graph::{canon_state_text, sha256};

pub struct Step {
    /// The line that starts the step
    pub header: String,
    /// The state as printed (empty for `Stuttering` and `Back to state`)
    pub state: String,
}

fn is_header(l: &str) -> bool {
    let after_no = |s: &str| s.trim_start_matches(|c: char| c.is_ascii_digit()).starts_with(": ");
    l.strip_prefix("State ").is_some_and(after_no) || l.strip_prefix("Back to state ").is_some_and(after_no)
}

/// The steps of the counterexample in `out`, in order
pub fn steps(out: &str) -> Vec<Step> {
    let mut steps: Vec<Step> = vec![];
    let mut in_state = false;
    for l in out.lines() {
        if is_header(l) {
            steps.push(Step { header: l.to_string(), state: String::new() });
            in_state = true;
        } else if l.is_empty() {
            in_state = false;
        } else if in_state {
            let s = &mut steps.last_mut().unwrap().state;
            if !s.is_empty() {
                s.push('\n');
            }
            s.push_str(l);
        }
    }
    steps
}

/// The canonical form: per step its first line, then the canonical text of its state
pub fn canon(out: &str) -> String {
    let mut o = String::new();
    for s in steps(out) {
        o += &s.header;
        o.push('\n');
        o += &canon_state_text(&s.state);
        o.push('\n');
    }
    o
}

/// `tla2rs --trace FILE` / `--trace-text FILE`
pub fn main(mode: &str, path: &str) -> i32 {
    let out = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("cannot read {path}: {e}");
            return 2;
        }
    };
    let text = canon(&out);
    if mode == "--trace-text" {
        print!("{text}");
        return 0;
    }
    let n = steps(&out).iter().filter(|s| s.header.starts_with("State ")).count();
    if n == 0 {
        println!("trace 0");
    } else {
        println!("trace {n} {}", sha256(text.as_bytes()));
    }
    0
}
