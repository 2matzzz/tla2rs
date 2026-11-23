//! The self-test of a library crate written by `tla2rs --emit-lib` (run by scripts/lib.sh for a
//! configuration TLC finds no error in): the graph the library builds is written in the form of
//! `-dumpgraph`, to be compared with TLC's, every state is read as values and built again from
//! them, and a `Checker` takes every step of the graph and refuses one that is no step.
//!
//!   driver GRAPH.dot

use spec::conform::*;
use std::collections::HashSet;
use std::fmt::Write;

fn esc(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"").replace('\n', "\\n")
}

fn opaque(v: &Val) -> bool {
    match v {
        Val::Opaque(_) => true,
        Val::Set(xs) | Val::Seq(xs) => xs.iter().any(opaque),
        Val::Rec(fs) => fs.iter().any(|(_, x)| opaque(x)),
        Val::Fun(ps) => ps.iter().any(|(k, x)| opaque(k) || opaque(x)),
        _ => false,
    }
}

fn fail(msg: String) -> ! {
    println!("FAIL {msg}");
    std::process::exit(1)
}

fn main() {
    let out = std::env::args().nth(1).expect("the file to write the graph to");
    let g = Graph::explore();

    // The graph, with the stuttering steps the spec takes (the library's graph leaves them out)
    let mut dot = String::from("strict digraph DiskGraph {\n");
    for (i, s) in g.states.iter().enumerate() {
        writeln!(dot, "{i} [label=\"{}\"{}", esc(&s.show()), if g.initial.contains(&i) { ",style = filled]" } else { "];" }).unwrap();
    }
    let mut stutters = 0;
    for (i, s) in g.states.iter().enumerate() {
        if successors(*s).iter().any(|(t, _)| t == s) {
            writeln!(dot, "{i} -> {i};").unwrap();
            stutters += 1;
        }
        for &e in &g.out[i] {
            writeln!(dot, "{i} -> {};", g.edges[e].1).unwrap();
        }
    }
    dot += "}\n";
    std::fs::write(&out, dot).expect("write the graph");

    // Every state read as values and built again
    let (mut built, mut unbuilt) = (0, 0);
    for s in &g.states {
        let vars = s.vars();
        if vars.iter().any(|(_, v)| opaque(v)) {
            unbuilt += 1;
            if state(&vars).is_ok() {
                fail(format!("a state with a value that cannot be converted was built:\n{}", s.show()));
            }
            continue;
        }
        match state(&vars) {
            Ok(t) if t == *s => built += 1,
            Ok(t) => fail(format!("built another state:\n{}\nfrom the values of\n{}", t.show(), s.show())),
            Err(e) => fail(format!("{e}, building\n{}", s.show())),
        }
        if !s.in_type() {
            fail(format!("a state of the graph outside its type:\n{}", s.show()));
        }
    }
    if !VARIABLES.is_empty() && !g.states.is_empty() {
        let vars = g.states[0].vars();
        if state(&vars[1..]).is_ok() || state(&[vars.clone(), vec![("no such variable", Val::Int(0))]].concat()).is_ok() || state(&[vars.clone(), vars.clone()].concat()).is_ok() {
            fail("a state was built from a missing, an unknown or a repeated variable".into());
        }
    }

    // A Checker takes every step of the graph, under the name of its action: each state is
    // reached along a shortest path, once for each of its steps. A deep graph has long paths, so
    // the steps taken on the way are bounded, and the states beyond are left out
    let none = HashSet::new();
    let mut steps = 0;
    let mut covered: HashSet<(Abs, Abs, u32)> = HashSet::new();
    let mut budget: usize = 200_000;
    let mut all = true;
    for i in 0..g.states.len() {
        let path = g.path_to(i, &none).unwrap_or_else(|| fail(format!("no path to state {i}")));
        let cost = (path.len() + 1) * (g.out[i].len() + 2);
        if cost > budget {
            all = false;
            break;
        }
        budget -= cost;
        let first = path.first().map_or(i, |&e| g.edges[e].0);
        let mut c = Checker::begin(g.states[first]).unwrap_or_else(|v| fail(format!("{v}, starting in\n{}", g.states[first].show())));
        for &e in &path {
            let (_, to, l) = g.edges[e];
            if let Err(v) = c.step(g.states[to], Some(action_name(l))) {
                fail(format!("{v}, on a step of the graph to\n{}", g.states[to].show()));
            }
        }
        for &e in &g.out[i] {
            let (_, to, l) = g.edges[e];
            let mut c = Checker::begin(g.states[first]).unwrap();
            for &p in &path {
                c.step(g.states[g.edges[p].1], None).unwrap();
            }
            match c.step(g.states[to], Some(action_name(l))) {
                Ok(by) if by.contains(&l) => steps += 1,
                Ok(_) => fail("a step explained by other actions than its own".into()),
                Err(v) => fail(format!("{v}, on a step of the graph to\n{}", g.states[to].show())),
            }
            if c.step(g.states[to], None).map_or(true, |by| !by.is_empty()) {
                fail("a stuttering step was not accepted as one".into());
            }
            covered.extend(c.steps);
        }
        // A state that is no successor is refused, and the run stays where it was
        let succ: HashSet<Abs> = successors(g.states[i]).into_iter().map(|(t, _)| t).collect();
        if let Some(other) = g.states.iter().find(|t| **t != g.states[i] && !succ.contains(t)) {
            let mut c = Checker::begin(g.states[first]).unwrap();
            for &p in &path {
                c.step(g.states[g.edges[p].1], None).unwrap();
            }
            match c.step(*other, None) {
                Err(Violation::NoSuchStep { .. }) if c.current() == g.states[i] => {}
                r => fail(format!("a step that is none of the spec was not refused: {r:?}")),
            }
        }
    }
    if all && g.covered(&covered).iter().any(|c| !c) {
        fail("an edge of the graph is not covered after every step was taken".into());
    }
    println!("ok states {} edges {} stutters {stutters} built {built} unbuilt {unbuilt} steps {steps} actions {}", g.states.len(), g.edges.len(), g.actions().len());
}
