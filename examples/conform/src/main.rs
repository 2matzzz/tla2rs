//! Checks an implementation of two-phase commit (imp.rs) against examples/TwoPhase.tla with the
//! library `tla2rs examples/TwoPhase.tla --emit-lib` writes, and measures how much of the spec's
//! state graph the runs exercised.
//!
//!   1. random runs: every step of the implementation must be a step of the spec
//!   2. coverage of the spec's states, transitions and actions
//!   3. guided runs: the implementation is driven along a shortest path to each transition not
//!      taken yet; what is left is what the implementation does not do
//!
//!   cargo run --release [-- --bug quorum-commit | lost-prepared] [--policy happy] [--runs N] [--steps N] [--seed N]

mod imp;

use imp::{Bugs, Event, Msg, RmState, System, TmState};
use spec::conform::{action_name, state, Abs, Checker, Graph, Val, Violation};
use std::collections::HashSet;

/// The abstraction function: the state of the spec the implementation is in. The one part
/// written for the spec; the rest of this file knows the implementation only by its events
fn abs(sys: &System) -> Abs {
    let rm = |i: usize| Val::model(&format!("r{}", i + 1));
    let rm_state = |s: RmState| match s {
        RmState::Working => "working",
        RmState::Prepared => "prepared",
        RmState::Committed => "committed",
        RmState::Aborted => "aborted",
    };
    let msg = |m: &Msg| match m {
        Msg::Prepared(r) => Val::rec([("type", "Prepared".into()), ("rm", rm(*r))]),
        Msg::Commit => Val::rec([("type", "Commit".into()), ("rm", "tm".into())]),
        Msg::Abort => Val::rec([("type", "Abort".into()), ("rm", "tm".into())]),
    };
    state(&[
        ("rmState", Val::fun(sys.rms.iter().map(|r| (rm(r.id), rm_state(r.state).into())))),
        (
            "tmState",
            match sys.tm.state {
                TmState::Init => "init".into(),
                TmState::Committed => "committed".into(),
                TmState::Aborted => "aborted".into(),
            },
        ),
        ("tmPrepared", Val::set(sys.tm.prepared.iter().map(|&r| rm(r)))),
        ("msgs", Val::set(sys.net.sent.iter().map(msg))),
    ])
    .expect("a state within the spec's types")
}

struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Policy {
    /// Any event
    Random,
    /// What a test suite of happy paths does: nobody ever aborts
    Happy,
}

struct Failure {
    events: Vec<Event>,
    from: Abs,
    event: Event,
    to: Abs,
    violation: Violation,
}

#[derive(Default)]
struct Cover {
    states: HashSet<Abs>,
    steps: HashSet<(Abs, Abs, u32)>,
}

impl Cover {
    fn add(&mut self, c: Checker) {
        self.states.extend(c.states);
        self.steps.extend(c.steps);
    }
}

fn random_run(bugs: Bugs, policy: Policy, rng: &mut Rng, steps: usize, cover: &mut Cover) -> Result<(), Failure> {
    let mut sys = System::new(bugs);
    let mut checker = Checker::begin(abs(&sys)).expect("the implementation starts in an initial state of the spec");
    let mut events = vec![];
    for _ in 0..steps {
        let mut choices = sys.events();
        if policy == Policy::Happy {
            choices.retain(|e| !matches!(e, Event::RmChooseToAbort(_) | Event::TmAbort));
        }
        let e = choices[rng.below(choices.len())];
        sys.apply(e);
        let (from, to) = (checker.current(), abs(&sys));
        match checker.step(to, None) {
            Ok(by) if by.is_empty() => {}
            Ok(_) => events.push(e),
            Err(violation) => return Err(Failure { events, from, event: e, to, violation }),
        }
    }
    cover.add(checker);
    Ok(())
}

/// The event that takes the implementation to state `to` of the spec, found by trying every
/// event on a copy
fn event_to(sys: &System, to: Abs) -> Option<Event> {
    sys.events().into_iter().find(|e| {
        let mut t = sys.clone();
        t.apply(*e);
        abs(&t) == to
    })
}

/// Drives a fresh implementation along `path` (edges of the spec's graph from an initial state),
/// then on along edges not covered yet for as long as it takes them. The error is the edge of
/// the path no event takes.
fn guided_run(g: &Graph, path: &[usize], hit: &mut [bool], bugs: Bugs, cover: &mut Cover) -> Result<(), usize> {
    let mut sys = System::new(bugs);
    let mut checker = Checker::begin(abs(&sys)).expect("an initial state");
    // Takes edge `e` if some event does, and marks the edges the step covers
    fn take(g: &Graph, sys: &mut System, checker: &mut Checker, hit: &mut [bool], e: usize) -> bool {
        let (from, to, l) = g.edges[e];
        let Some(event) = event_to(sys, g.states[to]) else { return false };
        sys.apply(event);
        let by = checker.step(abs(sys), Some(action_name(l))).expect("a step along an edge of the spec");
        for &k in &g.out[from] {
            if g.edges[k].1 == to && by.contains(&g.edges[k].2) {
                hit[k] = true;
            }
        }
        true
    }
    let mut failed = None;
    for &e in path {
        if !take(g, &mut sys, &mut checker, hit, e) {
            failed = Some(e);
            break;
        }
    }
    while failed.is_none() {
        let at = g.index[&checker.current()];
        let Some(&e) = g.out[at].iter().find(|&&e| !hit[e]) else { break };
        if !take(g, &mut sys, &mut checker, hit, e) {
            break;
        }
    }
    cover.add(checker);
    failed.map_or(Ok(()), Err)
}

fn pct(a: usize, b: usize) -> String {
    format!("{a:>6} / {b:<6} {:>5.1}%", 100.0 * a as f64 / b.max(1) as f64)
}

fn report(g: &Graph, cover: &Cover, title: &str) {
    let hit = g.covered(&cover.steps);
    println!("\n== coverage {title}");
    println!("  states       {}", pct(g.states.iter().filter(|s| cover.states.contains(s)).count(), g.states.len()));
    println!("  transitions  {}", pct(hit.iter().filter(|h| **h).count(), g.edges.len()));
    for l in g.actions() {
        let of: Vec<usize> = (0..g.edges.len()).filter(|&e| g.edges[e].2 == l).collect();
        let n = of.iter().filter(|&&e| hit[e]).count();
        println!("    {:<16} {}{}", action_name(l), pct(n, of.len()), if n == 0 { "   <- never taken" } else { "" });
    }
}

fn indent(s: &str) -> String {
    s.lines().map(|l| format!("      {l}")).collect::<Vec<_>>().join("\n")
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let opt = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned();
    let mut bugs = Bugs::default();
    match opt("--bug").as_deref() {
        Some("quorum-commit") => bugs.quorum_commit = true,
        Some("lost-prepared") => bugs.lost_prepared = true,
        Some(b) => panic!("unknown bug {b}"),
        None => {}
    }
    let policy = if opt("--policy").as_deref() == Some("happy") { Policy::Happy } else { Policy::Random };
    let runs: usize = opt("--runs").map_or(1000, |v| v.parse().unwrap());
    let steps: usize = opt("--steps").map_or(60, |v| v.parse().unwrap());
    let mut rng = Rng(opt("--seed").map_or(0x9E3779B97F4A7C15, |v| v.parse().unwrap()));

    let g = Graph::explore();
    println!("spec: {} reachable states, {} transitions (stuttering steps left out)", g.states.len(), g.edges.len());

    // 1. random runs, each step checked against the spec
    let mut cover = Cover::default();
    for run in 0..runs {
        if let Err(f) = random_run(bugs, policy, &mut rng, steps, &mut cover) {
            println!("\nrun {run}: the implementation left the spec after {} steps", f.events.len());
            for (n, e) in f.events.iter().enumerate() {
                println!("  {:>2}. {e:?}", n + 1);
            }
            println!("  state before:\n{}", indent(&f.from.show()));
            println!("  event: {:?}", f.event);
            println!("  state after:\n{}", indent(&f.to.show()));
            println!("  {}", f.violation);
            std::process::exit(1);
        }
    }
    println!("{runs} random runs of {steps} events: every step is a step of the spec");
    report(&g, &cover, "after the random runs");

    // 2. guided runs to each transition not covered yet
    let mut hit = g.covered(&cover.steps);
    let mut blocked: HashSet<usize> = HashSet::new();
    let mut unreachable = 0;
    let mut guided = 0;
    for target in 0..g.edges.len() {
        while !hit[target] && !blocked.contains(&target) {
            let Some(mut path) = g.path_to(g.edges[target].0, &blocked) else {
                unreachable += 1;
                break;
            };
            path.push(target);
            guided += 1;
            if let Err(e) = guided_run(&g, &path, &mut hit, bugs, &mut cover) {
                blocked.insert(e);
            }
        }
    }
    report(&g, &cover, &format!("after {guided} guided runs"));

    let left = g.covered(&cover.steps).iter().filter(|h| !**h).count();
    println!("\n== {left} transitions of the spec the implementation does not take");
    println!("  {} refused in a state the implementation reaches, {unreachable} from states it never reaches", blocked.len());
    for l in g.actions() {
        let of: Vec<usize> = blocked.iter().copied().filter(|&e| g.edges[e].2 == l).collect();
        if let Some(&e) = of.iter().min() {
            println!("  {}: {} refused, for example from\n{}", action_name(l), of.len(), indent(&g.states[g.edges[e].0].show()));
        }
    }
}
