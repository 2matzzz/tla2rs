//! Temporal formulas over atoms (state predicates, ENABLED, and action predicates on the step
//! taken from a state) and their translation into a generalized Büchi automaton, with the tableau
//! construction of Gerth, Peled, Vardi and Wolper. The checker looks for a fair cycle in the
//! product of the state graph with the automaton of the negated property.

use std::collections::BTreeSet;

/// A formula in negation normal form: negation only on atoms.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ltl {
    Bool(bool),
    /// Atom index and polarity (false: the atom is negated)
    Atom(usize, bool),
    And(Vec<Ltl>),
    Or(Vec<Ltl>),
    /// []
    Always(Box<Ltl>),
    /// <>
    Eventually(Box<Ltl>),
}

impl Ltl {
    /// The negation, kept in negation normal form
    pub fn not(&self) -> Ltl {
        match self {
            Ltl::Bool(b) => Ltl::Bool(!b),
            Ltl::Atom(a, p) => Ltl::Atom(*a, !p),
            Ltl::And(xs) => Ltl::Or(xs.iter().map(|x| x.not()).collect()),
            Ltl::Or(xs) => Ltl::And(xs.iter().map(|x| x.not()).collect()),
            Ltl::Always(x) => Ltl::Eventually(x.not().into()),
            Ltl::Eventually(x) => Ltl::Always(x.not().into()),
        }
    }
}

/// A state of the automaton. `lits` must hold at the position the automaton is in: state atoms on
/// the current state, action atoms on the step taken from it.
#[derive(Clone, Debug)]
pub struct Node {
    pub lits: Vec<(usize, bool)>,
    pub succ: Vec<usize>,
    pub init: bool,
    /// Bit j: the node is in acceptance set j
    pub acc: u64,
}

/// Binary formulas used by the construction: `U(a, b)` is a U b, `R(a, b)` is a R b
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum F {
    True,
    False,
    Lit(usize, bool),
    And(Box<F>, Box<F>),
    Or(Box<F>, Box<F>),
    U(Box<F>, Box<F>),
    R(Box<F>, Box<F>),
}

fn to_f(l: &Ltl) -> F {
    let fold = |xs: &[Ltl], and: bool| -> F {
        let mut it = xs.iter().map(to_f);
        let Some(first) = it.next() else { return if and { F::True } else { F::False } };
        it.fold(first, |a, b| if and { F::And(a.into(), b.into()) } else { F::Or(a.into(), b.into()) })
    };
    match l {
        Ltl::Bool(true) => F::True,
        Ltl::Bool(false) => F::False,
        Ltl::Atom(a, p) => F::Lit(*a, *p),
        Ltl::And(xs) => fold(xs, true),
        Ltl::Or(xs) => fold(xs, false),
        Ltl::Always(x) => F::R(F::False.into(), to_f(x).into()),
        Ltl::Eventually(x) => F::U(F::True.into(), to_f(x).into()),
    }
}

struct Proto {
    incoming: BTreeSet<usize>,
    new: Vec<F>,
    old: BTreeSet<F>,
    next: BTreeSet<F>,
}

/// usize::MAX in `incoming` marks an initial node
const INIT: usize = usize::MAX;

/// The automaton of `f` and the number of acceptance sets. Fails if the automaton grows beyond
/// `max_nodes` states, or its construction beyond 256 steps per such state (it can take
/// exponentially many steps per state: a conjunction of n []<> formulas branches 2^n ways at each).
pub fn automaton(f: &Ltl, max_nodes: usize) -> Result<(Vec<Node>, usize), String> {
    let mut done: Vec<Proto> = vec![];
    // The node of each (old, next), so that a finished node is merged into an equal one at once
    let mut index: std::collections::HashMap<(BTreeSet<F>, BTreeSet<F>), usize> = std::collections::HashMap::new();
    let mut work = vec![Proto { incoming: [INIT].into(), new: vec![to_f(f)], old: BTreeSet::new(), next: BTreeSet::new() }];
    let mut steps = 0usize;
    while let Some(mut n) = work.pop() {
        if done.len() > max_nodes {
            return Err(format!("the temporal property needs more than {max_nodes} automaton states"));
        }
        steps += 1;
        if steps > max_nodes * 256 {
            return Err(format!("the automaton of the temporal property takes more than {} steps to build", max_nodes * 256));
        }
        let Some(eta) = n.new.pop() else {
            let key = (n.old.clone(), n.next.clone());
            if let Some(&d) = index.get(&key) {
                done[d].incoming.extend(n.incoming);
                continue;
            }
            let id = done.len();
            index.insert(key, id);
            let next: Vec<F> = n.next.iter().cloned().collect();
            done.push(n);
            work.push(Proto { incoming: [id].into(), new: next, old: BTreeSet::new(), next: BTreeSet::new() });
            continue;
        };
        if n.old.contains(&eta) {
            work.push(n);
            continue;
        }
        match eta.clone() {
            F::True => {
                n.old.insert(eta);
                work.push(n);
            }
            F::False => {}
            F::Lit(a, p) => {
                if !n.old.contains(&F::Lit(a, !p)) {
                    n.old.insert(eta);
                    work.push(n);
                }
            }
            F::And(a, b) => {
                n.new.push(*a);
                n.new.push(*b);
                n.old.insert(eta);
                work.push(n);
            }
            F::Or(a, b) => {
                let mut n2 = Proto { incoming: n.incoming.clone(), new: n.new.clone(), old: n.old.clone(), next: n.next.clone() };
                n.new.push(*a);
                n2.new.push(*b);
                n.old.insert(eta.clone());
                n2.old.insert(eta);
                work.push(n);
                work.push(n2);
            }
            // a U b: b now, or a now and a U b next
            F::U(a, b) => {
                let mut n2 = Proto { incoming: n.incoming.clone(), new: n.new.clone(), old: n.old.clone(), next: n.next.clone() };
                n.new.push(*a);
                n.next.insert(eta.clone());
                n2.new.push(*b);
                n.old.insert(eta.clone());
                n2.old.insert(eta);
                work.push(n);
                work.push(n2);
            }
            // a R b: a and b now, or b now and a R b next
            F::R(a, b) => {
                let mut n2 = Proto { incoming: n.incoming.clone(), new: n.new.clone(), old: n.old.clone(), next: n.next.clone() };
                n.new.push(*a);
                n.new.push(*b.clone());
                n2.new.push(*b);
                n2.next.insert(eta.clone());
                n.old.insert(eta.clone());
                n2.old.insert(eta);
                work.push(n);
                work.push(n2);
            }
        }
    }
    // One acceptance set per U subformula: nodes where it is not pending, or where it is fulfilled
    let mut untils: BTreeSet<F> = BTreeSet::new();
    for d in &done {
        for x in &d.old {
            if let F::U(..) = x {
                untils.insert(x.clone());
            }
        }
    }
    if untils.len() > 64 {
        return Err("the temporal property has more than 64 eventualities".into());
    }
    let mut nodes: Vec<Node> = done
        .iter()
        .map(|d| {
            let lits = d.old.iter().filter_map(|x| if let F::Lit(a, p) = x { Some((*a, *p)) } else { None }).collect();
            let mut acc = 0u64;
            for (j, u) in untils.iter().enumerate() {
                let F::U(_, b) = u else { unreachable!() };
                if !d.old.contains(u) || d.old.contains(b) {
                    acc |= 1 << j;
                }
            }
            Node { lits, succ: vec![], init: d.incoming.contains(&INIT), acc }
        })
        .collect();
    for (m, d) in done.iter().enumerate() {
        for &i in &d.incoming {
            if i != INIT {
                nodes[i].succ.push(m);
            }
        }
    }
    Ok((nodes, untils.len()))
}
