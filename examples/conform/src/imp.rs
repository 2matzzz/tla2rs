//! The implementation under test: a two-phase commit written without reference to the spec's data
//! types. Nodes talk through a `Network` that keeps every message sent (a node may read any of them
//! at any time, and more than once), as the `msgs` of examples/TwoPhase.tla does.

use std::collections::BTreeSet;

pub const N: usize = 5;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RmState {
    Working,
    Prepared,
    Committed,
    Aborted,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TmState {
    Init,
    Committed,
    Aborted,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Msg {
    Prepared(usize),
    Commit,
    Abort,
}

/// Bugs to plant, to see whether the check finds them
#[derive(Clone, Copy, Default)]
pub struct Bugs {
    /// The TM commits once a majority is prepared instead of everyone
    pub quorum_commit: bool,
    /// The last RM becomes prepared but its Prepared message is never sent
    pub lost_prepared: bool,
}

#[derive(Clone, Default)]
pub struct Network {
    pub sent: BTreeSet<Msg>,
}

impl Network {
    fn send(&mut self, m: Msg) {
        self.sent.insert(m);
    }
}

#[derive(Clone)]
pub struct ResourceManager {
    pub id: usize,
    pub state: RmState,
}

impl ResourceManager {
    pub fn prepare(&mut self, net: &mut Network, bugs: Bugs) {
        if self.state == RmState::Working {
            self.state = RmState::Prepared;
            if !(bugs.lost_prepared && self.id == N - 1) {
                net.send(Msg::Prepared(self.id));
            }
        }
    }

    pub fn choose_to_abort(&mut self) {
        if self.state == RmState::Working {
            self.state = RmState::Aborted;
        }
    }

    pub fn on_message(&mut self, m: Msg) {
        match m {
            Msg::Commit => self.state = RmState::Committed,
            Msg::Abort => self.state = RmState::Aborted,
            Msg::Prepared(_) => {}
        }
    }
}

#[derive(Clone)]
pub struct TransactionManager {
    pub state: TmState,
    pub prepared: BTreeSet<usize>,
}

impl TransactionManager {
    pub fn on_message(&mut self, m: Msg) {
        if let (Msg::Prepared(r), TmState::Init) = (m, self.state) {
            self.prepared.insert(r);
        }
    }

    pub fn try_commit(&mut self, net: &mut Network, bugs: Bugs) {
        let need = if bugs.quorum_commit { N / 2 + 1 } else { N };
        if self.state == TmState::Init && self.prepared.len() >= need {
            self.state = TmState::Committed;
            net.send(Msg::Commit);
        }
    }

    /// A design choice the spec does not make: once every RM is prepared, this TM no longer
    /// aborts. The spec's TMAbort allows it, so the implementation takes fewer steps than the spec.
    pub fn abort(&mut self, net: &mut Network) {
        if self.state == TmState::Init && self.prepared.len() < N {
            self.state = TmState::Aborted;
            net.send(Msg::Abort);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Event {
    RmPrepare(usize),
    RmChooseToAbort(usize),
    TmCommit,
    TmAbort,
    DeliverToTm(Msg),
    DeliverToRm(usize, Msg),
}

#[derive(Clone)]
pub struct System {
    pub tm: TransactionManager,
    pub rms: Vec<ResourceManager>,
    pub net: Network,
    pub bugs: Bugs,
}

impl System {
    pub fn new(bugs: Bugs) -> Self {
        System {
            tm: TransactionManager { state: TmState::Init, prepared: BTreeSet::new() },
            rms: (0..N).map(|id| ResourceManager { id, state: RmState::Working }).collect(),
            net: Network::default(),
            bugs,
        }
    }

    /// Everything a scheduler may do next (an event may turn out to change nothing)
    pub fn events(&self) -> Vec<Event> {
        let mut v = vec![Event::TmCommit, Event::TmAbort];
        for i in 0..N {
            v.push(Event::RmPrepare(i));
            v.push(Event::RmChooseToAbort(i));
        }
        for &m in &self.net.sent {
            match m {
                Msg::Prepared(_) => v.push(Event::DeliverToTm(m)),
                Msg::Commit | Msg::Abort => (0..N).for_each(|i| v.push(Event::DeliverToRm(i, m))),
            }
        }
        v
    }

    pub fn apply(&mut self, e: Event) {
        match e {
            Event::RmPrepare(i) => self.rms[i].prepare(&mut self.net, self.bugs),
            Event::RmChooseToAbort(i) => self.rms[i].choose_to_abort(),
            Event::TmCommit => self.tm.try_commit(&mut self.net, self.bugs),
            Event::TmAbort => self.tm.abort(&mut self.net),
            Event::DeliverToTm(m) => self.tm.on_message(m),
            Event::DeliverToRm(i, m) => self.rms[i].on_message(m),
        }
    }
}
