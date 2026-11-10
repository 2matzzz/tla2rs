//! Runtime support pasted into every generated checker. The generated code depends on no external
//! crates.
//!
//! - States are bit-packed (`Packed`) into a flat array that serves as both the BFS queue and the
//!   record used to rebuild traces.
//! - The visited set stores only 64-bit fingerprints (the same approach as TLC). When a state fits
//!   in 64 bits, the fingerprint is invertible, so there are no collisions.

pub const RUNTIME: &str = r##"
// ---------------------------------------------------------------- runtime (tla2rs)

#[inline(always)]
fn put(w: &mut [u64], p: &mut u32, mut v: u128, mut n: u32) {
    if n <= 64 {
        let (i, o) = ((*p / 64) as usize, *p % 64);
        let x = (v as u64) & if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
        w[i] |= x << o;
        if o + n > 64 {
            w[i + 1] |= x >> (64 - o);
        }
        *p += n;
        return;
    }
    while n > 0 {
        let i = (*p / 64) as usize;
        let o = *p % 64;
        let take = (64 - o).min(n);
        let mask = if take == 64 { u64::MAX } else { (1u64 << take) - 1 };
        w[i] |= ((v as u64) & mask) << o;
        v >>= take;
        n -= take;
        *p += take;
    }
}

#[inline]
fn get(w: &[u64], p: &mut u32, mut n: u32) -> u128 {
    let mut out = 0u128;
    let mut got = 0;
    while n > 0 {
        let i = (*p / 64) as usize;
        let o = *p % 64;
        let take = (64 - o).min(n);
        let mask = if take == 64 { u64::MAX } else { (1u64 << take) - 1 };
        out |= (((w[i] >> o) & mask) as u128) << got;
        got += take;
        n -= take;
        *p += take;
    }
    out
}

/// Assigns a fingerprint to one of 1024 shards by its top 10 bits.
#[inline]
fn shard(fp: Fp) -> usize {
    (fp >> (FP_BITS - 10)) as usize
}

#[inline]
fn mix(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

/// Fingerprint of a packed state. The low 64 bits sum the words, each mixed with its position on
/// its own: no word waits for the one before it, so the CPU mixes several at a time. (With
/// WORDS == 1 this is a bijection, so there are no collisions.) With `-fp128`, an independent
/// 64-bit hash is placed above them to make 128 bits.
#[inline]
fn fingerprint(w: &[u64]) -> Fp {
    let mut h = 0u64;
    for (i, &x) in w.iter().enumerate() {
        h = h.wrapping_add(mix(x.wrapping_add((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15))));
    }
    let lo = mix(h);
    if FP_BITS == 64 {
        return lo as Fp;
    }
    let mut g = 0x9e37_79b9_7f4a_7c15u64;
    for (i, &x) in w.iter().enumerate() {
        g = mix(g ^ x).wrapping_add(i as u64).rotate_left(17);
    }
    (lo as Fp) | ((mix(g) as Fp) << 64)
}

/// The set of visited fingerprints (open addressing). 0 marks an empty slot, so the state whose
/// fingerprint is 0 is tracked separately.
/// With keep_pred, it also stores the fingerprint of the state each state was first reached from
/// (to reconstruct counterexamples). Initial states point to their own fingerprint.
struct FpSet {
    t: Vec<Fp>,
    /// Indexed in parallel with t. Empty when keep_pred is false.
    p: Vec<Fp>,
    n: usize,
    mask: usize,
    /// If the state with fingerprint 0 has been seen, the fingerprint of its predecessor.
    zero: Option<Fp>,
    keep_pred: bool,
}

impl FpSet {
    fn new(keep_pred: bool) -> Self {
        let cap = 1 << 8;
        FpSet {
            t: vec![0; cap],
            p: if keep_pred { vec![0; cap] } else { vec![] },
            n: 0,
            mask: cap - 1,
            zero: None,
            keep_pred,
        }
    }
    #[inline]
    fn insert(&mut self, fp: Fp) -> bool {
        self.insert_with(fp, 0)
    }
    #[inline]
    fn insert_with(&mut self, fp: Fp, pred: Fp) -> bool {
        if fp == 0 {
            let fresh = self.zero.is_none();
            if fresh {
                self.zero = Some(pred);
            }
            return fresh;
        }
        if (self.n + 1) * 4 > self.t.len() * 3 {
            self.grow();
        }
        let mut i = (fp as usize) & self.mask;
        loop {
            let x = self.t[i];
            if x == 0 {
                self.t[i] = fp;
                if self.keep_pred {
                    self.p[i] = pred;
                }
                self.n += 1;
                return true;
            }
            if x == fp {
                return false;
            }
            i = (i + 1) & self.mask;
        }
    }
    /// Whether fp is already in the set.
    #[inline]
    fn contains(&self, fp: Fp) -> bool {
        if fp == 0 {
            return self.zero.is_some();
        }
        let mut i = (fp as usize) & self.mask;
        loop {
            let x = self.t[i];
            if x == 0 {
                return false;
            }
            if x == fp {
                return true;
            }
            i = (i + 1) & self.mask;
        }
    }

    /// The fingerprint of the state this state was first reached from. For an initial state, its
    /// own fingerprint.
    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        if !self.keep_pred {
            return None;
        }
        if fp == 0 {
            return self.zero;
        }
        let mut i = (fp as usize) & self.mask;
        loop {
            let x = self.t[i];
            if x == 0 {
                return None;
            }
            if x == fp {
                return Some(self.p[i]);
            }
            i = (i + 1) & self.mask;
        }
    }
    fn grow(&mut self) {
        let old_t = std::mem::take(&mut self.t);
        let old_p = std::mem::take(&mut self.p);
        let cap = old_t.len() * 2;
        self.t = vec![0; cap];
        self.p = if self.keep_pred { vec![0; cap] } else { vec![] };
        self.mask = cap - 1;
        for (k, x) in old_t.into_iter().enumerate() {
            if x != 0 {
                let mut i = (x as usize) & self.mask;
                while self.t[i] != 0 {
                    i = (i + 1) & self.mask;
                }
                self.t[i] = x;
                if self.keep_pred {
                    self.p[i] = old_p[k];
                }
            }
        }
    }
}

/// The fingerprint used for deduplication. With a VIEW, it is the fingerprint of the view's value;
/// with a SYMMETRY, that of the smallest representation among all permutations of the state.
#[inline]
fn state_fp(s: &State, w: &Packed) -> Fp {
    if !HAS_VIEW && PERMS.is_empty() {
        return fingerprint(w);
    }
    canon_fp(s).unwrap_or_else(|| type_error("VIEW value", ""))
}

/// `state_fp` without the packed state, for when there is a VIEW or a SYMMETRY. None if the key
/// (the VIEW value, or the state without a VIEW) is out of type.
fn canon_fp(s: &State) -> Option<Fp> {
    fresh_fp(s, None).flatten()
}

/// `canon_fp`, or Some(None) if `mine` shows that this thread has fingerprinted the state before.
fn fresh_fp(s: &State, mut mine: Option<&mut Seen>) -> Option<Option<Fp>> {
    // The key under the first permutation decides the smallest one, so a repeat is caught before
    // trying the others. A VIEW that does not commute with the permutations breaks this: states
    // with equal VIEW values can then have different smallest keys.
    let by_first = mine.is_some() && (!HAS_VIEW || VIEW_EQUIV);
    let mut fresh = |fp| mine.as_mut().is_none_or(|m| m.fresh(fp));
    if PERMS.is_empty() {
        let fp = fingerprint(&key_of(s)?);
        return Some(fresh(fp).then_some(fp));
    }
    let v = if VIEW_EQUIV { Some(view_val(s)) } else { None };
    let mut best: Option<Key> = None;
    for (i, p) in PERMS.iter().enumerate() {
        let k = match &v {
            Some(v) if i == 0 && PERM0_IS_ID => view_pack_v(v)?,
            Some(v) => match view_perm_pack(v, p, PERMS_INV[i], best.as_ref())? {
                Some(k) => k,
                None => continue,
            },
            None if i == 0 && PERM0_IS_ID => key_of(s)?,
            None => key_of(&perm_state(s, p))?,
        };
        if i == 0 && by_first && !fresh(fingerprint(&k)) {
            return Some(None);
        }
        if best.as_ref().is_none_or(|b| k < *b) {
            best = Some(k);
        }
    }
    let fp = fingerprint(&best.unwrap());
    Some((by_first || fresh(fp)).then_some(fp))
}

/// `state_fp`, or None if `mine` shows that this thread has fingerprinted the state before.
#[inline]
fn fresh_state_fp(s: &State, w: &Packed, mine: &mut Seen) -> Option<Fp> {
    if !HAS_VIEW && PERMS.is_empty() {
        let fp = fingerprint(w);
        return mine.fresh(fp).then_some(fp);
    }
    fresh_fp(s, Some(mine)).unwrap_or_else(|| type_error("VIEW value", ""))
}

/// Compares the fully written words `*cw..done` of a key being packed with `best`. Returns true
/// once the key is known to be greater than `best`; once it is known to be smaller, moves `*cw`
/// past the end so later calls return false at once.
#[inline]
fn prune(w: &[u64], best: Option<&Key>, done: usize, cw: &mut usize) -> bool {
    let Some(b) = best else { return false };
    while *cw < done {
        let i = *cw;
        if w[i] != b[i] {
            if w[i] > b[i] {
                return true;
            }
            *cw = usize::MAX;
            return false;
        }
        *cw += 1;
    }
    false
}

#[inline]
fn bits(mut x: u128) -> impl Iterator<Item = u64> {
    std::iter::from_fn(move || {
        if x == 0 {
            None
        } else {
            let i = x.trailing_zeros() as u64;
            x &= x - 1;
            Some(i)
        }
    })
}

#[inline]
fn tla_div(a: i64, b: i64) -> i64 {
    if b == 0 {
        eval_error("division by zero".into());
    }
    let q = a / b;
    if a % b != 0 && ((a < 0) != (b < 0)) { q - 1 } else { q }
}

#[inline]
fn tla_mod(a: i64, b: i64) -> i64 {
    if b <= 0 {
        eval_error(format!("The second argument of % should be a positive number, but instead it is: {b}"));
    }
    a.rem_euclid(b)
}

/// An evaluation error. Raised via panic, caught outside state expansion, and reported with a
/// trace.
enum EvalErr {
    /// A value outside the type declared in TypeOK (a set element, a function argument, etc.).
    Type(String),
    /// Anything else (no matching CASE arm, a non-positive right operand of %, etc.).
    Other(String),
}

/// A type whose default value is a constant. An empty `SSet` is then copied from a constant as one
/// block; filling its slots with `Default::default()` stored every field of every slot separately.
trait ConstDefault: Copy {
    const DEFAULT: Self;
}

impl ConstDefault for bool {
    const DEFAULT: Self = false;
}

macro_rules! const_default_int {
    ($($t:ty)*) => { $(impl ConstDefault for $t { const DEFAULT: Self = 0; })* };
}
const_default_int!(i64 u16 u128);

macro_rules! const_default_tuple {
    ($($t:ident)*) => {
        impl<$($t: ConstDefault),*> ConstDefault for ($($t,)*) {
            const DEFAULT: Self = ($($t::DEFAULT,)*);
        }
    };
}
const_default_tuple!(A);
const_default_tuple!(A B);
const_default_tuple!(A B C);
const_default_tuple!(A B C D);
const_default_tuple!(A B C D E);
const_default_tuple!(A B C D E F);
const_default_tuple!(A B C D E F G);
const_default_tuple!(A B C D E F G H);
const_default_tuple!(A B C D E F G H I);
const_default_tuple!(A B C D E F G H I J);
const_default_tuple!(A B C D E F G H I J K);
const_default_tuple!(A B C D E F G H I J K L);

impl<T: ConstDefault, const N: usize> ConstDefault for [T; N] {
    const DEFAULT: Self = [T::DEFAULT; N];
}

impl<T: Copy + Ord + ConstDefault, const N: usize> ConstDefault for SSet<T, N> {
    const DEFAULT: Self = SSet { len: 0, items: [T::DEFAULT; N] };
}

/// A set over a large element type, stored as a fixed-size sorted array so it can stay `Copy`.
/// Unused slots hold the default value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SSet<T: Copy + Ord + ConstDefault, const N: usize> {
    len: u8,
    items: [T; N],
}

impl<T: Copy + Ord + ConstDefault, const N: usize> SSet<T, N> {
    fn new() -> Self {
        Self::DEFAULT
    }
    #[inline]
    fn slice(&self) -> &[T] {
        &self.items[..self.len as usize]
    }
    #[inline]
    fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.slice().iter().copied()
    }
    #[inline]
    fn contains(&self, x: &T) -> bool {
        self.slice().binary_search(x).is_ok()
    }
    #[inline]
    fn with(mut self, x: T) -> Self {
        self.insert(x);
        self
    }
    // Builders in generated code use this; `acc = acc.with(x)` in a loop moved the whole array per element.
    #[inline]
    fn insert(&mut self, x: T) {
        if let Err(i) = self.slice().binary_search(&x) {
            let n = self.len as usize;
            if n == N {
                eval_error(format!("a set grew beyond {N} elements; raise the capacity with `Cardinality(x) <= K` in TypeDecl / TypeOK or -setcap"));
            }
            self.items.copy_within(i..n, i + 1);
            self.items[i] = x;
            self.len += 1;
        }
    }
    #[inline]
    fn remove(&mut self, x: T) {
        if let Ok(i) = self.slice().binary_search(&x) {
            let n = self.len as usize;
            self.items.copy_within(i + 1..n, i);
            self.items[n - 1] = T::DEFAULT;
            self.len -= 1;
        }
    }
    fn union(self, o: Self) -> Self {
        let mut r = self;
        for x in o.iter() {
            r.insert(x);
        }
        r
    }
    fn inter(self, o: Self) -> Self {
        let mut r = Self::new();
        for x in self.iter() {
            if o.contains(&x) {
                r.insert(x);
            }
        }
        r
    }
    fn minus(self, o: Self) -> Self {
        let mut r = self;
        for x in o.iter() {
            r.remove(x);
        }
        r
    }
    fn subseteq(&self, o: &Self) -> bool {
        self.iter().all(|x| o.contains(&x))
    }
}

#[cold]
fn type_error(what: &str, v: &str) -> ! {
    std::panic::panic_any(EvalErr::Type(format!("{what} {v} is outside the type declared in TypeOK")))
}

#[cold]
fn eval_error(msg: String) -> ! {
    std::panic::panic_any(EvalErr::Other(msg))
}

fn describe_panic(p: Box<dyn std::any::Any + Send>) -> EvalErr {
    match p.downcast::<EvalErr>() {
        Ok(e) => *e,
        Err(p) => {
            let m = p.downcast_ref::<String>().cloned().or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()));
            EvalErr::Other(format!("internal error in the generated checker: {}", m.unwrap_or_default()))
        }
    }
}

/// The exit code when stopping on an evaluation error. As in TLC, it is distinct from that of an
/// invariant violation (12); it is 12 only when leaving the type is reported as a TypeOK violation.
fn eval_code(e: &EvalErr) -> i32 {
    match e {
        EvalErr::Type(_) if TYPE_INV_SUBSUMED || INVARIANTS.iter().any(|(n, _)| TYPE_INVARIANT == *n) => 12,
        _ => 255,
    }
}

/// Reports a state leaving its declared type in TLC's terms: if TypeOK is an invariant, as a
/// violation of it.
fn report_eval(e: &EvalErr) {
    match e {
        EvalErr::Type(m) => {
            // The invariant that declares the types may not be checked at run time, since `pack`
            // performs the same check.
            if TYPE_INV_SUBSUMED || INVARIANTS.iter().any(|(n, _)| TYPE_INVARIANT == *n) {
                println!("Error: Invariant {TYPE_INVARIANT} is violated.");
            } else {
                println!("Error: a successor leaves the type declared in {TYPE_INVARIANT}.");
            }
            println!("  ({m}; tla2rs cannot represent that state)");
        }
        EvalErr::Other(m) => println!("Error: {m}"),
    }
}

struct Graph {
    states: Vec<Packed>,
    /// (parent index, label). Initial states have (u32::MAX, u32::MAX).
    parent: Vec<(u32, u32)>,
}

impl Graph {
    fn trace_len(&self, mut id: u32) -> usize {
        let mut n = 0;
        while id != u32::MAX {
            n += 1;
            id = self.parent[id as usize].0;
        }
        n
    }

    fn print_trace(&self, mut id: u32, extra: Option<(&State, u32)>) {
        let mut ids = vec![];
        while id != u32::MAX {
            ids.push(id);
            id = self.parent[id as usize].0;
        }
        println!("Error: The behavior up to this point is:");
        let mut n = 0;
        for id in ids.iter().rev() {
            n += 1;
            let l = self.parent[*id as usize].1;
            let name = if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
            println!("State {n}: <{name}>\n{}\n", show(&unpack(&self.states[*id as usize])));
        }
        if let Some((s, l)) = extra {
            println!("State {}: <{}>\n{}\n", n + 1, LABELS[l as usize], show(s));
        }
    }
}

fn check_invariants(s: &State) -> Option<&'static str> {
    for (name, f) in INVARIANTS {
        if !f(s) {
            return Some(name);
        }
    }
    None
}

/// The visited set, split into shards with a lock each. `at` follows each shard's table (address
/// and mask) so that a slot can be prefetched without taking the lock.
struct Shards {
    sets: Vec<std::sync::Mutex<FpSet>>,
    at: Vec<(std::sync::atomic::AtomicPtr<Fp>, std::sync::atomic::AtomicUsize)>,
}

impl Shards {
    fn new(keep_pred: bool) -> Self {
        use std::sync::atomic::{AtomicPtr, AtomicUsize};
        let sets: Vec<FpSet> = (0..1024).map(|_| FpSet::new(keep_pred)).collect();
        let at = sets.iter().map(|f| (AtomicPtr::new(f.t.as_ptr().cast_mut()), AtomicUsize::new(f.mask))).collect();
        Shards { sets: sets.into_iter().map(std::sync::Mutex::new).collect(), at }
    }
    #[inline]
    fn insert(&self, fp: Fp) -> bool {
        self.sets[shard(fp)].lock().unwrap().insert(fp)
    }
    #[inline]
    fn insert_with(&self, fp: Fp, pred: Fp) -> bool {
        use std::sync::atomic::Ordering::Relaxed;
        let sh = shard(fp);
        let mut set = self.sets[sh].lock().unwrap();
        let fresh = set.insert_with(fp, pred);
        let (at, mask) = &self.at[sh];
        if mask.load(Relaxed) != set.mask {
            at.store(set.t.as_ptr().cast_mut(), Relaxed);
            mask.store(set.mask, Relaxed);
        }
        fresh
    }
    /// Prefetches the line where `insert_with` starts looking for fp. The shard may replace its
    /// table meanwhile; prefetching an address in the old one has no effect.
    #[inline]
    fn prefetch(&self, fp: Fp) {
        use std::sync::atomic::Ordering::Relaxed;
        let (at, mask) = &self.at[shard(fp)];
        prefetch(at.load(Relaxed).wrapping_add((fp as usize) & mask.load(Relaxed)));
    }
    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        self.sets[shard(fp)].lock().unwrap().pred_of(fp)
    }
    /// Whether fp is already present. Does not modify the table.
    #[inline]
    fn contains(&self, fp: Fp) -> bool {
        self.sets[shard(fp)].lock().unwrap().contains(fp)
    }
}

enum Found {
    /// A newly found state violates an invariant (worker, index within the worker, invariant).
    Inv(usize, usize, &'static str),
    /// A successor leaves its type (parent, successor, label, violated invariant if any).
    Type(u32, State, u32, Option<&'static str>),
    /// An evaluation error while expanding the parent state.
    Eval(u32, EvalErr),
    /// [][A]_v is violated (parent, successor, label, property).
    Action(u32, State, u32, &'static str),
    Deadlock(u32),
}

/// Liveness data collected during expansion.
#[derive(Default)]
struct LiveChunk {
    /// (source, target fingerprint, label, start in tags, count). Self-loops (stuttering) are
    /// omitted.
    edges: Vec<(u32, Fp, u32, u32, u32)>,
    /// Per edge: "this transition is also an <<A>>_v step of WF instance i".
    tags: Vec<u32>,
    /// (state, start in enab, count): the WF instances enabled in that state.
    en: Vec<(u32, u32, u32)>,
    enab: Vec<u32>,
}

struct Chunk {
    states: Vec<Packed>,
    parent: Vec<(u32, u32)>,
    generated: u64,
    found: Option<Found>,
    live: LiveChunk,
}

/// Expands a single state. Returns a Found on error.
fn expand_one(
    g: &Graph,
    head: usize,
    seen: &Shards,
    me: usize,
    check_deadlock: bool,
    c: &mut Chunk,
    buf: &mut Vec<(State, u32)>,
    fbuf: &mut Vec<(State, u32)>,
    fps: &mut Vec<Vec<Fp>>,
) -> Option<Found> {
    let s = unpack(&g.states[head]);
    buf.clear();
    next(&s, buf);
    if buf.is_empty() && check_deadlock {
        return Some(Found::Deadlock(head as u32));
    }
    // Liveness: for each WF instance, the targets (fingerprints) of its <<A>>_v steps and whether
    // it is enabled.
    if LIVENESS {
        let en_off = c.live.enab.len() as u32;
        for i in 0..FAIR.len() {
            fps[i].clear();
            fbuf.clear();
            fair_succ(&s, i, fbuf);
            let mut enabled = false;
            for (t, _) in fbuf.iter() {
                if fair_sub_changed(i, &s, t) {
                    enabled = true;
                    if let Some(w) = pack(t) {
                        fps[i].push(state_fp(t, &w));
                    }
                }
            }
            if enabled {
                c.live.enab.push(i as u32);
            }
        }
        let n = c.live.enab.len() as u32 - en_off;
        if n > 0 {
            c.live.en.push((head as u32, en_off, n));
        }
    }
    let sfp = if LIVENESS { state_fp(&s, &g.states[head]) } else { 0 };
    for &(t, l) in buf.iter() {
        c.generated += 1;
        // Drop states that violate CONSTRAINT (as in TLC, they are not counted).
        if !constraint(&t) {
            continue;
        }
        for (name, f) in ACTION_PROPS {
            if !f(&s, &t) {
                return Some(Found::Action(head as u32, t, l, name));
            }
        }
        let Some(w) = pack(&t) else {
            return Some(Found::Type(head as u32, t, l, check_invariants(&t)));
        };
        let tfp = state_fp(&t, &w);
        if LIVENESS && tfp != sfp {
            let off = c.live.tags.len() as u32;
            for i in 0..FAIR.len() {
                if fps[i].contains(&tfp) {
                    c.live.tags.push(i as u32);
                }
            }
            let n = c.live.tags.len() as u32 - off;
            c.live.edges.push((head as u32, tfp, l, off, n));
        }
        if seen.insert(tfp) {
            c.states.push(w);
            c.parent.push((head as u32, l));
            if let Some(inv) = check_invariants(&t) {
                return Some(Found::Inv(me, c.states.len() - 1, inv));
            }
        }
    }
    None
}

fn expand(g: &Graph, lo: usize, hi: usize, seen: &Shards, stop: &std::sync::atomic::AtomicBool, me: usize, check_deadlock: bool) -> Chunk {
    use std::sync::atomic::Ordering::Relaxed;
    let mut c = Chunk { states: vec![], parent: vec![], generated: 0, found: None, live: LiveChunk::default() };
    let mut buf: Vec<(State, u32)> = Vec::with_capacity(64);
    let mut fbuf: Vec<(State, u32)> = Vec::with_capacity(16);
    let mut fps: Vec<Vec<Fp>> = vec![vec![]; FAIR.len()];
    for head in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            expand_one(g, head, seen, me, check_deadlock, &mut c, &mut buf, &mut fbuf, &mut fps)
        }));
        let found = match r {
            Ok(f) => f,
            Err(p) => Some(Found::Eval(head as u32, describe_panic(p))),
        };
        if found.is_some() {
            c.found = found;
            stop.store(true, Relaxed);
            break;
        }
    }
    c
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().collect();
    let opt = Opt {
        check_deadlock: CHECK_DEADLOCK && !args.iter().any(|a| a == "-deadlock"),
        keep_pred: !args.iter().any(|a| a == "-notrace"),
        batched: args.iter().any(|a| a == "-batched" || a == "-metal"),
        metal: args.iter().any(|a| a == "-metal"),
        mem_limit: args
            .iter()
            .position(|a| a == "-memlimit")
            .and_then(|i| args.get(i + 1))
            .and_then(|w| w.parse::<usize>().ok())
            .map_or(256 << 20, |mb| mb << 20),
        tmpdir: args
            .iter()
            .position(|a| a == "-tmpdir")
            .and_then(|i| args.get(i + 1))
            .map(std::path::PathBuf::from)
            .unwrap_or_else(std::env::temp_dir),
        workers: args
            .iter()
            .position(|a| a == "-workers")
            .and_then(|i| args.get(i + 1))
            .and_then(|w| w.parse().ok())
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1))
            .max(1),
    };
    // Only when checking temporal properties is the whole state graph kept in memory (the SCC
    // search needs it). Otherwise only fingerprints and each state's predecessor fingerprint are
    // kept, and counterexamples are rebuilt by replaying from an initial state.
    // Evaluation errors are caught and reported where they occur. Anything that reaches this point
    // is unexpected, so print a message instead of exiting silently (the default panic output is
    // suppressed above).
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        if LIVENESS {
            run_liveness(&opt);
        } else if opt.batched {
            run_safety_batched(&opt);
        } else {
            run_safety(&opt);
        }
    }));
    if let Err(p) = run {
        let e = describe_panic(p);
        report_eval(&e);
        std::process::exit(eval_code(&e));
    }
}

struct Opt {
    check_deadlock: bool,
    keep_pred: bool,
    /// Process each level in batches through three phases (structured so phase 2 can run on the
    /// GPU).
    batched: bool,
    /// Offload phase 2 (the "already visited?" lookup) to the GPU.
    metal: bool,
    workers: usize,
    /// Max bytes of one level kept in memory. Anything beyond that is spilled to a temporary file.
    mem_limit: usize,
    tmpdir: std::path::PathBuf,
}

/// One BFS level. Kept in memory while small and spilled to a temporary file once it grows large.
/// Either way it is only ever read sequentially from the start, so the file needs nothing beyond
/// appends and sequential reads.
/// A queue entry: a state and its fingerprint (so the fingerprint isn't recomputed on every
/// expansion).
type Qitem = (Packed, Fp);

struct Level {
    mem: Vec<Qitem>,
    /// The spill file (already unlinked) and the number of entries in it.
    file: Option<(std::fs::File, usize)>,
    limit: usize,
}

const PACK_BYTES: usize = WORDS * 8 + FP_BITS / 8;

/// Time spent in each phase (printed at the end only when TLA2RS_PHASES=1).
static PH: [std::sync::atomic::AtomicU64; 4] = [const { std::sync::atomic::AtomicU64::new(0) }; 4];

#[inline]
fn ph(i: usize, t: std::time::Instant) {
    PH[i].fetch_add(t.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
}

/// A sequence number that keeps spill file names unique, and the total number of bytes spilled.
static SPILL_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static SPILLED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn to_bytes(v: &[Qitem], out: &mut Vec<u8>) {
    out.clear();
    out.reserve(v.len() * PACK_BYTES);
    for (w, fp) in v {
        for x in w {
            out.extend_from_slice(&x.to_le_bytes());
        }
        out.extend_from_slice(&fp.to_le_bytes());
    }
}

fn from_bytes(c: &[u8]) -> Qitem {
    let w: Packed = std::array::from_fn(|i| u64::from_le_bytes(c[i * 8..i * 8 + 8].try_into().unwrap()));
    let fp = Fp::from_le_bytes(c[WORDS * 8..WORDS * 8 + FP_BITS / 8].try_into().unwrap());
    (w, fp)
}

impl Level {
    fn new(limit: usize) -> Self {
        Level { mem: vec![], file: None, limit }
    }

    fn len(&self) -> usize {
        self.mem.len() + self.file.as_ref().map_or(0, |f| f.1)
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Appends states to the level. Once the memory limit is exceeded, writes everything buffered
    /// so far out to the file.
    fn extend(&mut self, v: Vec<Qitem>, opt: &Opt) {
        self.mem.extend(v);
        if self.mem.len() * PACK_BYTES <= self.limit {
            return;
        }
        if self.file.is_none() {
            let seq = SPILL_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let path = opt.tmpdir.join(format!("tla2rs-{}-{seq}.q", std::process::id()));
            match std::fs::File::options().create_new(true).read(true).write(true).open(&path) {
                Ok(f) => {
                    // Unlink the file right after opening it. Its contents remain readable and
                    // writable until it is closed, and nothing is left behind if the checker is
                    // killed partway through (signal, exit).
                    let _ = std::fs::remove_file(&path);
                    self.file = Some((f, 0));
                }
                Err(e) => {
                    // If we can't spill, keep everything in memory (better to try than to crash).
                    eprintln!("warning: cannot spill the queue to {}: {e}", path.display());
                    self.limit = usize::MAX;
                    return;
                }
            }
        }
        let (f, n) = self.file.as_mut().unwrap();
        let mut buf = vec![];
        to_bytes(&self.mem, &mut buf);
        use std::io::Write;
        if let Err(e) = f.write_all(&buf) {
            eprintln!("warning: cannot spill the queue: {e}");
            self.limit = usize::MAX;
            return;
        }
        *n += self.mem.len();
        SPILLED.fetch_add(buf.len() as u64, std::sync::atomic::Ordering::Relaxed);
        self.mem.clear();
        self.mem.shrink_to_fit();
    }

    /// Yields entries in order from the start, spilled entries first.
    fn batches(mut self, batch: usize) -> Batches {
        let file = self.file.take();
        let mem = std::mem::take(&mut self.mem);
        Batches { file, left: 0, mem: mem.into_iter(), batch, started: false }
    }
}

/// Reads a level back one batch at a time.
struct Batches {
    file: Option<(std::fs::File, usize)>,
    left: usize,
    mem: std::vec::IntoIter<Qitem>,
    batch: usize,
    started: bool,
}

impl Iterator for Batches {
    type Item = Vec<Qitem>;
    fn next(&mut self) -> Option<Vec<Qitem>> {
        if !self.started {
            self.started = true;
            if let Some((f, n)) = self.file.as_mut() {
                use std::io::Seek;
                let _ = f.seek(std::io::SeekFrom::Start(0));
                self.left = *n;
            }
        }
        if self.left > 0 {
            let take = self.batch.min(self.left);
            let (f, _) = self.file.as_mut().unwrap();
            let mut buf = vec![0u8; take * PACK_BYTES];
            use std::io::Read;
            // Skipping the unreadable part and carrying on would leave states unexplored while
            // still reporting "no error".
            if let Err(e) = f.read_exact(&mut buf) {
                eval_error(format!("cannot read the spilled queue back: {e}"));
            }
            self.left -= take;
            return Some(buf.chunks_exact(PACK_BYTES).map(from_bytes).collect());
        }
        let v: Vec<Qitem> = self.mem.by_ref().take(self.batch).collect();
        (!v.is_empty()).then_some(v)
    }
}

/// Computes the initial states, checks them against the invariants and constraints, and returns
/// them along with their fingerprints.
fn initial_states() -> Vec<(State, Packed, Fp)> {
    let mut inits = Vec::new();
    if let Err(p) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut inits))) {
        let e = describe_panic(p);
        report_eval(&e);
        println!("  (while computing the initial states)");
        std::process::exit(eval_code(&e));
    }
    let mut out = vec![];
    for s in inits {
        if !constraint(&s) {
            continue;
        }
        let inv = match std::panic::catch_unwind(|| check_invariants(&s)) {
            Ok(v) => v,
            Err(p) => {
                let e = describe_panic(p);
                report_eval(&e);
                println!("{}", show(&s));
                std::process::exit(eval_code(&e));
            }
        };
        if let Some(inv) = inv {
            println!("Error: Invariant {inv} is violated by the initial state:\n{}", show(&s));
            std::process::exit(12);
        }
        let Some(w) = pack(&s) else {
            let e = EvalErr::Type("an initial state".into());
            report_eval(&e);
            println!("{}", show(&s));
            std::process::exit(eval_code(&e));
        };
        let fp = state_fp(&s, &w);
        out.push((s, w, fp));
    }
    out
}

/// A detected error. The trace is shown by following fingerprints back from `fp`; if `extra` is
/// set, one more state is appended after it.
struct SFound {
    fp: Fp,
    extra: Option<(State, u32)>,
    msg: SMsg,
}

enum SMsg {
    Inv(&'static str),
    Deadlock,
    Action(&'static str),
    Eval(EvalErr),
    OutOfType,
}

/// A small per-thread table. The same fingerprints get looked up repeatedly, so it is checked
/// before the shared table.
/// It stores fingerprints verbatim, so it reports a hit only for fingerprints actually inserted
/// (it can never cause a state to be missed). With a SYMMETRY, they are the fingerprints of the key
/// under the first permutation where that decides the smallest key (see `fresh_fp`).
/// Sized to fit in L1/L2.
const SEEN_BITS: usize = 16;

struct Seen(Vec<Fp>);

impl Seen {
    fn new() -> Self {
        Seen(vec![0; 1 << SEEN_BITS])
    }
    #[inline]
    fn slot(fp: Fp) -> usize {
        // The shared table picks slots by the low bits, so use different bits here.
        ((fp >> 17) as usize) & ((1 << SEEN_BITS) - 1)
    }
    /// Records fp. False if it was already there.
    #[inline]
    fn fresh(&mut self, fp: Fp) -> bool {
        let slot = &mut self.0[Self::slot(fp)];
        let fresh = *slot != fp;
        *slot = fp;
        fresh
    }
}

struct SChunk {
    next: Vec<Qitem>,
    generated: u64,
    distinct: u64,
    found: Option<SFound>,
}

/// A successor that does not fit the packed layout: an invariant it violates, else an out-of-type
/// error
fn pack_failed(sfp: Fp, t: State, l: u32) -> SFound {
    let msg = match check_invariants(&t) {
        Some(inv) => SMsg::Inv(inv),
        None => SMsg::OutOfType,
    };
    SFound { fp: sfp, extra: Some((t, l)), msg }
}

/// Per-thread working storage for `expand_safety_one`.
struct SWork {
    /// The successors of the state being expanded, each with the label of its action.
    buf: Vec<(State, u32)>,
    /// The successors that may be new: index in `buf`, fingerprint, and the packed state if the
    /// fingerprint needed it.
    cand: Vec<(usize, Fp, Option<Packed>)>,
    mine: Seen,
}

/// Expands a single state, pushing newly found states onto c.next.
fn expand_safety_one(w: &Packed, sfp: Fp, seen: &Shards, opt: &Opt, c: &mut SChunk, ws: &mut SWork) -> Option<SFound> {
    let s = unpack(w);
    ws.buf.clear();
    ws.cand.clear();
    next(&s, &mut ws.buf);
    if ws.buf.is_empty() && opt.check_deadlock {
        return Some(SFound { fp: sfp, extra: None, msg: SMsg::Deadlock });
    }
    // All successors are fingerprinted before any is looked up, so that their table lines arrive
    // meanwhile. The successors are still reported on in order, as TLC does: an evaluation error in
    // a later one waits until the ones before it are in the table and checked, and c.generated
    // counts the successors up to the one that stops the search.
    let base = c.generated;
    let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fingerprint_successors(&s, sfp, seen, c, ws)
    }));
    let examined = c.generated;
    let found = insert_candidates(base, sfp, seen, c, ws);
    if found.is_some() {
        return found;
    }
    c.generated = examined;
    stopped.unwrap_or_else(|p| std::panic::resume_unwind(p))
}

/// Fills ws.cand with the successors in ws.buf that may be new and prefetches the table line of
/// each. Stops at a successor that is an error by itself and returns it.
fn fingerprint_successors(s: &State, sfp: Fp, seen: &Shards, c: &mut SChunk, ws: &mut SWork) -> Option<SFound> {
    for (i, &(ref t, l)) in ws.buf.iter().enumerate() {
        c.generated += 1;
        if !constraint(t) {
            continue;
        }
        for (name, f) in ACTION_PROPS {
            if !f(s, t) {
                return Some(SFound { fp: sfp, extra: Some((*t, l)), msg: SMsg::Action(name) });
            }
        }
        // With a VIEW, most successors are duplicates, so only new ones are packed. An out-of-type
        // duplicate then goes unreported, as TLC checks invariants only on new states.
        let (tfp, tw) = if HAS_VIEW {
            match fresh_fp(t, Some(&mut ws.mine)) {
                Some(Some(fp)) => (fp, None),
                Some(None) => continue,
                None if pack(t).is_none() => return Some(pack_failed(sfp, *t, l)),
                None => type_error("VIEW value", ""),
            }
        } else {
            let Some(tw) = pack(t) else {
                return Some(pack_failed(sfp, *t, l));
            };
            let Some(fp) = fresh_state_fp(t, &tw, &mut ws.mine) else { continue };
            (fp, Some(tw))
        };
        seen.prefetch(tfp);
        ws.cand.push((i, tfp, tw));
    }
    None
}

/// Adds the candidates to the visited set in order and queues the new ones. Stops at a new state
/// that is an error and returns it. `base` is c.generated before the first successor.
fn insert_candidates(base: u64, sfp: Fp, seen: &Shards, c: &mut SChunk, ws: &SWork) -> Option<SFound> {
    for &(i, tfp, tw) in ws.cand.iter() {
        if !seen.insert_with(tfp, sfp) {
            continue;
        }
        c.generated = base + i as u64 + 1;
        let (t, l) = &ws.buf[i];
        let Some(tw) = tw.or_else(|| pack(t)) else {
            return Some(pack_failed(sfp, *t, *l));
        };
        c.distinct += 1;
        if let Some(inv) = check_invariants(t) {
            return Some(SFound { fp: tfp, extra: None, msg: SMsg::Inv(inv) });
        }
        c.next.push((tw, tfp));
    }
    None
}

fn expand_safety(
    frontier: &[Qitem],
    lo: usize,
    hi: usize,
    seen: &Shards,
    stop: &std::sync::atomic::AtomicBool,
    opt: &Opt,
) -> SChunk {
    use std::sync::atomic::Ordering::Relaxed;
    let mut c = SChunk { next: vec![], generated: 0, distinct: 0, found: None };
    let mut ws = SWork { buf: Vec::with_capacity(64), cand: Vec::with_capacity(64), mine: Seen::new() };
    for i in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let (w, sfp) = &frontier[i];
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            expand_safety_one(w, *sfp, seen, opt, &mut c, &mut ws)
        }));
        let found = match r {
            Ok(f) => f,
            Err(p) => Some(SFound { fp: *sfp, extra: None, msg: SMsg::Eval(describe_panic(p)) }),
        };
        if found.is_some() {
            c.found = found;
            stop.store(true, Relaxed);
            break;
        }
    }
    c
}

/// Something that remembers visited states: the locked shards, or the single table used in
/// batched mode.
trait Visited {
    fn pred_of(&self, fp: Fp) -> Option<Fp>;
}

impl Visited for Shards {
    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        Shards::pred_of(self, fp)
    }
}

impl Visited for Table {
    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        Table::pred_of(self, fp)
    }
}

/// Follows fingerprints back to an initial state (the result starts with the initial state).
fn fp_chain(seen: &dyn Visited, target: Fp) -> Option<Vec<Fp>> {
    let mut chain = vec![target];
    let mut cur = target;
    for _ in 0..1_000_000 {
        let pred = seen.pred_of(cur)?;
        if pred == cur {
            chain.reverse();
            return Some(chain);
        }
        chain.push(pred);
        cur = pred;
    }
    None
}

/// Rebuilds the actual states by replaying a sequence of fingerprints from an initial state.
fn replay(chain: &[Fp]) -> Option<Vec<(State, u32)>> {
    let first = initial_states().into_iter().find(|(_, _, fp)| *fp == chain[0])?;
    let mut out = vec![(first.0, u32::MAX)];
    let mut cur = first.0;
    let mut buf: Vec<(State, u32)> = vec![];
    for want in &chain[1..] {
        buf.clear();
        next(&cur, &mut buf);
        let hit = buf.iter().find_map(|&(t, l)| {
            let w = pack(&t)?;
            (state_fp(&t, &w) == *want).then_some((t, l))
        })?;
        out.push(hit);
        cur = hit.0;
    }
    Some(out)
}

/// Prints a counterexample and returns the number of states shown.
fn print_states(trace: &[(State, u32)], extra: Option<(State, u32)>) -> usize {
    let name = |l: u32| if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
    println!("Error: The behavior up to this point is:");
    let mut n = 0;
    for (s, l) in trace {
        n += 1;
        println!("State {n}: <{}>\n{}\n", name(*l), show(s));
    }
    if let Some((s, l)) = extra {
        n += 1;
        println!("State {n}: <{}>\n{}\n", name(l), show(&s));
    }
    n
}

/// Prints a counterexample. If it can't be rebuilt by following fingerprints, prints at least the
/// final state.
fn report_trace(seen: &dyn Visited, f: &SFound) -> usize {
    if seen.pred_of(f.fp).is_none() {
        println!("Error: (re-run without -notrace to get the behavior that leads here)");
        if let Some((s, l)) = f.extra {
            println!("State: <{}>\n{}\n", LABELS[l as usize], show(&s));
        }
        return 0;
    }
    match fp_chain(seen, f.fp).and_then(|c| replay(&c)) {
        Some(trace) => print_states(&trace, f.extra),
        None => {
            println!("Error: could not reconstruct the behavior (this is a tla2rs bug; please report the spec)");
            if let Some((s, l)) = f.extra {
                println!("State: <{}>\n{}\n", LABELS[l as usize], show(&s));
            }
            0
        }
    }
}

fn run_safety(opt: &Opt) {
    let t0 = std::time::Instant::now();
    let seen = Shards::new(opt.keep_pred);
    let mut generated: u64 = 0;
    let mut frontier = Level::new(opt.mem_limit);
    let mut first = vec![];
    for (_, w, fp) in initial_states() {
        generated += 1;
        if seen.insert_with(fp, fp) {
            first.push((w, fp));
        }
    }
    let mut distinct = first.len() as u64;
    println!(
        "Finished computing initial states: {} distinct states generated. ({} workers)",
        first.len(),
        opt.workers
    );
    frontier.extend(first, opt);
    let stop = std::sync::atomic::AtomicBool::new(false);
    let mut depth = 1u32;
    let mut last = std::time::Instant::now();
    while !frontier.is_empty() {
        let left_before = frontier.len();
        let mut nxt = Level::new(opt.mem_limit);
        let mut found: Option<SFound> = None;
        let mut done = 0usize;
        // Read the level one batch at a time and split each batch across threads for expansion.
        // While the workers expand a batch, this thread merges the previous batch's results (which
        // may spill them to disk) and reads the next batch, so up to two batches are in memory.
        // Smaller batches leave less unoverlapped work at the start and end of a level.
        let batch = (opt.mem_limit / PACK_BYTES).clamp(1024, 1 << 18);
        let mut parts = frontier.batches(batch);
        let mut cur = parts.next();
        let mut pending: Vec<SChunk> = vec![];
        while let Some(part) = cur {
            let n = part.len();
            done += n;
            if stop.load(std::sync::atomic::Ordering::Relaxed) {
                // An earlier batch found an error: skip the rest of the level.
                for c in pending.drain(..) {
                    merge_chunk(c, &mut generated, &mut distinct, &mut nxt, &mut found, opt);
                }
                cur = parts.next();
                continue;
            }
            let k = if n < 1024 { 1 } else { opt.workers.min(n) };
            let per = n.div_ceil(k);
            let (chunks, next_part) = std::thread::scope(|sc| {
                let hs: Vec<_> = (0..k)
                    .map(|i| {
                        let (x, y) = (i * per, ((i + 1) * per).min(n));
                        let (pt, seen, stop) = (&part, &seen, &stop);
                        sc.spawn(move || expand_safety(pt, x, y, seen, stop, opt))
                    })
                    .collect();
                for c in pending.drain(..) {
                    merge_chunk(c, &mut generated, &mut distinct, &mut nxt, &mut found, opt);
                }
                let next_part = parts.next();
                let chunks: Vec<SChunk> =
                    hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect();
                (chunks, next_part)
            });
            pending = chunks;
            cur = next_part;
            if last.elapsed().as_secs() >= 10 {
                last = std::time::Instant::now();
                let (g, d, q) = pending.iter().fold((generated, distinct, nxt.len()), |(g, d, q), c| {
                    (g + c.generated, d + c.distinct, q + c.next.len())
                });
                println!(
                    "Progress({depth}): {g} states generated, {d} distinct states found, {} states left on queue. ({:.0}s)",
                    q + (left_before - done),
                    t0.elapsed().as_secs_f64()
                );
            }
        }
        for c in pending {
            merge_chunk(c, &mut generated, &mut distinct, &mut nxt, &mut found, opt);
        }
        if let Some(f) = found {
            report_and_exit(&seen, f, generated, distinct, nxt.len() + (left_before - done));
        }
        frontier = nxt;
        if !frontier.is_empty() {
            depth += 1;
        }
    }
    finish(opt, t0, generated, distinct, depth);
}

/// Adds one worker's results to the totals and the next level. Chunks are merged in worker
/// order, so the first error reported is the one from the earliest chunk.
fn merge_chunk(c: SChunk, generated: &mut u64, distinct: &mut u64, nxt: &mut Level, found: &mut Option<SFound>, opt: &Opt) {
    *generated += c.generated;
    *distinct += c.distinct;
    nxt.extend(c.next, opt);
    if found.is_none() {
        *found = c.found;
    }
}

/// Reports a detected error and exits. Never returns.
fn report_and_exit(seen: &dyn Visited, f: SFound, mut generated: u64, mut distinct: u64, left: usize) -> ! {
    let code = match &f.msg {
        SMsg::Deadlock => 11,
        SMsg::Eval(e) => eval_code(e),
        SMsg::OutOfType => eval_code(&EvalErr::Type(String::new())),
        _ => 12,
    };
    match &f.msg {
        SMsg::Inv(inv) => println!("Error: Invariant {inv} is violated."),
        SMsg::Deadlock => println!("Error: Deadlock reached."),
        SMsg::Action(name) => println!("Error: Action property {name} is violated."),
        SMsg::Eval(e) => report_eval(e),
        SMsg::OutOfType => report_eval(&EvalErr::Type("a variable".into())),
    }
    // As in TLC, a successor that left its type counts as one state.
    let pseudo = matches!(f.msg, SMsg::Eval(EvalErr::Type(_)));
    if pseudo || matches!(f.msg, SMsg::OutOfType) || (f.extra.is_some() && matches!(f.msg, SMsg::Inv(_))) {
        distinct += 1;
    }
    if pseudo {
        generated += 1;
    }
    let shown = report_trace(seen, &f);
    if pseudo && shown > 0 {
        println!("State {}: <a successor that tla2rs cannot represent>\n", shown + 1);
    }
    println!("{generated} states generated, {distinct} distinct states found, {left} states left on queue.");
    std::process::exit(code);
}

fn finish(opt: &Opt, t0: std::time::Instant, generated: u64, distinct: u64, depth: u32) {
    if std::env::var("TLA2RS_PHASES").is_ok() {
        let g = |i: usize| PH[i].load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e6;
        println!(
            "  phases: collect {:.2}s, lookup-wait {:.2}s, insert {:.2}s",
            g(0),
            g(1),
            g(2)
        );
    }

    println!("{generated} states generated, {distinct} distinct states found, 0 states left on queue.");
    println!("The depth of the complete state graph search is {depth}.");
    let spilled = SPILLED.load(std::sync::atomic::Ordering::Relaxed);
    if spilled > 0 {
        println!(
            "  The queue spilled {:.0} MB to {} (-memlimit MB raises the in-memory part).",
            spilled as f64 / (1u64 << 20) as f64,
            opt.tmpdir.display()
        );
    }
    if WORDS * 64 > FP_BITS {
        // Probability that two distinct states collided on a fingerprint and one of them was
        // skipped (birthday bound).
        let d = distinct as f64;
        println!(
            "  Estimate of the probability that a state was skipped because two distinct states shared a {FP_BITS}-bit fingerprint: {:.1e}",
            d * d / 2.0 / 2f64.powi(FP_BITS as i32)
        );
    }
    println!("Model checking completed. No error has been found.");
    println!("Finished in {:.3}s", t0.elapsed().as_secs_f64());
}

/// The table used in batched mode. It lives in one contiguous allocation so the GPU can read it
/// too, and is split into 1024 shards by the top 10 bits of the fingerprint. Probing wraps around
/// within a shard.
///
/// Nobody writes during phase 2 (lookup), so it is read-only there. In phase 3 the shards are
/// divided among threads, so each thread writes only to its own disjoint range. No locking is
/// needed. The table is grown only between batches (when nobody is touching it).
const SHARDS: usize = 1024;

struct Table {
    t: Aligned,
    p: Aligned,
    /// Slots per shard (a power of two).
    slots: usize,
    n: usize,
    keep_pred: bool,
    /// The state with fingerprint 0 (which cannot be stored in the table).
    zero: std::cell::UnsafeCell<Option<Fp>>,
}

unsafe impl Send for Table {}
unsafe impl Sync for Table {}

/// A page-aligned allocation that can be handed to Metal as a buffer as is.
struct Aligned {
    ptr: *mut Fp,
    len: usize,
}

unsafe impl Send for Aligned {}
unsafe impl Sync for Aligned {}

const PAGE: usize = 16384;

impl Aligned {
    fn new(len: usize) -> Self {
        if len == 0 {
            return Aligned { ptr: std::ptr::null_mut(), len: 0 };
        }
        let bytes = (len * std::mem::size_of::<Fp>()).next_multiple_of(PAGE);
        let layout = std::alloc::Layout::from_size_align(bytes, PAGE).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) } as *mut Fp;
        assert!(!ptr.is_null(), "out of memory for the visited table");
        Aligned { ptr, len }
    }
    #[inline]
    fn as_slice(&self) -> &[Fp] {
        if self.len == 0 {
            return &[];
        }
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
    #[inline]
    #[allow(clippy::mut_from_ref)]
    fn as_mut_slice(&self) -> &mut [Fp] {
        if self.len == 0 {
            return &mut [];
        }
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
    fn bytes(&self) -> usize {
        (self.len * std::mem::size_of::<Fp>()).next_multiple_of(PAGE)
    }
}

impl Drop for Aligned {
    fn drop(&mut self) {
        if self.len > 0 {
            let layout = std::alloc::Layout::from_size_align(self.bytes(), PAGE).unwrap();
            unsafe { std::alloc::dealloc(self.ptr as *mut u8, layout) };
        }
    }
}

impl Table {
    fn new(keep_pred: bool) -> Self {
        let slots = 64;
        Table {
            t: Aligned::new(SHARDS * slots),
            p: Aligned::new(if keep_pred { SHARDS * slots } else { 0 }),
            slots,
            n: 0,
            keep_pred,
            zero: std::cell::UnsafeCell::new(None),
        }
    }

    /// The record for fingerprint 0: (already seen?, where to write).
    #[allow(clippy::mut_from_ref)]
    fn zero_cell(&self) -> (bool, &mut Option<Fp>) {
        let p = unsafe { &mut *self.zero.get() };
        (p.is_some(), p)
    }

    #[inline]
    fn contains(&self, fp: Fp) -> bool {
        if fp == 0 {
            return self.zero_cell().0;
        }
        let t = self.t.as_slice();
        let base = shard(fp) * self.slots;
        let m = self.slots - 1;
        let mut i = (fp as usize) & m;
        loop {
            let x = t[base + i];
            if x == 0 {
                return false;
            }
            if x == fp {
                return true;
            }
            i = (i + 1) & m;
        }
    }

    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        if !self.keep_pred {
            return None;
        }
        if fp == 0 {
            return *self.zero_cell().1;
        }
        let (t, p) = (self.t.as_slice(), self.p.as_slice());
        let base = shard(fp) * self.slots;
        let m = self.slots - 1;
        let mut i = (fp as usize) & m;
        loop {
            let x = t[base + i];
            if x == 0 {
                return None;
            }
            if x == fp {
                return Some(p[base + i]);
            }
            i = (i + 1) & m;
        }
    }

    /// Writes only to shards in [lo, hi); other threads own other ranges.
    fn insert_range(&self, fp: Fp, pred: Fp, lo: usize, hi: usize) -> bool {
        if fp == 0 {
            // 0 marks an empty slot and can't be stored in the table. Only the thread that owns
            // shard 0 handles it.
            let me = self.zero_cell();
            if me.0 {
                return false;
            }
            *me.1 = Some(pred);
            return true;
        }
        let sh = shard(fp);
        debug_assert!(sh >= lo && sh < hi);
        let _ = (lo, hi);
        let (t, p) = (self.t.as_mut_slice(), self.p.as_mut_slice());
        let base = sh * self.slots;
        let m = self.slots - 1;
        let mut i = (fp as usize) & m;
        // A full shard has no empty slot. This can't happen as long as `reserve` left enough
        // headroom.
        for _ in 0..self.slots {
            let x = t[base + i];
            if x == 0 {
                t[base + i] = fp;
                if self.keep_pred {
                    p[base + i] = pred;
                }
                return true;
            }
            if x == fp {
                return false;
            }
            i = (i + 1) & m;
        }
        eval_error(format!(
            "the visited table's shard {sh} is full ({} slots); this is a tla2rs bug",
            self.slots
        ))
    }

    /// Prefetches the cache line where the fingerprint would go.
    #[inline]
    fn prefetch_slot(&self, fp: Fp) {
        if fp == 0 {
            return;
        }
        let i = shard(fp) * self.slots + ((fp as usize) & (self.slots - 1));
        prefetch(unsafe { self.t.ptr.add(i) });
    }

    /// Ensures that inserting `extra` more entries cannot overflow. Call only while nobody is
    /// touching the table. Leaves headroom for uneven load across shards. Returns true if it grew.
    fn reserve(&mut self, extra: usize, workers: usize) -> bool {
        let mut grew = false;
        while (self.n + extra + 1) * 10 > SHARDS * self.slots * 6 {
            self.grow(workers);
            grew = true;
        }
        grew
    }

    /// Adds to the count of inserted entries.
    fn count_added(&mut self, added: usize) {
        self.n += added;
    }

    /// Shards are independent, so rehash them in parallel (done serially, only one of 10 cores
    /// would be doing any work).
    fn grow(&mut self, workers: usize) {
        let slots = self.slots * 2;
        let nt = Aligned::new(SHARDS * slots);
        let np = Aligned::new(if self.keep_pred { SHARDS * slots } else { 0 });
        let (old_slots, keep) = (self.slots, self.keep_pred);
        let (ot, op) = (self.t.as_slice(), self.p.as_slice());
        let k = workers.clamp(1, SHARDS);
        let per = SHARDS.div_ceil(k);
        std::thread::scope(|sc| {
            for w in 0..k {
                let (lo, hi) = (w * per, ((w + 1) * per).min(SHARDS));
                let (nt, np) = (&nt, &np);
                sc.spawn(move || {
                    let (t, p) = (nt.as_mut_slice(), np.as_mut_slice());
                    let m = slots - 1;
                    for sh in lo..hi {
                        for j in 0..old_slots {
                            let x = ot[sh * old_slots + j];
                            if x == 0 {
                                continue;
                            }
                            let base = sh * slots;
                            let mut i = (x as usize) & m;
                            while t[base + i] != 0 {
                                i = (i + 1) & m;
                            }
                            t[base + i] = x;
                            if keep {
                                p[base + i] = op[sh * old_slots + j];
                            }
                        }
                    }
                });
            }
        });
        self.t = nt;
        self.p = np;
        self.slots = slots;

    }
}

/// One entry in batched mode: a successor state with its fingerprint already computed.
#[derive(Clone, Copy)]
struct Cand {
    w: Packed,
    fp: Fp,
    pred: Fp,
}

/// The output of phase 1, grouped by destination shard (so phase 3 can divide the work).
struct Collected {
    /// parts[t] is the share handled by thread t in phase 3.
    parts: Vec<Vec<Cand>>,
    generated: u64,
    found: Option<SFound>,
}

/// Which thread owns a fingerprint. The 1024 shards are split evenly as is, so no two threads
/// ever touch the same shard in phase 3.
#[inline]
fn part_of(fp: Fp, parts: usize) -> usize {
    shard(fp) * parts / 1024
}

/// Phase 1: generates successors, computes their fingerprints, filters duplicates, checks
/// invariants, and queues them. Never touches the shared table.
fn collect_phase(
    frontier: &[Qitem],
    lo: usize,
    hi: usize,
    opt: &Opt,
    stop: &std::sync::atomic::AtomicBool,
    parts: usize,
) -> Collected {
    use std::sync::atomic::Ordering::Relaxed;
    let mut out = Collected { parts: (0..parts).map(|_| vec![]).collect(), generated: 0, found: None };
    let mut buf: Vec<(State, u32)> = Vec::with_capacity(64);
    let mut mine = Seen::new();
    for i in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let (w, sfp) = &frontier[i];
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let s = unpack(w);
            buf.clear();
            next(&s, &mut buf);
            if buf.is_empty() && opt.check_deadlock {
                return Some(SFound { fp: *sfp, extra: None, msg: SMsg::Deadlock });
            }
            for &(t, l) in buf.iter() {
                out.generated += 1;
                if !constraint(&t) {
                    continue;
                }
                for (name, f) in ACTION_PROPS {
                    if !f(&s, &t) {
                        return Some(SFound { fp: *sfp, extra: Some((t, l)), msg: SMsg::Action(name) });
                    }
                }
                let Some(tw) = pack(&t) else {
                    let msg = match check_invariants(&t) {
                        Some(inv) => SMsg::Inv(inv),
                        None => SMsg::OutOfType,
                    };
                    return Some(SFound { fp: *sfp, extra: Some((t, l)), msg });
                };
                let Some(tfp) = fresh_state_fp(&t, &tw, &mut mine) else { continue };
                out.parts[part_of(tfp, parts)].push(Cand { w: tw, fp: tfp, pred: *sfp });
                // Stop generating once a violating state is found (so we stop at the same count as
                // the non-batched path). This candidate also goes into the table in phase 3, so the
                // counterexample can be traced back from its fingerprint.
                if let Some(inv) = check_invariants(&t) {
                    return Some(SFound { fp: tfp, extra: None, msg: SMsg::Inv(inv) });
                }
            }
            None
        }));
        let found = match r {
            Ok(f) => f,
            Err(p) => Some(SFound { fp: *sfp, extra: None, msg: SMsg::Eval(describe_panic(p)) }),
        };
        if found.is_some() {
            out.found = found;
            stop.store(true, Relaxed);
            break;
        }
    }
    out
}

/// Phase 2 (CPU version): only checks whether each candidate is already in the table; never
/// modifies it.
fn lookup_phase_cpu(cands: &[Cand], found: &mut [u8], tbl: &Table) {
    for (i, c) in cands.iter().enumerate() {
        found[i] = tbl.contains(c.fp) as u8;
    }
}

/// Prefetches a table line so that memory latencies overlap.
#[inline(always)]
fn prefetch(p: *const Fp) {
    #[cfg(target_arch = "aarch64")]
    unsafe {
        std::arch::asm!("prfm pldl1keep, [{0}]", in(reg) p, options(nostack, readonly, preserves_flags));
    }
    #[cfg(not(target_arch = "aarch64"))]
    {
        let _ = p;
    }
}

/// Phase 3: inserts the candidates that were not found and passes the truly new ones on to the
/// next level. The shard range [lo, hi) owned here doesn't overlap any other thread's, so no
/// locking is needed.
fn insert_phase(cands: &[Cand], found: &[u8], tbl: &Table, lo: usize, hi: usize) -> (Vec<Qitem>, u64) {
    let mut next_level = vec![];
    let mut distinct = 0;
    // Prefetch a few entries ahead. The table is large, so stalling on every entry is slow.
    const AHEAD: usize = 12;
    for (i, c) in cands.iter().enumerate() {
        if let Some(n) = cands.get(i + AHEAD) {
            if found.get(i + AHEAD) == Some(&0) {
                tbl.prefetch_slot(n.fp);
            }
        }
        if found[i] != 0 {
            continue;
        }
        if tbl.insert_range(c.fp, c.pred, lo, hi) {
            distinct += 1;
            next_level.push((c.w, c.fp));
        }
    }
    (next_level, distinct)
}

fn run_safety_batched(opt: &Opt) {
    let t0 = std::time::Instant::now();
    let mut tbl = Table::new(opt.keep_pred);
    // Skip the GPU path when fingerprints are wider than 64 bits (the kernel reads 64-bit values).
    let use_gpu = opt.metal && FP_BITS == 64 && gpu_ready();
    if use_gpu {
        gpu_set_table(&tbl);
    }
    let mut generated: u64 = 0;
    let mut frontier = Level::new(opt.mem_limit);
    let mut first = vec![];
    let inits = initial_states();
    tbl.reserve(inits.len(), opt.workers);
    if use_gpu {
        gpu_set_table(&tbl);
    }
    for (_, w, fp) in inits {
        generated += 1;
        if tbl.insert_range(fp, fp, 0, SHARDS) {
            first.push((w, fp));
        }
    }
    let mut distinct = first.len() as u64;
    tbl.count_added(first.len());
    println!(
        "Finished computing initial states: {} distinct states generated. ({} workers, batched, lookup on {})",
        first.len(),
        opt.workers,
        if use_gpu { "GPU" } else { "CPU" }
    );
    if opt.metal && !use_gpu {
        eprintln!("warning: -metal: falling back to the CPU (needs Metal and a 64-bit fingerprint)");
    }
    frontier.extend(first, opt);
    let stop = std::sync::atomic::AtomicBool::new(false);
    let parts = opt.workers;
    let mut depth = 1u32;
    let mut last = std::time::Instant::now();
    let cand_bytes = std::mem::size_of::<Cand>();
    let cand_max = (opt.mem_limit / cand_bytes).max(1 << 16);
    let batch = (cand_max / 8).max(1024);
    while !frontier.is_empty() {
        let left_before = frontier.len();
        let mut nxt = Level::new(opt.mem_limit);
        let mut found_err: Option<SFound> = None;
        let mut done = 0usize;
        // While the GPU handles lookups, run phase 1 of the next batch, to cut the time either
        // the CPU or the GPU sits idle.
        // Running phases 1 and 3 concurrently was tried, but it put 20 threads on 10 cores and
        // was slower (wall time 5.67 s -> 6.05 s), so those two run one after the other.
        let mut carried: Option<Vec<Vec<Vec<Cand>>>> = None;
        let mut batches = frontier.batches(batch);
        loop {
            let part = batches.next();
            if part.is_none() && carried.is_none() {
                break;
            }
            // First dispatch the previous batch (if any) to the GPU. The table must be grown before
            // this point, while nobody is touching it.
            let pending = match carried.take() {
                Some(by_part) => {
                    let n: usize = by_part.iter().flat_map(|g| g.iter()).map(|v| v.len()).sum();
                    if tbl.reserve(n, opt.workers) && use_gpu {
                        gpu_set_table(&tbl);
                    }
                    let total = if use_gpu { gpu_start(&by_part, &tbl) } else { n };
                    Some((by_part, total))
                }
                None => None,
            };
            // While the GPU is busy, run phase 1 of the next batch.
            let tph = std::time::Instant::now();
            if let Some(part) = part.filter(|_| found_err.is_none()) {
                let n = part.len();
                done += n;
                let k = if n < 1024 { 1 } else { opt.workers.min(n) };
                let per = n.div_ceil(k);
                let collected: Vec<Collected> = std::thread::scope(|sc| {
                    let hs: Vec<_> = (0..k)
                        .map(|i| {
                            let (x, y) = (i * per, ((i + 1) * per).min(n));
                            let (pt, stop) = (&part, &stop);
                            sc.spawn(move || collect_phase(pt, x, y, opt, stop, parts))
                        })
                        .collect();
                    hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
                });
                // Group the per-thread arrays by owner, moving them as is rather than copying
                // their contents.
                let mut by_part: Vec<Vec<Vec<Cand>>> = (0..parts).map(|_| vec![]).collect();
                for c in collected {
                    generated += c.generated;
                    if found_err.is_none() {
                        found_err = c.found;
                    }
                    for (t, v) in c.parts.into_iter().enumerate() {
                        if !v.is_empty() {
                            by_part[t].push(v);
                        }
                    }
                }
                carried = Some(by_part);
            }
            ph(0, tph);
            // Collect the results of the dispatched batch and move on to phase 3.
            // Even if phase 1 found an error, insert what was collected before reporting it.
            let Some((by_part, total)) = pending else { continue };
            let tph = std::time::Instant::now();
            let mut flags: Vec<Vec<u8>> =
                by_part.iter().map(|g| vec![0u8; g.iter().map(|v| v.len()).sum()]).collect();
            if use_gpu {
                gpu_wait(&by_part, &mut flags, total);
            } else {
                flags = std::thread::scope(|sc| {
                    let hs: Vec<_> = by_part
                        .iter()
                        .map(|g| {
                            let tbl = &tbl;
                            sc.spawn(move || {
                                let mut f = vec![0u8; g.iter().map(|v| v.len()).sum()];
                                let mut off = 0;
                                for cs in g {
                                    lookup_phase_cpu(cs, &mut f[off..off + cs.len()], tbl);
                                    off += cs.len();
                                }
                                f
                            })
                        })
                        .collect();
                    hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
                });
            }
            ph(1, tph);
            let tph = std::time::Instant::now();
            let results: Vec<(Vec<Qitem>, u64)> = std::thread::scope(|sc| {
                let hs: Vec<_> = by_part
                    .iter()
                    .zip(flags.iter())
                    .enumerate()
                    .map(|(t, (g, f))| {
                        let tbl = &tbl;
                        let (lo, hi) = (t * SHARDS / parts, (t + 1) * SHARDS / parts);
                        sc.spawn(move || {
                            let mut o: (Vec<Qitem>, u64) = (vec![], 0);
                            let mut off = 0;
                            for cs in g {
                                let (v, d) = insert_phase(cs, &f[off..off + cs.len()], tbl, lo, hi);
                                off += cs.len();
                                o.0.extend(v);
                                o.1 += d;
                            }
                            o
                        })
                    })
                    .collect();
                hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
            });
            ph(2, tph);
            let mut added = 0usize;
            for (v, d) in results {
                distinct += d;
                added += d as usize;
                nxt.extend(v, opt);
            }
            // Count after every batch, so that `reserve` for the next batch sees the current total.
            tbl.count_added(added);
            if found_err.is_some() {
                break;
            }
            if last.elapsed().as_secs() >= 10 {
                last = std::time::Instant::now();
                println!(
                    "Progress({depth}): {generated} states generated, {distinct} distinct states found, {} states left on queue. ({:.0}s)",
                    nxt.len() + (left_before - done),
                    t0.elapsed().as_secs_f64()
                );
            }
        }
        if let Some(f) = found_err {
            report_and_exit(&tbl, f, generated, distinct, nxt.len() + (left_before - done));
        }
        frontier = nxt;
        if !frontier.is_empty() {
            depth += 1;
        }
    }
    finish(opt, t0, generated, distinct, depth);
}

fn run_liveness(opt: &Opt) {
    let check_deadlock = opt.check_deadlock;
    let workers = opt.workers;
    let t0 = std::time::Instant::now();
    let mut g = Graph { states: Vec::new(), parent: Vec::new() };
    let seen = Shards::new(false);
    let mut generated: u64 = 0;
    for (_, w, fp) in initial_states() {
        generated += 1;
        if seen.insert(fp) {
            g.states.push(w);
            g.parent.push((u32::MAX, u32::MAX));
        }
    }
    println!("Finished computing initial states: {} distinct states generated. ({workers} workers)", g.states.len());
    let stop = std::sync::atomic::AtomicBool::new(false);
    let mut live = LiveChunk::default();
    let mut lo = 0usize;
    let mut depth = 1u32;
    let mut last = std::time::Instant::now();
    loop {
        let hi = g.states.len();
        if lo == hi {
            break;
        }
        // Split the level (all states at the same depth) into contiguous chunks and expand them
        // in parallel.
        let n = hi - lo;
        let k = if n < 1024 { 1 } else { workers.min(n) };
        let per = n.div_ceil(k);
        let chunks: Vec<Chunk> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..k)
                .map(|i| {
                    let (a, b) = (lo + i * per, (lo + (i + 1) * per).min(hi));
                    let (g, seen, stop) = (&g, &seen, &stop);
                    sc.spawn(move || expand(g, a, b, seen, stop, i, check_deadlock))
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
        });
        let mut found = None;
        let mut base = vec![];
        for (i, c) in chunks.into_iter().enumerate() {
            generated += c.generated;
            base.push(g.states.len());
            if LIVENESS {
                let (toff, eoff) = (live.tags.len() as u32, live.enab.len() as u32);
                live.edges.extend(c.live.edges.into_iter().map(|(a, b, l, o, n)| (a, b, l, o + toff, n)));
                live.tags.extend(c.live.tags);
                live.en.extend(c.live.en.into_iter().map(|(a, o, n)| (a, o + eoff, n)));
                live.enab.extend(c.live.enab);
            }
            g.states.extend(c.states);
            g.parent.extend(c.parent);
            if found.is_none() {
                found = c.found.map(|f| (i, f));
            }
        }
        if let Some((_, f)) = found {
            let mut distinct = g.states.len();
            let code = match &f {
                Found::Deadlock(_) => 11,
                Found::Type(_, _, _, None) => eval_code(&EvalErr::Type(String::new())),
                Found::Eval(_, e) => eval_code(e),
                _ => 12,
            };
            match f {
                Found::Inv(w, idx, inv) => {
                    println!("Error: Invariant {inv} is violated.");
                    g.print_trace((base[w] + idx) as u32, None);
                }
                Found::Deadlock(id) => {
                    println!("Error: Deadlock reached.");
                    g.print_trace(id, None);
                }
                Found::Type(p, t, l, inv) => {
                    // The out-of-type state counts as one state too (to match TLC).
                    distinct += 1;
                    match inv {
                        Some(inv) => println!("Error: Invariant {inv} is violated."),
                        None => report_eval(&EvalErr::Type("a variable".into())),
                    }
                    g.print_trace(p, Some((&t, l)));
                }
                Found::Action(p, t, l, name) => {
                    println!("Error: Action property {name} is violated.");
                    g.print_trace(p, Some((&t, l)));
                }
                Found::Eval(p, e) => {
                    report_eval(&e);
                    g.print_trace(p, None);
                    if let EvalErr::Type(_) = e {
                        // As in TLC, the out-of-type successor counts as one state (its contents
                        // can't be represented).
                        generated += 1;
                        distinct += 1;
                        println!("State {}: <a successor that tla2rs cannot represent>\n", g.trace_len(p) + 1);
                    }
                }
            }
            println!(
                "{generated} states generated, {distinct} distinct states found, {} states left on queue.",
                g.states.len() - lo
            );
            std::process::exit(code);
        }
        lo = hi;
        if g.states.len() > lo {
            depth += 1;
        }
        if last.elapsed().as_secs() >= 10 {
            last = std::time::Instant::now();
            println!(
                "Progress({depth}): {generated} states generated, {} distinct states found, {} states left on queue. ({:.0}s)",
                g.states.len(),
                g.states.len() - lo,
                t0.elapsed().as_secs_f64()
            );
        }
    }
    println!("{generated} states generated, {} distinct states found, 0 states left on queue.", g.states.len());
    println!("The depth of the complete state graph search is {depth}.");
    if WORDS * 64 > FP_BITS {
        let n = g.states.len() as f64;
        println!(
            "  Estimate of the probability that a state was skipped because two distinct states shared a {FP_BITS}-bit fingerprint: {:.1e}",
            n * n / 2.0 / 2f64.powi(FP_BITS as i32)
        );
    }
    if LIVENESS {
        let t1 = std::time::Instant::now();
        let ok = liveness(&g, live);
        println!("Checked temporal properties in {:.3}s", t1.elapsed().as_secs_f64());
        if !ok {
            std::process::exit(13);
        }
    }
    println!("Model checking completed. No error has been found.");
    println!("Finished in {:.3}s", t0.elapsed().as_secs_f64());
}
"##;

/// Liveness checking. Builds the state graph in CSR form and, for each property, looks for a fair
/// SCC (or a stuttering state) in which the property can stay violated forever.
/// The edge tags and enabledness (en) come from evaluating each fairness-constrained action on its
/// own.
pub const LIVENESS_RT: &str = r##"
// ---------------------------------------------------------------- liveness (tla2rs)

struct Csr {
    off: Vec<u64>,
    dst: Vec<u32>,
    label: Vec<u32>,
    /// The tags of edge e are tags[toff[e]..toff[e + 1]].
    toff: Vec<u32>,
    tags: Vec<u32>,
    /// The WF instances enabled in state s are enab[eoff[s]..eoff[s + 1]].
    eoff: Vec<u32>,
    enab: Vec<u32>,
}

impl Csr {
    #[inline]
    fn out(&self, s: u32) -> std::ops::Range<usize> {
        self.off[s as usize] as usize..self.off[s as usize + 1] as usize
    }
    #[inline]
    fn tags(&self, e: usize) -> &[u32] {
        &self.tags[self.toff[e] as usize..self.toff[e + 1] as usize]
    }
    #[inline]
    fn enabled(&self, s: u32) -> &[u32] {
        &self.enab[self.eoff[s as usize] as usize..self.eoff[s as usize + 1] as usize]
    }
}

/// The shortest path within C from `from` that takes at least one step and reaches `goal`, as a
/// list of (state, label of the edge entering it).
fn path_in(c: &Csr, comp: &[u32], cid: u32, from: u32, goal: &dyn Fn(u32) -> bool) -> Vec<(u32, u32)> {
    let mut prev: std::collections::HashMap<u32, (u32, u32)> = std::collections::HashMap::new();
    let mut q = std::collections::VecDeque::new();
    q.push_back(from);
    while let Some(u) = q.pop_front() {
        for e in c.out(u) {
            let v = c.dst[e];
            if comp[v as usize] != cid || prev.contains_key(&v) {
                continue;
            }
            prev.insert(v, (u, c.label[e]));
            if goal(v) {
                let mut out = vec![];
                let mut x = v;
                loop {
                    let (p, l) = prev[&x];
                    out.push((x, l));
                    if p == from {
                        break;
                    }
                    x = p;
                }
                out.reverse();
                return out;
            }
            if v != from {
                q.push_back(v);
            }
        }
    }
    vec![]
}

fn liveness(g: &Graph, mut live: LiveChunk) -> bool {
    let n = g.states.len();
    // Fingerprint -> state index
    let cap = (n * 2).next_power_of_two().max(16);
    let mut keys = vec![0 as Fp; cap];
    let mut vals = vec![u32::MAX; cap];
    let mut zero_id = u32::MAX;
    for (i, w) in g.states.iter().enumerate() {
        let fp = state_fp(&unpack(w), w);
        if fp == 0 {
            zero_id = i as u32;
            continue;
        }
        let mut k = (fp as usize) & (cap - 1);
        while keys[k] != 0 {
            k = (k + 1) & (cap - 1);
        }
        keys[k] = fp;
        vals[k] = i as u32;
    }
    let lookup = |fp: Fp| -> u32 {
        if fp == 0 {
            return zero_id;
        }
        let mut k = (fp as usize) & (cap - 1);
        loop {
            if keys[k] == fp {
                return vals[k];
            }
            if keys[k] == 0 {
                return u32::MAX;
            }
            k = (k + 1) & (cap - 1);
        }
    };
    // CSR
    live.edges.sort_by_key(|e| e.0);
    let m = live.edges.len();
    let mut c = Csr {
        off: vec![0; n + 1],
        dst: Vec::with_capacity(m),
        label: Vec::with_capacity(m),
        toff: Vec::with_capacity(m + 1),
        tags: Vec::new(),
        eoff: vec![0; n + 1],
        enab: Vec::new(),
    };
    c.toff.push(0);
    for &(s, tfp, l, o, k) in &live.edges {
        c.off[s as usize + 1] += 1;
        c.dst.push(lookup(tfp));
        c.label.push(l);
        c.tags.extend_from_slice(&live.tags[o as usize..(o + k) as usize]);
        c.toff.push(c.tags.len() as u32);
    }
    for i in 0..n {
        c.off[i + 1] += c.off[i];
    }
    live.en.sort_by_key(|e| e.0);
    let mut j = 0;
    for s in 0..n {
        while j < live.en.len() && live.en[j].0 as usize == s {
            let (_, o, k) = live.en[j];
            c.enab.extend_from_slice(&live.enab[o as usize..(o + k) as usize]);
            j += 1;
        }
        c.eoff[s + 1] = c.enab.len() as u32;
    }
    drop(live);
    let nf = FAIR.len();
    let inits: Vec<u32> = (0..n as u32).filter(|&i| g.parent[i as usize].0 == u32::MAX).collect();

    for (name, kind, p, q) in PROPS {
        let (pv, qv): (Vec<bool>, Vec<bool>) = (0..n)
            .map(|i| {
                let s = unpack(&g.states[i]);
                (p(&s), q(&s))
            })
            .unzip();
        if *kind == 4 {
            if let Some(bad) = (0..n).find(|&i| !pv[i]) {
                println!("Error: Temporal property {name} is violated.");
                g.print_trace(bad as u32, None);
                return false;
            }
            continue;
        }
        // allowed: states in which the property can keep being violated. starts: states to search
        // from. need: states the cycle must include.
        let allowed: Vec<bool> = (0..n).map(|i| match kind { 0 | 1 => !pv[i], 2 => true, _ => !qv[i] }).collect();
        let starts: Vec<u32> = match kind {
            0 => inits.iter().copied().filter(|&i| !pv[i as usize]).collect(),
            1 => (0..n as u32).filter(|&i| !pv[i as usize]).collect(),
            2 => inits.clone(),
            _ => (0..n as u32).filter(|&i| pv[i as usize] && !qv[i as usize]).collect(),
        };
        let need = |i: u32| -> bool { *kind != 2 || !pv[i as usize] };
        if let Some((prefix, cycle)) = find_fair(&c, &allowed, &starts, &need, nf) {
            println!("Error: Temporal property {name} is violated.");
            println!("Error: The following behavior constitutes a counter-example:");
            print_lasso(g, &prefix, &cycle);
            return false;
        }
    }
    println!("Temporal properties hold ({} properties, {} fairness instances, {} edges).", PROPS.len(), nf, c.dst.len());
    true
}

/// A counterexample found: `prefix` is a list of (state, label entering it) ending at the cycle's
/// entry. If `cycle` is empty, the behavior stutters forever at the entry; otherwise it is a cycle
/// back to the entry.
fn find_fair(
    c: &Csr,
    allowed: &[bool],
    starts: &[u32],
    need: &dyn Fn(u32) -> bool,
    nf: usize,
) -> Option<(Vec<(u32, u32)>, Vec<(u32, u32)>)> {
    let n = allowed.len();
    // BFS from starts, staying within allowed.
    let mut bpar = vec![(u32::MAX, u32::MAX); n];
    let mut inr = vec![false; n];
    let mut order = vec![];
    for &s in starts {
        if allowed[s as usize] && !inr[s as usize] {
            inr[s as usize] = true;
            order.push(s);
        }
    }
    let mut h = 0;
    while h < order.len() {
        let u = order[h];
        h += 1;
        for e in c.out(u) {
            let v = c.dst[e];
            if allowed[v as usize] && !inr[v as usize] {
                inr[v as usize] = true;
                bpar[v as usize] = (u, c.label[e]);
                order.push(v);
            }
        }
    }
    let prefix_to = |x: u32| -> Vec<(u32, u32)> {
        let mut v = vec![];
        let mut y = x;
        while y != u32::MAX {
            v.push((y, bpar[y as usize].1));
            y = bpar[y as usize].0;
        }
        v.reverse();
        v
    };
    // Stuttering: if no WF instance is enabled in a state, the behavior may stay there forever.
    for &s in &order {
        if need(s) && c.enabled(s).is_empty() {
            return Some((prefix_to(s), vec![]));
        }
    }
    // Find SCCs with (iterative) Tarjan and look for a fair one.
    let mut index = vec![u32::MAX; n];
    let mut low = vec![0u32; n];
    let mut on = vec![false; n];
    let mut comp = vec![u32::MAX; n];
    let mut stack: Vec<u32> = vec![];
    let mut idx = 0u32;
    let mut ncomp = 0u32;
    let mut en_count = vec![0u32; nf];
    let mut taken = vec![false; nf];
    for &root in &order {
        if index[root as usize] != u32::MAX {
            continue;
        }
        let mut call: Vec<(u32, usize)> = vec![(root, c.out(root).start)];
        index[root as usize] = idx;
        low[root as usize] = idx;
        idx += 1;
        stack.push(root);
        on[root as usize] = true;
        while let Some(&mut (u, ref mut ei)) = call.last_mut() {
            let end = c.out(u).end;
            if *ei < end {
                let v = c.dst[*ei];
                *ei += 1;
                if !inr[v as usize] {
                    continue;
                }
                if index[v as usize] == u32::MAX {
                    index[v as usize] = idx;
                    low[v as usize] = idx;
                    idx += 1;
                    stack.push(v);
                    on[v as usize] = true;
                    call.push((v, c.out(v).start));
                } else if on[v as usize] {
                    low[u as usize] = low[u as usize].min(index[v as usize]);
                }
                continue;
            }
            call.pop();
            if let Some(&(p, _)) = call.last() {
                low[p as usize] = low[p as usize].min(low[u as usize]);
            }
            if low[u as usize] != index[u as usize] {
                continue;
            }
            let mut members = vec![];
            loop {
                let w = stack.pop().unwrap();
                on[w as usize] = false;
                comp[w as usize] = ncomp;
                members.push(w);
                if w == u {
                    break;
                }
            }
            let cid = ncomp;
            ncomp += 1;
            if members.len() < 2 || !members.iter().any(|&m| need(m)) {
                continue;
            }
            // WF(A): if A is enabled in every state of C, C must contain an A step.
            let mut touched = vec![];
            for &m in &members {
                for &a in c.enabled(m) {
                    if en_count[a as usize] == 0 && !taken[a as usize] {
                        touched.push(a as usize);
                    }
                    en_count[a as usize] += 1;
                }
                for e in c.out(m) {
                    if comp[c.dst[e] as usize] != cid {
                        continue;
                    }
                    for &a in c.tags(e) {
                        if en_count[a as usize] == 0 && !taken[a as usize] {
                            touched.push(a as usize);
                        }
                        taken[a as usize] = true;
                    }
                }
            }
            let fair = touched.iter().all(|&a| taken[a] || (en_count[a] as usize) < members.len());
            let mut need_off = vec![];
            let mut need_step = vec![];
            for &a in &touched {
                if (en_count[a] as usize) < members.len() {
                    need_off.push(a as u32);
                } else if taken[a] {
                    need_step.push(a as u32);
                }
            }
            for &a in &touched {
                en_count[a] = 0;
                taken[a] = false;
            }
            if !fair {
                continue;
            }
            // Build the cycle. Its entry is the first state of C reached by the BFS that satisfies
            // `need`.
            let entry = *order.iter().find(|&&x| comp[x as usize] == cid && need(x)).unwrap();
            let mut cyc: Vec<(u32, u32)> = vec![];
            let mut cur = entry;
            for &a in &need_off {
                let off_here = std::iter::once(entry).chain(cyc.iter().map(|x| x.0)).any(|s| !c.enabled(s).contains(&a));
                if off_here {
                    continue;
                }
                let p = path_in(c, &comp, cid, cur, &|s| !c.enabled(s).contains(&a));
                if let Some(&(l, _)) = p.last() {
                    cur = l;
                }
                cyc.extend(p);
            }
            for &a in &need_step {
                let has = |x: u32| c.out(x).any(|e| comp[c.dst[e] as usize] == cid && c.tags(e).contains(&a));
                if !has(cur) {
                    let p = path_in(c, &comp, cid, cur, &has);
                    if let Some(&(l, _)) = p.last() {
                        cur = l;
                    }
                    cyc.extend(p);
                }
                let e = c.out(cur).find(|&e| comp[c.dst[e] as usize] == cid && c.tags(e).contains(&a)).unwrap();
                cur = c.dst[e];
                cyc.push((cur, c.label[e]));
            }
            // Return to the entry.
            if cur != entry || cyc.is_empty() {
                let p = path_in(c, &comp, cid, cur, &|s| s == entry);
                cyc.extend(p);
            }
            let mut prefix = prefix_to(entry);
            if prefix.is_empty() {
                prefix.push((entry, u32::MAX));
            }
            return Some((prefix, cyc));
        }
    }
    None
}

fn print_lasso(g: &Graph, prefix: &[(u32, u32)], cycle: &[(u32, u32)]) {
    // Prepend the path to the first state of prefix, following BFS parents.
    let first = prefix[0].0;
    let mut lead: Vec<(u32, u32)> = vec![];
    let mut y = g.parent[first as usize].0;
    while y != u32::MAX {
        lead.push((y, g.parent[y as usize].1));
        y = g.parent[y as usize].0;
    }
    lead.reverse();
    let mut all = lead;
    all.push((first, g.parent[first as usize].1));
    all.extend(prefix[1..].iter().copied());
    let entry_no = all.len();
    let name = |l: u32| if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
    for (i, &(s, l)) in all.iter().enumerate() {
        println!("State {}: <{}>\n{}\n", i + 1, name(l), show(&unpack(&g.states[s as usize])));
    }
    if cycle.is_empty() {
        println!("State {}: Stuttering", all.len() + 1);
        return;
    }
    let mut k = all.len();
    for (j, &(s, l)) in cycle.iter().enumerate() {
        if j + 1 == cycle.len() {
            println!("State {}: Back to state {}: <{}>", k + 1, entry_no, name(l));
        } else {
            k += 1;
            println!("State {}: <{}>\n{}\n", k, name(l), show(&unpack(&g.states[s as usize])));
        }
    }
}
"##;
