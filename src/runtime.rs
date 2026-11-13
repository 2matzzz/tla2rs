//! Runtime support pasted into every generated checker. The generated code depends on no external
//! crates.
//!
//! - States are bit-packed (`Packed`) into a flat array that serves as both the BFS queue and the
//!   record used to rebuild traces.
//! - The visited set stores only 64-bit fingerprints (the same approach as TLC). When a state fits
//!   in 64 bits, the fingerprint is invertible, so there are no collisions.

/// TLC's pretty printer (`src/ppr.rs`), pasted into the generated checker with the runtime
pub const PPR: &str = include_str!("ppr.rs");

pub const RUNTIME: &str = r##"
// ---------------------------------------------------------------- runtime (tla2rs)

/// A search thread, with a stack sized for the states it copies (a state holds its sequences and
/// sets inline, so long sequences make large states)
fn spawn_worker<'s, 'e, F, T>(sc: &'s std::thread::Scope<'s, 'e>, f: F) -> std::thread::ScopedJoinHandle<'s, T>
where
    F: FnOnce() -> T + Send + 's,
    T: Send + 's,
{
    std::thread::Builder::new().stack_size(worker_stack()).spawn_scoped(sc, f).expect("cannot start a search thread")
}

fn worker_stack() -> usize {
    (64 * std::mem::size_of::<State>()).max(16 << 20)
}

/// The search threads, started once per search. A job over 0..n is cut into consecutive pieces,
/// which the threads take one at a time: a thread that is done (or got more CPU) takes the next,
/// so a level waits for no thread holding a fixed share. Results come back in the order of the
/// pieces, so merging them in that order sees the states in the order of the level, as one
/// thread would.
struct Pool {
    shared: std::sync::Arc<PoolShared>,
    threads: Vec<std::thread::JoinHandle<()>>,
}

struct PoolShared {
    m: std::sync::Mutex<PoolState>,
    wake: std::sync::Condvar,
    idle: std::sync::Condvar,
}

struct PoolState {
    /// Counts the jobs posted, so that a thread takes each one at most once
    seq: u64,
    task: Option<PoolTask>,
    /// The threads running the posted task
    busy: usize,
    quit: bool,
}

/// The posted task, its lifetime erased: `Pool::run_with` withdraws it, and waits until no thread
/// runs it, before what it borrows goes away.
#[derive(Clone, Copy)]
struct PoolTask(*const (dyn Fn(usize) + Sync + 'static));

unsafe impl Send for PoolTask {}

impl Pool {
    fn new(workers: usize) -> Self {
        let shared = std::sync::Arc::new(PoolShared {
            m: std::sync::Mutex::new(PoolState { seq: 0, task: None, busy: 0, quit: false }),
            wake: std::sync::Condvar::new(),
            idle: std::sync::Condvar::new(),
        });
        let threads = (0..workers.max(1))
            .map(|wid| {
                let sh = shared.clone();
                std::thread::Builder::new()
                    .stack_size(worker_stack())
                    .spawn(move || sh.work(wid))
                    .expect("cannot start a search thread")
            })
            .collect();
        Pool { shared, threads }
    }

    fn workers(&self) -> usize {
        self.threads.len()
    }

    /// Pieces of a job over n items: small enough that every thread takes several, so the threads
    /// finish together, and at least `min` items each, so a piece costs more than taking it
    fn piece(&self, n: usize, min: usize) -> usize {
        (n / (self.workers() * 8)).max(min).max(1)
    }

    /// Runs f(thread, piece index, lo, hi) over the pieces of 0..n of `piece` items each on the
    /// threads, and meanwhile `side` on the calling thread. Returns the results of f in the order
    /// of the pieces. A thread's index is below `workers()`, and no two threads share one.
    fn run_with<T: Send, R>(
        &self,
        n: usize,
        piece: usize,
        f: impl Fn(usize, usize, usize, usize) -> T + Sync,
        side: impl FnOnce() -> R,
    ) -> (Vec<T>, R) {
        use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
        let piece = piece.max(1);
        let np = n.div_ceil(piece);
        let next = AtomicUsize::new(0);
        let out: Vec<std::sync::Mutex<Option<T>>> = (0..np).map(|_| std::sync::Mutex::new(None)).collect();
        let failed: std::sync::Mutex<Option<Box<dyn std::any::Any + Send>>> = std::sync::Mutex::new(None);
        let body = |wid: usize| loop {
            let i = next.fetch_add(1, Relaxed);
            if i >= np {
                break;
            }
            let (lo, hi) = (i * piece, ((i + 1) * piece).min(n));
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(wid, i, lo, hi))) {
                Ok(r) => *out[i].lock().unwrap() = Some(r),
                Err(p) => {
                    failed.lock().unwrap().get_or_insert(p);
                    next.store(np, Relaxed);
                }
            }
        };
        let sh = &*self.shared;
        if np > 0 {
            let task: &(dyn Fn(usize) + Sync) = &body;
            // Withdrawn below, before body goes out of scope
            let task = unsafe { std::mem::transmute::<&(dyn Fn(usize) + Sync), &'static (dyn Fn(usize) + Sync)>(task) };
            let mut st = sh.m.lock().unwrap();
            st.seq += 1;
            st.task = Some(PoolTask(task as *const _));
            drop(st);
            if np >= self.workers() {
                sh.wake.notify_all();
            } else {
                for _ in 0..np {
                    sh.wake.notify_one();
                }
            }
        }
        let side = std::panic::catch_unwind(std::panic::AssertUnwindSafe(side));
        if np > 0 {
            // Every piece is taken, and no thread runs the task
            let mut st = sh.m.lock().unwrap();
            while next.load(Relaxed) < np || st.busy > 0 {
                st = sh.idle.wait(st).unwrap();
            }
            st.task = None;
        }
        let side = side.unwrap_or_else(|p| std::panic::resume_unwind(p));
        if let Some(p) = failed.into_inner().unwrap() {
            std::panic::resume_unwind(p);
        }
        (out.into_iter().map(|r| r.into_inner().unwrap().unwrap()).collect(), side)
    }

    fn run<T: Send>(&self, n: usize, piece: usize, f: impl Fn(usize, usize, usize, usize) -> T + Sync) -> Vec<T> {
        self.run_with(n, piece, f, || ()).0
    }
}

impl PoolShared {
    fn work(&self, wid: usize) {
        let mut seen = 0;
        loop {
            let mut st = self.m.lock().unwrap();
            let task = loop {
                if st.quit {
                    return;
                }
                if st.seq != seen {
                    seen = st.seq;
                    if let Some(t) = st.task {
                        st.busy += 1;
                        break t;
                    }
                }
                st = self.wake.wait(st).unwrap();
            };
            drop(st);
            // The task catches what f raises
            unsafe { (*task.0)(wid) };
            let mut st = self.m.lock().unwrap();
            st.busy -= 1;
            if st.busy == 0 {
                self.idle.notify_all();
            }
        }
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        self.shared.m.lock().unwrap().quit = true;
        self.shared.wake.notify_all();
        for t in self.threads.drain(..) {
            let _ = t.join();
        }
    }
}

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
    // Without a VIEW, the key under the first permutation decides the smallest one, so a repeat is
    // caught before trying the others
    let by_first = mine.is_some() && !HAS_VIEW;
    let mut fresh = |fp| mine.as_mut().is_none_or(|m| m.fresh(fp));
    if PERMS.is_empty() {
        let fp = fingerprint(&key_of(s)?);
        return Some(fresh(fp).then_some(fp));
    }
    if HAS_VIEW {
        // As TLC does (`TLCStateMut.fingerPrint`): the smallest of the permuted states, comparing
        // values in TLC's order and the variables in the order TLC prints them, and then the VIEW
        // of that state. Two states with equal views can have smallest states whose views differ,
        // and TLC keeps both
        let mut best = *s;
        for p in PERMS.iter() {
            let t = perm_state(s, p);
            if tlc_state_cmp(&t, &best).is_lt() {
                best = t;
            }
        }
        let fp = fingerprint(&key_of(&best)?);
        return Some(fresh(fp).then_some(fp));
    }
    let mut best: Option<Key> = None;
    for (i, p) in PERMS.iter().enumerate() {
        let k = if i == 0 && PERM0_IS_ID { key_of(s)? } else { key_of(&perm_state(s, p))? };
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
        arith_error("The second argument of \\div is 0.".into());
    }
    let q = a / b;
    if a % b != 0 && ((a < 0) != (b < 0)) { q - 1 } else { q }
}

/// `\div` of Naturals in TLC, when the spec does not load Integers: rounded toward zero, then one
/// less only when that is negative (`(0 - 1) \div 3` is 0)
#[inline]
fn tla_div_nat(a: i64, b: i64) -> i64 {
    if b == 0 {
        arith_error("The second argument of \\div is 0.".into());
    }
    let q = a / b;
    if a % b != 0 && q < 0 { q - 1 } else { q }
}

#[inline]
fn tla_mod(a: i64, b: i64) -> i64 {
    if b <= 0 {
        arith_error(format!("The second argument of % should be a positive number, but instead it is:\n{b}"));
    }
    a.rem_euclid(b)
}

/// An evaluation error. Raised via panic, caught outside state expansion, and reported with a
/// trace.
#[derive(Clone)]
enum EvalErr {
    /// A value outside the type declared in TypeOK (a set element, a function argument, etc.).
    Type(String),
    /// A failed arithmetic operation (`\div` by zero, `%` by a non-positive number). TLC exits
    /// with a different code for these than for the other errors (see `eval_code`).
    Arith(String),
    /// Assert(P, msg) with P false. TLC exits with its own code for this (see `eval_code`).
    Assert(String),
    /// Anything else (no matching CASE arm, a missing record field, etc.).
    Other(String),
    /// A successor or initial state that leaves variables unassigned (see `incomplete_succ`).
    /// TLC reports it as its own error.
    Incomplete(String),
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
// The empty tuple: a value of a type with no fields (an element's << >> inside a sequence)
const_default_tuple!();
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
    len: u16,
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
                capacity_exceeded(CAP_SET, N + 1, format!("a set grew beyond {N} elements; raise the capacity with `Cardinality(x) <= K` in TypeDecl / TypeOK or -setcap"));
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
    // The other operand by reference: a set held as an array can be kilobytes
    fn union(self, o: &Self) -> Self {
        let mut r = self;
        if self.len as usize + o.len as usize > N {
            let need = self.len as usize + o.iter().filter(|x| !self.contains(x)).count();
            if need > N {
                capacity_exceeded(CAP_SET, need, format!("a set grew beyond {N} elements; raise the capacity with `Cardinality(x) <= K` in TypeDecl / TypeOK or -setcap"));
            }
        }
        for x in o.iter() {
            r.insert(x);
        }
        r
    }
    fn inter(self, o: &Self) -> Self {
        let mut r = Self::new();
        for x in self.iter() {
            if o.contains(&x) {
                r.insert(x);
            }
        }
        r
    }
    fn minus(self, o: &Self) -> Self {
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

/// A function over part of a large type (or a bag over one), held as the set of its (key, value)
/// pairs. The pairs sort by key first and no two share a key, so a key is found by binary search.
impl<K: Copy + Ord + ConstDefault, V: Copy + Ord + ConstDefault, const N: usize> SSet<(K, V), N> {
    #[inline]
    fn find(&self, k: &K) -> Result<usize, usize> {
        self.slice().binary_search_by(|p| p.0.cmp(k))
    }
    #[inline]
    fn get(&self, k: &K) -> Option<V> {
        self.find(k).ok().map(|i| self.items[i].1)
    }
    #[inline]
    fn put(&mut self, k: K, v: V) {
        match self.find(&k) {
            Ok(i) => self.items[i].1 = v,
            Err(i) => {
                let n = self.len as usize;
                if n == N {
                    capacity_exceeded(CAP_SET, N + 1, format!("the domain of a function or bag grew beyond {N} elements; raise the capacity with `Cardinality(DOMAIN f) <= K` in TypeDecl / TypeOK or -setcap"));
                }
                self.items.copy_within(i..n, i + 1);
                self.items[i] = (k, v);
                self.len += 1;
            }
        }
    }
    fn with_put(mut self, k: K, v: V) -> Self {
        self.put(k, v);
        self
    }
    #[inline]
    fn del(&mut self, k: &K) {
        if let Ok(i) = self.find(k) {
            let n = self.len as usize;
            self.items.copy_within(i + 1..n, i);
            self.items[n - 1] = <(K, V)>::DEFAULT;
            self.len -= 1;
        }
    }
}

#[cold]
fn type_error(what: &str, v: &str) -> ! {
    std::panic::panic_any(EvalErr::Type(format!("{what} {v} is outside the type declared in TypeOK")))
}

/// The kinds of capacity a value can outgrow (see `capacity_exceeded`)
const CAP_SET: u8 = 0;
const CAP_SEQ: u8 = 1;
/// The exit code that tells tla2rs which capacity to raise: CAP_EXIT + the kind
const CAP_EXIT: i32 = 70;

/// A set (or the domain of a sparse function or bag) or a sequence outgrew the capacity this checker
/// was built with. TLC has no such bound, so this is not an error of the spec: when tla2rs runs the
/// checker, it sets TLA2RS_GROW to the kinds it can raise (`s` for sets, `q` for sequences), and the
/// checker then exits at once with CAP_EXIT + kind so that tla2rs builds it again with more room and
/// checks from the start. `need` is how many elements the value needs, at least: one more than the
/// capacity, or all of a union's or a concatenation's; it is written to the file TLA2RS_NEED names,
/// so that tla2rs builds with room for it at once. Otherwise (the checker run directly, or the
/// capacity at its maximum) it is an evaluation error.
#[cold]
fn capacity_exceeded(kind: u8, need: usize, msg: String) -> ! {
    let letter = if kind == CAP_SET { 's' } else { 'q' };
    if std::env::var("TLA2RS_GROW").is_ok_and(|g| g.contains(letter)) {
        use std::io::Write;
        if let Some(f) = std::env::var_os("TLA2RS_NEED") {
            let _ = std::fs::write(f, format!("{need}\n"));
        }
        let _ = std::io::stdout().flush();
        std::process::exit(CAP_EXIT + kind as i32);
    }
    eval_error(msg)
}

#[cold]
fn eval_error(msg: String) -> ! {
    if FP_DEPTH.with(|d| d.get()) > 0 {
        *FP_ERR.lock().unwrap_or_else(|e| e.into_inner()) = Some(msg.clone());
    }
    std::panic::panic_any(EvalErr::Other(msg))
}

// TLC reports a second error after the behavior, `TLC was unable to fingerprint.` with the same
// reason, when the error is raised inside a value it built from an expression written in the
// spec, such as a set `{...}`, a tuple `<<...>>`, `[S -> T]` or `S \X T`: measured on TLC 2.19,
// `x \in {5, 6}`, `x \in {5} \cup {6}`, `{x} \subseteq S`, `f \in [Nat -> Nat]` and `<<5, 6, 7>>[i]`
// do, while `x \in S` for S from the state or a constant definition, `x \in 5..6`, `\E y \in {5, 6} :
// y = x` and a string's or tuple's own comparison (`<<"a">> \in {"ab"}`, `<<1, 2>> # s`) do not. Code generation puts such an operation inside an
// `FpSource` when it can fail (`Gen::fp_source`)
thread_local! {
    static FP_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// The message of the last error raised inside an `FpSource`
static FP_ERR: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

struct FpSource;

impl FpSource {
    fn enter() -> Self {
        FP_DEPTH.with(|d| d.set(d.get() + 1));
        FpSource
    }
}

impl Drop for FpSource {
    fn drop(&mut self) {
        FP_DEPTH.with(|d| d.set(d.get() - 1));
    }
}

/// TLC's second error after an error raised inside an `FpSource` (see above)
fn fp_note(e: &EvalErr) {
    if FP_ERR.lock().unwrap_or_else(|e| e.into_inner()).as_deref() == Some(e.msg()) {
        println!("Error: TLC was unable to fingerprint.\nReason:\n{}", e.msg());
    }
}

// ---------------------------------------------------------------- the order of printed lines
//
// With one worker TLC prints in a fixed order (measured on TLC 2.19, `tests/tlc/PrintNext*`): it
// checks each initial state and each successor as soon as it computes it, so what Init or an
// action prints before a state comes before what the invariants print on it, and nothing is
// printed past the state that stops the search. When it shows a behavior, it rebuilds it from
// fingerprints and evaluates Init again (all of it) and, for each step, the actions in order up to
// the one that yields the next state (each action as a whole), printing again: the states before
// the one it was expanding are rebuilt before `The behavior up to this point is:`, the steps to it
// and to the successor that stopped the search after it, each before its state. With PRINT_ORDER
// (Init, an action or an invariant prints), the checker computes successors as before but holds
// the lines printed meanwhile, with the number of successors pushed and of actions started before
// each, and prints them in that order; it then expands in order without -batched, and rebuilds a
// behavior as TLC does.

// ---------------------------------------------------------------- TLCGet and TLCSet
//
// What TLC 2.19 gives with one worker (measured, `tests/tlc/TlcGet*`): `TLCGet("level")` is the
// level of the state being expanded (an initial state's is 1), 0 in Init and in the checks of an
// initial state; a successor's CONSTRAINT and invariants see the level of the state it comes from.
// `"distinct"` counts the states added so far, a state counting from just before its invariants
// are checked (and after its CONSTRAINT); `"queue"` the states waiting to be expanded: an initial
// state is queued before its invariants are checked, a successor after. `"diameter"` is the
// largest level of a state added so far, 1 before any. The registers `TLCSet(i, v)` / `TLCGet(i)`
// are one store, which Init, the actions, the invariants, the constraints and the ASSUMEs share
// (`REG_INIT` holds what the ASSUMEs set); reading one never set is an error. `TLCSet("exit",
// TRUE)` ends the search, without an error, once the state being expanded (or Init) is done.
// TLC handles each state as soon as Init or an action computes it, so with TLCGET the checker
// does too (`pushed`, `expand_eager_one`). When it shows a behavior, the counts stay where the
// search stopped, the level is that of the state each step starts from (0 for Init, and when the
// failing step is evaluated once more), and the registers keep changing as TLC evaluates again.

static TG_LEVEL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static TG_DIAMETER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
static TG_DISTINCT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static TG_QUEUE: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(0);
static TG_EXIT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static TG_REGS: std::sync::Mutex<Option<std::collections::BTreeMap<i64, i64>>> = std::sync::Mutex::new(None);

fn tg_level() -> i64 {
    TG_LEVEL.load(std::sync::atomic::Ordering::Relaxed) as i64
}

fn tg_diameter() -> i64 {
    TG_DIAMETER.load(std::sync::atomic::Ordering::Relaxed) as i64
}

fn tg_distinct() -> i64 {
    TG_DISTINCT.load(std::sync::atomic::Ordering::Relaxed) as i64
}

fn tg_queue() -> i64 {
    TG_QUEUE.load(std::sync::atomic::Ordering::Relaxed)
}

fn tg_set_level(l: u64) {
    TG_LEVEL.store(l, std::sync::atomic::Ordering::Relaxed);
}

/// A new state added to the visited states (at the level after the one being expanded)
fn tg_added() {
    if TLCGET {
        TG_DISTINCT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        TG_DIAMETER.fetch_max(TG_LEVEL.load(std::sync::atomic::Ordering::Relaxed) + 1, std::sync::atomic::Ordering::Relaxed);
    }
}

/// A state queued (1) or taken off the queue (-1)
fn tg_queued(d: i64) {
    if TLCGET {
        TG_QUEUE.fetch_add(d, std::sync::atomic::Ordering::Relaxed);
    }
}

fn tg_regs<R>(f: impl FnOnce(&mut std::collections::BTreeMap<i64, i64>) -> R) -> R {
    let mut g = TG_REGS.lock().unwrap_or_else(|e| e.into_inner());
    f(g.get_or_insert_with(|| REG_INIT.iter().copied().collect()))
}

fn tg_get(i: i64) -> i64 {
    match tg_regs(|r| r.get(&i).copied()) {
        Some(v) => v,
        None => std::panic::panic_any(EvalErr::Arith(format!("TLCGet({i}) was undefined."))),
    }
}

fn tg_set(i: i64, v: i64) -> bool {
    tg_regs(|r| r.insert(i, v));
    true
}

fn tg_exit(b: bool) -> bool {
    TG_EXIT.store(b, std::sync::atomic::Ordering::Relaxed);
    true
}

fn tg_exiting() -> bool {
    TLCGET && TG_EXIT.load(std::sync::atomic::Ordering::Relaxed)
}

/// Runs f without changing the registers: for what the checker evaluates that TLC does not
/// (rebuilding a behavior before showing it)
fn tg_quiet<R>(f: impl FnOnce() -> R) -> R {
    if !TLCGET {
        return f();
    }
    let regs = tg_regs(|r| r.clone());
    let exit = TG_EXIT.load(std::sync::atomic::Ordering::Relaxed);
    let r = f();
    *TG_REGS.lock().unwrap_or_else(|e| e.into_inner()) = Some(regs);
    TG_EXIT.store(exit, std::sync::atomic::Ordering::Relaxed);
    r
}

/// Unwinds out of `init` or `next` when the search stops at a state they computed
struct EagerStop;

type PushHook = *mut (dyn FnMut(&State, u32) + 'static);

thread_local! {
    /// What handles each state as Init or an action computes it (TLCGET)
    static PUSHED: std::cell::Cell<Option<PushHook>> = const { std::cell::Cell::new(None) };
    /// Rebuilding a step: its action has yielded the next state, so the next action is not
    /// evaluated
    static STEP_DONE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// A state `init` (label u32::MAX) or `next` computed (TLCGET)
#[inline]
fn pushed(s: &State, l: u32) {
    let Some(p) = PUSHED.with(|c| c.take()) else { return };
    struct Back(PushHook);
    impl Drop for Back {
        fn drop(&mut self) {
            PUSHED.with(|c| c.set(Some(self.0)));
        }
    }
    let _back = Back(p);
    // SAFETY: the hook outlives this call (see `with_pushed`), and it is taken out of PUSHED
    // while it runs, so it is not entered twice
    unsafe { (*p)(s, l) }
}

/// Runs body with f handling each state computed
fn with_pushed<R>(f: &mut dyn FnMut(&State, u32), body: impl FnOnce() -> R) -> R {
    struct Reset(Option<PushHook>);
    impl Drop for Reset {
        fn drop(&mut self) {
            PUSHED.with(|c| c.set(self.0));
        }
    }
    let p: *mut (dyn FnMut(&State, u32) + '_) = f;
    // SAFETY: only the lifetime is changed; the pointer is removed before f goes away
    let p: PushHook = unsafe { std::mem::transmute(p) };
    let _reset = Reset(PUSHED.with(|c| c.replace(Some(p))));
    body()
}

/// Lines held while computing states (see above), and the strings made meanwhile (see "the
/// order of strings made")
#[derive(Default)]
struct Capture {
    pushes: u32,
    acts: u32,
    /// The action each pushed state came from
    push_acts: Vec<u32>,
    /// (states pushed before, actions started before, line)
    lines: Vec<(u32, u32, String)>,
    /// (states pushed before, string)
    made: Vec<(u32, u16)>,
}

thread_local! {
    static CAPTURE: std::cell::RefCell<Option<Capture>> = const { std::cell::RefCell::new(None) };
}

/// A line printed by Print or PrintT: held while capturing, printed otherwise
fn tlc_print(line: String) {
    CAPTURE.with(|c| match &mut *c.borrow_mut() {
        Some(c) => c.lines.push((c.pushes, c.acts, line)),
        None => put_line(&line),
    })
}

/// What starts a held line that is one of TLC's warnings (see `put_line`)
const WARNING_MARK: char = '\u{2}';

// TLC's options that change what the checker prints or whether it stops (set in `main`):
// -continue, -difftrace, -view, -nowarning
static CONTINUE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static DIFFTRACE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static VIEW_TRACE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static NOWARN: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn flag(f: &std::sync::atomic::AtomicBool) -> bool {
    f.load(std::sync::atomic::Ordering::Relaxed)
}

/// Keeps the reports of violations found while the search goes on (-continue) whole when several
/// workers find one at once
static REPORTING: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The text of an initial state that violates an invariant or a property: its view with -view
/// (and a VIEW), as in a behavior
fn init_text(s: &State) -> String {
    if flag(&VIEW_TRACE) && HAS_VIEW { show_view(s) } else { show(s) }
}
/// The text of a state in a behavior: its view with -view (and a VIEW), only the variables that
/// changed since `prev` with -difftrace, otherwise the state. TLC prints a view without the empty
/// line after it
fn trace_text(s: &State, prev: Option<&State>) -> String {
    if flag(&VIEW_TRACE) && HAS_VIEW {
        return show_view(s);
    }
    let Some(p) = prev.filter(|_| flag(&DIFFTRACE)) else { return format!("{}\n", show(s)) };
    let parts = |t: String| {
        let mut v: Vec<String> = vec![];
        for line in t.split('\n') {
            match v.last_mut() {
                Some(x) if !line.starts_with("/\\ ") => {
                    x.push('\n');
                    x.push_str(line);
                }
                _ => v.push(line.to_string()),
            }
        }
        v
    };
    let (a, b) = (parts(show(p)), parts(show(s)));
    let changed: Vec<&String> = b.iter().enumerate().filter(|(i, x)| a.get(*i) != Some(*x)).map(|(_, x)| x).collect();
    let mut o = String::new();
    for x in changed {
        o += x;
        o.push('\n');
    }
    o
}

/// The state before step `i` (from 0) of a behavior of `len` states, for -difftrace: TLC 2.19
/// prints the last state of a behavior of three states or more in full (measured)
fn diff_prev<'a>(i: usize, len: usize, prev: Option<&'a State>) -> Option<&'a State> {
    prev.filter(|_| !(len >= 3 && i + 1 == len))
}

/// Prints `State n: <action>` and the state (see `trace_text`)
fn print_step(head: &str, s: &State, prev: Option<&State>) {
    println!("{head}\n{}", trace_text(s, prev));
}

/// TLC's warnings printed so far, as printed (TLC prints a warning only when it has not printed
/// that text before, and the first warning of a run carries the note `NOWARNING`), and whether
/// one was printed. Starts from the warnings among STARTUP_PRINTS
static WARNED: std::sync::Mutex<Option<(std::collections::HashSet<String>, bool)>> = std::sync::Mutex::new(None);

const NOWARNING: &str = "(Use the -nowarning option to disable this warning.)";

/// With -userfile FILE (TLC's `-userFile FILE`), the file the lines the spec prints go to instead of
/// the standard output (TLC's own messages and warnings stay there)
static USER_FILE: std::sync::Mutex<Option<std::io::LineWriter<std::fs::File>>> = std::sync::Mutex::new(None);

/// What starts a line the spec printed, and what separates the values printed on it, as TLC writes
/// them to its `-userFile` (`compile::USER_MARK`, `USER_SEP`)
const USER_MARK: char = '\u{3}';
const USER_SEP: char = '\u{4}';

/// A line printed by Print or PrintT, of the values given as TLC shows them
fn printed(vals: &[&str]) -> String {
    let mut l = String::from(USER_MARK);
    for (i, v) in vals.iter().enumerate() {
        if i > 0 {
            l.push(USER_SEP);
        }
        l += v;
    }
    l
}

/// Prints a line the spec printed (without its USER_MARK): to the -userfile file if there is one,
/// as is, or else with each value pretty-printed, as TLC does
fn user_line(l: &str) {
    use std::io::Write;
    let vals = l.split(USER_SEP);
    match USER_FILE.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
        Some(w) => {
            if writeln!(w, "{}", vals.collect::<Vec<_>>().join("  ")).is_err() {
                eprintln!("cannot write the user file");
                std::process::exit(2);
            }
        }
        None => println!("{}", vals.map(ppr).collect::<Vec<_>>().join("  ")),
    }
}

/// Prints a line printed by the spec, or a warning (marked with WARNING_MARK) as TLC does
fn put_line(l: &str) {
    if let Some(u) = l.strip_prefix(USER_MARK) {
        user_line(u);
        return;
    }
    let Some(w) = l.strip_prefix(WARNING_MARK) else {
        println!("{l}");
        return;
    };
    if flag(&NOWARN) {
        return;
    }
    let mut g = WARNED.lock().unwrap_or_else(|e| e.into_inner());
    let (seen, any) = g.get_or_insert_with(|| {
        let mut seen = std::collections::HashSet::new();
        let mut any = false;
        for (i, l) in STARTUP_PRINTS.iter().enumerate() {
            if l.starts_with("Warning: ") {
                let noted = STARTUP_PRINTS.get(i + 1) == Some(&NOWARNING);
                seen.insert(if noted { format!("{l}\n{NOWARNING}") } else { l.to_string() });
                any = true;
            }
        }
        (seen, any)
    });
    let text = if *any { w.to_string() } else { format!("{w}\n{NOWARNING}") };
    *any = true;
    if seen.insert(text.clone()) {
        println!("{text}");
    }
}

/// TLC's warning for an EXCEPT that names an argument or field the value at `at` does not have
/// (the EXCEPT then changes nothing there)
#[cold]
fn except_warning(at: &str) {
    tlc_print(format!("{WARNING_MARK}Warning: The EXCEPT was applied to non-existing fields of the value at\n{at}"));
}

/// A state pushed by `init` or `next`
#[inline]
fn mark_push() {
    if !PRINT_ORDER && !STR_ORDER {
        return;
    }
    CAPTURE.with(|c| {
        if let Some(c) = &mut *c.borrow_mut() {
            c.push_acts.push(c.acts);
            c.pushes += 1;
        }
    })
}

/// The start of an action of the next-state relation
#[inline]
fn mark_action() {
    if !PRINT_ORDER && !STR_ORDER {
        return;
    }
    if TLCGET && STEP_DONE.with(|d| d.get()) {
        std::panic::panic_any(EagerStop);
    }
    CAPTURE.with(|c| {
        if let Some(c) = &mut *c.borrow_mut() {
            c.acts += 1;
        }
    })
}

/// Holds the lines printed (and the strings made) until `finish` (or until dropped, when they are
/// discarded, also while unwinding). Does nothing unless PRINT_ORDER, or strings made are noted
struct Capturing {
    active: bool,
    outer: Option<Capture>,
}

impl Capturing {
    fn start() -> Self {
        if PRINT_ORDER || str_on() {
            Capturing { active: true, outer: CAPTURE.with(|c| c.borrow_mut().replace(Capture::default())) }
        } else {
            Capturing { active: false, outer: None }
        }
    }
    fn finish(self) -> Held {
        if !self.active {
            return Held::default();
        }
        let cap = CAPTURE.with(|c| c.borrow_mut().take()).unwrap_or_default();
        Held { cap, next: 0, next_made: 0 }
    }
}

impl Drop for Capturing {
    fn drop(&mut self) {
        if self.active {
            // Back to what was there before (nothing, or an outer capture)
            let outer = self.outer.take();
            CAPTURE.with(|c| *c.borrow_mut() = outer);
        }
    }
}

/// Lines held, printed in order as the states they come before are handled (and strings made,
/// noted then)
#[derive(Default)]
struct Held {
    cap: Capture,
    next: usize,
    next_made: usize,
}

impl Held {
    /// Prints the lines printed before the `n`th state was pushed (all with u32::MAX), and notes
    /// the strings made before it
    #[inline]
    fn flush(&mut self, n: u32) {
        if !PRINT_ORDER && !STR_ORDER {
            return;
        }
        while let Some((p, _, l)) = self.cap.lines.get(self.next) {
            if *p >= n {
                break;
            }
            put_line(l);
            self.next += 1;
        }
        while let Some(&(p, a)) = self.cap.made.get(self.next_made) {
            if p >= n {
                break;
            }
            str_note(a);
            self.next_made += 1;
        }
    }
}

// ---------------------------------------------------------------- the order of strings made
//
// TLC orders strings by when it first creates them, so a string an operation makes while
// exploring (`\o`, Append, Head, Tail, SubSeq, ToString, or a constant expression TLC evaluates
// there) comes after every string made before it (measured on TLC 2.19, `tests/tlc/StrMade*`). The
// compiler numbers the strings the checker may make (from TRACK_FROM) in the order a checker built
// before made them, and the others after them as it meets them. When tla2rs runs the checker with
// one worker, it names a file in TLA2RS_ORDER, and the checker notes each such string the first
// time it makes one, where TLC would make it: what it makes while computing a successor counts
// after the invariants of the successors pushed before (as the lines printed above). A string made
// after one numbered later, or one TLC created when it parsed the spec (a name or number of a
// module, RANKED_LATE), means the order differs from TLC's: the checker still explores to the end,
// then writes the numbers of the strings in the order made to the file and exits with ORDER_EXIT,
// and tla2rs compiles the checker again with that order and checks from the start. With several
// workers the order TLC makes strings in depends on its threads, and nothing is noted.

/// The exit code that tells tla2rs to number the strings made in the order written to the file
const ORDER_EXIT: i32 = 72;

static STR_ON: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

struct Made {
    seen: Vec<bool>,
    order: Vec<u16>,
    /// One more than the largest string made so far
    top: usize,
    differs: bool,
}

static MADE: std::sync::Mutex<Option<Made>> = std::sync::Mutex::new(None);

#[inline]
fn str_on() -> bool {
    STR_ORDER && STR_ON.load(std::sync::atomic::Ordering::Relaxed)
}

/// Notes the strings made from here on, when tla2rs asks for it and there is one worker
fn str_order_start(workers: usize) {
    if STR_ORDER && workers == 1 && std::env::var_os("TLA2RS_ORDER").is_some() {
        *MADE.lock().unwrap() = Some(Made { seen: vec![false; ATOMS.len()], order: vec![], top: 0, differs: false });
        STR_ON.store(true, std::sync::atomic::Ordering::Relaxed);
    }
}

/// A string made by an operation
#[inline]
fn str_made(a: u16) {
    if (a as usize) >= TRACK_FROM && str_on() {
        str_made_now(a);
    }
}

#[inline(never)]
fn str_made_now(a: u16) {
    let held = CAPTURE.with(|c| match &mut *c.borrow_mut() {
        Some(c) => {
            c.made.push((c.pushes, a));
            true
        }
        None => false,
    });
    if !held {
        str_note(a);
    }
}

/// A string made, at the point TLC makes it
fn str_note(a: u16) {
    let mut g = MADE.lock().unwrap_or_else(|e| e.into_inner());
    let Some(m) = g.as_mut() else { return };
    let i = a as usize;
    if m.seen[i] {
        return;
    }
    m.seen[i] = true;
    m.order.push(a);
    if RANKED_LATE.get(i - TRACK_FROM).copied().unwrap_or(false) || i < m.top {
        m.differs = true;
    }
    m.top = m.top.max(i + 1);
}

/// When the strings were made in an order other than their numbers: tells tla2rs the order
fn str_order_finish() {
    if !str_on() {
        return;
    }
    let g = MADE.lock().unwrap_or_else(|e| e.into_inner());
    let Some(m) = g.as_ref().filter(|m| m.differs) else { return };
    let text: String = m.order.iter().map(|a| format!("{a}\n")).collect();
    let path = std::env::var_os("TLA2RS_ORDER").unwrap();
    if let Err(e) = std::fs::write(&path, text) {
        eprintln!("cannot write {}: {e}", std::path::Path::new(&path).display());
        return;
    }
    use std::io::Write;
    let _ = std::io::stdout().flush();
    std::process::exit(ORDER_EXIT);
}

/// The step s -> t evaluated again as TLC does while showing a behavior: the actions in order up
/// to the one that yields t, printing what they print
fn step_prints(s: &State, t: &State, level: usize) {
    let same = |x: &State| match (pack(x), pack(t)) {
        (Some(a), Some(b)) => state_fp(x, &a) == state_fp(t, &b),
        _ => x == t,
    };
    if TLCGET {
        // Printed as evaluated, and the actions after the one that yields t are not evaluated
        tg_set_level(level as u64);
        let mut hook = |x: &State, _: u32| {
            if same(x) {
                STEP_DONE.with(|d| d.set(true));
            }
        };
        let mut buf = vec![];
        with_pushed(&mut hook, || {
            let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| next(s, &mut buf)));
        });
        STEP_DONE.with(|d| d.set(false));
        return;
    }
    let cap = Capturing::start();
    let mut buf = vec![];
    let _ = successors(s, &mut buf, true);
    let held = cap.finish();
    let Some(j) = buf.iter().position(|(x, _)| same(x)) else { return };
    let last = held.cap.push_acts[j];
    for (_, a, l) in &held.cap.lines {
        if *a <= last {
            put_line(l);
        }
    }
}

/// After the behavior that ends with s, whose successors failed to evaluate: TLC evaluates them
/// again to show where the error is, printing again what they print up to the error
fn eval_again_prints(s: &State, e: &EvalErr) {
    if !PRINT_ORDER || matches!(e, EvalErr::Type(_) | EvalErr::Incomplete(_)) {
        return;
    }
    tg_set_level(0);
    let cap = Capturing::start();
    let mut buf = vec![];
    let _ = successors(s, &mut buf, true);
    cap.finish().flush(u32::MAX);
}

/// Shows a behavior as TLC does with PRINT_ORDER: `k` is the number of the state that was being
/// expanded (the states after it are successors), `extra` one more state after the trace
fn print_states_tlc(trace: &[(State, u32)], k: usize, extra: Option<(State, u32)>) -> usize {
    let name = |l: u32| if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
    let state = |n: usize, (s, l): &(State, u32), prev: Option<&State>| print_step(&format!("State {n}: <{}>", name(*l)), s, prev);
    if k >= 2 {
        let mut v = vec![];
        tg_set_level(0);
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut v)));
        for i in 1..k - 1 {
            step_prints(&trace[i - 1].0, &trace[i].0, i);
        }
    }
    println!("Error: The behavior up to this point is:");
    let len = trace.len() + extra.is_some() as usize;
    let prev = |i: usize| diff_prev(i, len, (i > 0).then(|| &trace[i - 1].0));
    for (i, st) in trace.iter().enumerate().take(k.saturating_sub(1)) {
        state(i + 1, st, prev(i));
    }
    for i in k.max(1) - 1..trace.len() {
        if i > 0 {
            step_prints(&trace[i - 1].0, &trace[i].0, i);
        }
        state(i + 1, &trace[i], prev(i));
    }
    let mut n = trace.len();
    if let Some(x) = extra {
        if let Some((last, _)) = trace.last() {
            step_prints(last, &x.0, trace.len());
        }
        n += 1;
        state(n, &x, diff_prev(n - 1, len, trace.last().map(|t| &t.0)));
    }
    n
}

/// The state that left variables unassigned (with the label of its action, `u32::MAX` for an
/// initial state, and the variables), shown at the end of the behavior with those variables null
static INCOMPLETE: std::sync::Mutex<Option<(State, u32, &'static [&'static str])>> = std::sync::Mutex::new(None);

fn incomplete() -> Option<(State, u32, &'static [&'static str])> {
    *INCOMPLETE.lock().unwrap_or_else(|e| e.into_inner())
}

/// An action that leaves the variables `null` unassigned. TLC counts the successor as generated,
/// and names the action when the next-state relation has more than one
#[cold]
fn incomplete_succ(st: State, label: u32, null: &'static [&'static str]) -> ! {
    let by = if ACTIONS > 1 {
        let name = LABELS[label as usize].split(" line ").next().unwrap_or("");
        format!("action {name} of the next-state relation")
    } else {
        "the next-state action".to_string()
    };
    let (s, are) = if null.len() > 1 { ("s", "are") } else { ("", "is") };
    let msg = format!(
        "Successor state is not completely specified by {by}. The following variable{s} {are} not assigned: {}.",
        null.join(", ")
    );
    INCOMPLETE.lock().unwrap_or_else(|e| e.into_inner()).get_or_insert((st, label, null));
    std::panic::panic_any(EvalErr::Incomplete(msg))
}

/// After the behavior up to the state whose successor left variables unassigned (`shown` states):
/// TLC shows that successor last, and counts it as generated. Returns the count to add
fn show_incomplete(shown: usize) -> u64 {
    let Some((s, l, null)) = incomplete() else { return 0 };
    if shown > 0 {
        println!("State {}: <{}>\n{}\n", shown + 1, LABELS[l as usize], show_with(&s, null));
    }
    1
}

/// An initial state that leaves the variables `null` unassigned
#[cold]
fn incomplete_init(st: State, null: &'static [&'static str]) -> ! {
    INCOMPLETE.lock().unwrap_or_else(|e| e.into_inner()).get_or_insert((st, u32::MAX, null));
    std::panic::panic_any(EvalErr::Incomplete("current state is not a legal state".into()))
}

#[cold]
fn arith_error(msg: String) -> ! {
    std::panic::panic_any(EvalErr::Arith(msg))
}

#[cold]
fn assert_error(msg: String) -> ! {
    std::panic::panic_any(EvalErr::Assert(msg))
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

/// The exit code when stopping on an evaluation error while computing successors. TLC exits with
/// 255 for a failed arithmetic operation and with 75 for the other errors. Leaving the type exits
/// with 12 when it is reported as a TypeOK violation.
fn eval_code(e: &EvalErr) -> i32 {
    match e {
        EvalErr::Type(_) if TYPE_INV_SUBSUMED || INVARIANTS.iter().any(|(n, _)| TYPE_INVARIANT == *n) => 12,
        EvalErr::Type(_) | EvalErr::Arith(_) => 255,
        EvalErr::Assert(_) => 14,
        EvalErr::Other(_) | EvalErr::Incomplete(_) => 75,
    }
}

/// The exit code for an evaluation error while computing or checking the initial states: TLC
/// exits with 75 whatever the error.
fn init_eval_code(e: &EvalErr) -> i32 {
    match e {
        EvalErr::Type(_) => eval_code(e),
        _ => 75,
    }
}

impl EvalErr {
    fn msg(&self) -> &str {
        match self {
            EvalErr::Type(m) | EvalErr::Arith(m) | EvalErr::Assert(m) | EvalErr::Other(m) | EvalErr::Incomplete(m) => m,
        }
    }
}

/// Reports a state leaving its declared type in TLC's terms: if TypeOK is an invariant, as a
/// violation of it. Returns false for any other error.
fn report_type(e: &EvalErr) -> bool {
    let EvalErr::Type(m) = e else { return false };
    // The invariant that declares the types may not be checked at run time, since `pack`
    // performs the same check.
    if TYPE_INV_SUBSUMED || INVARIANTS.iter().any(|(n, _)| TYPE_INVARIANT == *n) {
        println!("Error: Invariant {TYPE_INVARIANT} is violated.");
    } else {
        println!("Error: a successor leaves the type declared in {TYPE_INVARIANT}.");
    }
    eprintln!("  ({m}; tla2rs cannot represent that state)");
    true
}

/// Whether TLC raises the error as its own evaluation error (`EvalException`), as opposed to a
/// runtime exception: a failed arithmetic operation and a false Assert
fn tlc_eval_exception(e: &EvalErr) -> bool {
    matches!(e, EvalErr::Arith(_) | EvalErr::Assert(_) | EvalErr::Incomplete(_))
}

/// Reports an evaluation error as TLC does. TLC reports an error as an exception it did not expect
/// (with the lines below before the message, and the Java class of the exception, which a checker
/// does not have) when it is raised while evaluating the CONSTRAINT, ACTION_CONSTRAINT, VIEW or a
/// temporal property, or while computing successors when it is not one of TLC's own evaluation
/// errors (`unexpected` is then true).
fn report_eval_as(e: &EvalErr, unexpected: bool) {
    if report_type(e) {
        return;
    }
    if unexpected {
        println!("Error: TLC threw an unexpected exception.");
        println!("This was probably caused by an error in the spec or model.");
        println!("See the User Output or TLC Console for clues to what happened.");
        println!("{}", e.msg());
    } else {
        println!("Error: {}", e.msg());
    }
}

/// An error while computing successors, which TLC shows with the behavior up to the state
fn report_eval(e: &EvalErr) {
    report_eval_as(e, !tlc_eval_exception(e))
}

// ---------------------------------------------------------------- the state graph of a liveness check
/// The bytes the columns of the state graph hold in memory, how many they may hold (`-memlimit`)
/// before a column that grows moves to a file in `-tmpdir`, and the bytes written to such files
static COL_MEM: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static COL_LIMIT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(usize::MAX);
static COL_SPILLED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static COL_DIR: std::sync::Mutex<Option<std::path::PathBuf>> = std::sync::Mutex::new(None);
/// How many elements a column that is in a file collects before writing them out
const COL_BUF: usize = 8 << 20;
#[cfg(unix)]
extern "C" {
    fn mmap(addr: *mut std::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut std::ffi::c_void;
    fn munmap(addr: *mut std::ffi::c_void, len: usize) -> i32;
}
/// Maps the first `bytes` bytes of f for reading (PROT_READ, MAP_SHARED: the same values on Linux
/// and macOS)
#[cfg(unix)]
fn map_file(f: &std::fs::File, bytes: usize) -> Option<*const u8> {
    use std::os::fd::AsRawFd;
    let p = unsafe { mmap(std::ptr::null_mut(), bytes, 1, 1, f.as_raw_fd(), 0) };
    (p as isize != -1).then_some(p as *const u8)
}
#[cfg(not(unix))]
fn map_file(_: &std::fs::File, _: usize) -> Option<*const u8> {
    None
}
#[cfg(unix)]
fn unmap_file(p: *const u8, bytes: usize) {
    unsafe { munmap(p as *mut std::ffi::c_void, bytes) };
}
#[cfg(not(unix))]
fn unmap_file(_: *const u8, _: usize) {}
#[cfg(all(target_os = "linux", target_env = "gnu"))]
extern "C" {
    fn malloc_trim(pad: usize) -> i32;
}
/// Gives the memory the threads freed back to the system (glibc keeps it for each thread otherwise)
fn trim_heap() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    unsafe {
        malloc_trim(0);
    }
}
/// An array of plain values that only grows: a column of the state graph. It stays in memory until
/// the columns together hold more than `-memlimit`; a column that grows after that moves to a file
/// (unlinked as soon as it is opened), which is mapped into memory for reading, so the kernel keeps
/// in its page cache what fits and reads the rest back from the disk, as TLC keeps its liveness
/// graph on disk.
struct Col<T: Copy> {
    /// The elements after the first `written`, which are in the file
    mem: Vec<T>,
    file: Option<std::fs::File>,
    map: *const T,
    written: usize,
    /// The bytes of `mem` counted in COL_MEM
    counted: usize,
}
unsafe impl<T: Copy + Send> Send for Col<T> {}
unsafe impl<T: Copy + Sync> Sync for Col<T> {}
impl<T: Copy> Col<T> {
    fn new() -> Self {
        Col { mem: vec![], file: None, map: std::ptr::null(), written: 0, counted: 0 }
    }
    fn len(&self) -> usize {
        self.written + self.mem.len()
    }
    #[inline]
    fn get(&self, i: usize) -> T {
        if i < self.written {
            unsafe { *self.map.add(i) }
        } else {
            self.mem[i - self.written]
        }
    }
    /// All the elements, once they are either all in memory or all in the file (see `finish`)
    fn as_slice(&self) -> &[T] {
        if self.written == 0 {
            &self.mem
        } else {
            assert!(self.mem.is_empty(), "a column read before it is finished");
            unsafe { std::slice::from_raw_parts(self.map, self.written) }
        }
    }
    #[inline]
    fn push(&mut self, x: T) {
        self.mem.push(x);
        if self.mem.len() & 0xFFFF == 0 {
            self.grew();
        }
    }
    fn extend_from_slice(&mut self, xs: &[T]) {
        self.mem.extend_from_slice(xs);
        self.grew();
    }
    fn bytes(n: usize) -> usize {
        n * std::mem::size_of::<T>()
    }
    fn grew(&mut self) {
        use std::sync::atomic::Ordering::Relaxed;
        if self.file.is_some() {
            if Self::bytes(self.mem.len()) >= COL_BUF {
                self.flush();
            }
            return;
        }
        let now = Self::bytes(self.mem.len());
        let total = COL_MEM.fetch_add(now - self.counted, Relaxed) + now - self.counted;
        self.counted = now;
        if total > COL_LIMIT.load(Relaxed) {
            self.spill();
        }
    }
    /// Moves the column to a file
    fn spill(&mut self) {
        use std::sync::atomic::Ordering::Relaxed;
        let dir = COL_DIR.lock().unwrap().clone().unwrap_or_else(std::env::temp_dir);
        let seq = SPILL_SEQ.fetch_add(1, Relaxed);
        let path = dir.join(format!("tla2rs-{}-{seq}.g", std::process::id()));
        let opened = std::fs::File::options().create_new(true).read(true).write(true).open(&path);
        match opened {
            Ok(f) if cfg!(unix) => {
                let _ = std::fs::remove_file(&path);
                COL_MEM.fetch_sub(self.counted, Relaxed);
                self.counted = 0;
                self.file = Some(f);
                self.flush();
            }
            r => {
                if r.is_ok() {
                    let _ = std::fs::remove_file(&path);
                }
                // Better to try in memory than to stop
                eprintln!("warning: cannot spill the state graph to {}", path.display());
                COL_LIMIT.store(usize::MAX, Relaxed);
            }
        }
    }
    /// Writes the elements in memory to the file and maps all of it
    fn flush(&mut self) {
        let Some(f) = self.file.as_mut() else { return };
        if self.mem.is_empty() {
            return;
        }
        let bytes = unsafe { std::slice::from_raw_parts(self.mem.as_ptr() as *const u8, Self::bytes(self.mem.len())) };
        use std::io::Write;
        // As with the queue, carrying on without part of the graph could report "no error"
        if let Err(e) = f.write_all(bytes) {
            eval_error(format!("cannot write the state graph to the disk: {e}"));
        }
        COL_SPILLED.fetch_add(bytes.len() as u64, std::sync::atomic::Ordering::Relaxed);
        if self.written > 0 {
            unmap_file(self.map as *const u8, Self::bytes(self.written));
        }
        self.written += self.mem.len();
        self.mem.clear();
        match map_file(f, Self::bytes(self.written)) {
            Some(p) => self.map = p as *const T,
            None => eval_error("cannot map the state graph from the disk".into()),
        }
    }
    /// Done growing: with a file, everything goes to it
    fn finish(&mut self) {
        self.flush();
        self.mem.shrink_to_fit();
    }
}
impl<T: Copy> Default for Col<T> {
    fn default() -> Self {
        Col::new()
    }
}
impl<T: Copy> Drop for Col<T> {
    fn drop(&mut self) {
        COL_MEM.fetch_sub(self.counted, std::sync::atomic::Ordering::Relaxed);
        if self.written > 0 {
            unmap_file(self.map as *const u8, Self::bytes(self.written));
        }
    }
}

struct Graph {
    states: Col<Packed>,
    /// (parent index, label). Initial states have (u32::MAX, u32::MAX).
    parent: Col<(u32, u32)>,
    /// Per state, bit i: state atom i of the temporal properties, among those of the tableau, holds
    /// (evaluated when the state is found; liveness only)
    sbits: Col<u64>,
}

impl Graph {
    fn state(&self, i: usize) -> State {
        unpack(&self.states.get(i))
    }

    fn trace_len(&self, mut id: u32) -> usize {
        let mut n = 0;
        while id != u32::MAX {
            n += 1;
            id = self.parent.get(id as usize).0;
        }
        n
    }

    /// `succ`: the last state is a successor of the one being expanded (see `print_states_tlc`)
    fn print_trace(&self, mut id: u32, extra: Option<(&State, u32)>, succ: bool) {
        let mut ids = vec![];
        while id != u32::MAX {
            ids.push(id);
            id = self.parent.get(id as usize).0;
        }
        if PRINT_ORDER {
            let trace: Vec<(State, u32)> =
                ids.iter().rev().map(|i| (self.state(*i as usize), self.parent.get(*i as usize).1)).collect();
            print_states_tlc(&trace, trace.len() - succ as usize, extra.map(|(s, l)| (*s, l)));
            return;
        }
        println!("Error: The behavior up to this point is:");
        let mut n = 0;
        let mut prev: Option<State> = None;
        let len = ids.len() + extra.is_some() as usize;
        for id in ids.iter().rev() {
            n += 1;
            let l = self.parent.get(*id as usize).1;
            let name = if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
            let s = self.state(*id as usize);
            print_step(&format!("State {n}: <{name}>"), &s, diff_prev(n - 1, len, prev.as_ref()));
            prev = Some(s);
        }
        if let Some((s, l)) = extra {
            print_step(&format!("State {}: <{}>", n + 1, LABELS[l as usize]), s, diff_prev(n, len, prev.as_ref()));
        }
    }
}

/// Numbers the distinct values of a kind (the classes of edges or of states, see `LiveGraph`)
struct Classes<K: Copy + Eq + std::hash::Hash> {
    list: Vec<K>,
    ix: std::collections::HashMap<K, u32>,
}
impl<K: Copy + Eq + std::hash::Hash> Default for Classes<K> {
    fn default() -> Self {
        Classes { list: vec![], ix: std::collections::HashMap::new() }
    }
}
impl<K: Copy + Eq + std::hash::Hash> Classes<K> {
    #[inline]
    fn id(&mut self, k: K) -> u32 {
        if let Some(&i) = self.ix.get(&k) {
            return i;
        }
        let i = self.list.len() as u32;
        self.list.push(k);
        self.ix.insert(k, i);
        i
    }
}
/// What a step adds to the liveness search: (label, action atoms that hold on it, fairness
/// conditions whose <<A>>_v it is)
type EClass = (u32, u64, FMask);
/// What a state adds: (state atoms that hold in it, fairness conditions whose <<A>>_v is enabled
/// there, action atoms that hold on its stuttering step)
type SClass = (u64, FMask, u64);
/// The edges of the state graph as the search finds them. Each state and each edge has a class,
/// a number in a table of the distinct combinations, which are few.
#[derive(Default)]
struct LiveGraph {
    /// Per expanded state (states are expanded in the order of their numbers): the number of its
    /// first edge, and one more at the end with the number of edges
    off: Col<u64>,
    cls: ClassCol,
    /// Per edge: the target's fingerprint and the class
    tfp: Col<Fp>,
    ecls: ClassCol,
    /// (state, number of its edges before it) of each self-loop a successor makes, kept apart for
    /// TLC's order of successors (see `tlc_lasso`)
    selfs: Col<(u32, u32)>,
    ec: Classes<EClass>,
    sc: Classes<SClass>,
}
/// A column of class numbers, a byte each while they fit
enum ClassCol {
    Byte(Col<u8>),
    Word(Col<u32>),
}
impl Default for ClassCol {
    fn default() -> Self {
        ClassCol::Byte(Col::new())
    }
}
impl ClassCol {
    fn len(&self) -> usize {
        match self {
            ClassCol::Byte(c) => c.len(),
            ClassCol::Word(c) => c.len(),
        }
    }
    #[inline]
    fn get(&self, i: usize) -> u32 {
        match self {
            ClassCol::Byte(c) => c.get(i) as u32,
            ClassCol::Word(c) => c.get(i),
        }
    }
    fn widen(&mut self) {
        if let ClassCol::Byte(c) = self {
            let mut w = Col::new();
            for i in 0..c.len() {
                w.push(c.get(i) as u32);
            }
            *self = ClassCol::Word(w);
        }
    }
    fn push(&mut self, x: u32) {
        if x > u8::MAX as u32 {
            self.widen();
        }
        match self {
            ClassCol::Byte(c) => c.push(x as u8),
            ClassCol::Word(c) => c.push(x),
        }
    }
    fn extend(&mut self, xs: &[u32]) {
        if xs.iter().any(|&x| x > u8::MAX as u32) {
            self.widen();
        }
        match self {
            ClassCol::Byte(c) => c.extend_from_slice(&xs.iter().map(|&x| x as u8).collect::<Vec<u8>>()),
            ClassCol::Word(c) => c.extend_from_slice(xs),
        }
    }
    fn finish(&mut self) {
        match self {
            ClassCol::Byte(c) => c.finish(),
            ClassCol::Word(c) => c.finish(),
        }
    }
}
impl LiveGraph {
    /// Adds what a piece of a level found, its classes numbered anew
    fn add(&mut self, c: &mut LiveChunk) {
        let em: Vec<u32> = c.ec.list.iter().map(|&k| self.ec.id(k)).collect();
        let sm: Vec<u32> = c.sc.list.iter().map(|&k| self.sc.id(k)).collect();
        let mut e = self.tfp.len() as u64;
        for &(k, s) in &c.en {
            self.off.push(e);
            self.cls.push(sm[s as usize]);
            e += k as u64;
        }
        self.tfp.extend_from_slice(&c.tfp);
        for x in c.ecls.iter_mut() {
            *x = em[*x as usize];
        }
        self.ecls.extend(&c.ecls);
        self.selfs.extend_from_slice(&c.selfs);
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

/// `check_invariants`, with an evaluation error returned along with the invariant that raised it.
fn eval_invariants(s: &State) -> Result<Option<&'static str>, (&'static str, EvalErr)> {
    match std::panic::catch_unwind(|| if TLCGET { Err(()) } else { Ok(check_invariants(s)) }) {
        Ok(Ok(v)) => Ok(v),
        Ok(Err(())) => {
            for (name, f) in INVARIANTS {
                match std::panic::catch_unwind(|| f(s)) {
                    Ok(true) => {}
                    Ok(false) => return Ok(Some(name)),
                    Err(p) => return Err((name, describe_panic(p))),
                }
            }
            Ok(None)
        }
        // Evaluation is deterministic, so evaluating them one at a time again finds the one that
        // failed.
        Err(p) => {
            for (name, f) in INVARIANTS {
                match std::panic::catch_unwind(|| f(s)) {
                    Ok(true) => {}
                    Ok(false) => return Ok(Some(name)),
                    Err(p) => return Err((name, describe_panic(p))),
                }
            }
            Err(("?", describe_panic(p)))
        }
    }
}

/// For a state that does not pack when packing checks the type invariant (TYPE_INV_SUBSUMED), so
/// that it violates that invariant: the invariants TLC checks before it, in the order listed
fn eval_invariants_before_type(s: &State) -> Result<Option<&'static str>, (&'static str, EvalErr)> {
    for (name, f) in &INVARIANTS[..TYPE_INV_AT.min(INVARIANTS.len())] {
        match std::panic::catch_unwind(|| f(s)) {
            Ok(true) => {}
            Ok(false) => return Ok(Some(name)),
            Err(p) => return Err((name, describe_panic(p))),
        }
    }
    Ok(None)
}
/// TLC checks the invariants on a successor that violates the CONSTRAINT too (every time it is
/// generated; it is counted as generated but never added or explored). Returns what stops the
/// search, if anything.
fn check_out_of_model(t: &State) -> Option<SMsg> {
    if TYPE_INV_SUBSUMED && pack(t).is_none() {
        return Some(pack_failed_msg(t));
    }
    match eval_invariants(t) {
        Ok(Some(inv)) => Some(SMsg::Inv(inv)),
        Err((inv, e)) => Some(SMsg::InvEval(inv, e)),
        // The type invariant is not evaluated at run time; packing checks the same thing.
        Ok(None) if TYPE_INV_SUBSUMED && pack(t).is_none() => Some(SMsg::OutOfType),
        Ok(None) => None,
    }
}

/// Checks the action properties ([][A]_v) on the step s -> t. TLC does this on every successor,
/// after it is added (if new) and its invariants are checked.
fn check_action_props(s: &State, t: &State) -> Option<SMsg> {
    for (name, f) in ACTION_PROPS {
        match std::panic::catch_unwind(|| f(s, t)) {
            Ok(true) => {}
            Ok(false) => return Some(SMsg::Action(name)),
            Err(p) => return Some(SMsg::ActionEval(name, describe_panic(p))),
        }
    }
    None
}

/// The error raised by `next`, raised again once the successors computed before it have been
/// processed (see `successors`). It is reported with the behavior up to the state being expanded.
struct NextFailed(Box<dyn std::any::Any + Send>);

fn raise_next(p: Box<dyn std::any::Any + Send>) -> ! {
    std::panic::resume_unwind(Box::new(NextFailed(p)))
}

/// What an error caught while expanding a state means: an error in `next` or a value outside the
/// declared type (reported with the behavior up to the state being expanded), or anything else
/// raised while processing a successor, such as evaluating the CONSTRAINT or the VIEW (for which
/// TLC shows no behavior). Returns the error and whether it is shown with a behavior.
fn classify(p: Box<dyn std::any::Any + Send>) -> (EvalErr, bool) {
    match p.downcast::<NextFailed>() {
        Ok(n) => (describe_panic(n.0), true),
        Err(p) => {
            let e = describe_panic(p);
            let traced = matches!(e, EvalErr::Type(_));
            (e, traced)
        }
    }
}

/// Prints the message for a detected error and returns the exit code. `in_model` is false for a
/// state outside the CONSTRAINT.
fn report_msg(msg: &SMsg, in_model: bool) -> i32 {
    match msg {
        SMsg::Inv(inv) => {
            println!("Error: Invariant {inv} is violated.");
            12
        }
        SMsg::InvEval(inv, e) => {
            println!("Error: Evaluating invariant {inv} failed.\n{}", e.msg());
            // TLC's code for a failed invariant, except on a state outside the CONSTRAINT, where it
            // is the code of the error itself
            if in_model { 76 } else { eval_code(e) }
        }
        SMsg::Deadlock => {
            println!("Error: Deadlock reached.");
            11
        }
        SMsg::Action(name) => {
            println!("Error: Action property {name} is violated.");
            13
        }
        SMsg::ActionEval(name, e) => {
            println!("Error: Evaluating action property {name} failed.\n{}", e.msg());
            eval_code(e)
        }
        SMsg::Eval(e) => {
            report_eval(e);
            eval_code(e)
        }
        SMsg::Untraced(e) => {
            report_eval_as(e, true);
            eval_code(e)
        }
        SMsg::Live(what, e) => {
            report_eval_as(e, true);
            eprintln!("  (while evaluating {what})");
            // TLC stops with an unexpected exception, and exits with 255 whatever the error
            255
        }
        SMsg::OutOfType => {
            report_eval(&EvalErr::Type("a variable".into()));
            eval_code(&EvalErr::Type(String::new()))
        }
    }
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
    /// A newly found state violates an invariant or fails to evaluate one (worker, index within
    /// the worker, SMsg::Inv or SMsg::InvEval).
    New(usize, usize, SMsg),
    /// A successor that stops the search without being added: one that leaves its type, violates
    /// [][A]_v, or is outside the CONSTRAINT and fails the invariants (parent, successor, label,
    /// what, whether it satisfies the CONSTRAINT).
    Succ(u32, State, u32, SMsg, bool),
    /// An evaluation error while expanding the parent state.
    Eval(u32, EvalErr),
    /// An error for which TLC shows no behavior (SMsg::Untraced or SMsg::Live).
    Live(SMsg),
    Deadlock(u32),
}

/// Liveness data collected during expansion (see `LiveGraph`), with classes numbered in the piece
#[derive(Default)]
struct LiveChunk {
    /// Per edge: the target's fingerprint, and the class. Self-loops are left out: the stuttering
    /// step every state has covers them.
    tfp: Vec<Fp>,
    ecls: Vec<u32>,
    /// Per expanded state: its number of edges and its class
    en: Vec<(u32, u32)>,
    ec: Classes<EClass>,
    sc: Classes<SClass>,
    /// Working storage: the successors of the state being expanded that became edges, and those
    /// that are new
    pend: Vec<usize>,
    newk: Vec<usize>,
    /// (state, number of its edges before it) of each self-loop a successor makes, kept apart for
    /// TLC's order of successors (see `tlc_lasso`)
    selfs: Vec<(u32, u32)>,
}

struct Chunk {
    states: Vec<Packed>,
    parent: Vec<(u32, u32)>,
    /// Per new state, its state atoms (see Graph::sbits)
    sbits: Vec<u64>,
    generated: u64,
    found: Option<Found>,
    live: LiveChunk,
    /// With -dumpgraph, the lines for the states and edges found
    dump: String,
    /// The states taken off the queue (see `SChunk::expanded`), and whether the new state that
    /// stops the search is among `states`: TLC does not queue it
    expanded: usize,
    unqueued: bool,
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
    careful: bool,
) -> Option<Found> {
    let s = g.state(head);
    let cap = Capturing::start();
    let failed = successors(&s, buf, careful);
    let mut held = cap.finish();
    let g0 = c.generated;
    let r = expand_one_succ(g, head, seen, me, check_deadlock, c, buf, &s, failed, &mut held);
    // What was printed up to the successor that stops the search, or all of it
    held.flush(if r.is_some() { (c.generated - g0) as u32 } else { u32::MAX });
    r
}

/// The rest of `expand_one`, once the successors of s are computed
#[allow(clippy::too_many_arguments)]
fn expand_one_succ(
    g: &Graph,
    head: usize,
    seen: &Shards,
    me: usize,
    check_deadlock: bool,
    c: &mut Chunk,
    buf: &mut [(State, u32)],
    s: &State,
    failed: Option<Box<dyn std::any::Any + Send>>,
    held: &mut Held,
) -> Option<Found> {
    let s = *s;
    if failed.is_none() && buf.is_empty() && check_deadlock {
        held.flush(u32::MAX);
        return Some(Found::Deadlock(head as u32));
    }
    let w = g.states.get(head);
    let sfp = if LIVENESS { state_fp(&s, &w) } else { 0 };
    let sfp_dump = if dumping() { state_fp(&s, &w) } else { 0 };
    let first_edge = c.live.tfp.len();
    c.live.pend.clear();
    c.live.newk.clear();
    for (k, &(t, l)) in buf.iter().enumerate() {
        c.generated += 1;
        // States outside the CONSTRAINT are not added (as in TLC, they are not counted as
        // distinct), but their invariants and the action properties are checked.
        if !in_model(&s, &t) {
            if let Some(msg) = check_out_of_model(&t).or_else(|| check_action_props(&s, &t)) {
                return Some(Found::Succ(head as u32, t, l, msg, false));
            }
            continue;
        }
        let act = check_action_props(&s, &t);
        let Some(w) = pack(&t) else {
            if dumping() {
                dump_unpacked(&mut c.dump, sfp_dump, &t, l);
            }
            return Some(Found::Succ(head as u32, t, l, pack_failed(0, t, l).msg, true));
        };
        let tfp = state_fp(&t, &w);
        if dumping() {
            dump_edge(&mut c.dump, sfp_dump, &tfp, l);
        }
        if LIVENESS && tfp == sfp {
            c.live.selfs.push((head as u32, (c.live.tfp.len() - first_edge) as u32));
        }
        if LIVENESS && tfp != sfp {
            // Its atoms are evaluated with fairness, after the successors (as TLC does)
            c.live.tfp.push(tfp);
            c.live.pend.push(k);
        }
        let new = seen.insert(tfp);
        if new {
            if dumping() {
                dump_node(&mut c.dump, &tfp, &t, false);
            }
            c.states.push(w);
            c.parent.push((head as u32, l));
            c.unqueued = true;
            held.flush(k as u32 + 1);
            match eval_invariants(&t) {
                Ok(None) => {}
                Ok(Some(inv)) if flag(&CONTINUE) => {
                    let _g = REPORTING.lock().unwrap_or_else(|e| e.into_inner());
                    report_msg(&SMsg::Inv(inv), true);
                    g.print_trace(head as u32, Some((&t, l)), false);
                }
                Ok(Some(inv)) => return Some(Found::New(me, c.states.len() - 1, SMsg::Inv(inv))),
                Err((inv, e)) => return Some(Found::New(me, c.states.len() - 1, SMsg::InvEval(inv, e))),
            }
            c.unqueued = false;
            if LIVENESS {
                c.live.newk.push(k);
            }
        }
        if let Some(m) = act {
            if flag(&CONTINUE) && matches!(m, SMsg::Action(_)) {
                let _g = REPORTING.lock().unwrap_or_else(|e| e.into_inner());
                report_msg(&m, true);
                g.print_trace(head as u32, Some((&t, l)), false);
                continue;
            }
            c.unqueued = new;
            return Some(Found::Succ(head as u32, t, l, m, true));
        }
    }
    if let Some(p) = failed {
        held.flush(u32::MAX);
        raise_next(p);
    }
    // After the successors, in TLC's order: which fair actions are enabled in this state and its
    // state atoms that are not in the tableau, then the fairness steps and action atoms of each
    // step (including stuttering), then the tableau's state atoms of the new successors
    if LIVENESS {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut en: FMask = 0;
            for (i, (_, enabled, _)) in FAIRS.iter().enumerate() {
                if enabled(&s) {
                    en |= 1 << i;
                }
            }
            en
        }));
        let en = match r {
            Ok(en) => en,
            Err(p) => return Some(Found::Live(SMsg::Live("fairness".into(), describe_panic(p)))),
        };
        let cbits = match state_bits(&s, !SATOMS_TABLEAU) {
            Ok(b) => b,
            Err(m) => return Some(Found::Live(m)),
        };
        for j in 0..c.live.pend.len() {
            let (t, l) = &buf[c.live.pend[j]];
            match step_bits(&s, t) {
                Ok((a, f)) => {
                    let id = c.live.ec.id((*l, a, f));
                    c.live.ecls.push(id);
                }
                Err(m) => return Some(Found::Live(m)),
            }
        }
        let stut = match step_bits(&s, &s) {
            Ok((a, _)) => a,
            Err(m) => return Some(Found::Live(m)),
        };
        let id = c.live.sc.id((g.sbits.get(head) | cbits, en, stut));
        c.live.en.push(((c.live.tfp.len() - first_edge) as u32, id));
        for j in 0..c.live.newk.len() {
            match state_bits(&buf[c.live.newk[j]].0, SATOMS_TABLEAU) {
                Ok(b) => c.sbits.push(b),
                Err(m) => return Some(Found::Live(m)),
            }
        }
    }
    None
}

/// The state atoms of the temporal properties among `mask` that hold in s
fn state_bits(s: &State, mask: u64) -> Result<u64, SMsg> {
    let mut b = 0u64;
    for (i, f) in SATOMS.iter().enumerate() {
        if mask & (1 << i) == 0 {
            continue;
        }
        match std::panic::catch_unwind(|| f(s)) {
            Ok(true) => b |= 1 << i,
            Ok(false) => {}
            Err(p) => return Err(SMsg::Live("a temporal property".into(), describe_panic(p))),
        }
    }
    Ok(b)
}

/// The action atoms that hold on the step s -> t, and the fairness conditions whose <<A>>_v it is
/// (evaluated first, as TLC does)
fn step_bits(s: &State, t: &State) -> Result<(u64, FMask), SMsg> {
    let r = std::panic::catch_unwind(|| {
        let mut st: FMask = 0;
        for (i, (_, _, step)) in FAIRS.iter().enumerate() {
            if step(s, t) {
                st |= 1 << i;
            }
        }
        let mut a = 0u64;
        for (i, f) in AATOMS.iter().enumerate() {
            if f(s, t) {
                a |= 1 << i;
            }
        }
        (a, st)
    });
    r.map_err(|p| SMsg::Live("a temporal property".into(), describe_panic(p)))
}

fn expand(g: &Graph, lo: usize, hi: usize, seen: &Shards, stop: &std::sync::atomic::AtomicBool, me: usize, check_deadlock: bool) -> Chunk {
    use std::sync::atomic::Ordering::Relaxed;
    let mut c = Chunk {
        states: vec![],
        parent: vec![],
        sbits: vec![],
        generated: 0,
        found: None,
        live: LiveChunk::default(),
        dump: String::new(),
        expanded: 0,
        unqueued: false,
    };
    let mut buf: Vec<(State, u32)> = Vec::with_capacity(64);
    for head in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        c.expanded += 1;
        let mark = c.dump.len();
        let r = expand_caught(&mut c, |c| c.generated, |c, careful| {
            c.dump.truncate(mark);
            expand_one(g, head, seen, me, check_deadlock, c, &mut buf, careful)
        });
        if c.dump.len() > 1 << 20 {
            dump_write(&mut c.dump);
        }
        let found = match r {
            Ok(f) => f,
            Err(p) => Some(match classify(p) {
                (e, true) => Found::Eval(head as u32, e),
                (e, false) => Found::Live(SMsg::Untraced(e)),
            }),
        };
        if found.is_some() {
            c.found = found;
            stop.store(true, Relaxed);
            break;
        }
    }
    c
}

// ---------------------------------------------------------------- state graph dump (-dumpgraph)

/// With `-dumpgraph FILE`, the checker writes the states and transitions it explores to FILE in
/// the form of TLC's `-dump dot`: a node per state with the state's text as its label (initial
/// states filled), and an edge for each successor that satisfies the CONSTRAINT and
/// ACTION_CONSTRAINT, written when the successor is generated. When the search stops early, the
/// graph ends where TLC's ends: at the successor that stopped it. Node ids are fingerprints, so
/// only the labels mean anything outside the file. `tla2rs --graph FILE` reduces such a file
/// (TLC's or this one) to hashes that do not depend on ids or order.
static DUMPING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static DUMP: std::sync::Mutex<Option<std::io::BufWriter<std::fs::File>>> = std::sync::Mutex::new(None);
/// Ids for successors that tla2rs cannot pack (so has no fingerprint for)
static DUMP_SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// Whether the initial states have been written (initial_states also runs to rebuild a trace)
static DUMPED_INITS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

#[inline]
fn dumping() -> bool {
    DUMPING.load(std::sync::atomic::Ordering::Relaxed)
}

/// With -dumpstates FILE (TLC's `-dump FILE`), the file lists the distinct states in the order
/// found, as `State N:` and the state, instead of a graph
static DUMP_STATES: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static DUMP_NO: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
/// With -dumplabels (TLC's `-dump dot,actionlabels`), each edge is labelled with its action. With
/// -dumpattrs (TLC's `-dump dot`, with or without options), each edge has the attributes of a
/// label, with an empty one
static DUMP_LABELS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static DUMP_ATTRS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// With -dumpcolors (TLC's `-dump dot,colorize`), each edge has the color of its action: the
/// actions are numbered from 2 by name, in the order an edge of each is first written (measured
/// on TLC 2.19, `tests/tlc/OptDumpColor`), and the graph ends with a legend of them
static DUMP_COLORS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// The names of the actions with a color, in the order of their colors
static COLORED: std::sync::Mutex<Vec<&'static str>> = std::sync::Mutex::new(vec![]);
/// The color of each entry of LABELS, once known (0 before)
static LABEL_COLORS: std::sync::OnceLock<Vec<std::sync::atomic::AtomicU32>> = std::sync::OnceLock::new();

/// The name of an action labelled `l` (in LABELS) as TLC names it in the graph
fn action_name(l: u32) -> &'static str {
    LABELS.get(l as usize).map_or("", |n| n.split(" line ").next().unwrap_or(""))
}

/// The color of the action labelled `l` (in LABELS), numbering its name if it has none yet
fn action_color(l: u32) -> u32 {
    use std::sync::atomic::Ordering::Relaxed;
    let cs = LABEL_COLORS.get_or_init(|| LABELS.iter().map(|_| std::sync::atomic::AtomicU32::new(0)).collect());
    let Some(c) = cs.get(l as usize) else { return 0 };
    let k = c.load(Relaxed);
    if k != 0 {
        return k;
    }
    let name = action_name(l);
    let mut v = COLORED.lock().unwrap_or_else(|e| e.into_inner());
    let i = v.iter().position(|n| *n == name).unwrap_or_else(|| {
        v.push(name);
        v.len() - 1
    });
    let k = i as u32 + 2;
    c.store(k, Relaxed);
    k
}

/// The order in which a Java `HashMap` with these keys (`String`s, put in this order, into a map
/// made with its default capacity) goes through them, which is the order of TLC's legend: by
/// bucket of the key's hash, each bucket in the order put
fn java_hash_order(keys: &[&str]) -> Vec<usize> {
    let hash = |k: &str| {
        let h = k.encode_utf16().fold(0i32, |h, c| h.wrapping_mul(31).wrapping_add(c as i32)) as u32;
        (h ^ (h >> 16)) as usize
    };
    let mut cap = 16;
    let mut buckets: Vec<Vec<usize>> = vec![vec![]; cap];
    let resize = |buckets: &mut Vec<Vec<usize>>, cap: &mut usize| {
        *cap *= 2;
        let mut nb: Vec<Vec<usize>> = vec![vec![]; *cap];
        for i in buckets.iter().flatten() {
            nb[hash(keys[*i]) & (*cap - 1)].push(*i);
        }
        *buckets = nb;
    };
    for (i, k) in keys.iter().enumerate() {
        let b = &mut buckets[hash(k) & (cap - 1)];
        b.push(i);
        // A bucket of more than 8 entries makes a small table grow (a larger one would make it a tree)
        if b.len() > 8 && cap < 64 {
            resize(&mut buckets, &mut cap);
        }
        if i + 1 > cap * 3 / 4 {
            resize(&mut buckets, &mut cap);
        }
    }
    buckets.into_iter().flatten().collect()
}

fn dump_open(path: &std::path::Path, states: bool) {
    use std::io::Write;
    let mut w = match std::fs::File::create(path) {
        Ok(f) => std::io::BufWriter::new(f),
        Err(e) => {
            eprintln!("cannot write {}: {e}", path.display());
            std::process::exit(2);
        }
    };
    if states {
        DUMP_STATES.store(true, std::sync::atomic::Ordering::Relaxed);
    } else {
        let _ = w.write_all(b"strict digraph DiskGraph {\n");
        if flag(&DUMP_COLORS) {
            let _ = w.write_all(b"edge [colorscheme=\"paired12\"]\n");
        }
    }
    *DUMP.lock().unwrap() = Some(w);
    DUMPING.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// Where `dump_edge` leaves the color of an edge to `dump_write`, around the action's label
const COLOR_MARK: char = '\u{1}';

/// Appends a worker's buffered lines to the file
fn dump_write(buf: &mut String) {
    use std::io::Write;
    if buf.is_empty() {
        return;
    }
    if let Some(w) = DUMP.lock().unwrap().as_mut() {
        if flag(&DUMP_COLORS) && buf.contains(COLOR_MARK) {
            let mut out = String::with_capacity(buf.len());
            for (i, part) in buf.split(COLOR_MARK).enumerate() {
                match i % 2 {
                    0 => out += part,
                    _ => match action_color(part.parse().unwrap_or(u32::MAX)) {
                        0 => out += "black",
                        c => out += &c.to_string(),
                    },
                }
            }
            *buf = out;
        }
        if let Err(e) = w.write_all(buf.as_bytes()) {
            eprintln!("cannot write the state graph: {e}");
            std::process::exit(2);
        }
    }
    buf.clear();
}

fn dump_finish() {
    use std::io::Write;
    if DUMPING.swap(false, std::sync::atomic::Ordering::Relaxed) {
        if let Some(mut w) = DUMP.lock().unwrap().take() {
            let mut end = String::new();
            if !flag(&DUMP_STATES) {
                if flag(&DUMP_COLORS) {
                    end += "subgraph cluster_legend {graph[style=bold];label = \"Next State Actions\" style=\"solid\"\n";
                    end += "node [ labeljust=\"l\",colorscheme=\"paired12\",style=filled,shape=record ]\n";
                    let names = COLORED.lock().unwrap_or_else(|e| e.into_inner()).clone();
                    for i in java_hash_order(&names) {
                        end += &format!("{n} [label=\"{n}\",fillcolor={}]\n", i + 2, n = names[i]);
                    }
                    end += "}\n";
                }
                end += "}\n";
            }
            if w.write_all(end.as_bytes()).and_then(|_| w.flush()).is_err() {
                eprintln!("cannot write the state graph");
            }
        }
    }
}

/// Exits the checker, completing the state graph first
fn exit(code: i32) -> ! {
    dump_finish();
    str_order_finish();
    std::process::exit(code)
}

/// A state's text as a dot label, escaped as TLC escapes it
fn dot_label(s: &State) -> String {
    (if flag(&VIEW_TRACE) && HAS_VIEW { show_view(s) } else { show(s) }).replace('\\', "\\\\").replace('"', "\\\"").trim_matches(|c| c <= ' ').replace('\n', "\\n")
}

fn dump_node(buf: &mut String, id: &dyn std::fmt::Display, s: &State, init: bool) {
    use std::fmt::Write;
    if flag(&DUMP_STATES) {
        let n = DUMP_NO.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
        let _ = writeln!(buf, "State {n}:\n{}\n", show(s));
        return;
    }
    let _ = if init {
        writeln!(buf, "{id} [label=\"{}\",style = filled]", dot_label(s))
    } else {
        writeln!(buf, "{id} [label=\"{}\"];", dot_label(s))
    };
}

/// An edge, by the action labelled `l` (u32::MAX: unknown)
fn dump_edge(buf: &mut String, from: Fp, to: &dyn std::fmt::Display, l: u32) {
    use std::fmt::Write;
    if flag(&DUMP_STATES) {
        return;
    }
    if flag(&DUMP_ATTRS) {
        let name = if flag(&DUMP_LABELS) { action_name(l) } else { "" };
        // The color is numbered when the edge is written to the file (`dump_write`): an edge
        // buffered for a successor TLC does not reach is not
        let color = if flag(&DUMP_COLORS) { format!("{COLOR_MARK}{l}{COLOR_MARK}") } else { "black".to_string() };
        let _ = writeln!(buf, "{from} -> {to} [label=\"{name}\",color=\"{color}\",fontcolor=\"{color}\"];");
    } else {
        let _ = writeln!(buf, "{from} -> {to};");
    }
}

/// An edge to a successor that tla2rs cannot pack. TLC can represent it, and it is new to TLC (an
/// earlier one would have stopped tla2rs), so it gets a node of its own.
fn dump_unpacked(buf: &mut String, from: Fp, t: &State, l: u32) {
    let id = format!("u{}", DUMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
    dump_edge(buf, from, &id, l);
    dump_node(buf, &id, t, false);
}

/// The successor that left its type while `next` built it, which TLC adds as a new state. Its
/// contents are unknown here, so its node has a placeholder for a label; the cross-check
/// compares only the numbers of states and edges then.
fn dump_unrepresentable(from: Fp) {
    if dumping() {
        let mut buf = String::new();
        let id = format!("u{}", DUMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
        dump_edge(&mut buf, from, &id, u32::MAX);
        use std::fmt::Write;
        let _ = writeln!(buf, "{id} [label=\"(a successor that tla2rs cannot represent)\"];");
        dump_write(&mut buf);
    }
}

/// The id of a successor in the graph: its fingerprint, or None if it cannot be packed
fn dump_fp(t: &State) -> Option<Fp> {
    if !HAS_VIEW && PERMS.is_empty() {
        pack(t).map(|w| fingerprint(&w))
    } else {
        canon_fp(t)
    }
}

/// Records the edge s -> t for a successor in the model
fn dump_succ(buf: &mut String, sfp: Fp, t: &State, l: u32) {
    match dump_fp(t) {
        Some(fp) => dump_edge(buf, sfp, &fp, l),
        None => dump_unpacked(buf, sfp, t, l),
    }
}

/// After an error in evaluating an invariant on a new state, TLC evaluates the state it was
/// expanding again to report where the error is (`ModelChecker`, with `CallStackTool`), and that
/// pass writes to the graph too: it generates all the successors of the state once more, writes
/// an edge for each in the model, adds the ones it has not seen (the failing one was added the
/// first time, so it is passed over now), checks the invariants of new successors and of those
/// outside the model, and the action properties of all, and stops at the first that fails.
/// `visited` tells whether a fingerprint was visited by the search.
fn dump_replay(s: &State, sfp: Fp, visited: &dyn Fn(Fp) -> bool) {
    let mut buf = vec![];
    let _ = tg_quiet(|| successors(s, &mut buf, true));
    let mut out = String::new();
    let mut added = std::collections::HashSet::new();
    for (t, l) in buf {
        let Ok(inm) = std::panic::catch_unwind(|| in_model(s, &t)) else { break };
        let mut unseen = true;
        if inm {
            match std::panic::catch_unwind(|| dump_fp(&t)) {
                Ok(Some(fp)) => {
                    dump_edge(&mut out, sfp, &fp, l);
                    unseen = !visited(fp) && added.insert(fp);
                    if unseen {
                        dump_node(&mut out, &fp, &t, false);
                    }
                }
                Ok(None) => dump_unpacked(&mut out, sfp, &t, l),
                Err(_) => break,
            }
        }
        if unseen && check_out_of_model(&t).is_some() {
            break;
        }
        if check_action_props(s, &t).is_some() {
            break;
        }
    }
    dump_write(&mut out);
}

/// Where the checker spills when `-tmpdir` is not given: the system's temp dir, unless it is a tmpfs
/// (as `/tmp` is on many Linux systems), whose files take memory as much as the data they hold; then
/// the directory of the checker's executable
fn default_tmpdir() -> std::path::PathBuf {
    let t = std::env::temp_dir();
    if on_tmpfs(&t) {
        if let Some(d) = std::env::current_exe().ok().and_then(|e| e.parent().map(|p| p.to_path_buf())) {
            return d;
        }
    }
    t
}
/// Whether p is on a tmpfs: the type of the mount with the longest mount point above it (Linux)
fn on_tmpfs(p: &std::path::Path) -> bool {
    let Ok(mounts) = std::fs::read_to_string("/proc/self/mounts") else { return false };
    let p = std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let mount = mounts
        .lines()
        .filter_map(|l| {
            let mut f = l.split(' ');
            let (_, at, kind) = (f.next()?, f.next()?, f.next()?);
            Some((at.replace("\\040", " "), kind))
        })
        .filter(|(at, _)| p.starts_with(at))
        .max_by_key(|(at, _)| at.len());
    mount.is_some_and(|(_, kind)| kind == "tmpfs")
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().collect();
    for (f, a) in [(&CONTINUE, "-continue"), (&DIFFTRACE, "-difftrace"), (&VIEW_TRACE, "-view"), (&NOWARN, "-nowarning")] {
        f.store(args.iter().any(|x| x == a), std::sync::atomic::Ordering::Relaxed);
    }
    if let Some(p) = args.iter().position(|a| a == "-userfile").and_then(|i| args.get(i + 1)) {
        match std::fs::File::create(p) {
            Ok(f) => *USER_FILE.lock().unwrap() = Some(std::io::LineWriter::new(f)),
            Err(e) => {
                eprintln!("cannot write {p}: {e}");
                std::process::exit(2);
            }
        }
    }
    DUMP_LABELS.store(args.iter().any(|x| x == "-dumplabels"), std::sync::atomic::Ordering::Relaxed);
    DUMP_COLORS.store(args.iter().any(|x| x == "-dumpcolors"), std::sync::atomic::Ordering::Relaxed);
    OTHER_FP.store(args.iter().any(|x| x == "-tlcfp"), std::sync::atomic::Ordering::Relaxed);
    DUMP_ATTRS.store(args.iter().any(|x| x == "-dumplabels" || x == "-dumpattrs" || x == "-dumpcolors"), std::sync::atomic::Ordering::Relaxed);
    if let Some(p) = args.iter().position(|a| a == "-dumpgraph").and_then(|i| args.get(i + 1)) {
        dump_open(std::path::Path::new(p), false);
    } else if let Some(p) = args.iter().position(|a| a == "-dumpstates").and_then(|i| args.get(i + 1)) {
        dump_open(std::path::Path::new(p), true);
    }
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
            .unwrap_or_else(default_tmpdir),
        workers: args
            .iter()
            .position(|a| a == "-workers")
            .and_then(|i| args.get(i + 1))
            .and_then(|w| w.parse().ok())
            .unwrap_or_else(|| if TLCGET { 1 } else { std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1) })
            .max(1),
    };
    // Only when checking temporal properties is the whole state graph kept in memory (the SCC
    // search needs it). Otherwise only fingerprints and each state's predecessor fingerprint are
    // kept, and counterexamples are rebuilt by replaying from an initial state.
    // Evaluation errors are caught and reported where they occur. Anything that reaches this point
    // is unexpected, so print a message instead of exiting silently (the default panic output is
    // suppressed above).
    // What TLC prints when it starts: Print and PrintT in the constant definitions, its warnings,
    // Print and PrintT in the ASSUMEs
    for l in if flag(&NOWARN) { STARTUP_PRINTS_NOWARN } else { STARTUP_PRINTS } {
        for l in l.lines() {
            match l.strip_prefix(USER_MARK) {
                Some(u) => user_line(u),
                None => println!("{l}"),
            }
        }
    }
    if TLCGET {
        // TLC's counts and registers are those of its workers' shared queue and threads, and its
        // liveness checking evaluates the spec again in an order of its own
        let refuse = if opt.workers > 1 && args.iter().any(|a| a == "-workers") {
            Some("with several workers: TLC's values then depend on how its workers share the search (check with -workers 1)")
        } else if LIVENESS {
            Some("with temporal properties: TLC's liveness checking evaluates the spec again in an order of its own")
        } else {
            None
        };
        if let Some(why) = refuse {
            eprintln!("tla2rs: TLCGet and TLCSet are not supported {why}");
            std::process::exit(1);
        }
    }
    str_order_start(opt.workers);
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // A spec without [][Next]_v: TLC computes and checks the initial states, then stops; when
        // there are none, it finishes as a search of no states does (`tests/tlc/NoActions-NoInit`).
        // What Init prints is dropped here: the search computes the initial states again
        let no_inits = NO_NEXT && {
            let cap = Capturing::start();
            let mut raw = Vec::new();
            let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut raw))).is_ok();
            drop(cap.finish());
            ok && raw.is_empty()
        };
        if NO_NEXT && !no_inits {
            let (inits, _) = initial_states();
            println!("Finished computing initial states: {} distinct states generated.", inits.len());
            println!("Error: No next state actions defined to generate successor states from.");
            exit(75);
        }
        if LIVENESS {
            run_liveness(&opt);
        } else if opt.batched && !PRINT_ORDER && !str_on() && !flag(&CONTINUE) && !flag(&DUMP_STATES) {
            run_safety_batched(&opt);
        } else {
            run_safety(&opt);
        }
    }));
    if let Err(p) = run {
        let e = describe_panic(p);
        report_eval(&e);
        exit(eval_code(&e));
    }
    dump_finish();
    str_order_finish();
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

/// Computes the initial states and checks each one the way TLC does while generating them: every
/// state counts as generated, one that satisfies the CONSTRAINT is kept if it is new, and the
/// invariants are checked on the new ones and on those outside the CONSTRAINT. Returns the kept
/// states with their fingerprints, and the number of states generated.
fn initial_states() -> (Vec<(State, Packed, Fp)>, u64) {
    // TLC shows no behavior for an evaluation error in the initial states, only the counts so far.
    // An error that is not one of its own evaluation errors, raised while checking an initial
    // state (CONSTRAINT, invariant, property), comes with that state.
    fn stop(e: EvalErr, while_: &str, state: Option<&State>, generated: u64, distinct: usize) -> ! {
        report_eval_as(&e, false);
        if let Some(s) = state.filter(|_| !tlc_eval_exception(&e) && !matches!(e, EvalErr::Type(_))) {
            println!("While working on the initial state:\n{}\n", show(s));
        }
        fp_note(&e);
        eprintln!("  (while {while_})");
        println!("{generated} states generated, {distinct} distinct states found, {distinct} states left on queue.");
        exit(init_eval_code(&e));
    }
    let mut inits = Vec::new();
    // The states computed before an error are still checked first, as TLC checks each one as soon
    // as it is generated.
    let mut failed = None;
    let mut held = Held::default();
    if !TLCGET {
        let cap = Capturing::start();
        failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut inits))).err();
        held = cap.finish();
    }
    let mut out = vec![];
    let mut seen = std::collections::HashSet::new();
    let mut generated = 0u64;
    // The first call writes the initial states to the graph; later ones rebuild traces
    let dump = dumping() && !DUMPED_INITS.swap(true, std::sync::atomic::Ordering::Relaxed);
    let mut buf = String::new();
    let mut handle = |s: State| {
        generated += 1;
        held.flush(generated as u32);
        let step = std::panic::catch_unwind(|| {
            let in_model = constraint(&s);
            let w = pack(&s);
            let fp = w.filter(|_| in_model).map(|w| state_fp(&s, &w));
            (in_model, w, fp)
        });
        let (in_model, w, fp) = match step {
            Ok(v) => v,
            Err(p) => stop(describe_panic(p), "checking an initial state", Some(&s), generated, out.len()),
        };
        if let (Some(w), Some(fp)) = (w, fp) {
            if !seen.insert(fp) {
                return;
            }
            out.push((s, w, fp));
            tg_added();
            tg_queued(1);
            if dump {
                dump_node(&mut buf, &fp, &s, true);
                dump_write(&mut buf);
            }
        } else if dump && in_model && w.is_none() {
            let id = format!("u{}", DUMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
            dump_node(&mut buf, &id, &s, true);
            dump_write(&mut buf);
        }
        // An initial state that does not pack violates the type invariant, which TLC checks where
        // the cfg lists it
        let out_of_type = w.is_none() && TYPE_INV_SUBSUMED && !flag(&CONTINUE);
        match if out_of_type { eval_invariants_before_type(&s) } else { eval_invariants(&s) } {
            Ok(None) if out_of_type => {
                println!("Error: Invariant {TYPE_INVARIANT} is violated by the initial state:\n{}", init_text(&s));
                exit(12);
            }
            Ok(None) => {}
            Ok(Some(inv)) => {
                // With -continue, reported once (initial_states also runs to rebuild a behavior)
                if flag(&CONTINUE) {
                    if !INITS_REPORTED.load(std::sync::atomic::Ordering::Relaxed) {
                        let _g = REPORTING.lock().unwrap_or_else(|e| e.into_inner());
                        println!("Error: Invariant {inv} is violated by the initial state:\n{}\n", init_text(&s));
                        // TLC reports every invariant an initial state violates, a successor only the
                        // first (`tests/tlc/OptContinueInit`)
                        let at = INVARIANTS.iter().position(|(n, _)| *n == inv).map_or(INVARIANTS.len(), |k| k + 1);
                        for (name, f) in &INVARIANTS[at..] {
                            match std::panic::catch_unwind(|| f(&s)) {
                                Ok(true) => {}
                                Ok(false) => println!("Error: Invariant {name} is violated by the initial state:\n{}\n", init_text(&s)),
                                Err(p) => stop(describe_panic(p), &format!("evaluating invariant {name} on an initial state"), Some(&s), generated, out.len()),
                            }
                        }
                    }
                } else {
                    println!("Error: Invariant {inv} is violated by the initial state:\n{}", init_text(&s));
                    exit(12);
                }
            }
            Err((inv, e)) => {
                stop(e, &format!("evaluating invariant {inv} on an initial state"), Some(&s), generated, out.len())
            }
        }
        // A PROPERTY that is a state predicate holds if it holds in every initial state
        for (name, f) in INIT_PROPS {
            match std::panic::catch_unwind(|| f(&s)) {
                Ok(true) => {}
                Ok(false) => {
                    println!("Error: Property {name} is violated by the initial state:\n{}", init_text(&s));
                    exit(13);
                }
                Err(p) => stop(describe_panic(p), &format!("evaluating property {name} on an initial state"), Some(&s), generated, out.len()),
            }
        }
        if w.is_none() && (in_model || TYPE_INV_SUBSUMED) {
            let e = EvalErr::Type("an initial state".into());
            report_eval(&e);
            println!("{}", show(&s));
            exit(eval_code(&e));
        }
    };
    if TLCGET {
        // TLC handles each initial state as Init computes it (see TLCGET)
        tg_set_level(0);
        let mut hook = |s: &State, _: u32| handle(*s);
        failed = with_pushed(&mut hook, || std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut inits))).err());
    } else {
        for s in std::mem::take(&mut inits) {
            handle(s);
        }
    }
    held.flush(u32::MAX);
    INITS_REPORTED.store(true, std::sync::atomic::Ordering::Relaxed);
    if let Some(p) = failed {
        let e = describe_panic(p);
        // TLC shows the state with the variables it leaves unassigned null, and no counts
        if let (EvalErr::Incomplete(m), Some((s, _, null))) = (&e, incomplete()) {
            println!("Error: {m}\nWhile working on the initial state:\n{}\n", show_with(&s, null));
            exit(255);
        }
        stop(e, "computing the initial states", None, generated, out.len());
    }
    (out, generated)
}

/// Whether the violations of the initial states have been reported (-continue)
static INITS_REPORTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// With -continue, reports a violation of an invariant or an action property found while the
/// search goes on, with the behavior to it, as TLC does
fn report_continued(seen: &dyn Visited, f: &SFound) {
    let _g = REPORTING.lock().unwrap_or_else(|e| e.into_inner());
    report_msg(&f.msg, f.in_model);
    report_trace(seen, f);
}

/// A detected error. The trace is shown by following fingerprints back from `fp`; if `extra` is
/// set, one more state is appended after it.
struct SFound {
    fp: Fp,
    extra: Option<(State, u32)>,
    msg: SMsg,
    /// False for a successor outside the CONSTRAINT (`extra`), which TLC does not count as
    /// distinct.
    in_model: bool,
}

impl SFound {
    fn new(fp: Fp, extra: Option<(State, u32)>, msg: SMsg) -> Self {
        SFound { fp, extra, msg, in_model: true }
    }
}

enum SMsg {
    Inv(&'static str),
    /// Evaluating an invariant failed.
    InvEval(&'static str, EvalErr),
    Deadlock,
    Action(&'static str),
    /// Evaluating an action property failed.
    ActionEval(&'static str, EvalErr),
    Eval(EvalErr),
    /// An error while evaluating the CONSTRAINT, the ACTION_CONSTRAINT or the VIEW on a successor.
    /// TLC shows no behavior for it.
    Untraced(EvalErr),
    /// An error while evaluating fairness or a temporal property on the liveness path (what was
    /// being evaluated). TLC shows no behavior for it.
    Live(String, EvalErr),
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
        // Slots start at 0, so 0 cannot be recorded here (the fingerprint of an all-zero packed
        // state is 0): leave it to the shared table, which keeps 0 apart
        if fp == 0 {
            return true;
        }
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
    /// The states of the level taken off the queue, including the one whose expansion stopped
    /// the search
    expanded: usize,
}

/// A successor that does not fit the packed layout: an invariant it violates, else an out-of-type
/// error
fn pack_failed(sfp: Fp, t: State, l: u32) -> SFound {
    let msg = pack_failed_msg(&t);
    SFound::new(sfp, Some((t, l)), msg)
}
fn pack_failed_msg(t: &State) -> SMsg {
    let checked = if TYPE_INV_SUBSUMED { eval_invariants_before_type(t) } else { eval_invariants(t) };
    match checked {
        Ok(Some(inv)) => SMsg::Inv(inv),
        Err((inv, e)) => SMsg::InvEval(inv, e),
        Ok(None) => SMsg::OutOfType,
    }
}

/// A successor outside the CONSTRAINT or the ACTION_CONSTRAINT that stops the search: its
/// invariants (see `check_out_of_model`), then the action properties of the step.
fn out_of_model(s: &State, sfp: Fp, t: &State, l: u32) -> Option<SFound> {
    let msg = check_out_of_model(t).or_else(|| check_action_props(s, t))?;
    Some(SFound { fp: sfp, extra: Some((*t, l)), msg, in_model: false })
}

/// Whether the step s -> t stays in the model: t satisfies the CONSTRAINT and the step the
/// ACTION_CONSTRAINT.
#[inline]
fn in_model(s: &State, t: &State) -> bool {
    constraint(t) && action_constraint(s, t)
}

/// Computes the successors of s into buf. When `careful` is set and that fails, buf keeps the
/// successors computed before the error, and the error is returned to be raised once they have
/// been processed: TLC checks each successor as soon as it is generated, so those come first.
/// Catching around `next` costs several percent on the hot path, so `expand_caught` first runs
/// it as is and expands the state again carefully only when `next` failed.
fn successors(s: &State, buf: &mut Vec<(State, u32)>, careful: bool) -> Option<Box<dyn std::any::Any + Send>> {
    buf.clear();
    if careful {
        return std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| next(s, buf))).err();
    }
    next(s, buf);
    None
}

/// Runs the expansion of one state, `f(c, careful)`, catching an evaluation error. An error that
/// left the generated count unchanged came from `next` (every successor is counted before anything
/// else is done with it), so the state is expanded again carefully (see `successors`).
#[inline(always)]
fn expand_caught<C, R>(c: &mut C, generated: fn(&C) -> u64, mut f: impl FnMut(&mut C, bool) -> R) -> std::thread::Result<R> {
    // One call site for f, so that it is inlined as it was without the retry.
    let mut careful = false;
    loop {
        let before = generated(c);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(c, careful)));
        if r.is_err() && !careful && generated(c) == before {
            careful = true;
            continue;
        }
        return r;
    }
}

/// Per-thread working storage for `expand_safety_one`.
struct SWork {
    /// The successors of the state being expanded, each with the label of its action.
    buf: Vec<(State, u32)>,
    /// The successors that may be new: index in `buf`, fingerprint, and the packed state if the
    /// fingerprint needed it.
    cand: Vec<(usize, Fp, Option<Packed>)>,
    mine: Seen,
    /// With -dumpgraph: the edges from the state being expanded, each with the index of its
    /// successor (those past the successor that stops the search are dropped), and the lines
    /// ready to be written
    dpend: Vec<(usize, String)>,
    dump: String,
    /// The lines printed while computing the successors (PRINT_ORDER)
    held: Held,
    /// With -continue, the successors (index in `buf`) that violate an action property
    acts: Vec<(usize, &'static str)>,
}

impl SWork {
    fn new() -> Self {
        SWork {
            buf: Vec::with_capacity(64),
            cand: Vec::with_capacity(64),
            mine: Seen::new(),
            dpend: vec![],
            dump: String::new(),
            held: Held::default(),
            acts: vec![],
        }
    }
}

/// The fewest states in a piece of a level (see `Pool`): a smaller level runs on one thread
const MIN_PIECE: usize = 64;

/// Expands a single state, pushing newly found states onto c.next.
fn expand_safety_one(
    w: &Packed,
    sfp: Fp,
    seen: &Shards,
    opt: &Opt,
    c: &mut SChunk,
    ws: &mut SWork,
    careful: bool,
) -> Option<SFound> {
    let s = unpack(w);
    ws.cand.clear();
    ws.dpend.clear();
    ws.acts.clear();
    let cap = Capturing::start();
    let failed = successors(&s, &mut ws.buf, careful);
    ws.held = cap.finish();
    if failed.is_none() && ws.buf.is_empty() && opt.check_deadlock {
        ws.held.flush(u32::MAX);
        return Some(SFound::new(sfp, None, SMsg::Deadlock));
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
        ws.held.flush((c.generated - base) as u32);
        return found;
    }
    c.generated = examined;
    // What was printed up to the successor that stops the search, or all of it
    ws.held.flush(if matches!(stopped, Ok(None)) { u32::MAX } else { (examined - base) as u32 });
    // A successor that violates an action property is added to the visited states, but TLC
    // stops before queueing it
    if let (Ok(Some(f)), Some(&(i, tfp, _))) = (&stopped, ws.cand.last()) {
        let act = f.in_model && matches!(f.msg, SMsg::Action(_) | SMsg::ActionEval(..));
        if act && base + i as u64 + 1 == examined && c.next.last().is_some_and(|q| q.1 == tfp) {
            c.next.pop();
        }
    }
    match stopped {
        Err(p) => match classify(p) {
            (e, false) => Some(SFound::new(sfp, None, SMsg::Untraced(e))),
            (e, true) => std::panic::panic_any(e),
        },
        Ok(Some(f)) => Some(f),
        Ok(None) => match failed {
            Some(p) => raise_next(p),
            None => None,
        },
    }
}

/// `expand_safety_one` with TLCGET: each successor is handled as `next` computes it, as TLC does
fn expand_eager_one(w: &Packed, sfp: Fp, seen: &Shards, opt: &Opt, c: &mut SChunk, ws: &mut SWork) -> Option<SFound> {
    let s = unpack(w);
    tg_queued(-1);
    let mut found: Option<SFound> = None;
    let mut pushes = 0u64;
    let mut out: Vec<(State, u32)> = vec![];
    let failed = {
        let mut hook = |t: &State, l: u32| {
            pushes += 1;
            if let Some(f) = eager_succ(&s, sfp, *t, l, seen, c, ws) {
                found = Some(f);
                std::panic::panic_any(EagerStop);
            }
        };
        with_pushed(&mut hook, || std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| next(&s, &mut out))).err())
    };
    if found.is_some() {
        return found;
    }
    if let Some(p) = failed {
        raise_next(p);
    }
    if pushes == 0 && opt.check_deadlock {
        return Some(SFound::new(sfp, None, SMsg::Deadlock));
    }
    None
}

/// One successor handled as in `expand_safety_one`
fn eager_succ(s: &State, sfp: Fp, t: State, l: u32, seen: &Shards, c: &mut SChunk, ws: &mut SWork) -> Option<SFound> {
    ws.buf.clear();
    ws.buf.push((t, l));
    ws.cand.clear();
    ws.acts.clear();
    ws.dpend.clear();
    let base = c.generated;
    let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| fingerprint_successors(s, sfp, seen, c, ws)));
    let examined = c.generated;
    let found = insert_candidates(base, sfp, seen, c, ws);
    for (_, e) in ws.dpend.drain(..) {
        ws.dump += &e;
    }
    if found.is_some() {
        return found;
    }
    c.generated = examined;
    if let (Ok(Some(f)), Some(&(_, tfp, _))) = (&stopped, ws.cand.last()) {
        let act = f.in_model && matches!(f.msg, SMsg::Action(_) | SMsg::ActionEval(..));
        if act && c.next.last().is_some_and(|q| q.1 == tfp) {
            c.next.pop();
            tg_queued(-1);
        }
    }
    match stopped {
        Err(p) => match classify(p) {
            (e, false) => Some(SFound::new(sfp, None, SMsg::Untraced(e))),
            (e, true) => Some(SFound::new(sfp, None, SMsg::Eval(e))),
        },
        Ok(f) => f,
    }
}

/// Fills ws.cand with the successors in ws.buf that may be new and prefetches the table line of
/// each. Stops at a successor that is an error by itself and returns it.
fn fingerprint_successors(s: &State, sfp: Fp, seen: &Shards, c: &mut SChunk, ws: &mut SWork) -> Option<SFound> {
    for (i, &(ref t, l)) in ws.buf.iter().enumerate() {
        c.generated += 1;
        if !in_model(s, t) {
            if let Some(f) = out_of_model(s, sfp, t, l) {
                return Some(f);
            }
            continue;
        }
        if dumping() {
            let mut e = String::new();
            dump_succ(&mut e, sfp, t, l);
            ws.dpend.push((i, e));
        }
        // A violated action property is reported after t is added (if new) and its invariants are
        // checked, as TLC does: t stays a candidate, and the search stops after it.
        let act = match check_action_props(s, t) {
            // With -continue, reported in `insert_candidates` and the search goes on
            Some(SMsg::Action(name)) if flag(&CONTINUE) => {
                ws.acts.push((i, name));
                None
            }
            m => m.map(|m| SFound::new(sfp, Some((*t, l)), m)),
        };
        // With a VIEW, most successors are duplicates, so only new ones are packed. An out-of-type
        // duplicate then goes unreported, as TLC checks invariants only on new states.
        let (tfp, tw) = if HAS_VIEW {
            match fresh_fp(t, Some(&mut ws.mine)) {
                Some(Some(fp)) => (fp, None),
                Some(None) if act.is_some() => return act,
                Some(None) => continue,
                None if pack(t).is_none() => return Some(pack_failed(sfp, *t, l)),
                None => type_error("VIEW value", ""),
            }
        } else {
            let Some(tw) = pack(t) else {
                return Some(pack_failed(sfp, *t, l));
            };
            let Some(fp) = fresh_state_fp(t, &tw, &mut ws.mine) else {
                if act.is_some() {
                    return act;
                }
                continue;
            };
            (fp, Some(tw))
        };
        seen.prefetch(tfp);
        ws.cand.push((i, tfp, tw));
        if act.is_some() {
            return act;
        }
    }
    None
}

/// Adds the candidates to the visited set in order and queues the new ones. Stops at a new state
/// that is an error and returns it. `base` is c.generated before the first successor.
fn insert_candidates(base: u64, sfp: Fp, seen: &Shards, c: &mut SChunk, ws: &mut SWork) -> Option<SFound> {
    // With -continue, the violations of action properties, each after its successor is checked
    let mut acts = 0;
    let report_acts = |upto: usize, acts: &mut usize, ws: &SWork| {
        while let Some(&(j, name)) = ws.acts.get(*acts).filter(|(j, _)| *j < upto) {
            report_continued(seen, &SFound::new(sfp, Some(ws.buf[j]), SMsg::Action(name)));
            *acts += 1;
        }
    };
    let r = insert_candidates_in(base, sfp, seen, c, ws, &mut |upto, ws| report_acts(upto, &mut acts, ws));
    if r.is_none() {
        report_acts(usize::MAX, &mut acts, ws);
    }
    r
}

fn insert_candidates_in(base: u64, sfp: Fp, seen: &Shards, c: &mut SChunk, ws: &mut SWork, acts: &mut dyn FnMut(usize, &SWork)) -> Option<SFound> {
    for k in 0..ws.cand.len() {
        let (i, tfp, tw) = ws.cand[k];
        acts(i, ws);
        if !seen.insert_with(tfp, sfp) {
            acts(i + 1, ws);
            continue;
        }
        c.generated = base + i as u64 + 1;
        let (t, l) = &ws.buf[i];
        if dumping() {
            dump_node(&mut ws.dump, &tfp, t, false);
        }
        let Some(tw) = tw.or_else(|| pack(t)) else {
            return Some(pack_failed(sfp, *t, *l));
        };
        c.distinct += 1;
        tg_added();
        ws.held.flush(i as u32 + 1);
        match eval_invariants(t) {
            Ok(None) => {}
            Ok(Some(inv)) if flag(&CONTINUE) => report_continued(seen, &SFound::new(tfp, None, SMsg::Inv(inv))),
            Ok(Some(inv)) => return Some(SFound::new(tfp, None, SMsg::Inv(inv))),
            Err((inv, e)) => return Some(SFound::new(tfp, None, SMsg::InvEval(inv, e))),
        }
        c.next.push((tw, tfp));
        tg_queued(1);
        acts(i + 1, ws);
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
    ws: &mut SWork,
) -> SChunk {
    use std::sync::atomic::Ordering::Relaxed;
    let mut c = SChunk { next: vec![], generated: 0, distinct: 0, found: None, expanded: 0 };
    for i in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let (w, sfp) = &frontier[i];
        let base = c.generated;
        c.expanded += 1;
        let r = if TLCGET {
            // Not again on an error: evaluating sets registers and prints
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| expand_eager_one(w, *sfp, seen, opt, &mut c, &mut *ws)))
        } else {
            expand_caught(&mut c, |c| c.generated, |c, careful| expand_safety_one(w, *sfp, seen, opt, c, &mut *ws, careful))
        };
        if dumping() {
            // The successors examined up to the one that stopped the search, if any
            let n = (c.generated - base) as usize;
            for (k, e) in ws.dpend.drain(..) {
                if k < n {
                    ws.dump += &e;
                }
            }
            if ws.dump.len() > 1 << 20 {
                dump_write(&mut ws.dump);
            }
        }
        let found = match r {
            Ok(f) => f,
            Err(p) => Some(match classify(p) {
                (e, true) => SFound::new(*sfp, None, SMsg::Eval(e)),
                (e, false) => SFound::new(*sfp, None, SMsg::Untraced(e)),
            }),
        };
        if found.is_some() {
            c.found = found;
            stop.store(true, Relaxed);
            break;
        }
        if tg_exiting() {
            stop.store(true, Relaxed);
            break;
        }
    }
    dump_write(&mut ws.dump);
    c
}

/// Something that remembers visited states: the locked shards, or the single table used in
/// batched mode.
trait Visited {
    fn pred_of(&self, fp: Fp) -> Option<Fp>;
    fn contains(&self, fp: Fp) -> bool;
}

impl Visited for Shards {
    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        Shards::pred_of(self, fp)
    }
    fn contains(&self, fp: Fp) -> bool {
        Shards::contains(self, fp)
    }
}

impl Visited for Table {
    fn pred_of(&self, fp: Fp) -> Option<Fp> {
        Table::pred_of(self, fp)
    }
    fn contains(&self, fp: Fp) -> bool {
        Table::contains(self, fp)
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
    tg_quiet(|| replay_in(chain))
}

fn replay_in(chain: &[Fp]) -> Option<Vec<(State, u32)>> {
    // With PRINT_ORDER, quietly: `print_states_tlc` prints what TLC prints meanwhile
    let _quiet = Capturing::start();
    let first = if PRINT_ORDER {
        let mut v = vec![];
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut v)));
        v.into_iter().find_map(|s| pack(&s).map(|w| (s, w, state_fp(&s, &w))).filter(|x| x.2 == chain[0]))?
    } else {
        initial_states().0.into_iter().find(|(_, _, fp)| *fp == chain[0])?
    };
    let mut out = vec![(first.0, u32::MAX)];
    let mut cur = first.0;
    let mut buf: Vec<(State, u32)> = vec![];
    for want in &chain[1..] {
        // An error raised after the wanted successor was computed (see `successors`) is ignored.
        let _ = successors(&cur, &mut buf, true);
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
    let mut prev: Option<&State> = None;
    let len = trace.len() + extra.is_some() as usize;
    for (s, l) in trace {
        n += 1;
        print_step(&format!("State {n}: <{}>", name(*l)), s, diff_prev(n - 1, len, prev));
        prev = Some(s);
    }
    if let Some((s, l)) = extra {
        n += 1;
        print_step(&format!("State {n}: <{}>", name(l)), &s, diff_prev(n - 1, len, prev));
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
        // The state being expanded is the one before a new state that violates an invariant
        Some(trace) if PRINT_ORDER => {
            let succ = f.extra.is_none() && matches!(f.msg, SMsg::Inv(_) | SMsg::InvEval(..));
            print_states_tlc(&trace, trace.len() - succ as usize, f.extra)
        }
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
    let (inits, mut generated) = initial_states();
    let mut frontier = Level::new(opt.mem_limit);
    let mut first = vec![];
    for (_, w, fp) in inits {
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
    let pool = Pool::new(opt.workers);
    let work: Vec<std::sync::Mutex<SWork>> = (0..pool.workers()).map(|_| std::sync::Mutex::new(SWork::new())).collect();
    let mut depth = 1u32;
    let mut last = std::time::Instant::now();
    if tg_exiting() {
        return finish(opt, t0, generated, distinct, depth, frontier.len());
    }
    while !frontier.is_empty() {
        tg_set_level(depth as u64);
        let left_before = frontier.len();
        let mut nxt = Level::new(opt.mem_limit);
        let mut found: Option<SFound> = None;
        let mut done = 0usize;
        let mut expanded = 0usize;
        // Read the level one batch at a time and split each batch into pieces for the threads.
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
                    merge_chunk(c, &mut generated, &mut distinct, &mut nxt, &mut found, opt, &mut expanded);
                }
                cur = parts.next();
                continue;
            }
            let (chunks, next_part) = pool.run_with(
                n,
                pool.piece(n, MIN_PIECE),
                |wid, _, x, y| expand_safety(&part, x, y, &seen, &stop, opt, &mut work[wid].lock().unwrap()),
                || {
                    for c in pending.drain(..) {
                        merge_chunk(c, &mut generated, &mut distinct, &mut nxt, &mut found, opt, &mut expanded);
                    }
                    parts.next()
                },
            );
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
            merge_chunk(c, &mut generated, &mut distinct, &mut nxt, &mut found, opt, &mut expanded);
        }
        if let Some(f) = found {
            // As TLC counts its queue when it stops: the states of this level not yet expanded
            // and those queued for the next (with one worker; with more, what the others had
            // taken off the queue varies)
            report_and_exit(&seen, f, generated, distinct, nxt.len() + (left_before - expanded));
        }
        if tg_exiting() {
            let depth = depth + !nxt.is_empty() as u32;
            return finish(opt, t0, generated, distinct, depth, nxt.len() + (left_before - expanded));
        }
        frontier = nxt;
        if !frontier.is_empty() {
            depth += 1;
        }
    }
    finish(opt, t0, generated, distinct, depth, 0);
}

/// Adds one worker's results to the totals and the next level. Chunks are merged in worker
/// order, so the first error reported is the one from the earliest chunk.
fn merge_chunk(c: SChunk, generated: &mut u64, distinct: &mut u64, nxt: &mut Level, found: &mut Option<SFound>, opt: &Opt, expanded: &mut usize) {
    *expanded += c.expanded;
    *generated += c.generated;
    *distinct += c.distinct;
    nxt.extend(c.next, opt);
    if found.is_none() {
        *found = c.found;
    }
}

/// Reports a detected error and exits. Never returns.
fn report_and_exit(seen: &dyn Visited, f: SFound, mut generated: u64, mut distinct: u64, left: usize) -> ! {
    if dumping() && f.extra.is_none() && matches!(f.msg, SMsg::InvEval(..)) {
        // The state whose successor failed: the one before it on the trace
        let parent = seen.pred_of(f.fp).and_then(|p| fp_chain(seen, p)).and_then(|c| replay(&c));
        if let Some(&(s, _)) = parent.as_ref().and_then(|t| t.last()) {
            let p = state_fp(&s, &pack(&s).unwrap());
            dump_replay(&s, p, &|fp| seen.contains(fp));
        }
    }
    let code = report_msg(&f.msg, f.in_model);
    // As in TLC, a successor that left its type counts as one state, and so does a new successor
    // that could not be packed (unless it is outside the CONSTRAINT).
    let pseudo = matches!(f.msg, SMsg::Eval(EvalErr::Type(_)));
    let unpacked = f.in_model
        && (matches!(f.msg, SMsg::OutOfType)
            || (f.extra.is_some() && matches!(f.msg, SMsg::Inv(_) | SMsg::InvEval(..))));
    if pseudo || unpacked {
        distinct += 1;
    }
    if pseudo {
        generated += 1;
        dump_unrepresentable(f.fp);
    }
    // TLC shows no behavior for an error in the CONSTRAINT, the VIEW, or the liveness checks
    let shown = if matches!(f.msg, SMsg::Untraced(_) | SMsg::Live(..)) { 0 } else { report_trace(seen, &f) };
    if pseudo && shown > 0 {
        println!("State {}: <a successor that tla2rs cannot represent>\n", shown + 1);
    }
    if let SMsg::Eval(e) | SMsg::InvEval(_, e) | SMsg::ActionEval(_, e) = &f.msg {
        fp_note(e);
    }
    let code = continued_inv_eval(&f.msg, f.in_model).unwrap_or(code);
    if matches!(f.msg, SMsg::Eval(EvalErr::Incomplete(_))) {
        generated += show_incomplete(shown);
    }
    if let (SMsg::Eval(e), true) = (&f.msg, shown > 0) {
        if let Some(chain) = fp_chain(seen, f.fp) {
            if let Some((s, _)) = replay(&chain).and_then(|t| t.last().copied()) {
                eval_again_prints(&s, e);
            }
        }
    }
    println!("{generated} states generated, {distinct} distinct states found, {left} states left on queue.");
    exit(code);
}

/// With -continue, TLC reports a failed invariant as without it, then stops with an exception it
/// did not expect (measured on TLC 2.19): prints that and returns its exit code
fn continued_inv_eval(msg: &SMsg, in_model: bool) -> Option<i32> {
    let SMsg::InvEval(_, e) = msg else { return None };
    if !flag(&CONTINUE) || !in_model {
        return None;
    }
    report_eval_as(e, true);
    Some(255)
}

fn finish(opt: &Opt, t0: std::time::Instant, generated: u64, distinct: u64, depth: u32, left: usize) {
    if std::env::var("TLA2RS_PHASES").is_ok() {
        let g = |i: usize| PH[i].load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e6;
        println!(
            "  phases: collect {:.2}s, lookup-wait {:.2}s, insert {:.2}s",
            g(0),
            g(1),
            g(2)
        );
    }

    println!("{generated} states generated, {distinct} distinct states found, {left} states left on queue.");
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
                spawn_worker(sc, move || {
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
    /// With -dumpgraph, the edges collected (written by the caller)
    dump: String,
    /// The states taken off the queue (see `SChunk::expanded`), and the candidate that stops the
    /// search if it was collected: TLC does not queue it
    expanded: usize,
    bad: Option<Fp>,
}

/// Which thread owns a fingerprint. The 1024 shards are split evenly as is, so no two threads
/// ever touch the same shard in phase 3.
#[inline]
fn part_of(fp: Fp, parts: usize) -> usize {
    shard(fp) * parts / 1024
}

/// Phase 1: generates successors, computes their fingerprints, filters duplicates, checks
/// invariants, and queues them. Never writes to the shared table; `tbl` and `prev` (the previous
/// batch, not inserted yet) are only read when a candidate would stop the search.
#[allow(clippy::too_many_arguments)]
fn collect_phase(
    frontier: &[Qitem],
    lo: usize,
    hi: usize,
    opt: &Opt,
    stop: &std::sync::atomic::AtomicBool,
    parts: usize,
    tbl: &Table,
    prev: &[Vec<Vec<Cand>>],
) -> Collected {
    use std::sync::atomic::Ordering::Relaxed;
    let mut out = Collected {
        parts: (0..parts).map(|_| vec![]).collect(),
        generated: 0,
        found: None,
        dump: String::new(),
        expanded: 0,
        bad: None,
    };
    let mut buf: Vec<(State, u32)> = Vec::with_capacity(64);
    let mut mine = Seen::new();
    for i in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let (w, sfp) = &frontier[i];
        let mark = out.dump.len();
        out.expanded += 1;
        let r = expand_caught(&mut out, |o| o.generated, |out, careful| {
            out.dump.truncate(mark);
            let s = unpack(w);
            let failed = successors(&s, &mut buf, careful);
            if failed.is_none() && buf.is_empty() && opt.check_deadlock {
                return Some(SFound::new(*sfp, None, SMsg::Deadlock));
            }
            for &(t, l) in buf.iter() {
                out.generated += 1;
                if !in_model(&s, &t) {
                    if let Some(f) = out_of_model(&s, *sfp, &t, l) {
                        return Some(f);
                    }
                    continue;
                }
                if dumping() {
                    dump_succ(&mut out.dump, *sfp, &t, l);
                }
                // As in `fingerprint_successors`, a violated action property stops the search after
                // t is collected (and its invariants are checked)
                let act = check_action_props(&s, &t).map(|m| SFound::new(*sfp, Some((t, l)), m));
                // As in `fingerprint_successors`: with a VIEW, a duplicate is dropped before it is
                // packed.
                let (tfp, tw) = if HAS_VIEW {
                    match fresh_fp(&t, Some(&mut mine)) {
                        Some(Some(fp)) => (fp, pack(&t)),
                        Some(None) if act.is_some() => return act,
                        Some(None) => continue,
                        None if pack(&t).is_none() => return Some(pack_failed(*sfp, t, l)),
                        None => type_error("VIEW value", ""),
                    }
                } else {
                    let Some(tw) = pack(&t) else {
                        return Some(pack_failed(*sfp, t, l));
                    };
                    let Some(fp) = fresh_state_fp(&t, &tw, &mut mine) else {
                        if act.is_some() {
                            return act;
                        }
                        continue;
                    };
                    (fp, Some(tw))
                };
                // Phase 1 checks the invariants of every candidate not seen by this thread, also one
                // visited before, which only matters when they print: TLC evaluates them on new
                // states only, so then a candidate already visited or collected is not checked
                let known = INV_PRINTS && {
                    let has = |v: &Vec<Cand>| v.iter().any(|c| c.fp == tfp);
                    tbl.contains(tfp) || prev.iter().flatten().any(has) || out.parts.iter().any(has)
                };
                let inv = if tw.is_some() && !known { eval_invariants(&t) } else { Ok(None) };
                // TLC checks only new states. With a VIEW or a SYMMETRY, a state already visited
                // under the same fingerprint can be a different one, so before stopping, look the
                // candidate up among the states visited or collected so far.
                let bad = tw.is_none() || !matches!(inv, Ok(None));
                if bad && (HAS_VIEW || !PERMS.is_empty()) {
                    let has = |v: &Vec<Cand>| v.iter().any(|c| c.fp == tfp);
                    if tbl.contains(tfp) || prev.iter().flatten().any(has) || out.parts.iter().any(has) {
                        if act.is_some() {
                            return act;
                        }
                        continue;
                    }
                }
                let Some(tw) = tw else {
                    if dumping() {
                        dump_node(&mut out.dump, &tfp, &t, false);
                    }
                    return Some(pack_failed(*sfp, t, l));
                };
                out.parts[part_of(tfp, parts)].push(Cand { w: tw, fp: tfp, pred: *sfp });
                if act.is_some() || !matches!(inv, Ok(None)) {
                    out.bad = Some(tfp);
                }
                // Stop generating once a violating state is found (so we stop at the same count as
                // the non-batched path). This candidate also goes into the table in phase 3, so the
                // counterexample can be traced back from its fingerprint.
                match inv {
                    Ok(None) => {}
                    Ok(Some(inv)) => return Some(SFound::new(tfp, None, SMsg::Inv(inv))),
                    Err((inv, e)) => return Some(SFound::new(tfp, None, SMsg::InvEval(inv, e))),
                }
                if act.is_some() {
                    return act;
                }
            }
            if let Some(p) = failed {
                raise_next(p);
            }
            None
        });
        let found = match r {
            Ok(f) => f,
            Err(p) => Some(match classify(p) {
                (e, true) => SFound::new(*sfp, None, SMsg::Eval(e)),
                (e, false) => SFound::new(*sfp, None, SMsg::Untraced(e)),
            }),
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
    let mut dump = String::new();
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
            if dumping() {
                dump_node(&mut dump, &c.fp, &unpack(&c.w), false);
                if dump.len() > 1 << 20 {
                    dump_write(&mut dump);
                }
            }
        }
    }
    dump_write(&mut dump);
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
    let mut frontier = Level::new(opt.mem_limit);
    let mut first = vec![];
    let (inits, mut generated) = initial_states();
    tbl.reserve(inits.len(), opt.workers);
    if use_gpu {
        gpu_set_table(&tbl);
    }
    for (_, w, fp) in inits {
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
    let pool = Pool::new(opt.workers);
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
        let (mut expanded, mut bad, mut unqueued) = (0usize, None, 0usize);
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
                // One piece per thread, as each sees only the candidates it collected itself (see
                // `collect_phase`): with one thread, all those of the batch
                let k = if n < 1024 { 1 } else { opt.workers.min(n) };
                let prev: &[Vec<Vec<Cand>>] = pending.as_ref().map_or(&[], |(b, _)| b.as_slice());
                let collected: Vec<Collected> = pool.run(n, n.div_ceil(k), |_, _, x, y| {
                    collect_phase(&part, x, y, opt, &stop, parts, &tbl, prev)
                });
                // Group the per-thread arrays by owner, moving them as is rather than copying
                // their contents.
                let mut by_part: Vec<Vec<Vec<Cand>>> = (0..parts).map(|_| vec![]).collect();
                for mut c in collected {
                    dump_write(&mut c.dump);
                    generated += c.generated;
                    expanded += c.expanded;
                    if found_err.is_none() {
                        found_err = c.found;
                        bad = c.bad;
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
                flags = pool.run(by_part.len(), 1, |_, t, _, _| {
                    let g = &by_part[t];
                    let mut f = vec![0u8; g.iter().map(|v| v.len()).sum()];
                    let mut off = 0;
                    for cs in g {
                        lookup_phase_cpu(cs, &mut f[off..off + cs.len()], &tbl);
                        off += cs.len();
                    }
                    f
                });
            }
            ph(1, tph);
            let tph = std::time::Instant::now();
            let results: Vec<(Vec<Qitem>, u64)> = pool.run(by_part.len(), 1, |_, t, _, _| {
                let (g, f) = (&by_part[t], &flags[t]);
                let (lo, hi) = (t * SHARDS / parts, (t + 1) * SHARDS / parts);
                let mut o: (Vec<Qitem>, u64) = (vec![], 0);
                let mut off = 0;
                for cs in g {
                    let (v, d) = insert_phase(cs, &f[off..off + cs.len()], &tbl, lo, hi);
                    off += cs.len();
                    o.0.extend(v);
                    o.1 += d;
                }
                o
            });
            ph(2, tph);
            let mut added = 0usize;
            for (v, d) in results {
                distinct += d;
                added += d as usize;
                if let Some(b) = bad.filter(|b| v.iter().any(|q| q.1 == *b)) {
                    unqueued += 1;
                    bad = bad.filter(|x| *x != b);
                }
                nxt.extend(v, opt);
            }
            // Count after every batch, so that `reserve` for the next batch sees the current total.
            tbl.count_added(added);
            // The batch that found the error goes through phases 2 and 3 on the next round, so
            // that the states collected before it (the error state among them) are counted and in
            // the table for the trace.
            if found_err.is_some() && carried.is_none() {
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
            // As in `run_safety`
            report_and_exit(&tbl, f, generated, distinct, nxt.len() - unqueued + (left_before - expanded));
        }
        frontier = nxt;
        if !frontier.is_empty() {
            depth += 1;
        }
    }
    finish(opt, t0, generated, distinct, depth, 0);
}

/// The most states of a level the threads expand before what they found is merged (see
/// `run_liveness`)
const LEVEL_SLICE: usize = 1 << 20;
fn run_liveness(opt: &Opt) {
    let check_deadlock = opt.check_deadlock;
    let workers = opt.workers;
    let t0 = std::time::Instant::now();
    // TLC's warning that the search runs on the graph folded by symmetry is among STARTUP_PRINTS
    COL_LIMIT.store(opt.mem_limit, std::sync::atomic::Ordering::Relaxed);
    *COL_DIR.lock().unwrap() = Some(opt.tmpdir.clone());
    let mut g = Graph { states: Col::new(), parent: Col::new(), sbits: Col::new() };
    let seen = Shards::new(false);
    let (inits, mut generated) = initial_states();
    // TLC evaluates the tableau's state atoms on the initial states once they are all computed
    let mut ibits = vec![];
    for (s, _, _) in &inits {
        match state_bits(s, SATOMS_TABLEAU) {
            Ok(b) => ibits.push(b),
            Err(m) => {
                // As an error in checking an initial state (see `initial_states`)
                let code = match &m {
                    SMsg::Live(what, e) => {
                        report_eval_as(e, false);
                        if !tlc_eval_exception(e) && !matches!(e, EvalErr::Type(_)) {
                            println!("While working on the initial state:\n{}\n", show(s));
                        }
                        eprintln!("  (while evaluating {what})");
                        255
                    }
                    m => report_msg(m, true),
                };
                println!("{generated} states generated, {n} distinct states found, {n} states left on queue.", n = inits.len());
                exit(code);
            }
        }
    }
    for ((_, w, fp), b) in inits.into_iter().zip(ibits) {
        if seen.insert(fp) {
            g.states.push(w);
            g.parent.push((u32::MAX, u32::MAX));
            g.sbits.push(b);
        }
    }
    println!("Finished computing initial states: {} distinct states generated. ({workers} workers)", g.states.len());
    let stop = std::sync::atomic::AtomicBool::new(false);
    let pool = Pool::new(workers);
    let mut live = LiveGraph::default();
    let mut lo = 0usize;
    let mut depth = 1u32;
    let mut last = std::time::Instant::now();
    loop {
        let hi = g.states.len();
        if lo == hi {
            break;
        }
        // The level (all states at the same depth) a slice at a time, so that what the threads
        // find before it is merged stays small, each slice split into pieces for the threads
        let mut expanded = 0usize;
        for from in (lo..hi).step_by(LEVEL_SLICE) {
            let to = (from + LEVEL_SLICE).min(hi);
            let n = to - from;
            let chunks: Vec<Chunk> = pool.run(n, pool.piece(n, MIN_PIECE), |_, i, a, b| {
                expand(&g, from + a, from + b, &seen, &stop, i, check_deadlock)
            });
            let mut found = None;
            let mut base = vec![];
            let mut unqueued = false;
            for (i, mut c) in chunks.into_iter().enumerate() {
                dump_write(&mut c.dump);
                generated += c.generated;
                expanded += c.expanded;
                base.push(g.states.len());
                live.add(&mut c.live);
                g.sbits.extend_from_slice(&c.sbits);
                g.states.extend_from_slice(&c.states);
                g.parent.extend_from_slice(&c.parent);
                if found.is_none() {
                    found = c.found.map(|f| (i, f));
                    unqueued = c.unqueued && found.is_some();
                }
            }
            if let Some((_, f)) = found {
                let mut distinct = g.states.len();
                let code = match f {
                    Found::New(w, idx, msg) => {
                        if dumping() && matches!(msg, SMsg::InvEval(..)) {
                            let p = g.parent.get(base[w] + idx).0 as usize;
                            let s = g.state(p);
                            dump_replay(&s, state_fp(&s, &g.states.get(p)), &|fp| seen.contains(fp));
                        }
                        let code = report_msg(&msg, true);
                        g.print_trace((base[w] + idx) as u32, None, true);
                        if let SMsg::InvEval(_, e) = &msg {
                            fp_note(e);
                        }
                        continued_inv_eval(&msg, true).unwrap_or(code)
                    }
                    Found::Deadlock(id) => {
                        println!("Error: Deadlock reached.");
                        g.print_trace(id, None, false);
                        11
                    }
                    Found::Succ(p, t, l, msg, in_model) => {
                        // A new state that could not be packed counts as one state too (to match TLC).
                        if in_model && matches!(msg, SMsg::Inv(_) | SMsg::InvEval(..) | SMsg::OutOfType) {
                            distinct += 1;
                        }
                        let code = report_msg(&msg, in_model);
                        g.print_trace(p, Some((&t, l)), false);
                        code
                    }
                    // TLC shows no behavior for these
                    Found::Live(m) => report_msg(&m, true),
                    Found::Eval(p, e) => {
                        let pseudo = matches!(e, EvalErr::Type(_));
                        let unassigned = matches!(e, EvalErr::Incomplete(_));
                        let again = e.clone();
                        let code = report_msg(&SMsg::Eval(e), true);
                        g.print_trace(p, None, false);
                        eval_again_prints(&g.state(p as usize), &again);
                        fp_note(&again);
                        if unassigned {
                            generated += show_incomplete(g.trace_len(p));
                        }
                        if pseudo {
                            // As in TLC, the out-of-type successor counts as one state (its contents
                            // can't be represented).
                            dump_unrepresentable(state_fp(&g.state(p as usize), &g.states.get(p as usize)));
                            generated += 1;
                            distinct += 1;
                            println!("State {}: <a successor that tla2rs cannot represent>\n", g.trace_len(p) + 1);
                        }
                        code
                    }
                };
                // As in `run_safety`
                println!(
                    "{generated} states generated, {distinct} distinct states found, {} states left on queue.",
                    (hi - lo - expanded) + (g.states.len() - hi) - unqueued as usize
                );
                exit(code);
            }
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
        dump_finish();
        // The classes of the states hold their state atoms now
        drop(seen);
        g.sbits = Col::new();
        trim_heap();
        let ok = liveness(&g, live, workers);
        println!("Checked temporal properties in {:.3}s", t1.elapsed().as_secs_f64());
        let spilled = COL_SPILLED.load(std::sync::atomic::Ordering::Relaxed);
        if spilled > 0 {
            eprintln!(
                "tla2rs: the state graph spilled {:.0} MB to {} (-memlimit MB raises the in-memory part)",
                spilled as f64 / (1u64 << 20) as f64,
                opt.tmpdir.display()
            );
        }
        if !ok {
            exit(13);
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

/// A state of the automaton of a negated property (see ltl.rs): the atoms that must hold (state
/// atoms on the current state, action atoms on the step taken from it), its successors, whether it
/// is initial, and the acceptance sets it is in.
struct LNode {
    s_pos: u64,
    s_neg: u64,
    a_pos: u64,
    a_neg: u64,
    succ: &'static [u32],
    init: bool,
    acc: u64,
}

/// The automaton of a negated property, or of one disjunct of its normal form with its []<>S
/// (`ae_state`), []<>A (`ae_action`) and <>[]A (`ea`) parts as conditions on cycles (see
/// `split_disjuncts` in tla2rs's live.rs)
struct LProp {
    #[allow(dead_code)]
    name: &'static str,
    nodes: &'static [LNode],
    nacc: u32,
    ae_state: &'static [LP],
    ae_action: &'static [LP],
    ea: &'static [LP],
}

/// The label of the stuttering step every state has
const STUTTER: u32 = u32::MAX - 1;
/// The state graph for the liveness search, in columns (see `LiveGraph`). The steps of a state are
/// its edges plus stuttering.
struct Steps {
    /// Per state, the number of its first edge, and the number of edges at the end
    off: Col<u64>,
    /// Per edge, the target and the class
    dst: Col<u32>,
    ecls: ClassCol,
    ec: Vec<EClass>,
    /// Per state, the class
    scls: ClassCol,
    sc: Vec<SClass>,
}
impl Steps {
    fn n(&self) -> usize {
        self.scls.len()
    }
    #[inline]
    fn class(&self, s: usize) -> SClass {
        self.sc[self.scls.get(s) as usize]
    }
    fn sbits(&self, s: usize) -> u64 {
        self.class(s).0
    }
    fn fen(&self, s: usize) -> FMask {
        self.class(s).1
    }
    fn stut(&self, s: usize) -> u64 {
        self.class(s).2
    }
    /// The edges of s
    #[inline]
    fn edges(&self, s: usize) -> std::ops::Range<usize> {
        self.off.get(s) as usize..self.off.get(s + 1) as usize
    }
    /// (target, label, action atoms, fairness steps) of edge e
    #[inline]
    fn edge(&self, e: usize) -> (u32, u32, u64, FMask) {
        let (l, a, f) = self.ec[self.ecls.get(e) as usize];
        (self.dst.get(e), l, a, f)
    }
}
/// Where an enumeration of the successors of product node (s, q) is: the step (an edge; the end of
/// the state's edges is the stuttering step) and the successor of the automaton's node. On the stack
/// of `sccs` (one per node, so kept small), also the node's number there and whether it has a
/// self-loop.
struct At {
    e: usize,
    s: u32,
    j: u32,
    id: u32,
    q: u16,
    selfloop: bool,
}
/// The product of the state graph with the automaton of one negated property; with `ea`, only the
/// steps that keep the property's <>[]A parts
struct Product<'a> {
    st: &'a Steps,
    nodes: &'static [LNode],
    q: usize,
    ea: &'static [LP],
}
impl Product<'_> {
    fn valid(&self, s: u32, q: usize) -> bool {
        let (b, n) = (self.st.sbits(s as usize), &self.nodes[q]);
        b & n.s_pos == n.s_pos && b & n.s_neg == 0
    }
    fn start(&self, p: usize, id: u32) -> At {
        let (s, q) = ((p / self.q) as u32, (p % self.q) as u16);
        At { e: self.st.edges(s as usize).start, s, j: 0, id, q, selfloop: false }
    }
    fn node(&self, at: &At) -> usize {
        at.s as usize * self.q + at.q as usize
    }
    /// The next successor of a product node: (node, label, fairness steps, action atoms)
    #[inline]
    fn next(&self, at: &mut At) -> Option<(usize, u32, FMask, u64)> {
        let n = &self.nodes[at.q as usize];
        let end = self.st.edges(at.s as usize).end;
        while at.e <= end {
            let (t, l, a, f) = if at.e < end { self.st.edge(at.e) } else { (at.s, STUTTER, self.st.stut(at.s as usize), 0) };
            if a & n.a_pos == n.a_pos && a & n.a_neg == 0 && self.ea.iter().all(|x| self.holds(x, self.node(at), a, f)) {
                while (at.j as usize) < n.succ.len() {
                    let q2 = n.succ[at.j as usize] as usize;
                    at.j += 1;
                    if self.valid(t, q2) {
                        return Some((t as usize * self.q + q2, l, f, a));
                    }
                }
            }
            at.e += 1;
            at.j = 0;
        }
        None
    }
    /// Successors of product node p: (node, label, fairness steps, action atoms)
    fn succ(&self, p: usize, out: &mut Vec<(usize, u32, FMask, u64)>) {
        out.clear();
        let mut at = self.start(p, 0);
        while let Some(x) = self.next(&mut at) {
            out.push(x);
        }
    }
    /// Whether predicate x holds of product node p's state, and of the step with action atoms a
    /// and fairness steps f from it
    fn holds(&self, x: &LP, p: usize, a: u64, f: FMask) -> bool {
        let s = p / self.q;
        x.eval(self.st.sbits(s), self.st.fen(s), a, f)
    }
    fn state(&self, p: usize) -> u32 {
        (p / self.q) as u32
    }
}
/// The number of each product node the search reaches, in the order it reaches them: an array over
/// all product nodes when the automaton is small, otherwise a hash map
enum Rank {
    Dense(Vec<u32>),
    Sparse(std::collections::HashMap<usize, u32>),
}
impl Rank {
    fn new(total: usize, q: usize) -> Self {
        if q <= 16 {
            Rank::Dense(vec![u32::MAX; total])
        } else {
            Rank::Sparse(std::collections::HashMap::new())
        }
    }
    #[inline]
    fn get(&self, p: usize) -> Option<u32> {
        match self {
            Rank::Dense(v) => Some(v[p]).filter(|&r| r != u32::MAX),
            Rank::Sparse(m) => m.get(&p).copied(),
        }
    }
    fn set(&mut self, p: usize, r: u32) {
        assert!(r < u32::MAX, "more product nodes than the liveness search can number");
        match self {
            Rank::Dense(v) => v[p] = r,
            Rank::Sparse(m) => {
                m.insert(p, r);
            }
        }
    }
}
/// A set of product nodes: a bitmap over all of them when it is large, otherwise a hash set
enum Members {
    Bits(Vec<u64>),
    Hash(std::collections::HashSet<usize>),
}
impl Members {
    fn new(of: &[usize], total: usize) -> Self {
        if of.len() * 64 >= total {
            let mut b = vec![0u64; total.div_ceil(64)];
            for &p in of {
                b[p / 64] |= 1 << (p % 64);
            }
            Members::Bits(b)
        } else {
            Members::Hash(of.iter().copied().collect())
        }
    }
    #[inline]
    fn contains(&self, p: usize) -> bool {
        match self {
            Members::Bits(b) => b[p / 64] >> (p % 64) & 1 == 1,
            Members::Hash(h) => h.contains(&p),
        }
    }
}
/// Strongly connected components of the product nodes that `id` numbers (from 0 to below `count`;
/// None: left out), reachable from `roots` without leaving them (iterative Tarjan), handed to `f`
/// as they complete until it returns true. Trivial components without a self-loop are left out.
fn sccs(pr: &Product, roots: &[usize], count: usize, id: &dyn Fn(usize) -> Option<u32>, f: &mut dyn FnMut(Vec<usize>) -> bool) {
    const NEW: u32 = u32::MAX;
    let mut index = vec![NEW; count];
    let mut low = vec![0u32; count];
    let mut on = vec![false; count];
    let mut stack: Vec<usize> = vec![];
    let mut call: Vec<At> = vec![];
    let mut idx = 0u32;
    for &root in roots {
        let Some(r) = id(root) else { continue };
        if index[r as usize] != NEW {
            continue;
        }
        index[r as usize] = idx;
        low[r as usize] = idx;
        on[r as usize] = true;
        idx += 1;
        stack.push(root);
        call.push(pr.start(root, r));
        while let Some(fr) = call.last_mut() {
            let (u, ui) = (pr.node(fr), fr.id as usize);
            if let Some((v, _, _, _)) = pr.next(fr) {
                if v == u {
                    fr.selfloop = true;
                }
                let Some(vi) = id(v) else { continue };
                let vi = vi as usize;
                if index[vi] == NEW {
                    index[vi] = idx;
                    low[vi] = idx;
                    on[vi] = true;
                    idx += 1;
                    stack.push(v);
                    call.push(pr.start(v, vi as u32));
                } else if on[vi] {
                    low[ui] = low[ui].min(index[vi]);
                }
                continue;
            }
            let selfloop = fr.selfloop;
            call.pop();
            if let Some(p) = call.last() {
                let pi = p.id as usize;
                low[pi] = low[pi].min(low[ui]);
            }
            if low[ui] != index[ui] {
                continue;
            }
            let mut members = vec![];
            loop {
                let w = stack.pop().unwrap();
                on[id(w).unwrap() as usize] = false;
                members.push(w);
                if w == u {
                    break;
                }
            }
            if (members.len() > 1 || selfloop) && f(members) {
                return;
            }
        }
    }
}
/// What a fair accepting cycle in component `c` must visit: (acceptance set, node predicate) or
/// (fairness condition, step). None if `c` has no such cycle; Some(Err(c')) if strong fairness
/// requires leaving out the states where an action is enabled.
enum Verdict {
    Reject,
    Narrow(Vec<usize>),
    Accept { steps: Vec<usize>, off: Vec<usize> },
}
fn judge(pr: &Product, prop: &LProp, c: &[usize], total: usize) -> Verdict {
    let nacc = prop.nacc;
    let mut acc = 0u64;
    for &p in c {
        acc |= pr.nodes[p % pr.q].acc;
    }
    let all = if nacc == 64 { u64::MAX } else { (1u64 << nacc) - 1 };
    if acc & all != all {
        return Verdict::Reject;
    }
    if !prop.ae_state.iter().all(|x| c.iter().any(|&p| pr.holds(x, p, 0, 0))) {
        return Verdict::Reject;
    }
    let set = Members::new(c, total);
    let mut taken: FMask = 0;
    let mut ae_taken = vec![false; prop.ae_action.len()];
    let mut buf = vec![];
    for &p in c {
        pr.succ(p, &mut buf);
        for &(v, _, f, a) in &buf {
            if set.contains(v) {
                taken |= f;
                for (j, x) in prop.ae_action.iter().enumerate() {
                    ae_taken[j] |= pr.holds(x, p, a, f);
                }
            }
        }
    }
    if ae_taken.contains(&false) {
        return Verdict::Reject;
    }
    let mut some_off: FMask = 0;
    let mut all_off = FMask::MAX;
    for &p in c {
        let en = pr.st.fen(pr.state(p) as usize);
        some_off |= !en;
        all_off &= !en;
    }
    let mut steps = vec![];
    let mut off = vec![];
    let mut strong_bad: FMask = 0;
    for (i, (weak, _, _)) in FAIRS.iter().enumerate() {
        let b: FMask = 1 << i;
        if taken & b != 0 {
            steps.push(i);
        } else if *weak {
            if some_off & b == 0 {
                return Verdict::Reject;
            }
            off.push(i);
        } else if all_off & b == 0 {
            strong_bad |= b;
        }
    }
    if strong_bad != 0 {
        let keep: Vec<usize> = c.iter().copied().filter(|&p| pr.st.fen(pr.state(p) as usize) & strong_bad == 0).collect();
        return Verdict::Narrow(keep);
    }
    Verdict::Accept { steps, off }
}
/// Searches a component for a fair accepting cycle, narrowing it for strong fairness
fn search(pr: &Product, prop: &LProp, c: Vec<usize>, total: usize) -> Option<(Vec<usize>, Vec<usize>, Vec<usize>)> {
    match judge(pr, prop, &c, total) {
        Verdict::Reject => None,
        Verdict::Accept { steps, off } => Some((c, steps, off)),
        Verdict::Narrow(keep) => {
            if keep.is_empty() {
                return None;
            }
            let ids: std::collections::HashMap<usize, u32> = keep.iter().enumerate().map(|(i, &p)| (p, i as u32)).collect();
            let mut found = None;
            sccs(pr, &keep, keep.len(), &|p| ids.get(&p).copied(), &mut |sub| {
                found = search(pr, prop, sub, total);
                found.is_some()
            });
            found
        }
    }
}
/// A shortest path inside `set` from `from` (excluded) that ends at a node satisfying `goal` or with
/// a step satisfying `edge` (on the node it leaves, its fairness bits and its action atoms):
/// [(node, label, fairness bits of the step)]
fn path_to(
    pr: &Product,
    set: &Members,
    from: usize,
    goal: &dyn Fn(usize) -> bool,
    edge: &dyn Fn(usize, FMask, u64) -> bool,
) -> Vec<(usize, u32, FMask)> {
    let mut prev: std::collections::HashMap<usize, (usize, u32, FMask)> = std::collections::HashMap::new();
    let mut q = std::collections::VecDeque::from([from]);
    let mut buf = vec![];
    while let Some(u) = q.pop_front() {
        pr.succ(u, &mut buf);
        for &(v, l, f, a) in &buf {
            if !set.contains(v) {
                continue;
            }
            if goal(v) || edge(u, f, a) {
                let mut out = vec![(v, l, f)];
                let mut x = u;
                while x != from {
                    let (p, l2, f2) = prev[&x];
                    out.push((x, l2, f2));
                    x = p;
                }
                out.reverse();
                return out;
            }
            if v != from && !prev.contains_key(&v) {
                prev.insert(v, (u, l, f));
                q.push_back(v);
            }
        }
    }
    vec![]
}
/// f over lo..hi on `threads` threads, in order
fn par_map<T: Send>(lo: usize, hi: usize, threads: usize, f: &(dyn Fn(usize) -> T + Sync)) -> Vec<T> {
    let per = (hi - lo).div_ceil(threads.max(1)).max(1);
    std::thread::scope(|sc| {
        let hs: Vec<_> = (lo..hi)
            .step_by(per)
            .map(|a| spawn_worker(sc, move || (a..(a + per).min(hi)).map(f).collect::<Vec<T>>()))
            .collect();
        hs.into_iter().flat_map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
    })
}
fn liveness(g: &Graph, mut live: LiveGraph, workers: usize) -> bool {
    let n = g.states.len();
    // Fingerprint -> state index (at most 3/4 full, as the visited set)
    let cap = (n + n / 3 + 1).next_power_of_two().max(16);
    let mut keys = vec![0 as Fp; cap];
    let mut vals = vec![u32::MAX; cap];
    let mut zero_id = u32::MAX;
    // The fingerprints and the edges' targets are worked out by the threads, a block at a time
    const BLOCK: usize = 1 << 22;
    for lo in (0..n).step_by(BLOCK) {
        let fps = par_map(lo, (lo + BLOCK).min(n), workers, &|i| {
            let w = g.states.get(i);
            state_fp(&unpack(&w), &w)
        });
        for (i, fp) in (lo..).zip(fps) {
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
    let edges = live.tfp.len();
    let mut dst: Col<u32> = Col::new();
    for lo in (0..edges).step_by(BLOCK) {
        let ts = par_map(lo, (lo + BLOCK).min(edges), workers, &|e| lookup(live.tfp.get(e)));
        // Every target was found new by some expansion
        assert!(!ts.contains(&u32::MAX), "an edge of the state graph leads to a state it does not have");
        dst.extend_from_slice(&ts);
    }
    drop((keys, vals));
    live.tfp = Col::new();
    live.off.push(edges as u64);
    dst.finish();
    live.off.finish();
    live.ecls.finish();
    live.cls.finish();
    live.selfs.finish();
    let st = Steps { off: live.off, dst, ecls: live.ecls, ec: live.ec.list, scls: live.cls, sc: live.sc.list };
    let selfs = live.selfs;
    // The initial states come first
    let inits: Vec<u32> = (0..n as u32).take_while(|&i| g.parent.get(i as usize).0 == u32::MAX).collect();
    // The properties are independent, so several threads check them, and the first one in order
    // that is violated is reported, as when they are checked one after another. A property after
    // one found violated is given up.
    use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
    let (next, first_bad) = (AtomicUsize::new(0), AtomicUsize::new(usize::MAX));
    let found: Vec<Vec<(usize, Lasso)>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..workers.clamp(1, LPROPS.len().max(1)))
            .map(|_| {
                spawn_worker(sc, || {
                    let mut out = vec![];
                    loop {
                        let i = next.fetch_add(1, Relaxed);
                        if i >= LPROPS.len() {
                            break;
                        }
                        let quit = || first_bad.load(Relaxed) < i;
                        if quit() {
                            continue;
                        }
                        if let Some(l) = check_prop(&st, &LPROPS[i], &inits, &quit) {
                            first_bad.fetch_min(i, Relaxed);
                            out.push((i, l));
                        }
                    }
                    out
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
    });
    if let Some((_, (prefix, cycle))) = found.into_iter().flatten().min_by_key(|x| x.0) {
        println!("Error: Temporal properties were violated.");
        println!("Error: The following behavior constitutes a counter-example:");
        match tlc_lasso(g, &st, &inits, selfs.as_slice()) {
            Ok(true) => return false,
            Ok(false) => eprintln!("tla2rs: TLC's search found no counterexample on this graph; showing tla2rs's own"),
            Err(why) => eprintln!("tla2rs: the counterexample is tla2rs's own, not TLC's ({why})"),
        }
        print_lasso(g, &prefix, &cycle);
        return false;
    }
    println!("Temporal properties hold ({} properties, {} fairness conditions, {} edges).", NPROPS, FAIRS.len(), edges);
    true
}
/// A lasso: the steps from an initial state to the entry of the cycle, and the cycle
type Lasso = (Vec<(u32, u32)>, Vec<(u32, u32)>);
/// Looks for a behavior that violates one property: a fair cycle in its product with the state
/// graph that the property's automaton accepts. None also when `quit` says to give up.
fn check_prop(st: &Steps, prop: &LProp, inits: &[u32], quit: &dyn Fn() -> bool) -> Option<Lasso> {
    // The path to a cycle may take any step; the cycle only steps that keep the <>[]A parts
    let all = Product { st, nodes: prop.nodes, q: prop.nodes.len().max(1), ea: &[] };
    let pr = Product { ea: prop.ea, ..all };
    if prop.nodes.is_empty() {
        return None;
    }
    assert!(pr.q <= 1 << 16, "an automaton too large for the liveness search");
    let total = st.n() * pr.q;
    // Reachable product nodes, in BFS order, with the number of their BFS parents in that order
    let mut rank = Rank::new(total, pr.q);
    let mut order: Vec<usize> = vec![];
    let mut par: Vec<u32> = vec![];
    for &s in inits {
        for (q, nd) in prop.nodes.iter().enumerate() {
            let p = s as usize * pr.q + q;
            if nd.init && pr.valid(s, q) && rank.get(p).is_none() {
                rank.set(p, order.len() as u32);
                order.push(p);
                par.push(u32::MAX);
            }
        }
    }
    let mut h = 0;
    let mut buf = vec![];
    while h < order.len() {
        if h % 4096 == 0 && quit() {
            return None;
        }
        let u = order[h];
        all.succ(u, &mut buf);
        for &(v, _, _, _) in &buf {
            if rank.get(v).is_none() {
                rank.set(v, order.len() as u32);
                order.push(v);
                par.push(h as u32);
            }
        }
        h += 1;
    }
    let mut lasso = None;
    sccs(&pr, &order, order.len(), &|p| rank.get(p), &mut |c| {
        if quit() {
            return true;
        }
        let Some((c, steps, off)) = search(&pr, prop, c, total) else { return false };
        let set = Members::new(&c, total);
        let entry = *c.iter().min_by_key(|p| rank.get(**p)).unwrap();
        // The cycle: visit each acceptance set; for each weakly fair action, a state where it is
        // disabled or one of its steps; for each strongly fair action that is enabled somewhere
        // on the cycle, one of its steps; then return to the entry
        let _ = &off;
        let fen = |p: usize| st.fen(pr.state(p) as usize);
        let mut cyc: Vec<(usize, u32, FMask)> = vec![];
        let mut cur = entry;
        let go = |cyc: &mut Vec<(usize, u32, FMask)>, cur: &mut usize, goal: &dyn Fn(usize) -> bool, edge: &dyn Fn(usize, FMask, u64) -> bool| {
            let p = path_to(&pr, &set, *cur, goal, edge);
            if let Some(&(l, _, _)) = p.last() {
                *cur = l;
            }
            cyc.extend(p);
        };
        let visited = |cyc: &[(usize, u32, FMask)], f: &dyn Fn(usize) -> bool| f(entry) || cyc.iter().any(|&(p, _, _)| f(p));
        for j in 0..prop.nacc {
            let here = |p: usize| prop.nodes[p % pr.q].acc & (1 << j) != 0;
            if !visited(&cyc, &here) {
                go(&mut cyc, &mut cur, &here, &|_, _, _| false);
            }
        }
        // A state of each []<>S part, and a step of each []<>A part
        for x in prop.ae_state {
            let here = |p: usize| pr.holds(x, p, 0, 0);
            if !visited(&cyc, &here) {
                go(&mut cyc, &mut cur, &here, &|_, _, _| false);
            }
        }
        for x in prop.ae_action {
            go(&mut cyc, &mut cur, &|_| false, &|u, f, a| pr.holds(x, u, a, f));
        }
        for (i, (weak, _, _)) in FAIRS.iter().enumerate() {
            let off_here = |p: usize| fen(p) & (1 << i) == 0;
            if !*weak || visited(&cyc, &off_here) {
                continue;
            }
            if c.iter().any(|&p| off_here(p)) {
                go(&mut cyc, &mut cur, &off_here, &|_, _, _| false);
            } else {
                go(&mut cyc, &mut cur, &|_| false, &|_, f, _| f & (1 << i) != 0);
            }
        }
        loop {
            // Back to the entry (at least one step)
            if cur != entry || cyc.is_empty() {
                go(&mut cyc, &mut cur, &|p| p == entry, &|_, _, _| false);
            }
            let mut added = false;
            for (i, (weak, _, _)) in FAIRS.iter().enumerate() {
                let b: FMask = 1 << i;
                let on = |p: usize| fen(p) & b != 0;
                if *weak || !steps.contains(&i) || cyc.iter().any(|&(_, _, f)| f & b != 0) || !visited(&cyc, &on) {
                    continue;
                }
                go(&mut cyc, &mut cur, &|_| false, &|_, f, _| f & b != 0);
                added = true;
            }
            if !added && cur == entry {
                break;
            }
        }
        // Each step of the path from an initial state, by the first step the BFS reached it by
        let mut prefix = vec![];
        let mut y = rank.get(entry).unwrap();
        while y != u32::MAX {
            let (py, v) = (par[y as usize], order[y as usize]);
            let l = if py == u32::MAX {
                u32::MAX
            } else {
                all.succ(order[py as usize], &mut buf);
                buf.iter().find(|x| x.0 == v).unwrap().1
            };
            prefix.push((pr.state(v), l));
            y = py;
        }
        prefix.reverse();
        let cycle: Vec<(u32, u32)> = cyc.iter().map(|&(p, l, _)| (pr.state(p), l)).collect();
        lasso = Some((prefix, cycle));
        true
    });
    lasso
}
/// Prints a lasso as TLC does: the states from an initial state to the entry of the cycle, then
/// the cycle, ending with "Back to state N" (or "Stuttering" if it never leaves the entry state).
/// Stuttering steps inside are not shown.
///
/// The graph keeps, for each fingerprint, the first state reached. With a VIEW or a SYMMETRY that
/// state need not be a successor of the one before it on the lasso, so the lasso is replayed on
/// actual states, as TLC rebuilds a behavior from fingerprints (`lasso_states`).
// ---------------------------------------------------------------- TLC's liveness counterexample
//
// TLC's search for a counterexample (tlc2.tool.liveness: LiveCheck, LiveWorker, DiskGraph), followed
// on the state graph so that the checker prints the lasso TLC prints, for the possible error
// models `TLC_LIVE` lists (see `tlc_live` in tla2rs's live.rs). Its order depends on TLC's
// fingerprints of the states, which `tlc_fp` computes as TLC does with `-fp 0`.

/// A predicate over a state (`S`, `FE`) or a step from it (`A`, `FS`): state atom, action atom,
/// fairness condition i's <<A>>_v enabled, a step of it
#[allow(dead_code)]
enum LP {
    B(bool),
    S(u32),
    A(u32),
    FE(u32),
    FS(u32),
    Not(&'static LP),
    And(&'static [LP]),
    Or(&'static [LP]),
}

impl LP {
    fn eval(&self, sb: u64, fen: FMask, ab: u64, fb: FMask) -> bool {
        match self {
            LP::B(b) => *b,
            LP::S(i) => sb >> i & 1 == 1,
            LP::A(i) => ab >> i & 1 == 1,
            LP::FE(i) => fen >> i & 1 == 1,
            LP::FS(i) => fb >> i & 1 == 1,
            LP::Not(x) => !x.eval(sb, fen, ab, fb),
            LP::And(xs) => xs.iter().all(|x| x.eval(sb, fen, ab, fb)),
            LP::Or(xs) => xs.iter().any(|x| x.eval(sb, fen, ab, fb)),
        }
    }
}

/// A possible error model: indices into check_state / check_action
#[allow(dead_code)]
struct TPem {
    ae_state: &'static [usize],
    ae_action: &'static [usize],
    ea_action: &'static [usize],
}

/// A particle of TLC's tableau (TBGraphNode): the state atoms it requires to hold (or not), the
/// particles that can follow it, and the promises (<> parts) it fulfils, as a bit mask
#[allow(dead_code)]
struct TNode {
    preds: &'static [(u32, bool)],
    nexts: &'static [u32],
    fulfils: u64,
}

/// An order of solution (tlc2.tool.liveness.OrderOfSolution): a tableau or none, its first
/// `init_cnt` particles those of the formula, the number of its promises, the predicates and the
/// possible error models
#[allow(dead_code)]
struct TOos {
    tableau: Option<&'static [TNode]>,
    init_cnt: usize,
    promises: usize,
    check_state: &'static [LP],
    check_action: &'static [LP],
    pems: &'static [TPem],
}

#[allow(dead_code)]
struct TLive {
    oos: &'static [TOos],
}

/// TLC's fingerprint polynomial for `-fp 0` (tlc2.util.FP64.Polys[0])
const FP64_POLY: u64 = 0x911498AE0E66BAD6;

/// TLC's `-fp` chose another polynomial
static OTHER_FP: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn fp64_table() -> &'static [u64; 256] {
    static T: std::sync::OnceLock<[u64; 256]> = std::sync::OnceLock::new();
    T.get_or_init(|| {
        let mut pow = [0u64; 72];
        let mut t: u64 = 1 << 63;
        for p in pow.iter_mut() {
            *p = t;
            t = (t >> 1) ^ if t & 1 != 0 { FP64_POLY } else { 0 };
        }
        let mut tab = [0u64; 256];
        for (j, v) in tab.iter_mut().enumerate() {
            for k in 0..8 {
                if j & (1 << k) != 0 {
                    *v ^= pow[127 - 56 - k];
                }
            }
        }
        tab
    })
}

fn fp_byte(fp: u64, b: u8) -> u64 {
    (fp >> 8) ^ fp64_table()[((b as u64 ^ fp) & 0xFF) as usize]
}

fn fp_int(mut fp: u64, x: i32) -> u64 {
    for b in x.to_le_bytes() {
        fp = fp_byte(fp, b);
    }
    fp
}

/// A value as TLC fingerprints it: functions, tuples and records alike as a list of pairs; a model
/// value by the number TLC gave its name (`TLC_MODEL_VALUES`)
enum TV {
    B(bool),
    I(i64),
    S(String),
    M(i32),
    Set(Vec<TV>),
    Fcn(Vec<(TV, TV)>),
}

impl TV {
    fn fp(&self, fp: u64) -> u64 {
        match self {
            TV::B(b) => fp_byte(fp_byte(fp, 0), if *b { b't' } else { b'f' }),
            TV::I(i) => fp_int(fp_byte(fp, 1), *i as i32),
            TV::M(t) => fp_int(fp_byte(fp, 21), *t),
            TV::S(s) => {
                let u: Vec<u16> = s.encode_utf16().collect();
                let mut fp = fp_int(fp_byte(fp, 3), u.len() as i32);
                for c in u {
                    fp = fp_byte(fp, c as u8);
                }
                fp
            }
            TV::Set(xs) => xs.iter().fold(fp_int(fp_byte(fp, 5), xs.len() as i32), |fp, x| x.fp(fp)),
            TV::Fcn(xs) => xs.iter().fold(fp_int(fp_byte(fp, 9), xs.len() as i32), |fp, (k, v)| v.fp(k.fp(fp))),
        }
    }
}

/// Reads a value as the checker prints it on one line. None for a form not read here.
struct TvParse<'a> {
    b: &'a [u8],
    i: usize,
}

impl TvParse<'_> {
    fn ws(&mut self) {
        while self.i < self.b.len() && (self.b[self.i] as char).is_whitespace() {
            self.i += 1;
        }
    }
    fn eat(&mut self, t: &str) -> bool {
        self.ws();
        if self.b[self.i..].starts_with(t.as_bytes()) {
            self.i += t.len();
            true
        } else {
            false
        }
    }
    fn int(&mut self) -> Option<i64> {
        self.ws();
        let st = self.i;
        if self.i < self.b.len() && self.b[self.i] == b'-' {
            self.i += 1;
        }
        while self.i < self.b.len() && self.b[self.i].is_ascii_digit() {
            self.i += 1;
        }
        std::str::from_utf8(&self.b[st..self.i]).ok()?.parse().ok()
    }
    fn list(&mut self, end: &str) -> Option<Vec<TV>> {
        let mut v = vec![];
        if self.eat(end) {
            return Some(v);
        }
        loop {
            v.push(self.val()?);
            if self.eat(end) {
                return Some(v);
            }
            if !self.eat(",") {
                return None;
            }
        }
    }
    fn val(&mut self) -> Option<TV> {
        self.ws();
        let c = *self.b.get(self.i)?;
        if c.is_ascii_alphabetic() || c == b'_' {
            let st = self.i;
            while self.i < self.b.len() && (self.b[self.i].is_ascii_alphanumeric() || self.b[self.i] == b'_') {
                self.i += 1;
            }
            return match std::str::from_utf8(&self.b[st..self.i]).ok()? {
                "TRUE" => Some(TV::B(true)),
                "FALSE" => Some(TV::B(false)),
                name => TLC_MODEL_VALUES.iter().find(|m| m.0 == name).map(|m| TV::M(m.1)),
            };
        }
        if c == b'-' || c.is_ascii_digit() {
            let lo = self.int()?;
            if self.eat("..") {
                let hi = self.int()?;
                return Some(TV::Set((lo..=hi).map(TV::I).collect()));
            }
            return Some(TV::I(lo));
        }
        if c == b'"' {
            self.i += 1;
            let mut s = String::new();
            loop {
                let ch = std::str::from_utf8(&self.b[self.i..]).ok()?.chars().next()?;
                self.i += ch.len_utf8();
                match ch {
                    '"' => break,
                    '\\' => {
                        let e = *self.b.get(self.i)? as char;
                        self.i += 1;
                        s.push(match e {
                            'n' => '\n',
                            't' => '\t',
                            'r' => '\r',
                            'f' => '\u{c}',
                            e => e,
                        });
                    }
                    ch => s.push(ch),
                }
            }
            return Some(TV::S(s));
        }
        if self.eat("<<") {
            let xs = self.list(">>")?;
            return Some(TV::Fcn(xs.into_iter().enumerate().map(|(i, x)| (TV::I(i as i64 + 1), x)).collect()));
        }
        if self.eat("{") {
            return Some(TV::Set(self.list("}")?));
        }
        if self.eat("[") {
            let mut v = vec![];
            loop {
                self.ws();
                let st = self.i;
                while self.i < self.b.len() && (self.b[self.i].is_ascii_alphanumeric() || self.b[self.i] == b'_') {
                    self.i += 1;
                }
                let name = std::str::from_utf8(&self.b[st..self.i]).ok()?.to_string();
                if name.is_empty() || !self.eat("|->") {
                    return None;
                }
                v.push((TV::S(name), self.val()?));
                if self.eat("]") {
                    return Some(TV::Fcn(v));
                }
                if !self.eat(",") {
                    return None;
                }
            }
        }
        if self.eat("(") {
            let mut v = vec![];
            loop {
                let k = self.val()?;
                if !self.eat(":>") {
                    return None;
                }
                v.push((k, self.val()?));
                if self.eat(")") {
                    return Some(TV::Fcn(v));
                }
                if !self.eat("@@") {
                    return None;
                }
            }
        }
        None
    }
}

/// TLC's fingerprint of a state (TLCStateMut.fingerPrint without VIEW): under a SYMMETRY, that of
/// the smallest of the permuted states in TLC's order of values (as `fresh_fp` with a VIEW)
fn tlc_fp(s: &State) -> Option<u64> {
    let mut best = *s;
    for p in PERMS.iter() {
        let t = perm_state(s, p);
        if tlc_state_cmp(&t, &best).is_lt() {
            best = t;
        }
    }
    let mut fp = FP64_POLY;
    for v in tlc_vals(&best) {
        let mut p = TvParse { b: v.as_bytes(), i: 0 };
        let tv = p.val()?;
        p.ws();
        if p.i != p.b.len() {
            return None;
        }
        fp = tv.fp(fp);
    }
    Some(fp)
}

/// TLC's stack of longs and ints (tlc2.util.MemIntStack), its size counted in ints
struct TStack {
    v: Vec<i64>,
    ints: usize,
}

impl TStack {
    fn pl(&mut self, x: i64) {
        self.v.push(x);
        self.ints += 2;
    }
    fn pi(&mut self, x: i64) {
        self.v.push(x);
        self.ints += 1;
    }
    fn ol(&mut self) -> i64 {
        self.ints -= 2;
        self.v.pop().unwrap()
    }
    fn oi(&mut self) -> i64 {
        self.ints -= 1;
        self.v.pop().unwrap()
    }
}

/// TLC's liveness graph for one order of solution (LiveCheck's LiveChecker and TableauLiveChecker):
/// its nodes (a state, and a particle of the tableau if there is one), each node's transitions in
/// TLC's order (target, check_action bits), whether TLC wrote the node (a node it never wrote is
/// left out of the search), the initial nodes, and the promises each node fulfils
#[derive(Default)]
struct TGraph {
    state: Vec<u32>,
    succ: Vec<Vec<(u32, TBits)>>,
    written: Vec<bool>,
    inits: Vec<u32>,
    fulfils: Vec<u64>,
}

/// TLC's counterexample, printed if TLC's search finds one: Ok(true). The graph's states have no
/// VIEW or SYMMETRY folded in. Each state's transitions come in the order TLC's liveness graph
/// keeps them: its distinct successors and itself (the stuttering step) out of a hash table keyed
/// by TLC's fingerprint (tlc2.util.SetOfStates, whose starting size grows over the search). For
/// each order of solution and each of its possible error models in turn, TLC's depth-first search
/// for components (LiveWorker.checkSccs) from the initial nodes, skipping a step that breaks a
/// <>[]A part; then for the first component that has every []<> part and fulfils every promise of
/// the tableau, the path to it (getPath: breadth first from the initial nodes), and the cycle
/// (LiveWorker.dfsPostFix: greedily to the steps and nodes that fulfil the []<> parts and the
/// promises, then bfsPostFix: back to the start).
fn tlc_lasso(g: &Graph, st: &Steps, inits: &[u32], selfs: &[(u32, u32)]) -> Result<bool, &'static str> {
    let tl = match &TLC_LIVE {
        Ok(t) => t,
        Err(m) => return Err(m),
    };
    if HAS_VIEW {
        return Err("VIEW");
    }
    if flag(&OTHER_FP) {
        return Err("a fingerprint polynomial other than that of -fp 0");
    }
    let n = g.states.len();
    let mut tfp = Vec::with_capacity(n);
    for i in 0..n {
        match tlc_fp(&g.state(i)) {
            Some(f) => tfp.push(f),
            None => return Err("a value tla2rs does not fingerprint as TLC does"),
        }
    }
    let mut self_at: Vec<Vec<u32>> = vec![vec![]; n];
    for &(s, k) in selfs {
        self_at[s as usize].push(k);
    }
    // The order of TLC's set of each state's successors with the state itself put last: (target,
    // action atoms, fairness steps). And, kept only for a tableau, the successors as generated
    // (those in the model, itself included where an action yields it).
    let tableau = tl.oos.iter().any(|o| o.tableau.is_some());
    let mut gen: Vec<Vec<(u32, u64, FMask)>> = Vec::with_capacity(if tableau { n } else { 0 });
    let mut order: Vec<Vec<(u32, u64, FMask)>> = Vec::with_capacity(n);
    let mut mult = 1usize;
    for s in 0..n {
        let mut puts: Vec<(u32, u64, FMask)> = vec![];
        let r = st.edges(s);
        let mut k = 0u32;
        let mut sa = self_at[s].iter().peekable();
        for e in r.clone() {
            while sa.peek().is_some_and(|&&x| x == k) {
                puts.push((s as u32, st.stut(s), 0));
                sa.next();
            }
            let (t, _, a, f) = st.edge(e);
            puts.push((t, a, f));
            k += 1;
        }
        for _ in sa {
            puts.push((s as u32, st.stut(s), 0));
        }
        let target = |i: usize| if i < puts.len() { puts[i].0 } else { s as u32 };
        let mut len = mult * 16;
        let mut tab: Vec<Option<usize>> = vec![None; len];
        let mut count = 0usize;
        let slot = |fp: u64, len: usize| ((fp as u32 & 0x7FFF_FFFF) as usize) % len;
        for i in 0..=puts.len() {
            if count >= len / 2 {
                let old = std::mem::take(&mut tab);
                len = 2 * len + 1;
                tab = vec![None; len];
                for o in old.into_iter().flatten() {
                    let mut l = slot(tfp[target(o) as usize], len);
                    while tab[l].is_some() {
                        l = (l + 1) % len;
                    }
                    tab[l] = Some(o);
                }
            }
            let t = target(i);
            let mut l = slot(tfp[t as usize], len);
            loop {
                match tab[l] {
                    None => {
                        tab[l] = Some(i);
                        count += 1;
                        break;
                    }
                    Some(o) if target(o) == t => break,
                    Some(_) => l = (l + 1) % len,
                }
            }
        }
        if len > mult * 16 {
            mult += 1;
        }
        order.push(tab.into_iter().flatten().map(|o| if o < puts.len() { puts[o] } else { (s as u32, st.stut(s), 0) }).collect());
        if tableau {
            gen.push(puts);
        }
    }
    for oos in tl.oos {
        let cs: Vec<TBits> = (0..n)
            .map(|s| oos.check_state.iter().enumerate().fold(0, |b, (j, p)| b | (p.eval(st.sbits(s), st.fen(s), 0, 0) as TBits) << j))
            .collect();
        let cact = |s: usize, ab: u64, fb: FMask| -> TBits {
            oos.check_action.iter().enumerate().fold(0, |b, (j, p)| b | (p.eval(st.sbits(s), st.fen(s), ab, fb) as TBits) << j)
        };
        let pg = match oos.tableau {
            None => TGraph {
                state: (0..n as u32).collect(),
                succ: (0..n)
                    .map(|s| {
order[s].iter().map(|&(t, ab, fb)| (t, cact(s, ab, fb))).collect()
                    })
                    .collect(),
                written: vec![true; n],
                inits: inits.to_vec(),
                fulfils: vec![],
            },
            Some(tab) => tableau_graph(n, tab, oos.init_cnt, inits, st, &order, &gen, &cact),
        };
        let cs: Vec<TBits> = pg.state.iter().map(|&s| cs[s as usize]).collect();
        for pem in oos.pems {
            if let Some((prefix, postfix)) = tlc_search(&pg, &cs, pem, oos.promises)? {
                tlc_print_lasso(g, &tfp, &prefix, &postfix)?;
                return Ok(true);
            }
        }
    }
    Ok(false)
}

/// TLC's liveness graph with a tableau (LiveCheck.TableauLiveChecker): a node per state and
/// particle consistent with it. The initial nodes: each initial state with each of the formula's
/// particles consistent with it. Then each state in turn, as TLC's search takes it, gets for each
/// of its nodes so far a transition to each successor in the set's order (the state itself
/// included) with each particle that can follow and is consistent with it. A node new to a state
/// already taken gets its transitions at once: the stuttering step first, then the successors as
/// each action generates them; TLC writes it only if it has some.
#[allow(clippy::too_many_arguments)]
fn tableau_graph(
    n: usize,
    tab: &[TNode],
    init_cnt: usize,
    inits: &[u32],
    st: &Steps,
    order: &[Vec<(u32, u64, FMask)>],
    gen: &[Vec<(u32, u64, FMask)>],
    cact: &dyn Fn(usize, u64, FMask) -> TBits,
) -> TGraph {
    let cons = |ti: usize, s: usize| tab[ti].preds.iter().all(|&(a, p)| (st.sbits(s) >> a & 1 == 1) == p);
    // The nodes of each state, in the order recorded: (particle, node)
    let mut rows: Vec<Vec<(u32, u32)>> = vec![vec![]; n];
    let mut pg = TGraph::default();
    let mut tidx: Vec<u32> = vec![];
    let new_node = |pg: &mut TGraph, tidx: &mut Vec<u32>, rows: &mut Vec<Vec<(u32, u32)>>, s: u32, ti: u32| -> u32 {
        let id = pg.state.len() as u32;
        pg.state.push(s);
        tidx.push(ti);
        pg.succ.push(vec![]);
        pg.written.push(false);
        pg.fulfils.push(tab[ti as usize].fulfils);
        rows[s as usize].push((ti, id));
        id
    };
    for &s in inits {
        for ti in 0..init_cnt {
            if cons(ti, s as usize) {
                let id = new_node(&mut pg, &mut tidx, &mut rows, s, ti as u32);
                pg.inits.push(id);
            }
        }
    }
    let mut done = vec![false; n];
    // A transition from `node` (of state s) to state t with particle ti1 unless it has one: the
    // node of t if new, and whether it is new
    let link = |pg: &mut TGraph, tidx: &mut Vec<u32>, rows: &mut Vec<Vec<(u32, u32)>>, node: u32, t: u32, ti1: u32, bits: TBits| -> Option<(u32, bool)> {
        let ex = rows[t as usize].iter().find(|x| x.0 == ti1).map(|x| x.1);
        if let Some(e) = ex {
            if pg.succ[node as usize].iter().any(|x| x.0 == e) {
                return None;
            }
        }
        let id = match ex {
            Some(e) => e,
            None => new_node(pg, tidx, rows, t, ti1),
        };
        pg.succ[node as usize].push((id, bits));
        Some((id, ex.is_none()))
    };
    for s in 0..n {
        done[s] = true;
        let mine = rows[s].clone();
        for &(ti0, node0) in &mine {
            for &(t, ab, fb) in &order[s] {
                let tdone = done[t as usize];
                for &ti1 in tab[ti0 as usize].nexts {
                    if !cons(ti1 as usize, t as usize) {
                        continue;
                    }
                    let Some((id, new)) = link(&mut pg, &mut tidx, &mut rows, node0, t, ti1, cact(s, ab, fb)) else { continue };
                    if !(new && tdone) {
                        continue;
                    }
                    // The node's transitions at once (depth first, as TLC recurses): step 0 is
                    // the stuttering one, step k + 1 the k-th generated
                    let mut stack: Vec<(u32, usize, usize)> = vec![(id, 0, 0)];
                    while let Some(f) = stack.last_mut() {
                        let (node, s1) = (f.0, pg.state[f.0 as usize] as usize);
                        let nexts = tab[tidx[node as usize] as usize].nexts;
                        if f.1 > gen[s1].len() {
                            pg.written[node as usize] = !pg.succ[node as usize].is_empty();
                            stack.pop();
                            continue;
                        }
                        if f.2 >= nexts.len() {
                            f.1 += 1;
                            f.2 = 0;
                            continue;
                        }
                        let (t2, ab2, fb2) = if f.1 == 0 { (s1 as u32, st.stut(s1), 0) } else { gen[s1][f.1 - 1] };
                        let ti2 = nexts[f.2];
                        f.2 += 1;
                        if !cons(ti2 as usize, t2 as usize) {
                            continue;
                        }
                        if let Some((id2, true)) = link(&mut pg, &mut tidx, &mut rows, node, t2, ti2, cact(s1, ab2, fb2)) {
                            if done[t2 as usize] {
                                stack.push((id2, 0, 0));
                            }
                        }
                    }
                }
            }
            pg.written[node0 as usize] = true;
        }
    }
    pg
}

/// TLC's search on its liveness graph for one possible error model (LiveWorker.checkSccs,
/// checkComponent, getPath, dfsPostFix and bfsPostFix): the nodes from an initial node to the
/// start of the component found, and the nodes of the cycle as TLC lists them (printed from the
/// last), as states. None if no component is a counterexample.
#[allow(clippy::type_complexity)]
fn tlc_search(pg: &TGraph, cs: &[TBits], pem: &TPem, promises: usize) -> Result<Option<(Vec<u32>, Vec<u32>)>, &'static str> {
    let gs = &pg.succ;
    let n = pg.state.len();
    const MAX_PTR: i64 = 0x4000_0000_0000_0000;
    const MAX_LINK: i64 = i64::MAX;
    const MARK: i64 = -42;
    let ea = |b: TBits| pem.ea_action.iter().all(|&j| b >> j & 1 == 1);
    // A node TLC did not write has no link: it is not searched
    let mut link: Vec<i64> = pg.written.iter().map(|&w| if w { 0 } else { -1 }).collect();
    let mut queue: std::collections::VecDeque<(u32, i64)> =
        pg.inits.iter().filter(|&&s| pg.written[s as usize]).map(|&s| (s, 0)).collect();
    let mut com: Vec<u32> = vec![];
    let mut found = None;
    'search: while let Some((s0, loc0)) = queue.pop_front() {
        let mut dfs = TStack { v: vec![], ints: 0 };
        dfs.pl(s0 as i64);
        dfs.pi(-1);
        dfs.pl(loc0);
        dfs.pl(MAX_PTR);
        let mut new_link = MAX_PTR;
        while dfs.ints >= 7 {
            let low = dfs.ol();
            let loc = dfs.ol();
            dfs.oi();
            let cur = dfs.ol() as usize;
            if loc == MARK {
                if link[cur] == low {
                    // LiveWorker.checkComponent
                    let top = com.pop().unwrap() as usize;
                    let stutters = || gs[top].iter().find(|x| x.0 as usize == top).is_some_and(|x| ea(x.1));
                    if top == cur && !stutters() {
                        link[cur] = MAX_LINK;
                    } else {
                        let mut c = vec![top as u32];
                        link[top] = MAX_LINK;
                        let mut y = top;
                        while y != cur {
                            y = com.pop().unwrap() as usize;
                            link[y] = MAX_LINK;
                            c.push(y as u32);
                        }
                        let mut inc = vec![false; n];
                        c.iter().for_each(|&y| inc[y as usize] = true);
                        let aes = pem.ae_state.iter().all(|&j| c.iter().any(|&y| cs[y as usize] >> j & 1 == 1));
                        let aea = pem.ae_action.iter().all(|&j| {
                            c.iter().any(|&y| gs[y as usize].iter().any(|&(t, b)| inc[t as usize] && ea(b) && b >> j & 1 == 1))
                        });
                        let prom = (0..promises).all(|p| c.iter().any(|&y| pg.fulfils[y as usize] >> p & 1 == 1));
                        if aes && aea && prom {
                            found = Some((cur, c, inc));
                            break 'search;
                        }
                    }
                }
                let plow = dfs.ol();
                dfs.pl(plow.min(low));
            } else if link[cur] < MAX_PTR {
                link[cur] = new_link;
                dfs.pl(low);
                dfs.pl(cur as i64);
                dfs.pi(-1);
                dfs.pl(MARK);
                com.push(cur as u32);
                let mut next_low = new_link;
                new_link += 1;
                for &(t, b) in &gs[cur] {
                    let nl = link[t as usize];
                    if nl < 0 {
                        continue;
                    }
                    if ea(b) {
                        if nl < MAX_PTR {
                            dfs.pl(t as i64);
                            dfs.pi(-1);
                            dfs.pl(nl);
                        } else {
                            next_low = next_low.min(nl);
                        }
                    } else if nl < MAX_PTR {
                        queue.push_back((t, nl));
                    }
                }
                dfs.pl(next_low);
            } else {
                dfs.pl(low.min(link[cur]));
            }
        }
    }
    let Some((start, comp, inc)) = found else { return Ok(None) };
    // The path from an initial node (getPath)
    let mut prefix: Vec<u32> = vec![];
    if pg.inits.contains(&(start as u32)) {
        prefix.push(start as u32);
    } else {
        let mut par = vec![u32::MAX; n];
        let mut vis = vec![false; n];
        let mut q: std::collections::VecDeque<u32> = std::collections::VecDeque::new();
        for &s in &pg.inits {
            if pg.written[s as usize] {
                vis[s as usize] = true;
                q.push_back(s);
            }
        }
        'bfs: while let Some(c) = q.pop_front() {
            for &(t, _) in &gs[c as usize] {
                if t == c {
                    continue;
                }
                if t as usize == start {
                    let mut y = c;
                    prefix.push(t);
                    loop {
                        prefix.push(y);
                        if par[y as usize] == u32::MAX {
                            break;
                        }
                        y = par[y as usize];
                    }
                    break 'bfs;
                }
                if pg.written[t as usize] && !vis[t as usize] {
                    vis[t as usize] = true;
                    par[t as usize] = c;
                    q.push_back(t);
                }
            }
        }
        if prefix.is_empty() {
            return Err("no path to the component");
        }
        prefix.reverse();
    }
    // LiveWorker.dfsPostFix
    let mut seen = vec![false; n];
    let mut cnt = pem.ae_state.len() + pem.ae_action.len() + promises;
    let mut aes = vec![false; pem.ae_state.len()];
    let mut aea = vec![false; pem.ae_action.len()];
    let mut prom = vec![false; promises];
    let mut stack: Vec<usize> = vec![];
    let mut cur = start;
    seen[cur] = true;
    while cnt > 0 {
        let cnt0 = cnt;
        loop {
            for (i, &j) in pem.ae_state.iter().enumerate() {
                if !aes[i] && cs[cur] >> j & 1 == 1 {
                    aes[i] = true;
                    cnt -= 1;
                }
            }
            for (p, done) in prom.iter_mut().enumerate() {
                if !*done && pg.fulfils[cur] >> p & 1 == 1 {
                    *done = true;
                    cnt -= 1;
                }
            }
            if cnt == 0 {
                break;
            }
            let (mut next1, mut next2) = (None, None);
            let mut unvisited = false;
            let cnt1 = cnt;
            let mut took = None;
            for &(t, b) in &gs[cur] {
                let t = t as usize;
                if inc[t] {
                    if !ea(b) {
                        continue;
                    }
                    next1 = Some(t);
                    for (i, &j) in pem.ae_action.iter().enumerate() {
                        if !aea[i] && b >> j & 1 == 1 {
                            aea[i] = true;
                            cnt -= 1;
                        }
                    }
                }
                if cnt < cnt1 {
                    took = Some(t);
                    break;
                }
                if inc[t] && !seen[t] {
                    unvisited = true;
                    next2 = Some(t);
                }
            }
            if let Some(t) = took {
                stack.push(cur);
                cur = t;
                seen.iter_mut().for_each(|x| *x = false);
                break;
            }
            if cnt < cnt0 {
                stack.push(cur);
                cur = next1.ok_or("no step in the component")?;
                seen.iter_mut().for_each(|x| *x = false);
                break;
            }
            while !unvisited {
                cur = stack.pop().ok_or("the search for the cycle ran out of nodes")?;
                if let Some(&(t, _)) = gs[cur].iter().find(|&&(t, _)| inc[t as usize] && !seen[t as usize]) {
                    unvisited = true;
                    next2 = Some(t as usize);
                }
            }
            stack.push(cur);
            cur = next2.unwrap();
            seen[cur] = true;
        }
    }
    // LiveWorker.bfsPostFix: breadth first over the states of the component, each with all its
    // nodes in the component (in the order the component was taken off the stack), back to the
    // start node
    let end = cur;
    let mut postfix: Vec<u32> = vec![];
    if end != start {
        let mut rows: std::collections::HashMap<u32, Vec<usize>> = std::collections::HashMap::new();
        for &y in &comp {
            rows.entry(pg.state[y as usize]).or_default().push(y as usize);
        }
        let mut sseen: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut par: std::collections::HashMap<u32, Option<u32>> = std::collections::HashMap::new();
        let mut q: std::collections::VecDeque<(u32, u32)> = std::collections::VecDeque::new();
        let end_s = pg.state[end];
        let (mut cur_s, mut pl) = (end_s, None);
        sseen.insert(end_s);
        'b: loop {
            for &x in &rows[&cur_s] {
                for &(t, b) in &gs[x] {
                    let t = t as usize;
                    if t == x || !ea(b) {
                        continue;
                    }
                    if t == start {
                        let (mut y, mut p) = (cur_s, pl);
                        while y != end_s {
                            postfix.push(y);
                            let pn: u32 = p.ok_or("no way back")?;
                            y = pn;
                            p = par[&pn];
                        }
                        postfix.push(end_s);
                        break 'b;
                    }
                    let ts = pg.state[t];
                    if rows.contains_key(&ts) && sseen.insert(ts) {
                        q.push_back((ts, cur_s));
                    }
                }
            }
            par.insert(cur_s, pl);
            let (y, p) = q.pop_front().ok_or("no way back to the start of the cycle")?;
            cur_s = y;
            pl = Some(p);
        }
    }
    // As states: the path, and the cycle (bfsPostFix's states, then the stack of dfsPostFix)
    let prefix: Vec<u32> = prefix.iter().map(|&x| pg.state[x as usize]).collect();
    postfix.extend(stack.iter().rev().map(|&x| pg.state[x]));
    Ok(Some((prefix, postfix)))
}

/// Prints TLC's lasso: the prefix, then the cycle (from the last of `postfix`), each state rebuilt
/// from its predecessor by the first action that yields it (Tool.getState), a state equal to the
/// one before it left out
fn tlc_print_lasso(g: &Graph, tfp: &[u64], prefix: &[u32], postfix: &[u32]) -> Result<(), &'static str> {
    let start = *prefix.last().unwrap() as usize;
    let _quiet = Capturing::start();
    let mut buf: Vec<(State, u32)> = vec![];
    // Under a SYMMETRY, the first successor of the node's fingerprint, which can be another
    // member of the class than the state the graph keeps
    let mut next = |cur: &State, to: usize| -> Option<(State, u32)> {
        let _ = successors(cur, &mut buf, true);
        if PERMS.is_empty() {
            buf.iter().find(|x| pack(&x.0).is_some_and(|w| w == g.states.get(to))).copied()
        } else {
            buf.iter().find(|x| tlc_fp(&x.0) == Some(tfp[to])).copied()
        }
    };
    let mut out: Vec<(State, u32)> = vec![(g.state(prefix[0] as usize), u32::MAX)];
    let mut at = prefix[0] as usize;
    for &y in &prefix[1..] {
        if y as usize != at {
            let t = next(&out[out.len() - 1].0, y as usize).ok_or("a step TLC cannot rebuild")?;
            out.push(t);
            at = y as usize;
        }
    }
    let cycle_no = out.len();
    for &y in postfix.iter().rev() {
        if y as usize != at {
            let t = next(&out[out.len() - 1].0, y as usize).ok_or("a step TLC cannot rebuild")?;
            out.push(t);
            at = y as usize;
        }
    }
    let back = if at == start {
        None
    } else {
        Some(next(&out[out.len() - 1].0, start).ok_or("a step TLC cannot rebuild")?)
    };
    drop(_quiet);
    let name = |l: u32| if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
    let mut texts = vec![];
    for (i, (s, l)) in out.iter().enumerate() {
        print_step(&format!("State {}: <{}>", i + 1, name(*l)), s, (i > 0).then(|| &out[i - 1].0));
        texts.push(show(s));
    }
    match back {
        None => {
            println!("State {}: Stuttering", cycle_no + 1);
            write_lasso_check(&texts, None);
        }
        Some((t, l)) => {
            println!("Back to state {cycle_no}: <{}>", name(l));
            // Under a SYMMETRY the step back can reach another member of the class, which
            // the lasso check folds into the state returned to
            let folded = (t != out[cycle_no - 1].0).then(|| show(&t));
            write_lasso_check(&texts, Some((cycle_no, folded)));
        }
    }
    Ok(())
}

fn print_lasso(g: &Graph, prefix: &[(u32, u32)], cycle: &[(u32, u32)]) {
    let name = |l: u32| if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
    let mut shown: Vec<(u32, u32)> = vec![];
    for &(s, l) in prefix {
        if shown.last().is_some_and(|x| x.0 == s) && (l == STUTTER || l == u32::MAX) {
            continue;
        }
        shown.push((s, l));
    }
    let entry_no = shown.len();
    let entry = shown[entry_no - 1].0;
    let mut moves: Vec<(u32, u32)> = vec![];
    let mut at = entry;
    for &(s, l) in cycle {
        if s == at && l == STUTTER {
            continue;
        }
        moves.push((s, l));
        at = s;
    }
    // The lasso's nodes in order, without the last step back to the entry
    let back_label = (!moves.is_empty()).then(|| moves[moves.len() - 1].1);
    let mut path = shown.clone();
    if back_label.is_some() {
        path.extend_from_slice(&moves[..moves.len() - 1]);
    }
    let (states, ret) = lasso_states(g, &path, entry_no, back_label);
    // The states shown, for -lassocheck
    let mut texts: Vec<String> = vec![];
    for (i, &(s, l)) in states.iter().enumerate() {
        print_step(&format!("State {}: <{}>", i + 1, name(l)), &s, (i > 0).then(|| &states[i - 1].0));
        texts.push(show(&s));
    }
    match ret {
        None => {
            println!("State {}: Stuttering", states.len() + 1);
            write_lasso_check(&texts, None);
        }
        Some((back, l, folded)) => {
            println!("Back to state {back}: <{}>", name(l));
            write_lasso_check(&texts, Some((back, folded.map(|t| show(&t)))));
        }
    }
}

/// The states of a lasso through the graph's nodes `path` (with the action of each step), whose
/// cycle starts at the node numbered `entry` (from 1) and returns to it by a step of action `back`
/// (none: it ends stuttering), replayed on actual states: from the first state, an initial one,
/// each step takes the successor whose fingerprint is the next node's, by the same action if one
/// is. Without a VIEW, the state the cycle returns to has the fingerprint of the entry but may be
/// another member of its symmetry class, so the cycle is followed again from there until it
/// returns to a state it went through at the entry (at most once per permutation). With a VIEW the
/// actual states need not repeat at all (a view can leave out a counter that only grows), so the
/// lasso returns to its entry under the VIEW: the result names the successor it returns by, which
/// the lasso check folds into the entry as TLC does. If a step has no such successor (TLC cannot
/// rebuild such a behavior either), the states the graph keeps are shown instead.
/// Returns the states, and the number of the state returned to, the action, and that successor.
#[allow(clippy::type_complexity)]
fn lasso_states(g: &Graph, path: &[(u32, u32)], entry: usize, back: Option<u32>) -> (Vec<(State, u32)>, Option<(usize, u32, Option<State>)>) {
    let kept = || {
        let states: Vec<(State, u32)> = path.iter().map(|&(s, l)| (g.state(s as usize), l)).collect();
        (states, back.map(|l| (entry, l, None)))
    };
    if !HAS_VIEW && PERMS.is_empty() {
        return kept();
    }
    let _quiet = Capturing::start();
    let fp_of = |s: u32| {
        let w = g.states.get(s as usize);
        state_fp(&unpack(&w), &w)
    };
    let mut buf: Vec<(State, u32)> = vec![];
    let mut step = |cur: &State, want: Fp, l: u32| -> Option<(State, u32)> {
        let _ = successors(cur, &mut buf, true);
        let fits = |t: &State| pack(t).is_some_and(|w| state_fp(t, &w) == want);
        buf.iter().find(|x| x.1 == l && fits(&x.0)).or_else(|| buf.iter().find(|x| fits(&x.0))).copied()
    };
    let mut out = vec![(g.state(path[0].0 as usize), path[0].1)];
    for &(s, l) in &path[1..] {
        let Some(t) = step(&out[out.len() - 1].0, fp_of(s), l) else { return kept() };
        out.push(t);
    }
    let Some(lb) = back else { return (out, None) };
    let entry_fp = fp_of(path[entry - 1].0);
    // The states at the entry on each round, by their number
    let mut entries = vec![entry];
    for _ in 0..=PERMS.len() {
        let Some((y, _)) = step(&out[out.len() - 1].0, entry_fp, lb) else { return kept() };
        let wy = pack(&y);
        if let Some(&k) = entries.iter().find(|&&k| pack(&out[k - 1].0) == wy) {
            return (out, Some((k, lb, None)));
        }
        if HAS_VIEW {
            return (out, Some((entry, lb, Some(y))));
        }
        out.push((y, lb));
        entries.push(out.len());
        for &(s, l) in &path[entry..] {
            let Some(t) = step(&out[out.len() - 1].0, fp_of(s), l) else { return kept() };
            out.push(t);
        }
    }
    kept()
}

/// With `-lassocheck DIR`, writes DIR/Tla2rsLasso.tla and .cfg: a spec whose only behavior is the
/// lasso `states` (as printed), returning to state `back` (1-based) or ending stuttering, for TLC
/// to confirm that it is a behavior of the spec that violates the properties (see lasso.rs in
/// tla2rs)
fn write_lasso_check(states: &[String], back: Option<(usize, Option<String>)>) {
    let args: Vec<String> = std::env::args().collect();
    let Some(dir) = args.iter().position(|a| a == "-lassocheck").and_then(|i| args.get(i + 1)) else { return };
    let [module, pre, post, cfg, fold] = match LASSO_CHECK {
        Ok(parts) => parts,
        Err(why) => {
            println!("The lasso check is not written: {why}.");
            return;
        }
    };
    let indent = |t: &str| t.lines().map(|l| format!("  {l}\n")).collect::<String>();
    // The state with its variables primed: `/\ x = v` (or `x = v` for a single variable) starts
    // each variable's lines
    let primed = |t: &str| {
        t.lines()
            .enumerate()
            .map(|(i, l)| if l.starts_with("/\\ ") || i == 0 { l.replacen(" = ", "' = ", 1) } else { l.to_string() })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let folded = back.as_ref().and_then(|b| b.1.as_ref());
    let tlc = states.iter().chain(folded).any(|t| t.contains(":>") || t.contains("@@"));
    let mut o = format!("---- MODULE Tla2rsLasso ----\nEXTENDS {module}{}\n{pre}", if tlc { ", TLC" } else { "" });
    for (i, t) in states.iter().enumerate() {
        o += &format!("Tla2rsState{} ==\n{}Tla2rsGo{} ==\n{}", i + 1, indent(t), i + 1, indent(&primed(t)));
    }
    // A lasso that returns to its entry under the VIEW only steps to the successor it returns by,
    // which the VIEW in the cfg folds into the entry
    if let Some(t) = folded {
        o += &format!("Tla2rsGoBack ==\n{}", indent(&primed(t)));
    }
    o += "Tla2rsStep ==\n";
    let n = states.len();
    for i in 1..=n {
        let to = if i < n { i + 1 } else { back.as_ref().map_or(n, |b| b.0) };
        let go = if i == n && folded.is_some() { "Tla2rsGoBack".to_string() } else { format!("Tla2rsGo{to}") };
        o += &format!("  \\/ tla2rsAt = {i} /\\ tla2rsAt' = {to} /\\ {go}\n");
    }
    o += post;
    o += "====\n";
    let cfg = if folded.is_some() { format!("{cfg}{fold}") } else { cfg.to_string() };
    let dir = std::path::Path::new(dir);
    let written = std::fs::write(dir.join("Tla2rsLasso.tla"), o).and_then(|_| std::fs::write(dir.join("Tla2rsLasso.cfg"), cfg));
    if let Err(e) = written {
        eprintln!("cannot write the lasso check to {}: {e}", dir.display());
    }
}
"##;
