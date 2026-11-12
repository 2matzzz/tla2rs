//! Runtime support pasted into every generated checker. The generated code depends on no external
//! crates.
//!
//! - States are bit-packed (`Packed`) into a flat array that serves as both the BFS queue and the
//!   record used to rebuild traces.
//! - The visited set stores only 64-bit fingerprints (the same approach as TLC). When a state fits
//!   in 64 bits, the fingerprint is invertible, so there are no collisions.

pub const RUNTIME: &str = r##"
// ---------------------------------------------------------------- runtime (tla2rs)

/// A search thread, with a stack sized for the states it copies (a state holds its sequences and
/// sets inline, so long sequences make large states)
fn spawn_worker<'s, 'e, F, T>(sc: &'s std::thread::Scope<'s, 'e>, f: F) -> std::thread::ScopedJoinHandle<'s, T>
where
    F: FnOnce() -> T + Send + 's,
    T: Send + 's,
{
    let stack = (64 * std::mem::size_of::<State>()).max(16 << 20);
    std::thread::Builder::new().stack_size(stack).spawn_scoped(sc, f).expect("cannot start a search thread")
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
        arith_error("The second argument of \\div is 0.".into());
    }
    let q = a / b;
    if a % b != 0 && ((a < 0) != (b < 0)) { q - 1 } else { q }
}

#[inline]
fn tla_mod(a: i64, b: i64) -> i64 {
    if b <= 0 {
        arith_error(format!("The second argument of % should be a positive number, but instead it is: {b}"));
    }
    a.rem_euclid(b)
}

/// An evaluation error. Raised via panic, caught outside state expansion, and reported with a
/// trace.
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
                    eval_error(format!("the domain of a function or bag grew beyond {N} elements; raise the capacity with `Cardinality(DOMAIN f) <= K` in TypeDecl / TypeOK or -setcap"));
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

#[cold]
fn eval_error(msg: String) -> ! {
    std::panic::panic_any(EvalErr::Other(msg))
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
        EvalErr::Other(_) => 75,
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
            EvalErr::Type(m) | EvalErr::Arith(m) | EvalErr::Assert(m) | EvalErr::Other(m) => m,
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
    matches!(e, EvalErr::Arith(_) | EvalErr::Assert(_))
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

struct Graph {
    states: Vec<Packed>,
    /// (parent index, label). Initial states have (u32::MAX, u32::MAX).
    parent: Vec<(u32, u32)>,
    /// Per state, bit i: state atom i of the temporal properties holds (liveness only)
    sbits: Vec<u64>,
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

/// `check_invariants`, with an evaluation error returned along with the invariant that raised it.
fn eval_invariants(s: &State) -> Result<Option<&'static str>, (&'static str, EvalErr)> {
    match std::panic::catch_unwind(|| check_invariants(s)) {
        Ok(v) => Ok(v),
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

/// TLC checks the invariants on a successor that violates the CONSTRAINT too (every time it is
/// generated; it is counted as generated but never added or explored). Returns what stops the
/// search, if anything.
fn check_out_of_model(t: &State) -> Option<SMsg> {
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

/// Liveness data collected during expansion.
#[derive(Default)]
struct LiveChunk {
    /// (source, target fingerprint, label, action atoms that hold on the step, fairness conditions
    /// whose <<A>>_v the step is). Self-loops are left out: the stuttering step every state has
    /// covers them.
    edges: Vec<(u32, Fp, u32, u64, u64)>,
    /// (state, fairness conditions whose <<A>>_v is enabled there, action atoms that hold on its
    /// stuttering step, state atoms evaluated when it is expanded)
    en: Vec<(u32, u64, u64, u64)>,
    /// Working storage: the successors of the state being expanded that became edges, and those
    /// that are new
    pend: Vec<usize>,
    newk: Vec<usize>,
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
    let s = unpack(&g.states[head]);
    let failed = successors(&s, buf, careful);
    if failed.is_none() && buf.is_empty() && check_deadlock {
        return Some(Found::Deadlock(head as u32));
    }
    let sfp = if LIVENESS { state_fp(&s, &g.states[head]) } else { 0 };
    let sfp_dump = if dumping() { state_fp(&s, &g.states[head]) } else { 0 };
    let first_edge = c.live.edges.len();
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
                dump_unpacked(&mut c.dump, sfp_dump, &t);
            }
            return Some(Found::Succ(head as u32, t, l, pack_failed(0, t, l).msg, true));
        };
        let tfp = state_fp(&t, &w);
        if dumping() {
            dump_edge(&mut c.dump, sfp_dump, &tfp);
        }
        if LIVENESS && tfp != sfp {
            // Its atoms are evaluated with fairness, after the successors (as TLC does)
            c.live.edges.push((head as u32, tfp, l, 0, 0));
            c.live.pend.push(k);
        }
        if seen.insert(tfp) {
            if dumping() {
                dump_node(&mut c.dump, &tfp, &t, false);
            }
            c.states.push(w);
            c.parent.push((head as u32, l));
            match eval_invariants(&t) {
                Ok(None) => {}
                Ok(Some(inv)) => return Some(Found::New(me, c.states.len() - 1, SMsg::Inv(inv))),
                Err((inv, e)) => return Some(Found::New(me, c.states.len() - 1, SMsg::InvEval(inv, e))),
            }
            if LIVENESS {
                c.live.newk.push(k);
            }
        }
        if let Some(m) = act {
            return Some(Found::Succ(head as u32, t, l, m, true));
        }
    }
    if let Some(p) = failed {
        raise_next(p);
    }
    // After the successors, in TLC's order: the action atoms and fairness steps of each step
    // (including stuttering), then the state atoms of this state that are not in the tableau and
    // which fair actions are enabled, then the tableau's state atoms of the new successors
    if LIVENESS {
        for j in 0..c.live.pend.len() {
            let t = &buf[c.live.pend[j]].0;
            match step_bits(&s, t) {
                Ok((a, f)) => {
                    let e = &mut c.live.edges[first_edge + j];
                    e.3 = a;
                    e.4 = f;
                }
                Err(m) => return Some(Found::Live(m)),
            }
        }
        let stut = match step_bits(&s, &s) {
            Ok((a, _)) => a,
            Err(m) => return Some(Found::Live(m)),
        };
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut en = 0u64;
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
        c.live.en.push((head as u32, en, stut, cbits));
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
fn step_bits(s: &State, t: &State) -> Result<(u64, u64), SMsg> {
    let r = std::panic::catch_unwind(|| {
        let mut a = 0u64;
        for (i, f) in AATOMS.iter().enumerate() {
            if f(s, t) {
                a |= 1 << i;
            }
        }
        let mut st = 0u64;
        for (i, (_, _, step)) in FAIRS.iter().enumerate() {
            if step(s, t) {
                st |= 1 << i;
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
    };
    let mut buf: Vec<(State, u32)> = Vec::with_capacity(64);
    for head in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
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

// ---------------------------------------------------------------- printing values as TLC does

/// TLC's pretty printer (`tlc2.pprint`, called by `Values.ppr` with width 80 on each variable's
/// value when it prints a state). It parses the value's text and breaks it over lines when it is
/// wider than 80 columns; if the text does not parse (TLC's parser does not know escaped quotes in
/// strings or `_` in names), it is printed as is. Ported as written, quirks included.
fn ppr(s: &str) -> String {
    let c: Vec<char> = s.chars().collect();
    match pp_parse(&c, 0) {
        Some(n) if n.last + 1 >= c.len() => pp_format(&c, &n, 80, 0, "").unwrap_or_else(|| s.to_string()),
        _ => s.to_string(),
    }
}

/// A node of TLC's parse tree of a value: its kind (Node.CONSTANT .. Node.SUBSET), the first and
/// last character, and its children (the elements, or the two halves of a pair)
struct PNode {
    kind: u8,
    first: usize,
    last: usize,
    kids: Vec<PNode>,
}

const PP_CONST: u8 = 1;
const PP_SET: u8 = 2;
const PP_SEQ: u8 = 3;
const PP_REC: u8 = 4;
const PP_FUN: u8 = 6;
const PP_SUBSET: u8 = 8;

fn pp_ws(c: char) -> bool {
    // Character.isWhitespace
    matches!(c, ' ' | '\t' | '\n' | '\u{b}' | '\u{c}' | '\r' | '\u{1c}'..='\u{1f}')
}

fn pp_digit(c: char) -> bool {
    c.is_ascii_digit() || (!c.is_ascii() && c.is_numeric())
}

fn pp_alnum(c: char) -> bool {
    c.is_ascii_alphanumeric() || (!c.is_ascii() && c.is_alphanumeric())
}

fn pp_skip(c: &[char], mut i: usize) -> Option<usize> {
    while pp_ws(*c.get(i)?) {
        i += 1;
    }
    Some(i)
}

fn pp_at(c: &[char], i: usize, w: &str) -> bool {
    w.chars().enumerate().all(|(k, x)| c.get(i + k) == Some(&x))
}

fn pp_parse(c: &[char], i: usize) -> Option<PNode> {
    if i >= c.len() {
        return None;
    }
    let i = pp_skip(c, i)?;
    match c[i] {
        '{' => pp_list(c, i, PP_SET, 1, '}', false),
        '<' => pp_list(c, i, PP_SEQ, 2, '>', false),
        '[' => pp_list(c, i, PP_REC, 1, ']', true),
        '(' => pp_list(c, i, PP_FUN, 1, ')', true),
        _ if pp_at(c, i, "SUBSET") => {
            let e = pp_parse(c, pp_skip(c, i + 6)?)?;
            Some(PNode { kind: PP_SUBSET, first: i, last: e.last, kids: vec![e] })
        }
        _ => pp_constant(c, i),
    }
}

/// A set, sequence, record or function: elements (pairs for the last two) up to the closing
/// character, separated by "," ("@@" between the pairs of a function)
fn pp_list(c: &[char], i: usize, kind: u8, open: usize, close: char, pairs: bool) -> Option<PNode> {
    let mut last = pp_skip(c, i + open)?;
    let mut kids = vec![];
    while *c.get(last)? != close {
        let e = if pairs { pp_pair(c, last, if kind == PP_REC { "|->" } else { ":>" })? } else { pp_parse(c, last)? };
        last = pp_skip(c, e.last + 1)?;
        if kind == PP_FUN {
            if pp_at(c, last, "@@") {
                last += 2;
            }
        } else if c[last] == ',' {
            last += 1;
        }
        last = pp_skip(c, last)?;
        kids.push(e);
    }
    if kind == PP_SEQ {
        last += 1;
    }
    Some(PNode { kind, first: i, last, kids })
}

fn pp_pair(c: &[char], i: usize, div: &str) -> Option<PNode> {
    let a = pp_parse(c, i)?;
    let mut last = pp_skip(c, a.last + 1)?;
    if !pp_at(c, last, div) {
        return None;
    }
    last = pp_skip(c, last + div.len())?;
    let b = pp_parse(c, last)?;
    Some(PNode { kind: 0, first: i, last: b.last, kids: vec![a, b] })
}

fn pp_constant(c: &[char], i: usize) -> Option<PNode> {
    let first = pp_skip(c, i)?;
    let k = |last| Some(PNode { kind: PP_CONST, first, last, kids: vec![] });
    let mut last = first;
    if c[first] == '"' {
        loop {
            last += 1;
            if *c.get(last)? == '"' {
                return k(last);
            }
        }
    }
    if pp_digit(c[last]) {
        // An interval i..j
        let mut j = i;
        while j < c.len() && pp_digit(c[j]) {
            j += 1;
        }
        if pp_at(c, j, "..") && c.get(j + 2).is_some_and(|&x| pp_digit(x)) {
            j += 2;
            while j < c.len() && pp_digit(c[j]) {
                j += 1;
            }
            return Some(PNode { kind: PP_CONST, first: i, last: j - 1, kids: vec![] });
        }
    }
    if c[last] == '-' {
        last += 1;
        while pp_digit(*c.get(last)?) {
            last += 1;
            if last == c.len() {
                break;
            }
        }
        return k(last - 1);
    }
    if pp_alnum(c[last]) {
        while pp_alnum(c[last]) {
            last += 1;
            if last == c.len() {
                break;
            }
        }
        return k(last - 1);
    }
    None
}

fn pp_text(c: &[char], n: &PNode) -> String {
    c[n.first..=n.last].iter().collect()
}

fn pp_len(n: &PNode) -> i64 {
    (n.last - n.first + 1) as i64
}

fn pp_format(c: &[char], n: &PNode, cw: i64, tw: i64, pad: &str) -> Option<String> {
    if pp_len(n) <= cw - tw {
        return Some(pp_text(c, n));
    }
    match n.kind {
        PP_CONST => Some(pp_text(c, n)),
        PP_SET => pp_simple(c, n, cw, tw, pad, "{ ", " }", "  "),
        PP_SEQ => pp_simple(c, n, cw, tw, pad, "<< ", " >>", "   "),
        PP_SUBSET => pp_simple(c, n, cw, tw, pad, "SUBSET ", " ", " "),
        PP_FUN => pp_pairs(c, n, cw, tw, pad, ["( ", " )", "  ", " @@", " :>", "    "]),
        PP_REC => pp_pairs(c, n, cw, tw, pad, ["[ ", " ]", "  ", ",", " |->", "    "]),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn pp_simple(c: &[char], n: &PNode, cw: i64, tw: i64, pad: &str, open: &str, close: &str, opad: &str) -> Option<String> {
    let cw = cw - open.len().max(opad.len()) as i64;
    let (tw, lp) = (tw + close.len() as i64, format!("{pad}{opad}"));
    let mut o = String::from(open);
    for (k, e) in n.kids.iter().enumerate() {
        if k + 1 < n.kids.len() {
            o += &pp_format(c, e, cw, 1, &lp)?;
            o += ",\n";
            o += &lp;
        } else {
            o += &pp_format(c, e, cw, tw, &lp)?;
        }
    }
    o += close;
    Some(o)
}

/// A record or function: [open, close, pad, sep, div, divpad]
fn pp_pairs(c: &[char], n: &PNode, cw: i64, tw: i64, pad: &str, d: [&str; 6]) -> Option<String> {
    let [open, close, opad, sep, div, divpad] = d;
    let cw = cw - open.len().max(opad.len()) as i64;
    let (tw, lp) = (tw + close.len() as i64, format!("{pad}{opad}"));
    let (sl, dl, dpl) = (sep.len() as i64, div.len() as i64, divpad.len() as i64);
    let lpd = format!("{lp}{divpad}");
    let mut o = String::from(open);
    for (k, p) in n.kids.iter().enumerate() {
        let (a, v) = (&p.kids[0], &p.kids[1]);
        let more = k + 1 < n.kids.len();
        // The last pair leaves room for the closing delimiter; the others for the separator
        let (fits, vtw, end) = if more {
            (pp_len(a) + dl + 1 + pp_len(v) + sl <= cw, sl, format!("{sep}\n{lp}"))
        } else {
            (pp_len(a) + dl + 1 + pp_len(v) <= cw - tw, tw, String::new())
        };
        if fits {
            o += &format!("{}{div} {}{end}", pp_text(c, a), pp_text(c, v));
            continue;
        }
        if pp_len(a) + dl <= cw {
            o += &pp_text(c, a);
        } else {
            o += &pp_format(c, a, cw, tw + dl, &lp)?;
        }
        o += &format!("{div}\n{lpd}{}{end}", pp_format(c, v, cw - dpl, vtw, &lpd)?);
    }
    o += close;
    Some(o)
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

fn dump_open(path: &std::path::Path) {
    use std::io::Write;
    let mut w = match std::fs::File::create(path) {
        Ok(f) => std::io::BufWriter::new(f),
        Err(e) => {
            eprintln!("cannot write {}: {e}", path.display());
            std::process::exit(2);
        }
    };
    let _ = w.write_all(b"strict digraph DiskGraph {\n");
    *DUMP.lock().unwrap() = Some(w);
    DUMPING.store(true, std::sync::atomic::Ordering::Relaxed);
}

/// Appends a worker's buffered lines to the file
fn dump_write(buf: &mut String) {
    use std::io::Write;
    if buf.is_empty() {
        return;
    }
    if let Some(w) = DUMP.lock().unwrap().as_mut() {
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
            if w.write_all(b"}\n").and_then(|_| w.flush()).is_err() {
                eprintln!("cannot write the state graph");
            }
        }
    }
}

/// Exits the checker, completing the state graph first
fn exit(code: i32) -> ! {
    dump_finish();
    std::process::exit(code)
}

/// A state's text as a dot label, escaped as TLC escapes it
fn dot_label(s: &State) -> String {
    show(s).replace('\\', "\\\\").replace('"', "\\\"").trim_matches(|c| c <= ' ').replace('\n', "\\n")
}

fn dump_node(buf: &mut String, id: &dyn std::fmt::Display, s: &State, init: bool) {
    use std::fmt::Write;
    let _ = if init {
        writeln!(buf, "{id} [label=\"{}\",style = filled]", dot_label(s))
    } else {
        writeln!(buf, "{id} [label=\"{}\"];", dot_label(s))
    };
}

fn dump_edge(buf: &mut String, from: Fp, to: &dyn std::fmt::Display) {
    use std::fmt::Write;
    let _ = writeln!(buf, "{from} -> {to};");
}

/// An edge to a successor that tla2rs cannot pack. TLC can represent it, and it is new to TLC (an
/// earlier one would have stopped tla2rs), so it gets a node of its own.
fn dump_unpacked(buf: &mut String, from: Fp, t: &State) {
    let id = format!("u{}", DUMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
    dump_edge(buf, from, &id);
    dump_node(buf, &id, t, false);
}

/// The successor that left its type while `next` built it, which TLC adds as a new state. Its
/// contents are unknown here, so its node has a placeholder for a label; the cross-check
/// compares only the numbers of states and edges then.
fn dump_unrepresentable(from: Fp) {
    if dumping() {
        let mut buf = String::new();
        let id = format!("u{}", DUMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
        dump_edge(&mut buf, from, &id);
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
fn dump_succ(buf: &mut String, sfp: Fp, t: &State) {
    match dump_fp(t) {
        Some(fp) => dump_edge(buf, sfp, &fp),
        None => dump_unpacked(buf, sfp, t),
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
    let _ = successors(s, &mut buf, true);
    let mut out = String::new();
    let mut added = std::collections::HashSet::new();
    for (t, _) in buf {
        let Ok(inm) = std::panic::catch_unwind(|| in_model(s, &t)) else { break };
        let mut unseen = true;
        if inm {
            match std::panic::catch_unwind(|| dump_fp(&t)) {
                Ok(Some(fp)) => {
                    dump_edge(&mut out, sfp, &fp);
                    unseen = !visited(fp) && added.insert(fp);
                    if unseen {
                        dump_node(&mut out, &fp, &t, false);
                    }
                }
                Ok(None) => dump_unpacked(&mut out, sfp, &t),
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

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().collect();
    if let Some(p) = args.iter().position(|a| a == "-dumpgraph").and_then(|i| args.get(i + 1)) {
        dump_open(std::path::Path::new(p));
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
    // What TLC prints when it starts: Print and PrintT in the constant definitions and ASSUMEs
    for l in STARTUP_PRINTS {
        println!("{l}");
    }
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        // A spec without [][Next]_v: TLC computes and checks the initial states, then stops
        if NO_NEXT {
            let (inits, _) = initial_states();
            println!("Finished computing initial states: {} distinct states generated.", inits.len());
            println!("Error: No next state actions defined to generate successor states from.");
            exit(75);
        }
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
        exit(eval_code(&e));
    }
    dump_finish();
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
        eprintln!("  (while {while_})");
        println!("{generated} states generated, {distinct} distinct states found, {distinct} states left on queue.");
        exit(init_eval_code(&e));
    }
    let mut inits = Vec::new();
    // The states computed before an error are still checked first, as TLC checks each one as soon
    // as it is generated.
    let failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| init(&mut inits))).err();
    let mut out = vec![];
    let mut seen = std::collections::HashSet::new();
    let mut generated = 0u64;
    // The first call writes the initial states to the graph; later ones rebuild traces
    let dump = dumping() && !DUMPED_INITS.swap(true, std::sync::atomic::Ordering::Relaxed);
    let mut buf = String::new();
    for s in inits {
        generated += 1;
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
                continue;
            }
            out.push((s, w, fp));
            if dump {
                dump_node(&mut buf, &fp, &s, true);
                dump_write(&mut buf);
            }
        } else if dump && in_model && w.is_none() {
            let id = format!("u{}", DUMP_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
            dump_node(&mut buf, &id, &s, true);
            dump_write(&mut buf);
        }
        match eval_invariants(&s) {
            Ok(None) => {}
            Ok(Some(inv)) => {
                println!("Error: Invariant {inv} is violated by the initial state:\n{}", show(&s));
                exit(12);
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
                    println!("Error: Property {name} is violated by the initial state:\n{}", show(&s));
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
    }
    if let Some(p) = failed {
        stop(describe_panic(p), "computing the initial states", None, generated, out.len());
    }
    (out, generated)
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
}

/// A successor that does not fit the packed layout: an invariant it violates, else an out-of-type
/// error
fn pack_failed(sfp: Fp, t: State, l: u32) -> SFound {
    let msg = match eval_invariants(&t) {
        Ok(Some(inv)) => SMsg::Inv(inv),
        Err((inv, e)) => SMsg::InvEval(inv, e),
        Ok(None) => SMsg::OutOfType,
    };
    SFound::new(sfp, Some((t, l)), msg)
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
}

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
    let failed = successors(&s, &mut ws.buf, careful);
    if failed.is_none() && ws.buf.is_empty() && opt.check_deadlock {
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
        return found;
    }
    c.generated = examined;
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
            dump_succ(&mut e, sfp, t);
            ws.dpend.push((i, e));
        }
        // A violated action property is reported after t is added (if new) and its invariants are
        // checked, as TLC does: t stays a candidate, and the search stops after it.
        let act = check_action_props(s, t).map(|m| SFound::new(sfp, Some((*t, l)), m));
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
    for k in 0..ws.cand.len() {
        let (i, tfp, tw) = ws.cand[k];
        if !seen.insert_with(tfp, sfp) {
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
        match eval_invariants(t) {
            Ok(None) => {}
            Ok(Some(inv)) => return Some(SFound::new(tfp, None, SMsg::Inv(inv))),
            Err((inv, e)) => return Some(SFound::new(tfp, None, SMsg::InvEval(inv, e))),
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
    let mut ws = SWork {
        buf: Vec::with_capacity(64),
        cand: Vec::with_capacity(64),
        mine: Seen::new(),
        dpend: vec![],
        dump: String::new(),
    };
    for i in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let (w, sfp) = &frontier[i];
        let base = c.generated;
        let r = expand_caught(&mut c, |c| c.generated, |c, careful| {
            expand_safety_one(w, *sfp, seen, opt, c, &mut ws, careful)
        });
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
    let first = initial_states().0.into_iter().find(|(_, _, fp)| *fp == chain[0])?;
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
                        spawn_worker(sc, move || expand_safety(pt, x, y, seen, stop, opt))
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
    println!("{generated} states generated, {distinct} distinct states found, {left} states left on queue.");
    exit(code);
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
    let mut out = Collected { parts: (0..parts).map(|_| vec![]).collect(), generated: 0, found: None, dump: String::new() };
    let mut buf: Vec<(State, u32)> = Vec::with_capacity(64);
    let mut mine = Seen::new();
    for i in lo..hi {
        if stop.load(Relaxed) {
            break;
        }
        let (w, sfp) = &frontier[i];
        let mark = out.dump.len();
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
                    dump_succ(&mut out.dump, *sfp, &t);
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
                let inv = if tw.is_some() { eval_invariants(&t) } else { Ok(None) };
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
                let prev: &[Vec<Vec<Cand>>] = pending.as_ref().map_or(&[], |(b, _)| b.as_slice());
                let collected: Vec<Collected> = std::thread::scope(|sc| {
                    let hs: Vec<_> = (0..k)
                        .map(|i| {
                            let (x, y) = (i * per, ((i + 1) * per).min(n));
                            let (pt, stop, tbl) = (&part, &stop, &tbl);
                            spawn_worker(sc, move || collect_phase(pt, x, y, opt, stop, parts, tbl, prev))
                        })
                        .collect();
                    hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
                });
                // Group the per-thread arrays by owner, moving them as is rather than copying
                // their contents.
                let mut by_part: Vec<Vec<Vec<Cand>>> = (0..parts).map(|_| vec![]).collect();
                for mut c in collected {
                    dump_write(&mut c.dump);
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
                            spawn_worker(sc, move || {
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
                        spawn_worker(sc, move || {
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
    if !PERMS.is_empty() {
        // As TLC warns: the search runs on the graph folded by symmetry
        println!("Warning: Declaring symmetry during liveness checking is dangerous. It might cause the checker to miss violations of the stated liveness properties. Please check liveness without symmetry defined.");
    }
    let mut g = Graph { states: Vec::new(), parent: Vec::new(), sbits: Vec::new() };
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
                    spawn_worker(sc, move || expand(g, a, b, seen, stop, i, check_deadlock))
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap_or_else(|p| std::panic::resume_unwind(p))).collect()
        });
        let mut found = None;
        let mut base = vec![];
        for (i, mut c) in chunks.into_iter().enumerate() {
            dump_write(&mut c.dump);
            generated += c.generated;
            base.push(g.states.len());
            live.edges.extend(c.live.edges);
            live.en.extend(c.live.en);
            g.sbits.extend(c.sbits);
            g.states.extend(c.states);
            g.parent.extend(c.parent);
            if found.is_none() {
                found = c.found.map(|f| (i, f));
            }
        }
        if let Some((_, f)) = found {
            let mut distinct = g.states.len();
            let code = match f {
                Found::New(w, idx, msg) => {
                    if dumping() && matches!(msg, SMsg::InvEval(..)) {
                        let p = g.parent[base[w] + idx].0 as usize;
                        let s = unpack(&g.states[p]);
                        dump_replay(&s, state_fp(&s, &g.states[p]), &|fp| seen.contains(fp));
                    }
                    let code = report_msg(&msg, true);
                    g.print_trace((base[w] + idx) as u32, None);
                    code
                }
                Found::Deadlock(id) => {
                    println!("Error: Deadlock reached.");
                    g.print_trace(id, None);
                    11
                }
                Found::Succ(p, t, l, msg, in_model) => {
                    // A new state that could not be packed counts as one state too (to match TLC).
                    if in_model && matches!(msg, SMsg::Inv(_) | SMsg::InvEval(..) | SMsg::OutOfType) {
                        distinct += 1;
                    }
                    let code = report_msg(&msg, in_model);
                    g.print_trace(p, Some((&t, l)));
                    code
                }
                // TLC shows no behavior for these
                Found::Live(m) => report_msg(&m, true),
                Found::Eval(p, e) => {
                    let pseudo = matches!(e, EvalErr::Type(_));
                    let code = report_msg(&SMsg::Eval(e), true);
                    g.print_trace(p, None);
                    if pseudo {
                        // As in TLC, the out-of-type successor counts as one state (its contents
                        // can't be represented).
                        dump_unrepresentable(state_fp(&unpack(&g.states[p as usize]), &g.states[p as usize]));
                        generated += 1;
                        distinct += 1;
                        println!("State {}: <a successor that tla2rs cannot represent>\n", g.trace_len(p) + 1);
                    }
                    code
                }
            };
            println!(
                "{generated} states generated, {distinct} distinct states found, {} states left on queue.",
                g.states.len() - lo
            );
            exit(code);
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
        let ok = liveness(&g, live);
        println!("Checked temporal properties in {:.3}s", t1.elapsed().as_secs_f64());
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

struct LProp {
    #[allow(dead_code)]
    name: &'static str,
    nodes: &'static [LNode],
    nacc: u32,
}

/// The label of the stuttering step every state has
const STUTTER: u32 = u32::MAX - 1;

/// The state graph for the liveness search. The steps of a state are its edges plus stuttering.
struct Steps {
    off: Vec<usize>,
    dst: Vec<u32>,
    label: Vec<u32>,
    abits: Vec<u64>,
    fbits: Vec<u64>,
    sbits: Vec<u64>,
    fen: Vec<u64>,
    stut: Vec<u64>,
}

impl Steps {
    /// (target, label, action atoms, fairness steps) of each step from s, stuttering last
    fn of(&self, s: u32) -> impl Iterator<Item = (u32, u32, u64, u64)> + '_ {
        let r = self.off[s as usize]..self.off[s as usize + 1];
        r.map(move |e| (self.dst[e], self.label[e], self.abits[e], self.fbits[e]))
            .chain(std::iter::once((s, STUTTER, self.stut[s as usize], 0)))
    }
}

/// The product of the state graph with the automaton of one negated property
struct Product<'a> {
    st: &'a Steps,
    nodes: &'static [LNode],
    q: usize,
}

impl Product<'_> {
    fn valid(&self, s: u32, q: usize) -> bool {
        let (b, n) = (self.st.sbits[s as usize], &self.nodes[q]);
        b & n.s_pos == n.s_pos && b & n.s_neg == 0
    }

    /// Successors of product node p: (node, label, fairness steps)
    fn succ(&self, p: usize, out: &mut Vec<(usize, u32, u64)>) {
        out.clear();
        let (s, q) = ((p / self.q) as u32, p % self.q);
        let n = &self.nodes[q];
        for (t, l, a, f) in self.st.of(s) {
            if a & n.a_pos != n.a_pos || a & n.a_neg != 0 {
                continue;
            }
            for &q2 in n.succ {
                if self.valid(t, q2 as usize) {
                    out.push((t as usize * self.q + q2 as usize, l, f));
                }
            }
        }
    }

    fn state(&self, p: usize) -> u32 {
        (p / self.q) as u32
    }
}

/// Strongly connected components of the product nodes for which `inside` holds, reachable from
/// `roots` without leaving them (iterative Tarjan). Trivial components without a self-loop are
/// left out.
fn sccs(pr: &Product, roots: &[usize], inside: &dyn Fn(usize) -> bool) -> Vec<Vec<usize>> {
    let mut index: std::collections::HashMap<usize, (u32, u32, bool)> = std::collections::HashMap::new();
    let mut out = vec![];
    let mut stack: Vec<usize> = vec![];
    let mut idx = 0u32;
    let mut buf = vec![];
    for &root in roots {
        if !inside(root) || index.contains_key(&root) {
            continue;
        }
        pr.succ(root, &mut buf);
        let mut call: Vec<(usize, Vec<usize>, usize)> = vec![(root, buf.iter().map(|x| x.0).collect(), 0)];
        index.insert(root, (idx, idx, true));
        idx += 1;
        stack.push(root);
        while let Some((u, ref succ, ref mut i)) = call.last_mut() {
            let u = *u;
            if *i < succ.len() {
                let v = succ[*i];
                *i += 1;
                if !inside(v) {
                    continue;
                }
                match index.get(&v).copied() {
                    None => {
                        index.insert(v, (idx, idx, true));
                        idx += 1;
                        stack.push(v);
                        pr.succ(v, &mut buf);
                        call.push((v, buf.iter().map(|x| x.0).collect(), 0));
                    }
                    Some((vi, _, true)) => {
                        let e = index.get_mut(&u).unwrap();
                        e.1 = e.1.min(vi);
                    }
                    _ => {}
                }
                continue;
            }
            let succ_u = std::mem::take(&mut call.last_mut().unwrap().1);
            call.pop();
            let (ui, ul, _) = index[&u];
            if let Some((p, _, _)) = call.last() {
                let p = *p;
                let e = index.get_mut(&p).unwrap();
                e.1 = e.1.min(ul);
            }
            if ul != ui {
                continue;
            }
            let mut members = vec![];
            loop {
                let w = stack.pop().unwrap();
                index.get_mut(&w).unwrap().2 = false;
                members.push(w);
                if w == u {
                    break;
                }
            }
            if members.len() > 1 || succ_u.contains(&u) {
                out.push(members);
            }
        }
    }
    out
}

/// What a fair accepting cycle in component `c` must visit: (acceptance set, node predicate) or
/// (fairness condition, step). None if `c` has no such cycle; Some(Err(c')) if strong fairness
/// requires leaving out the states where an action is enabled.
enum Verdict {
    Reject,
    Narrow(Vec<usize>),
    Accept { steps: Vec<usize>, off: Vec<usize> },
}

fn judge(pr: &Product, nacc: u32, c: &[usize]) -> Verdict {
    let set: std::collections::HashSet<usize> = c.iter().copied().collect();
    let mut acc = 0u64;
    for &p in c {
        acc |= pr.nodes[p % pr.q].acc;
    }
    let all = if nacc == 64 { u64::MAX } else { (1u64 << nacc) - 1 };
    if acc & all != all {
        return Verdict::Reject;
    }
    let mut taken = 0u64;
    let mut buf = vec![];
    for &p in c {
        pr.succ(p, &mut buf);
        for &(v, _, f) in &buf {
            if set.contains(&v) {
                taken |= f;
            }
        }
    }
    let mut some_off = 0u64;
    let mut all_off = u64::MAX;
    for &p in c {
        let en = pr.st.fen[pr.state(p) as usize];
        some_off |= !en;
        all_off &= !en;
    }
    let mut steps = vec![];
    let mut off = vec![];
    let mut strong_bad = 0u64;
    for (i, (weak, _, _)) in FAIRS.iter().enumerate() {
        let b = 1u64 << i;
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
        let keep: Vec<usize> = c.iter().copied().filter(|&p| pr.st.fen[pr.state(p) as usize] & strong_bad == 0).collect();
        return Verdict::Narrow(keep);
    }
    Verdict::Accept { steps, off }
}

/// Searches a component for a fair accepting cycle, narrowing it for strong fairness
fn search(pr: &Product, nacc: u32, c: Vec<usize>) -> Option<(Vec<usize>, Vec<usize>, Vec<usize>)> {
    match judge(pr, nacc, &c) {
        Verdict::Reject => None,
        Verdict::Accept { steps, off } => Some((c, steps, off)),
        Verdict::Narrow(keep) => {
            if keep.is_empty() {
                return None;
            }
            let set: std::collections::HashSet<usize> = keep.iter().copied().collect();
            for sub in sccs(pr, &keep, &|p| set.contains(&p)) {
                if let Some(r) = search(pr, nacc, sub) {
                    return Some(r);
                }
            }
            None
        }
    }
}

/// A shortest path inside `set` from `from` (excluded) that ends at a node satisfying `goal` or with
/// a step satisfying `edge` (on its fairness bits): [(node, label, fairness bits of the step)]
fn path_to(
    pr: &Product,
    set: &std::collections::HashSet<usize>,
    from: usize,
    goal: &dyn Fn(usize) -> bool,
    edge: &dyn Fn(u64) -> bool,
) -> Vec<(usize, u32, u64)> {
    let mut prev: std::collections::HashMap<usize, (usize, u32, u64)> = std::collections::HashMap::new();
    let mut q = std::collections::VecDeque::from([from]);
    let mut buf = vec![];
    while let Some(u) = q.pop_front() {
        pr.succ(u, &mut buf);
        for &(v, l, f) in &buf {
            if !set.contains(&v) {
                continue;
            }
            if goal(v) || edge(f) {
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
    live.edges.sort_by_key(|e| e.0);
    let mut st = Steps {
        off: vec![0; n + 1],
        dst: vec![],
        label: vec![],
        abits: vec![],
        fbits: vec![],
        sbits: g.sbits.clone(),
        fen: vec![0; n],
        stut: vec![0; n],
    };
    for &(s, tfp, l, a, f) in &live.edges {
        let t = lookup(tfp);
        if t == u32::MAX {
            continue;
        }
        st.off[s as usize + 1] += 1;
        st.dst.push(t);
        st.label.push(l);
        st.abits.push(a);
        st.fbits.push(f);
    }
    for i in 0..n {
        st.off[i + 1] += st.off[i];
    }
    for &(s, en, stut, cbits) in &live.en {
        st.fen[s as usize] = en;
        st.stut[s as usize] = stut;
        st.sbits[s as usize] |= cbits;
    }
    drop(live);
    let inits: Vec<u32> = (0..n as u32).filter(|&i| g.parent[i as usize].0 == u32::MAX).collect();
    let edges = st.dst.len();
    for prop in LPROPS {
        let pr = Product { st: &st, nodes: prop.nodes, q: prop.nodes.len().max(1) };
        if prop.nodes.is_empty() {
            continue;
        }
        // Reachable product nodes, in BFS order, with their BFS parents
        let mut par: std::collections::HashMap<usize, (usize, u32)> = std::collections::HashMap::new();
        let mut order = vec![];
        for &s in &inits {
            for (q, nd) in prop.nodes.iter().enumerate() {
                let p = s as usize * pr.q + q;
                if nd.init && pr.valid(s, q) && !par.contains_key(&p) {
                    par.insert(p, (usize::MAX, u32::MAX));
                    order.push(p);
                }
            }
        }
        let mut h = 0;
        let mut buf = vec![];
        while h < order.len() {
            let u = order[h];
            h += 1;
            pr.succ(u, &mut buf);
            for &(v, l, _) in &buf {
                if let std::collections::hash_map::Entry::Vacant(e) = par.entry(v) {
                    e.insert((u, l));
                    order.push(v);
                }
            }
        }
        let rank: std::collections::HashMap<usize, usize> = order.iter().enumerate().map(|(i, &p)| (p, i)).collect();
        for c in sccs(&pr, &order, &|_| true) {
            let Some((c, steps, off)) = search(&pr, prop.nacc, c) else { continue };
            let set: std::collections::HashSet<usize> = c.iter().copied().collect();
            let entry = *c.iter().min_by_key(|p| rank[p]).unwrap();
            // The cycle: visit each acceptance set; for each weakly fair action, a state where it is
            // disabled or one of its steps; for each strongly fair action that is enabled somewhere
            // on the cycle, one of its steps; then return to the entry
            let _ = &off;
            let fen = |p: usize| st.fen[pr.state(p) as usize];
            let mut cyc: Vec<(usize, u32, u64)> = vec![];
            let mut cur = entry;
            let go = |cyc: &mut Vec<(usize, u32, u64)>, cur: &mut usize, goal: &dyn Fn(usize) -> bool, edge: &dyn Fn(u64) -> bool| {
                let p = path_to(&pr, &set, *cur, goal, edge);
                if let Some(&(l, _, _)) = p.last() {
                    *cur = l;
                }
                cyc.extend(p);
            };
            let visited = |cyc: &[(usize, u32, u64)], f: &dyn Fn(usize) -> bool| f(entry) || cyc.iter().any(|&(p, _, _)| f(p));
            for j in 0..prop.nacc {
                let here = |p: usize| prop.nodes[p % pr.q].acc & (1 << j) != 0;
                if !visited(&cyc, &here) {
                    go(&mut cyc, &mut cur, &here, &|_| false);
                }
            }
            for (i, (weak, _, _)) in FAIRS.iter().enumerate() {
                let off_here = |p: usize| fen(p) & (1 << i) == 0;
                if !*weak || visited(&cyc, &off_here) {
                    continue;
                }
                if c.iter().any(|&p| off_here(p)) {
                    go(&mut cyc, &mut cur, &off_here, &|_| false);
                } else {
                    go(&mut cyc, &mut cur, &|_| false, &|f| f & (1 << i) != 0);
                }
            }
            loop {
                // Back to the entry (at least one step)
                if cur != entry || cyc.is_empty() {
                    go(&mut cyc, &mut cur, &|p| p == entry, &|_| false);
                }
                let mut added = false;
                for (i, (weak, _, _)) in FAIRS.iter().enumerate() {
                    let b = 1u64 << i;
                    let on = |p: usize| fen(p) & b != 0;
                    if *weak || !steps.contains(&i) || cyc.iter().any(|&(_, _, f)| f & b != 0) || !visited(&cyc, &on) {
                        continue;
                    }
                    go(&mut cyc, &mut cur, &|_| false, &|f| f & b != 0);
                    added = true;
                }
                if !added && cur == entry {
                    break;
                }
            }
            let mut prefix = vec![];
            let mut y = entry;
            while y != usize::MAX {
                let (p, l) = par[&y];
                prefix.push((pr.state(y), l));
                y = p;
            }
            prefix.reverse();
            let cycle: Vec<(u32, u32)> = cyc.iter().map(|&(p, l, _)| (pr.state(p), l)).collect();
            println!("Error: Temporal properties were violated.");
            println!("Error: The following behavior constitutes a counter-example:");
            print_lasso(g, &prefix, &cycle);
            return false;
        }
    }
    println!("Temporal properties hold ({} properties, {} fairness conditions, {} edges).", LPROPS.len(), FAIRS.len(), edges);
    true
}

/// Prints a lasso as TLC does: the states from an initial state to the entry of the cycle, then
/// the cycle, ending with "Back to state N" (or "Stuttering" if it never leaves the entry state).
/// Stuttering steps inside are not shown.
fn print_lasso(g: &Graph, prefix: &[(u32, u32)], cycle: &[(u32, u32)]) {
    let name = |l: u32| if l == u32::MAX { "Initial predicate" } else { LABELS[l as usize] };
    let mut shown: Vec<(u32, u32)> = vec![];
    for &(s, l) in prefix {
        if shown.last().is_some_and(|x| x.0 == s) && (l == STUTTER || l == u32::MAX) {
            continue;
        }
        shown.push((s, l));
    }
    // The states shown, for -lassocheck
    let mut texts: Vec<String> = vec![];
    for (i, &(s, l)) in shown.iter().enumerate() {
        let t = show(&unpack(&g.states[s as usize]));
        println!("State {}: <{}>\n{t}\n", i + 1, name(l));
        texts.push(t);
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
    if moves.is_empty() {
        println!("State {}: Stuttering", entry_no + 1);
        write_lasso_check(&texts, None);
        return;
    }
    let last = moves.len() - 1;
    let mut back = None;
    for (j, &(s, l)) in moves.iter().enumerate() {
        if j == last && s == entry {
            println!("Back to state {entry_no}: <{}>", name(l));
            back = Some(entry_no);
        } else {
            let t = show(&unpack(&g.states[s as usize]));
            println!("State {}: <{}>\n{t}\n", entry_no + j + 1, name(l));
            texts.push(t);
        }
    }
    write_lasso_check(&texts, back);
}

/// With `-lassocheck DIR`, writes DIR/Tla2rsLasso.tla and .cfg: a spec whose only behavior is the
/// lasso `states` (as printed), returning to state `back` (1-based) or ending stuttering, for TLC
/// to confirm that it is a behavior of the spec that violates the properties (see lasso.rs in
/// tla2rs)
fn write_lasso_check(states: &[String], back: Option<usize>) {
    let args: Vec<String> = std::env::args().collect();
    let Some(dir) = args.iter().position(|a| a == "-lassocheck").and_then(|i| args.get(i + 1)) else { return };
    let [module, pre, post, cfg] = match LASSO_CHECK {
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
    let tlc = states.iter().any(|t| t.contains(":>") || t.contains("@@"));
    let mut o = format!("---- MODULE Tla2rsLasso ----\nEXTENDS {module}{}\n{pre}", if tlc { ", TLC" } else { "" });
    for (i, t) in states.iter().enumerate() {
        o += &format!("Tla2rsState{} ==\n{}Tla2rsGo{} ==\n{}", i + 1, indent(t), i + 1, indent(&primed(t)));
    }
    o += "Tla2rsStep ==\n";
    let n = states.len();
    for i in 1..=n {
        let to = if i < n { i + 1 } else { back.unwrap_or(n) };
        o += &format!("  \\/ tla2rsAt = {i} /\\ tla2rsAt' = {to} /\\ Tla2rsGo{to}\n");
    }
    o += post;
    o += "====\n";
    let dir = std::path::Path::new(dir);
    let written = std::fs::write(dir.join("Tla2rsLasso.tla"), o).and_then(|_| std::fs::write(dir.join("Tla2rsLasso.cfg"), cfg));
    if let Err(e) = written {
        eprintln!("cannot write the lasso check to {}: {e}", dir.display());
    }
}
"##;
