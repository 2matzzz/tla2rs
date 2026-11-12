//! Modules of the CommunityModules (https://github.com/tlaplus/CommunityModules, MIT licence),
//! which tla2rs provides itself when a spec names one in EXTENDS or INSTANCE and no module of that
//! name is next to it (`compile::find_module`).
//!
//! The definitions below are written for tla2rs from the documented meaning of each operator, and
//! checked against TLC 2.19 (`tests/tlc/Cm*`). TLC 2.19 cannot load the Java overrides in the
//! CommunityModules jar (every release since 2023 needs a class TLC 2.19 does not have), so it
//! evaluates the modules' TLA+ definitions, and so do these: an operator defined with CHOOSE picks
//! what the module's definition picks, and a fold applies its operator in the order the module's
//! definition does.
//!
//! Each module exports the same names in the same order as the release's (what it extends, then
//! its definitions and RECURSIVE declarations), since SANY's context, and with it the order TLC
//! prints variables in, depends on them (see `sany::var_order`). The operators listed in
//! `UNSUPPORTED` are refused when used: TLC 2.19 cannot evaluate them without their Java overrides
//! (they enumerate `Seq(S)`), or they are not written yet.

/// The source of each module, by name
pub fn source(name: &str) -> Option<&'static str> {
    Some(match name {
        "Folds" => FOLDS,
        "Functions" => FUNCTIONS,
        _ => return None,
    })
}

/// The operators of each module that are refused when used, with the reason
pub const UNSUPPORTED: &[(&str, &str, &str)] = &[
];

/// Folding a set: `op(f(x1), op(f(x2), ... op(f(xn), base)))` where x1 is `choose(S)`, x2 is
/// `choose(S \ {x1})`, and so on
const FOLDS: &str = r#"
---- MODULE Folds ----
RECURSIVE MapThenFoldSet(_, _, _, _, _)
MapThenFoldSet(op(_, _), base, f(_), choose(_), S) ==
  IF S = {} THEN base
  ELSE LET x == choose(S) IN op(f(x), MapThenFoldSet(op, base, f, choose, S \ {x}))
====
"#;

const FUNCTIONS: &str = r#"
---- MODULE Functions ----
EXTENDS Integers, Folds
Restrict(f, S) == [a \in S |-> f[a]]
RestrictDomain(f, Test(_)) == Restrict(f, {a \in DOMAIN f : Test(a)})
RestrictValues(f, Test(_)) == Restrict(f, {a \in DOMAIN f : Test(f[a])})
IsRestriction(narrow, wide) ==
  /\ DOMAIN narrow \subseteq DOMAIN wide
  /\ \A a \in DOMAIN narrow \cap DOMAIN wide : narrow[a] = wide[a]
Range(f) == {f[a] : a \in DOMAIN f}
Pointwise(f, g, T(_, _)) == [a \in DOMAIN f |-> T(f[a], g[a])]
Inverse(f, S, T) == [b \in T |-> CHOOSE a \in S : b \in Range(f) => f[a] = b]
AntiFunction(f) == Inverse(f, DOMAIN f, Range(f))
IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b
Injection(S, T) == {g \in [S -> T] : IsInjective(g)}
Surjection(S, T) == {g \in [S -> T] : \A b \in T : \E a \in S : g[a] = b}
Bijection(S, T) == Injection(S, T) \cap Surjection(S, T)
ExistsInjection(S, T) == Injection(S, T) # {}
ExistsSurjection(S, T) == Surjection(S, T) # {}
ExistsBijection(S, T) == Bijection(S, T) # {}
FoldFunctionOnSet(op(_, _), base, fun, indices) ==
  MapThenFoldSet(op, base, LAMBDA a : fun[a], LAMBDA T : CHOOSE a \in T : TRUE, indices)
FoldFunction(op(_, _), base, fun) == FoldFunctionOnSet(op, base, fun, DOMAIN fun)
SumFunctionOnSet(fun, indices) == FoldFunctionOnSet(LAMBDA a, b : a + b, 0, fun, indices)
SumFunction(fun) == SumFunctionOnSet(fun, DOMAIN fun)
====
"#;
