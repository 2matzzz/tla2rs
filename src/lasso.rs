//! The lasso check: a TLA+ module and cfg whose only behavior is a liveness counterexample found
//! by the checker, for TLC to confirm that it is a behavior of the spec and violates a property.
//!
//! With `-lassocheck DIR`, a checker that finds a lasso writes `DIR/Tla2rsLasso.tla` and
//! `DIR/Tla2rsLasso.cfg` (`write_lasso_check` in runtime.rs). The module EXTENDS the spec's module,
//! adds a variable `tla2rsAt` (the position on the lasso) and defines
//!
//! - `Tla2rsInit`: position 1, the first state of the lasso, and the spec's initial predicate
//! - `Tla2rsNext`: a step to the next position of the lasso (from the last, back to the state the
//!   lasso returns to, or to itself if it ends stuttering), with its state, conjoined with the
//!   spec's `[Next]_vars`
//! - `Tla2rsSpec`: `Tla2rsInit /\ [][Tla2rsNext]_w /\ WF_w(Tla2rsNext)` and the spec's other
//!   temporal conjuncts (its fairness), with w the variables and `tla2rsAt`
//!
//! The cfg keeps the spec's constants, PROPERTIES and constraints, and checks deadlock. Since each
//! position has one successor and WF forces every step but the stuttering at the end, the only
//! behavior satisfying `Tla2rsSpec`'s fairness is the lasso. TLC then reports that the properties
//! are violated, with one distinct state per position, exactly when the first state is initial,
//! every step is a step of Next (otherwise the lasso deadlocks, or a state is missing), the lasso
//! satisfies the spec's fairness (otherwise no behavior is fair and nothing is violated), and it
//! violates the properties. Fairness and ENABLED stay those of the spec: its actions do not mention
//! `tla2rsAt`.
//!
//! A lasso that returns to its entry only under the spec's VIEW (`lasso_states` in runtime.rs) ends
//! with a step to the actual successor instead, and the cfg gets `VIEW Tla2rsView`, the spec's view
//! with the position, so TLC folds that successor into the entry.

use crate::ast::*;
use crate::cfg::Cfg;

/// The parts of a SPECIFICATION as TLC splits it, as written in the spec's module
#[derive(Default)]
pub struct Written {
    pub init: Vec<Expr>,
    /// `[A]_v`
    pub next: Option<Expr>,
    pub temporal: Vec<Expr>,
}

/// `e` as TLA+ text, fully parenthesized. Fails on what the parser added (bound tuples, unbounded
/// quantifiers, subexpression names) or does not keep as written (LET, LAMBDA)
pub fn tla(e: &Expr) -> Result<String, String> {
    use Expr::*;
    let list = |xs: &[Expr], sep: &str| -> Result<String, String> { Ok(xs.iter().map(tla).collect::<Result<Vec<_>, _>>()?.join(sep)) };
    let name = |n: &str| if n.starts_with('#') { Err(format!("`{n}` cannot be written out")) } else { Ok(n.to_string()) };
    let binds = |bs: &[(String, Expr)]| -> Result<String, String> {
        Ok(bs.iter().map(|(x, s)| Ok(format!("{} \\in {}", name(x)?, tla(s)?))).collect::<Result<Vec<_>, String>>()?.join(", "))
    };
    let sub = |v: &Expr| match v {
        Ident(n, _) => name(n),
        Tuple(xs) => Ok(format!("<<{}>>", list(xs, ", ")?)),
        _ => Err("a subscript other than a name or a tuple".to_string()),
    };
    Ok(match e {
        Num(n) => n.to_string(),
        Str(s) => format!("{s:?}"),
        Bool(b) => if *b { "TRUE".into() } else { "FALSE".into() },
        // A model value of the cfg
        Ident(n, _) if n.starts_with("@model:") => n["@model:".len()..].to_string(),
        Ident(n, _) => name(n)?,
        Call(n, a) if n == "\\X" => format!("({})", list(a, " \\X ")?),
        Call(n, a) if n.starts_with(|c: char| c.is_ascii_alphabetic()) => {
            if a.is_empty() { n.clone() } else { format!("{n}({})", list(a, ", ")?) }
        }
        Call(n, a) if a.len() == 2 && !n.starts_with('#') => format!("({} {n} {})", tla(&a[0])?, tla(&a[1])?),
        Prime(x) => format!("({})'", tla(x)?),
        Un(op, x) => {
            let o = match op {
                UOp::Not => "~",
                UOp::Neg => "-",
                UOp::Always => "[]",
                UOp::Eventually => "<>",
                UOp::Subset => "SUBSET ",
                UOp::Union => "UNION ",
                UOp::Domain => "DOMAIN ",
                UOp::Unchanged => "UNCHANGED ",
                UOp::Enabled => "ENABLED ",
            };
            format!("({o}({}))", tla(x)?)
        }
        Bin(op, a, b) => {
            let o = match op {
                BOp::Implies => "=>",
                BOp::Equiv => "<=>",
                BOp::LeadsTo => "~>",
                BOp::Eq => "=",
                BOp::Neq => "#",
                BOp::Lt => "<",
                BOp::Le => "<=",
                BOp::Gt => ">",
                BOp::Ge => ">=",
                BOp::In => "\\in",
                BOp::NotIn => "\\notin",
                BOp::Subseteq => "\\subseteq",
                BOp::Cup => "\\cup",
                BOp::Cap => "\\cap",
                BOp::SetMinus => "\\",
                BOp::Range => "..",
                BOp::Add => "+",
                BOp::Sub => "-",
                BOp::Mul => "*",
                BOp::Div => "\\div",
                BOp::Mod => "%",
            };
            format!("({} {o} {})", tla(a)?, tla(b)?)
        }
        And(xs) if xs.is_empty() => "TRUE".into(),
        Or(xs) if xs.is_empty() => "FALSE".into(),
        And(xs) => format!("({})", list(xs, " /\\ ")?),
        Or(xs) => format!("({})", list(xs, " \\/ ")?),
        If(c, a, b) => format!("(IF {} THEN {} ELSE {})", tla(c)?, tla(a)?, tla(b)?),
        Case(arms, other) => {
            let mut v: Vec<String> = arms.iter().map(|(p, x)| Ok(format!("{} -> {}", tla(p)?, tla(x)?))).collect::<Result<_, String>>()?;
            if let Some(o) = other {
                v.push(format!("OTHER -> {}", tla(o)?));
            }
            format!("(CASE {})", v.join(" [] "))
        }
        Quant(ex, bs, b) => format!("({} {} : {})", if *ex { "\\E" } else { "\\A" }, binds(bs)?, tla(b)?),
        Choose(x, s, p) => format!("(CHOOSE {} \\in {} : {})", name(x)?, tla(s)?, tla(p)?),
        SetLit(xs) => format!("{{{}}}", list(xs, ", ")?),
        SetFilter(x, s, p) => format!("{{{} \\in {} : {}}}", name(x)?, tla(s)?, tla(p)?),
        SetMap(e, bs) => format!("{{{} : {}}}", tla(e)?, binds(bs)?),
        FunCons(x, s, b) => format!("[{} \\in {} |-> {}]", name(x)?, tla(s)?, tla(b)?),
        FunSet(a, b) => format!("[{} -> {}]", tla(a)?, tla(b)?),
        RecLit(fs) => format!("[{}]", fs.iter().map(|(k, v)| Ok(format!("{k} |-> {}", tla(v)?))).collect::<Result<Vec<_>, String>>()?.join(", ")),
        RecSet(fs) => format!("[{}]", fs.iter().map(|(k, v)| Ok(format!("{k} : {}", tla(v)?))).collect::<Result<Vec<_>, String>>()?.join(", ")),
        App(f, a) => format!("{}[{}]", tla(f)?, tla(a)?),
        Field(r, k) => format!("{}.{k}", tla(r)?),
        Except(f, ups) => {
            let mut v = vec![];
            for (path, val) in ups {
                let mut p = String::from("!");
                for s in path {
                    match s {
                        Path::Idx(i) => p += &format!("[{}]", tla(i)?),
                        Path::Field(k) => p += &format!(".{k}"),
                    }
                }
                v.push(format!("{p} = {}", tla(val)?));
            }
            format!("[{} EXCEPT {}]", tla(f)?, v.join(", "))
        }
        At => "@".into(),
        Tuple(xs) => format!("<<{}>>", list(xs, ", ")?),
        BoxAction(a, v) => format!("[{}]_{}", tla(a)?, sub(v)?),
        Fair(w, v, a) => format!("{}_{}({})", if *w { "WF" } else { "SF" }, sub(v)?, tla(a)?),
        // Labels change nothing in what a formula means
        Label(n, _, b) if pos_of(n).is_some() || err_pos_of(n).is_some() || n.ends_with("::") || n.starts_with(crate::ast::SUBVAR) || n.starts_with(crate::ast::FN) || n == crate::ast::ENINST => tla(b)?,
        Label(n, _, b) if n == crate::parser::INFIX_JUNCTION => tla(b)?,
        _ => return Err(format!("cannot write out {}", crate::codegen::short(e))),
    })
}

/// The Rust static `LASSO_CHECK` for the generated checker: the spec's module, then the parts of
/// Tla2rsLasso.tla before and after the lasso's states, Tla2rsLasso.cfg, and the lines added to the
/// cfg when the lasso returns to its entry only under the VIEW; or why they cannot be written
pub fn template(m: &Module, cfg: &Cfg, written: &Result<Written, String>) -> String {
    let r = (|| -> Result<[String; 5], String> {
        let w = written.as_ref().map_err(|e| e.clone())?;
        let next = w.next.as_ref().ok_or("no next-state relation")?;
        // The model values of the cfg that the module does not declare as constants (VIEW and
        // SYMMETRY are left out: the lasso is checked as a behavior of the spec itself)
        let mut mvs: Vec<String> = vec![];
        for (_, v) in &cfg.constants {
            model_values(v, &mut mvs);
        }
        for (_, _, v) in &cfg.mod_values {
            model_values(v, &mut mvs);
        }
        mvs.retain(|n| !m.constants.contains(n));
        let mut pre = String::new();
        if !mvs.is_empty() {
            pre += &format!("CONSTANTS {}\n", mvs.join(", "));
        }
        pre += "VARIABLE tla2rsAt\n";
        let vars: Vec<String> = m.variables.iter().cloned().chain(["tla2rsAt".to_string()]).collect();
        let mut post = String::from("Tla2rsInit ==\n  /\\ tla2rsAt = 1\n  /\\ Tla2rsState1\n");
        for e in &w.init {
            post += &format!("  /\\ {}\n", tla(e)?);
        }
        post += &format!("Tla2rsNext ==\n  /\\ Tla2rsStep\n  /\\ {}\n", tla(next)?);
        post += &format!("Tla2rsVars == <<{}>>\n", vars.join(", "));
        post += "Tla2rsSpec ==\n  /\\ Tla2rsInit\n  /\\ [][Tla2rsNext]_Tla2rsVars\n  /\\ WF_Tla2rsVars(Tla2rsNext)\n";
        for e in &w.temporal {
            post += &format!("  /\\ {}\n", tla(e)?);
        }
        let mut c = String::from("CONSTANTS\n");
        for (n, v) in &cfg.constants {
            c += &format!("  {n} = {}\n", tla(v)?);
        }
        for (n, mm, v) in &cfg.mod_values {
            c += &format!("  {n} = [{mm}] {}\n", tla(v)?);
        }
        for (n, module, d) in &cfg.substs {
            match module {
                Some(mm) => c += &format!("  {n} <- [{mm}] {d}\n"),
                None => c += &format!("  {n} <- {d}\n"),
            }
        }
        for n in &mvs {
            c += &format!("  {n} = {n}\n");
        }
        c += "SPECIFICATION Tla2rsSpec\n";
        if !cfg.properties.is_empty() {
            c += &format!("PROPERTIES {}\n", cfg.properties.join(" "));
        }
        if !cfg.constraints.is_empty() {
            c += &format!("CONSTRAINTS {}\n", cfg.constraints.join(" "));
        }
        if !cfg.action_constraints.is_empty() {
            c += &format!("ACTION_CONSTRAINTS {}\n", cfg.action_constraints.join(" "));
        }
        c += "CHECK_DEADLOCK TRUE\n";
        // For a lasso that returns to a state equal to its entry only under the VIEW: the cfg lines
        // that fold states as the spec's cfg does, with the position kept apart
        let mut fold = String::new();
        if let Some(v) = &cfg.view {
            post += &format!("Tla2rsView == <<tla2rsAt, {v}>>\n");
            fold += "VIEW Tla2rsView\n";
            if let Some(s) = &cfg.symmetry {
                fold += &format!("SYMMETRY {s}\n");
            }
        }
        Ok([m.name.clone(), pre, post, c, fold])
    })();
    match r {
        Ok(parts) => format!("static LASSO_CHECK: Result<[&str; 5], &str> = Ok({parts:?});\n"),
        Err(e) => format!("static LASSO_CHECK: Result<[&str; 5], &str> = Err({e:?});\n"),
    }
}

fn model_values(e: &Expr, out: &mut Vec<String>) {
    if let Some(n) = matches!(e, Expr::Ident(_, _)).then_some(e).and_then(|e| match e {
        Expr::Ident(n, _) => n.strip_prefix("@model:"),
        _ => None,
    }) {
        if !out.iter().any(|x| x == n) {
            out.push(n.to_string());
        }
    }
    for c in e.children() {
        model_values(c, out);
    }
}
