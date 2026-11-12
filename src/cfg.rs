//! TLC .cfg files (common directives only)

use crate::ast::Expr;
use crate::lexer::{lex, Tok, R};

#[derive(Debug, Default)]
pub struct Cfg {
    pub specification: Option<String>,
    pub init: Option<String>,
    pub next: Option<String>,
    /// CONSTANT name = value. Values are kept as expressions (model values as Ident)
    pub constants: Vec<(String, Expr)>,
    /// CONSTANT name <- def and name <- [module] def: (name, module, def)
    pub substs: Vec<(String, Option<String>, String)>,
    pub invariants: Vec<String>,
    pub properties: Vec<String>,
    pub check_deadlock: Option<bool>,
    pub constraints: Vec<String>,
    pub action_constraints: Vec<String>,
    pub view: Option<String>,
    pub symmetry: Option<String>,
    /// CONSTANT name = [module] value: the definition `name` of that module (also when it is
    /// instantiated) replaced by the value, as TLC does (measured on TLC 2.19)
    pub mod_values: Vec<(String, String, Expr)>,
}

pub fn parse_cfg(src: &str) -> R<Cfg> {
    let toks = lex(src)?;
    let mut c = Cfg::default();
    let mut i = 0;
    let kw = |t: &Tok| -> Option<String> {
        match t {
            Tok::Ident(s)
                if matches!(
                    s.as_str(),
                    "SPECIFICATION" | "INIT" | "NEXT" | "CONSTANT" | "CONSTANTS" | "INVARIANT"
                        | "INVARIANTS" | "PROPERTY" | "PROPERTIES" | "CHECK_DEADLOCK" | "SYMMETRY"
                        | "VIEW" | "CONSTRAINT" | "CONSTRAINTS" | "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS"
                        | "TYPE" | "TYPE_CONSTRAINT" | "ALIAS" | "POSTCONDITION"
                ) =>
            {
                Some(s.clone())
            }
            _ => None,
        }
    };
    let mut section = String::new();
    while toks[i].tok != Tok::Eof {
        if let Some(k) = kw(&toks[i].tok) {
            section = k;
            i += 1;
            continue;
        }
        let name = match &toks[i].tok {
            Tok::Ident(s) => s.clone(),
            t => return Err(format!("cfg line {}: unexpected {t:?}", toks[i].line)),
        };
        i += 1;
        match section.as_str() {
            "SPECIFICATION" => c.specification = Some(name),
            "INIT" => c.init = Some(name),
            "NEXT" => c.next = Some(name),
            "INVARIANT" | "INVARIANTS" => c.invariants.push(name),
            "PROPERTY" | "PROPERTIES" => c.properties.push(name),
            "CHECK_DEADLOCK" => c.check_deadlock = Some(name == "TRUE"),
            "CONSTRAINT" | "CONSTRAINTS" => c.constraints.push(name),
            "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => c.action_constraints.push(name),
            // TLC accepts these and does nothing with them
            "TYPE" | "TYPE_CONSTRAINT" => {}
            // Later TLC versions read these; TLC 2.19 does not know them and stops with an error
            "ALIAS" | "POSTCONDITION" => {
                return Err(format!("cfg line {}: {section} is not a section TLC 2.19 accepts", toks[i - 1].line))
            }
            "VIEW" => c.view = Some(name),
            "SYMMETRY" => c.symmetry = Some(name),
            "CONSTANT" | "CONSTANTS" => {
                match &toks[i].tok {
                    Tok::Sym(s) if s == "=" => {}
                    Tok::Sym(s) if s == "<-" => {
                        i += 1;
                        let mut module = None;
                        if matches!(&toks[i].tok, Tok::Sym(s) if s == "[") {
                            let (Tok::Ident(m), Tok::Sym(close)) = (&toks[i + 1].tok, &toks[i + 2].tok) else {
                                return Err(format!("cfg line {}: expected `[Module]` after `{name} <-`", toks[i].line));
                            };
                            if close != "]" {
                                return Err(format!("cfg line {}: expected `]` after `[{m}`", toks[i].line));
                            }
                            module = Some(m.clone());
                            i += 3;
                        }
                        let Tok::Ident(def) = &toks[i].tok else {
                            return Err(format!("cfg line {}: expected a definition name after `{name} <-`", toks[i].line));
                        };
                        c.substs.push((name, module, def.clone()));
                        i += 1;
                        continue;
                    }
                    t => return Err(format!("cfg line {}: expected `=` after {name}, got {t:?}", toks[i].line)),
                }
                i += 1;
                if matches!(&toks[i].tok, Tok::Sym(s) if s == "[") {
                    let (Tok::Ident(m), Tok::Sym(close)) = (&toks[i + 1].tok, &toks[i + 2].tok) else {
                        return Err(format!("cfg line {}: expected `[Module]` after `{name} =`", toks[i].line));
                    };
                    if close != "]" {
                        return Err(format!("cfg line {}: expected `]` after `[{m}`", toks[i].line));
                    }
                    let m = m.clone();
                    let (v, ni) = cfg_value(&toks, i + 3)?;
                    i = ni;
                    c.mod_values.push((name, m, v));
                    continue;
                }
                let (v, ni) = cfg_value(&toks, i)?;
                i = ni;
                c.constants.push((name, v));
            }
            s => return Err(format!("cfg: section {s} is not supported yet")),
        }
    }
    Ok(c)
}

fn cfg_value(toks: &[crate::lexer::Token], mut i: usize) -> R<(Expr, usize)> {
    let t = &toks[i].tok;
    i += 1;
    Ok(match t {
        Tok::Num(n) => (Expr::Num(*n), i),
        // TLC accepts only natural numbers here
        Tok::Sym(s) if s == "-" => return Err("cfg: TLC does not accept a negative number as a constant value".into()),
        Tok::Str(s) => (Expr::Str(s.clone()), i),
        Tok::Ident(s) if s == "TRUE" || s == "FALSE" => (Expr::Bool(s == "TRUE"), i),
        // Model value. Prefixed with `@model:` to keep it distinct from constant names
        Tok::Ident(s) => (Expr::Ident(format!("@model:{s}")), i),
        Tok::Sym(s) if s == "{" => {
            let mut v = vec![];
            loop {
                if matches!(&toks[i].tok, Tok::Sym(s) if s == "}") {
                    i += 1;
                    break;
                }
                let (e, ni) = cfg_value(toks, i)?;
                v.push(e);
                i = ni;
                if matches!(&toks[i].tok, Tok::Sym(s) if s == ",") {
                    i += 1;
                }
            }
            (Expr::SetLit(v), i)
        }
        t => return Err(format!("cfg: unsupported constant value {t:?}")),
    })
}
