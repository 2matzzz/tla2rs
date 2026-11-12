//! Syntax tree. Operator definitions are inlined before type checking and code generation.

#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Num(i64),
    Str(String),
    Bool(bool),
    /// A variable, constant, bound variable, or zero-argument operator
    Ident(String),
    /// An operator application (including built-ins such as Cardinality)
    Call(String, Vec<Expr>),
    Prime(Box<Expr>),
    Un(UOp, Box<Expr>),
    Bin(BOp, Box<Expr>, Box<Expr>),
    And(Vec<Expr>),
    Or(Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Case(Vec<(Expr, Expr)>, Option<Box<Expr>>),
    /// true = \E, false = \A
    Quant(bool, Vec<(String, Expr)>, Box<Expr>),
    Choose(String, Box<Expr>, Box<Expr>),
    SetLit(Vec<Expr>),
    SetFilter(String, Box<Expr>, Box<Expr>),
    SetMap(Box<Expr>, Vec<(String, Expr)>),
    FunCons(String, Box<Expr>, Box<Expr>),
    FunSet(Box<Expr>, Box<Expr>),
    RecLit(Vec<(String, Expr)>),
    RecSet(Vec<(String, Expr)>),
    App(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, String),
    Except(Box<Expr>, Vec<(Vec<Path>, Expr)>),
    At,
    Tuple(Vec<Expr>),
    Let(Vec<Def>, Box<Expr>),
    /// [A]_v
    BoxAction(Box<Expr>, Box<Expr>),
    /// WF_v(A) / SF_v(A); true = weak
    Fair(bool, Box<Expr>, Box<Expr>),
    /// Marks where an operator was inlined: its name and (expanded) arguments.
    Label(String, Vec<Expr>, Box<Expr>),
    /// LAMBDA x, y : e (only as the argument of an operator parameter)
    Lambda(Vec<String>, Box<Expr>),
    /// A call of a recursive operator that is not inlined: an index into `expand::rec_def` and the
    /// (expanded) arguments
    RecCall(usize, Vec<Expr>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Path {
    Idx(Expr),
    Field(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UOp {
    Not,
    Neg,
    Always,
    Eventually,
    Subset,
    Union,
    Domain,
    Unchanged,
    Enabled,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BOp {
    Implies,
    Equiv,
    LeadsTo,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    In,
    NotIn,
    Subseteq,
    Cup,
    Cap,
    SetMinus,
    Range,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    pub name: String,
    pub params: Vec<String>,
    /// Per parameter, the number of arguments it takes: 0 for an ordinary parameter, n for an
    /// operator parameter `F(_, ...)`
    pub arity: Vec<usize>,
    pub body: Expr,
}

#[derive(Clone, Debug, Default)]
pub struct Module {
    pub name: String,
    /// Modules written inside this one (`---- MODULE M ---- ... ====`), which it can EXTEND or
    /// INSTANCE
    pub nested: Vec<Module>,
    pub extends: Vec<String>,
    pub constants: Vec<String>,
    pub variables: Vec<String>,
    pub defs: Vec<Def>,
    /// ASSUME / ASSUMPTION. As in TLC, a false assumption is an error before exploration starts
    pub assumes: Vec<Assume>,
    /// Names of this module and of the modules it EXTENDS from files next to it
    pub modules: Vec<String>,
    /// CONSTANTs declared with parameters (`CONSTANT F(_, _)`) and their number of parameters
    pub op_constants: Vec<(String, usize)>,
    /// Operators declared RECURSIVE (also in LET), and the operators that recursive function
    /// definitions are turned into
    pub recursive: Vec<String>,
    /// INSTANCE statements and definitions `N(p) == INSTANCE M WITH ...`
    pub instances: Vec<Instance>,
    /// Definitions declared LOCAL (not visible to a module that instantiates this one)
    pub local_defs: Vec<String>,
    /// For each INSTANCE: the prefix of the hidden names of its definitions (`M#iK#`), the
    /// prefix TLC names them with (`N!` or nothing), and the number of constants and variables
    /// substituted
    pub inst_prefixes: Vec<(String, String, usize)>,
    /// The module's statements in the order written, for SANY's scoping (see `sany.rs`)
    pub units: Vec<Unit>,
}

/// A statement of a module, in the order written. SANY resolves a name only against what is
/// declared or defined before it
#[derive(Clone, Debug)]
pub enum Unit {
    /// A CONSTANT or VARIABLE
    Decl(String),
    /// A definition (an index into `defs`); `true` for a function definition `f[x \in S] == e`,
    /// whose name is in scope in its body
    Def(usize, bool),
    /// The name of a THEOREM (or the like), whose formula is not checked
    Theorem(String),
    /// An unnamed ASSUME (an index into `assumes`)
    Assume(usize),
    /// An INSTANCE statement or definition (an index into `instances`); `true` when LOCAL
    Inst(usize, bool),
    /// A RECURSIVE declaration
    Recursive(String),
    /// A nested module (an index into `nested`)
    Nested(usize),
}

/// `[LOCAL] INSTANCE M WITH x <- e, ...` (no name) or `N(p, ...) == INSTANCE M WITH ...`
#[derive(Clone, Debug)]
pub struct Instance {
    pub name: Option<String>,
    pub params: Vec<String>,
    /// Per parameter, the number of arguments it takes (0 for an ordinary parameter)
    pub arity: Vec<usize>,
    pub module: String,
    pub subs: Vec<(String, Expr)>,
    /// The position of the statement as TLC prints it (see POS)
    pub at: String,
}

/// An ASSUME expression and the position TLC reports on failure (1-based line and column; the end
/// column is inclusive)
#[derive(Clone, Debug)]
pub struct Assume {
    pub module: String,
    pub expr: Expr,
    pub span: (usize, usize, usize, usize),
}

/// The name of the label that records where an expression is written: `#pos` followed by the
/// position as TLC prints it (`line 3, col 9 to line 4, col 20 of module M`). The parser puts one
/// around the subexpressions TLC can name an action by (see `Gen::gen_split`): definition bodies,
/// disjuncts, the bodies of `\E`, LET and labels, and the action of `[A]_v`. Expansion drops them
/// except while expanding the next-state relation (`Expander::keep_pos`).
pub const POS: &str = "#pos ";

/// The name of the label that records where an expression whose evaluation can fail is written,
/// for TLC's messages: `#at ` followed by the position as TLC prints it. The parser puts one
/// around CASE and CHOOSE (whose errors TLC reports with their position), around labels, RTnow and
/// RTBound (temporal formulas TLC refuses by position) and around `[]` (TLC names a part of a
/// property by position). Expansion keeps it; code generation, constant evaluation and the
/// liveness compiler read it (`codegen::err_at`, `live::refused`, `split_property`).
pub const AT: &str = "#at ";

/// The name of the label `parse_module_spans` puts around temporal operators and infix junctions:
/// `#span ` followed by the position as SANY prints it, for SANY's report of a level error
pub const SPAN: &str = "#span ";

/// The name of the label the parser puts around a function constructor `[x \in S |-> e]`: `#fn `
/// followed by how TLC prints the function when it cannot enumerate S (`FcnLambdaValue`): its
/// bound variables with `\u{2}k\u{3}` where the k-th part of the domain goes (`*` for the whole
/// domain), `\u{1}`, and its body, a number as written or the body's position. Read by
/// `codegen::lazy_fun_string`
pub const FN: &str = "#fn ";

/// `e` wrapped in an AT label for the position `at`
pub fn at_err(at: &str, e: Expr) -> Expr {
    Expr::Label(format!("{AT}{at}"), vec![], e.b())
}

/// The position recorded by an AT label named `n`
pub fn err_pos_of(n: &str) -> Option<&str> {
    n.strip_prefix(AT)
}

/// `e` wrapped in a POS label for the position `at`
pub fn at_pos(at: &str, e: Expr) -> Expr {
    Expr::Label(format!("{POS}{at}"), vec![], e.b())
}

/// The name of the label around what a variable of an instantiated module stands for, when an
/// INSTANCE substitutes another expression for it: `#var ` followed by the variable's name. It
/// changes nothing, except where TLC computes whether an action is enabled in an ENABLED or a
/// WF / SF written in the instantiated module (marked with ENINST): there TLC binds a primed
/// variable by its name and does not read the substitution (`Gen::gen_phantom`, measured on TLC
/// 2.19, `tests/tlc/EnSubst*`)
pub const SUBVAR: &str = "#var ";

/// The name of the label around the action of an ENABLED, WF or SF written in an instantiated
/// module (see SUBVAR). An ENABLED written in the instantiating module reads the substitutions
pub const ENINST: &str = "#en_inst";

/// For an expression that is a substituted variable of an instantiated module (inside other
/// labels): the variable's name and what it stands for
pub fn subvar_of(e: &Expr) -> Option<(&str, &Expr)> {
    match e {
        Expr::Label(n, _, b) => match n.strip_prefix(SUBVAR) {
            Some(v) => Some((v, b)),
            None => subvar_of(b),
        },
        _ => None,
    }
}

/// The position recorded by a POS label named `n`
pub fn pos_of(n: &str) -> Option<&str> {
    n.strip_prefix(POS)
}

/// `e` without POS labels
pub fn strip_pos(e: &Expr) -> Expr {
    match e {
        Expr::Label(n, _, b) if pos_of(n).is_some() => strip_pos(b),
        _ => crate::codegen::map_children(e, &strip_pos),
    }
}

impl Expr {
    pub fn b(self) -> Box<Expr> {
        Box::new(self)
    }

    /// Visits the children in order (read-only)
    pub fn children(&self) -> Vec<&Expr> {
        use Expr::*;
        match self {
            Num(_) | Str(_) | Bool(_) | Ident(_) | At => vec![],
            Call(_, a) | And(a) | Or(a) | SetLit(a) | Tuple(a) => a.iter().collect(),
            Prime(x) | Un(_, x) | Field(x, _) => vec![x],
            Bin(_, a, b) | App(a, b) | FunSet(a, b) | BoxAction(a, b) | Fair(_, a, b) => vec![a, b],
            If(a, b, c) => vec![a, b, c],
            Case(arms, o) => {
                let mut v: Vec<&Expr> = arms.iter().flat_map(|(a, b)| [a, b]).collect();
                if let Some(o) = o {
                    v.push(o);
                }
                v
            }
            Quant(_, bs, body) => {
                let mut v: Vec<&Expr> = bs.iter().map(|(_, s)| s).collect();
                v.push(body);
                v
            }
            SetMap(e, bs) => {
                let mut v: Vec<&Expr> = bs.iter().map(|(_, s)| s).collect();
                v.push(e);
                v
            }
            Choose(_, s, p) | SetFilter(_, s, p) | FunCons(_, s, p) => vec![s, p],
            RecLit(fs) | RecSet(fs) => fs.iter().map(|(_, e)| e).collect(),
            Except(f, us) => {
                let mut v = vec![f.as_ref()];
                for (path, val) in us {
                    for p in path {
                        if let Path::Idx(e) = p {
                            v.push(e);
                        }
                    }
                    v.push(val);
                }
                v
            }
            Let(defs, body) => {
                let mut v: Vec<&Expr> = defs.iter().map(|d| &d.body).collect();
                v.push(body);
                v
            }
            Lambda(_, body) => vec![body],
            RecCall(_, a) => a.iter().collect(),
            Label(_, args, body) => {
                let mut v: Vec<&Expr> = args.iter().collect();
                v.push(body);
                v
            }
        }
    }

    pub fn any(&self, f: &dyn Fn(&Expr) -> bool) -> bool {
        f(self) || self.children().into_iter().any(|c| c.any(f))
    }

    /// Whether this contains a prime, UNCHANGED or [A]_v outside ENABLED (i.e. is action-level;
    /// ENABLED A is a state predicate)
    pub fn is_action(&self) -> bool {
        match self {
            Expr::Prime(_) | Expr::Un(UOp::Unchanged, _) | Expr::BoxAction(..) => true,
            Expr::Un(UOp::Enabled, _) => false,
            e => e.children().into_iter().any(|c| c.is_action()),
        }
    }

    /// Whether this is \EE, \AA or -+-> (temporal operators TLC cannot check)
    pub fn is_unchecked_temporal(&self) -> bool {
        matches!(self, Expr::Call(n, _) if n == "\\EE" || n == "\\AA" || n == "-+->")
    }

    /// Whether this is a label written in the spec (`l :: e`), as opposed to a call site
    pub fn is_user_label(&self) -> bool {
        matches!(self, Expr::Label(n, ..) if n.ends_with("::"))
    }

    /// Strips POS labels (see POS)
    pub fn unpos(&self) -> &Expr {
        match self {
            Expr::Label(n, _, b) if pos_of(n).is_some() => b.unpos(),
            e => e,
        }
    }

    /// Strips Label wrappers
    pub fn strip(&self) -> &Expr {
        match self {
            Expr::Label(_, _, b) => b.strip(),
            e => e,
        }
    }
}
