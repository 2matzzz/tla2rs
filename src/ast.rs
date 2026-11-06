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
    pub body: Expr,
}

#[derive(Debug, Default)]
pub struct Module {
    pub name: String,
    pub extends: Vec<String>,
    pub constants: Vec<String>,
    pub variables: Vec<String>,
    pub defs: Vec<Def>,
    /// ASSUME / ASSUMPTION. As in TLC, a false assumption is an error before exploration starts
    pub assumes: Vec<Assume>,
}

/// An ASSUME expression and the position TLC reports on failure (1-based line and column; the end
/// column is inclusive)
#[derive(Clone, Debug)]
pub struct Assume {
    pub module: String,
    pub expr: Expr,
    pub span: (usize, usize, usize, usize),
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

    /// Whether this contains a prime or UNCHANGED (i.e. is action-level)
    pub fn is_action(&self) -> bool {
        self.any(&|e| matches!(e, Expr::Prime(_) | Expr::Un(UOp::Unchanged, _)))
    }

    /// Strips Label wrappers
    pub fn strip(&self) -> &Expr {
        match self {
            Expr::Label(_, _, b) => b.strip(),
            e => e,
        }
    }
}
