use alloc::{boxed::Box, string::String, vec::Vec};

use crate::module::{name::QualifiedName, unique::Unique};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    BVar(usize),
    FVar(Unique),
    MVar(Unique),
    App(Box<Term>, Box<Term>),
    Sort(Level),
    Const(QualifiedName),
    Lam(BinderInfo, Box<Term>, Box<Term>),
    Pi(BinderInfo, Box<Term>, Box<Term>),
    Sigma(BinderInfo, Box<Term>, Box<Term>),
    Let(Box<Term>, Box<Term>, Box<Term>),
    Lit(Literal),
    Unit,
}

impl Term {
    pub fn boxed(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn mk_app(l: Term, r: Term) -> Self {
        Self::App(l.boxed(), r.boxed())
    }

    pub fn type0() -> Self {
        Term::Sort(Level::type0())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderInfo {
    Explicit,
    Implicit,
    InstanceImplicit,
    StrictImplicit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Nat(u64),
    Str(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    MVar(Unique),
}

impl Level {
    pub fn type0() -> Self {
        Level::Succ(Box::new(Level::Zero))
    }

    pub fn type_n(n: u64) -> Self {
        let mut level = Level::Zero;
        for _ in 0..n {
            level = Level::Succ(Box::new(level));
        }
        level
    }
}

pub fn uncurry(term: Term) -> (Term, Vec<(BinderInfo, Term)>) {
    let mut args = Vec::new();
    let mut current = term;
    while let Term::Pi(info, param, body) = current {
        args.push((info, *param));
        current = *body;
    }
    (current, args)
}
