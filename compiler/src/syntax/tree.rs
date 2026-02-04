extern crate alloc;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

pub trait Phase: core::fmt::Debug + Clone + PartialEq + Eq {
    type ExprAnn: core::fmt::Debug + Clone + PartialEq + Eq;
    type TyAnn: core::fmt::Debug + Clone + PartialEq + Eq;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed;
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Typed;

impl Phase for Parsed {
    type ExprAnn = ();
    type TyAnn = ();
}

impl Phase for Typed {
    type ExprAnn = ();
    type TyAnn = ();
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr<P: Phase> {
    pub ann: P::ExprAnn,
    pub kind: ExprKind<P>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind<P: Phase> {
    Root(Vec<Expr<P>>),
    Def {
        name: String,
        binders: Vec<Binder>,
        return_type: TypeExpr,
        body: Box<Expr<P>>,
    },
    Var(String),
    Constructor(String),
    App(Box<Expr<P>>, Box<Expr<P>>),
    Lambda {
        binders: Vec<Binder>,
        body: Box<Expr<P>>,
    },
    Let {
        name: String,
        type_ann: Option<TypeExpr>,
        value: Box<Expr<P>>,
        body: Box<Expr<P>>,
    },
    Lit(Literal),
    Tuple(Vec<Expr<P>>),
    Proj(Box<Expr<P>>, String),
    Hole,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Nat(u64),
    String(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr {
    Var(String),
    Constructor(String),
    App(Box<TypeExpr>, Box<TypeExpr>),
    Arrow(Box<TypeExpr>, Box<TypeExpr>),
    Tuple(Vec<TypeExpr>),
    List(Box<TypeExpr>),
    Pi(Binder, Box<TypeExpr>),
    Sigma(Binder, Box<TypeExpr>),
    Lit(Literal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Binder {
    Explicit(String, Box<TypeExpr>),
    Implicit(String, Box<TypeExpr>),
    Instance(String, Box<TypeExpr>),
}
