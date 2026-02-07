extern crate alloc;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use crate::spine::Literal;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxExpr {
    Root(Vec<SyntaxExpr>),
    Def {
        name: String,
        binders: Vec<SyntaxBinder>,
        return_type: Box<SyntaxExpr>,
        body: Box<SyntaxExpr>,
    },
    Var(String),
    Constructor(String),
    App(Box<SyntaxExpr>, Box<SyntaxExpr>),
    Lambda {
        binders: Vec<SyntaxBinder>,
        body: Box<SyntaxExpr>,
    },
    Let {
        name: String,
        type_ann: Option<Box<SyntaxExpr>>,
        value: Box<SyntaxExpr>,
        body: Box<SyntaxExpr>,
    },
    Lit(Literal),
    Tuple(Vec<SyntaxExpr>),
    Proj(Box<SyntaxExpr>, String),
    Hole,
    Arrow(Box<SyntaxExpr>, Box<SyntaxExpr>),
    List(Box<SyntaxExpr>),
    Pi(SyntaxBinder, Box<SyntaxExpr>),
    Sigma(SyntaxBinder, Box<SyntaxExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxBinder {
    Explicit(String, Box<SyntaxExpr>),
    Implicit(String, Box<SyntaxExpr>),
    Instance(String, Box<SyntaxExpr>),
}
