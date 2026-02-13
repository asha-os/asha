extern crate alloc;

use crate::spine::Literal;
use crate::syntax::{Span, Spanned};
use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InfixOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxExpr {
    Root(Vec<SyntaxExpr>),
    Def {
        name: String,
        binders: Vec<SyntaxBinder>,
        return_type: Box<SyntaxExpr>,
        body: Box<SyntaxExpr>,
        span: Span,
    },
    Var {
        namespace: Vec<String>,
        member: String,
        span: Span,
    },
    Constructor {
        namespace: Vec<String>,
        name: String,
        span: Span,
    },
    App {
        fun: Box<SyntaxExpr>,
        arg: Box<SyntaxExpr>,
        span: Span,
    },
    Lambda {
        binders: Vec<SyntaxBinder>,
        body: Box<SyntaxExpr>,
        span: Span,
    },
    Let {
        name: String,
        type_ann: Option<Box<SyntaxExpr>>,
        value: Box<SyntaxExpr>,
        body: Box<SyntaxExpr>,
        span: Span,
    },
    Lit {
        value: Literal,
        span: Span,
    },
    Tuple {
        elements: Vec<SyntaxExpr>,
        span: Span,
    },
    Proj {
        value: Box<SyntaxExpr>,
        field: String,
        span: Span,
    },
    Hole(Span),
    Unit(Span),
    Arrow {
        param_type: Box<SyntaxExpr>,
        return_type: Box<SyntaxExpr>,
        span: Span,
    },
    Array {
        elements: Vec<SyntaxExpr>,
        span: Span,
    },
    Pi {
        binder: SyntaxBinder,
        codomain: Box<SyntaxExpr>,
        span: Span,
    },
    Sigma {
        binder: SyntaxBinder,
        codomain: Box<SyntaxExpr>,
        span: Span,
    },
    Eval {
        expr: Box<SyntaxExpr>,
        span: Span,
    },
    Record {
        name: String,
        binders: Vec<SyntaxBinder>,
        fields: Vec<SyntaxExpr>,
        span: Span,
    },
    RecordField {
        name: String,
        type_ann: Box<SyntaxExpr>,
        span: Span,
    },
    RecordLiteral {
        fields: Vec<SyntaxExpr>,
        span: Span,
    },
    RecordLiteralField {
        name: String,
        value: Box<SyntaxExpr>,
        span: Span,
    },
    Extern {
        name: String,
        type_ann: Box<SyntaxExpr>,
        span: Span,
    },
    Inductive {
        name: String,
        binders: Vec<SyntaxBinder>,
        constructors: Vec<SyntaxExpr>,
        span: Span,
    },
    InductiveConstructor {
        name: String,
        binders: Vec<SyntaxBinder>,
        type_ann: Option<Box<SyntaxExpr>>,
        span: Span,
    },
    InfixOp {
        op: InfixOp,
        lhs: Box<SyntaxExpr>,
        rhs: Box<SyntaxExpr>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxBinder {
    Explicit(Span, String, Box<SyntaxExpr>),
    Implicit(Span, String, Box<SyntaxExpr>),
    Instance(Span, String, Box<SyntaxExpr>),
}

impl Spanned for SyntaxExpr {
    fn span(&self) -> Span {
        match self {
            SyntaxExpr::Root(_) => Span {
                file: 0,
                start: 0,
                end: 0,
            },
            SyntaxExpr::Def { span, .. } => *span,
            SyntaxExpr::Var { span, .. } => *span,
            SyntaxExpr::Constructor { span, .. } => *span,
            SyntaxExpr::App { span, .. } => *span,
            SyntaxExpr::Lambda { span, .. } => *span,
            SyntaxExpr::Let { span, .. } => *span,
            SyntaxExpr::Lit { span, .. } => *span,
            SyntaxExpr::Tuple { span, .. } => *span,
            SyntaxExpr::Proj { span, .. } => *span,
            SyntaxExpr::Hole(span) => *span,
            SyntaxExpr::Arrow { span, .. } => *span,
            SyntaxExpr::Array { span, .. } => *span,
            SyntaxExpr::Pi { span, .. } => *span,
            SyntaxExpr::Sigma { span, .. } => *span,
            SyntaxExpr::Eval { span, .. } => *span,
            SyntaxExpr::Record { span, .. } => *span,
            SyntaxExpr::RecordField { span, .. } => *span,
            SyntaxExpr::RecordLiteral { span, .. } => *span,
            SyntaxExpr::RecordLiteralField { span, .. } => *span,
            SyntaxExpr::Extern { span, .. } => *span,
            SyntaxExpr::Unit(span) => *span,
            SyntaxExpr::Inductive { span, .. } => *span,
            SyntaxExpr::InductiveConstructor { span, .. } => *span,
            SyntaxExpr::InfixOp { span, .. } => *span,
        }
    }
}

impl Spanned for SyntaxBinder {
    fn span(&self) -> Span {
        match self {
            SyntaxBinder::Explicit(span, ..) => *span,
            SyntaxBinder::Implicit(span, ..) => *span,
            SyntaxBinder::Instance(span, ..) => *span,
        }
    }
}
