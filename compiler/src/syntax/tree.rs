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
pub struct SyntaxTree {
    pub declarations: Vec<SyntaxTreeDeclaration>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxTreeDeclaration {
    Def {
        name: String,
        binders: Vec<SyntaxBinder>,
        return_type: Box<SyntaxExpr>,
        body: Box<SyntaxExpr>,
        span: Span,
    },
    Class {
        name: String,
        binders: Vec<SyntaxBinder>,
        members: Vec<RecordField>,
        span: Span,
    },
    Instance {
        name: String,
        binders: Vec<SyntaxBinder>,
        type_ann: Box<SyntaxExpr>,
        members: Vec<InstanceMember>,
        span: Span,
    },
    Record {
        name: String,
        binders: Vec<SyntaxBinder>,
        fields: Vec<RecordField>,
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
        constructors: Vec<InductiveConstructor>,
        span: Span,
    },
    Eval {
        expr: Box<SyntaxExpr>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub name: String,
    pub type_ann: Box<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordLiteralField {
    pub name: String,
    pub value: Box<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceMember {
    pub name: String,
    pub value: Box<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveConstructor {
    pub name: String,
    pub binders: Vec<SyntaxBinder>,
    pub type_ann: Option<Box<SyntaxExpr>>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxExpr {
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
    InfixOp {
        op: InfixOp,
        lhs: Box<SyntaxExpr>,
        rhs: Box<SyntaxExpr>,
        span: Span,
    },
    RecordLiteral {
        fields: Vec<RecordLiteralField>,
        span: Span,
    },
    Match {
        scrutinees: Vec<SyntaxExpr>,
        arms: Vec<MatchArm>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub patterns: Vec<Pattern>,
    pub rhs: Box<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Var(String, Span),
    Constructor(Vec<String>, String, Vec<Pattern>, Span),
    Lit(Literal, Span),
    Wildcard(Span),
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
            SyntaxExpr::Unit(span) => *span,
            SyntaxExpr::InfixOp { span, .. } => *span,
            SyntaxExpr::RecordLiteral { span, .. } => *span,
            SyntaxExpr::Match { span, .. } => *span,
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
