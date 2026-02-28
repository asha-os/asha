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
        return_type: SyntaxExpr,
        body: DefBody,
        span: Span,
    },
    Class {
        attributes: Vec<SyntaxAttribute>,
        name: String,
        binders: Vec<SyntaxBinder>,
        members: Vec<RecordField>,
        span: Span,
    },
    Instance {
        name: String,
        binders: Vec<SyntaxBinder>,
        type_ann: SyntaxExpr,
        members: Vec<InstanceMember>,
        span: Span,
    },
    Record {
        attributes: Vec<SyntaxAttribute>,
        name: String,
        binders: Vec<SyntaxBinder>,
        fields: Vec<RecordField>,
        span: Span,
    },
    Extern {
        name: String,
        type_ann: SyntaxExpr,
        span: Span,
    },
    Inductive {
        name: String,
        attributes: Vec<SyntaxAttribute>,
        index_type: Option<SyntaxExpr>,
        binders: Vec<SyntaxBinder>,
        constructors: Vec<InductiveConstructor>,
        span: Span,
    },
    Eval {
        expr: SyntaxExpr,
        span: Span,
    },
    Alias {
        name: String,
        binders: Vec<SyntaxBinder>,
        type_ann: Option<SyntaxExpr>,
        value: SyntaxExpr,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefBody {
    Expr(SyntaxExpr),
    PatternMatch {
        arms: Vec<PatternMatchArm>,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PatternMatchArm {
    pub patterns: Vec<SyntaxPattern>,
    pub rhs: Box<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField {
    pub attributes: Vec<SyntaxAttribute>,
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
    pub value: SyntaxExpr,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveConstructor {
    pub name: String,
    pub binders: Vec<SyntaxBinder>,
    pub type_ann: Option<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxPattern {
    Var(String, Span),
    Constructor {
        namespace: Vec<String>,
        name: String,
        args: Vec<SyntaxPattern>,
        span: Span,
    },
    Lit(Literal, Span),
    Wildcard(Span),
    Tuple {
        elements: Vec<SyntaxPattern>,
        span: Span,
    },
    As {
        name: String,
        pattern: Box<SyntaxPattern>,
        span: Span,
    },
    Or(Vec<SyntaxPattern>, Span),
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
    pub patterns: Vec<SyntaxPattern>,
    pub rhs: Box<SyntaxExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxAttribute {
    pub name: String,
    pub args: Vec<SyntaxExpr>,
    pub span: Span,
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
            SyntaxExpr::Var { span, .. }
            | SyntaxExpr::Constructor { span, .. }
            | SyntaxExpr::App { span, .. }
            | SyntaxExpr::Lambda { span, .. }
            | SyntaxExpr::Let { span, .. }
            | SyntaxExpr::Lit { span, .. }
            | SyntaxExpr::Tuple { span, .. }
            | SyntaxExpr::Proj { span, .. }
            | SyntaxExpr::Hole(span)
            | SyntaxExpr::Arrow { span, .. }
            | SyntaxExpr::Array { span, .. }
            | SyntaxExpr::Pi { span, .. }
            | SyntaxExpr::Sigma { span, .. }
            | SyntaxExpr::Unit(span)
            | SyntaxExpr::InfixOp { span, .. }
            | SyntaxExpr::RecordLiteral { span, .. }
            | SyntaxExpr::Match { span, .. } => *span,
        }
    }
}

impl Spanned for SyntaxBinder {
    fn span(&self) -> Span {
        match self {
            SyntaxBinder::Explicit(span, ..)
            | SyntaxBinder::Implicit(span, ..)
            | SyntaxBinder::Instance(span, ..) => *span,
        }
    }
}

impl Spanned for SyntaxPattern {
    fn span(&self) -> Span {
        match self {
            SyntaxPattern::Var(_, span)
            | SyntaxPattern::Constructor { span, .. }
            | SyntaxPattern::Lit(_, span)
            | SyntaxPattern::Wildcard(span)
            | SyntaxPattern::Tuple { span, .. }
            | SyntaxPattern::As { span, .. }
            | SyntaxPattern::Or(_, span) => *span,
        }
    }
}

impl Spanned for SyntaxTreeDeclaration {
    fn span(&self) -> Span {
        match self {
            SyntaxTreeDeclaration::Def { span, .. }
            | SyntaxTreeDeclaration::Class { span, .. }
            | SyntaxTreeDeclaration::Instance { span, .. }
            | SyntaxTreeDeclaration::Record { span, .. }
            | SyntaxTreeDeclaration::Extern { span, .. }
            | SyntaxTreeDeclaration::Inductive { span, .. }
            | SyntaxTreeDeclaration::Eval { span, .. }
            | SyntaxTreeDeclaration::Alias { span, .. } => *span,
        }
    }
}

impl Spanned for DefBody {
    fn span(&self) -> Span {
        match self {
            DefBody::Expr(expr) => expr.span(),
            DefBody::PatternMatch { span, .. } => *span,
        }
    }
}

impl Spanned for PatternMatchArm {
    fn span(&self) -> Span {
        self.span
    }
}

impl<T: Spanned> Spanned for Vec<T> {
    fn span(&self) -> Span {
        if self.is_empty() {
            Span {
                file: 0,
                start: 0,
                end: 0,
            }
        } else {
            let file_id = self[0].span().file;
            let (min_start, max_end) =
                self.iter()
                    .fold((usize::MAX, 0), |(min_start, max_end), item| {
                        let span = item.span();
                        (min_start.min(span.start), max_end.max(span.end))
                    });
            Span::new(file_id, min_start, max_end - min_start)
        }
    }
}
