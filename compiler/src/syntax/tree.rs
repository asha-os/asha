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
        binders: Vec<SyntaxBinder>,
        constructors: Vec<InductiveConstructor>,
        span: Span,
    },
    Eval {
        expr: SyntaxExpr,
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

impl Spanned for SyntaxPattern {
    fn span(&self) -> Span {
        match self {
            SyntaxPattern::Var(_, span) => *span,
            SyntaxPattern::Constructor { span, .. } => *span,
            SyntaxPattern::Lit(_, span) => *span,
            SyntaxPattern::Wildcard(span) => *span,
            SyntaxPattern::Tuple { span, .. } => *span,
            SyntaxPattern::As { span, .. } => *span,
            SyntaxPattern::Or(_, span) => *span,
        }
    }
}

impl Spanned for SyntaxTreeDeclaration {
    fn span(&self) -> Span {
        match self {
            SyntaxTreeDeclaration::Def { span, .. } => *span,
            SyntaxTreeDeclaration::Class { span, .. } => *span,
            SyntaxTreeDeclaration::Instance { span, .. } => *span,
            SyntaxTreeDeclaration::Record { span, .. } => *span,
            SyntaxTreeDeclaration::Extern { span, .. } => *span,
            SyntaxTreeDeclaration::Inductive { span, .. } => *span,
            SyntaxTreeDeclaration::Eval { span, .. } => *span,
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
