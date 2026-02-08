use core::fmt::Display;

use alloc::{boxed::Box, format, string::{String, ToString}};
use miette::{Diagnostic, LabeledSpan};
use crate::syntax::Span;

#[derive(Debug)]
pub struct ElabError {
    pub kind: ElabErrorKind,
    pub span: Span
}

impl ElabError {
    pub fn new(kind: ElabErrorKind, span: Span) -> Self {
        Self { kind, span }
    }
}

impl Display for ElabError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.kind {
            ElabErrorKind::ExpectedRoot => write!(f, "expected a root-level declaration"),
            ElabErrorKind::UndefinedVariable(name) => write!(f, "undefined variable '{}'", name),
            ElabErrorKind::UndefinedConstructor(name) => write!(f, "undefined constructor '{}'", name),
            ElabErrorKind::TypeMismatch { expected, found } => write!(f, "type mismatch: expected '{:?}', found '{:?}'", expected, found),
            ElabErrorKind::UnsupportedSyntax(syntax) => write!(f, "unsupported syntax: '{:?}'", syntax),
            ElabErrorKind::NotAFunction(term) => write!(f, "not a function: '{:?}'", term),
        }
    }
}

#[derive(Debug)]
pub enum ElabErrorKind {
    ExpectedRoot,
    UndefinedVariable(String),
    UndefinedConstructor(String),
    TypeMismatch { expected: crate::spine::Term, found: crate::spine::Term },
    UnsupportedSyntax(crate::syntax::tree::SyntaxExpr),
    NotAFunction(crate::spine::Term),
}

impl miette::StdError for ElabError {}

impl Diagnostic for ElabError {
    fn severity(&self) -> Option<miette::Severity> {
        Some(miette::Severity::Error)
    }
    
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let label = match &self.kind {
            ElabErrorKind::ExpectedRoot => "expected a root-level declaration".to_string(),
            ElabErrorKind::UndefinedVariable(name) => format!("undefined variable '{}'", name),
            ElabErrorKind::UndefinedConstructor(name) => format!("undefined constructor '{}'", name),
            ElabErrorKind::TypeMismatch { expected, found } => format!("type mismatch: expected '{:?}', found '{:?}'", expected, found),
            ElabErrorKind::UnsupportedSyntax(syntax) => format!("unsupported syntax: '{:?}'", syntax),
            ElabErrorKind::NotAFunction(term) => format!("not a function: '{:?}'", term),
        };
        Some(Box::new(core::iter::once(LabeledSpan::new(
            Some(label),
            self.span.start,
            self.span.end.saturating_sub(self.span.start).max(1)
        ))))
    }
}