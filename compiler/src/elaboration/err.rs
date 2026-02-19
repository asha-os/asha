use core::fmt::Display;

use crate::{
    spine::Term,
    syntax::{Span, tree::SyntaxExpr},
};
use alloc::{
    boxed::Box,
    string::{String, ToString},
};
use miette::{Diagnostic, LabeledSpan};

#[derive(Debug)]
pub struct ElabError {
    pub kind: ElabErrorKind,
    pub span: Span,
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
            ElabErrorKind::UndefinedConstructor(name) => {
                write!(f, "undefined constructor '{}'", name)
            }
            ElabErrorKind::TypeMismatch { expected, found } => write!(
                f,
                "type mismatch: expected '{}', found '{}'",
                expected, found
            ),
            ElabErrorKind::UnsupportedSyntax(syntax) => {
                write!(f, "unsupported syntax: '{:?}'", syntax)
            }
            ElabErrorKind::NotAFunction(term) => write!(f, "not a function: '{}'", term),
            ElabErrorKind::CannotProject(term, field) => {
                write!(f, "can't project field '{}' from '{}'", field, term)
            }
            ElabErrorKind::TypeExpected(term) => {
                write!(f, "type expected, got '{}'", term)
            }
            ElabErrorKind::NonExhaustiveMatch(term) => {
                if let Some(term) = term {
                    write!(f, "non-exhaustive match, missing case '{}'", term)
                } else {
                    write!(f, "non-exhaustive match")
                }
            }
            ElabErrorKind::NotInductive(term) => {
                write!(f, "not an inductive type: '{}'", term)
            }
            ElabErrorKind::NotAConstructorType(term) => {
                write!(f, "not a constructor type: '{}'", term)
            }
        }
    }
}

#[derive(Debug)]
pub enum ElabErrorKind {
    ExpectedRoot,
    UndefinedVariable(String),
    UndefinedConstructor(String),
    TypeMismatch { expected: Term, found: Term },
    UnsupportedSyntax(SyntaxExpr),
    NotAFunction(Term),
    CannotProject(Term, String),
    TypeExpected(Term),
    NonExhaustiveMatch(Option<Term>),
    NotInductive(Term),
    NotAConstructorType(Term),
}

impl miette::StdError for ElabError {}

impl Diagnostic for ElabError {
    fn severity(&self) -> Option<miette::Severity> {
        Some(miette::Severity::Error)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let label = self.to_string();
        Some(Box::new(core::iter::once(LabeledSpan::new(
            Some(label),
            self.span.start,
            self.span.end.saturating_sub(self.span.start).max(1),
        ))))
    }
}
