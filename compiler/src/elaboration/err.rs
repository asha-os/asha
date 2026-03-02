use core::fmt::Display;

use crate::{
    module::name::QualifiedName,
    spine::Term,
    syntax::{Span, tree::SyntaxExpr},
};
use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
};
use miette::{Diagnostic, LabeledSpan};

#[derive(Debug)]
pub struct ElabError {
    pub kind: ElabErrorKind,
    pub span: Span,
}

impl ElabError {
    #[must_use]
    pub fn new(kind: ElabErrorKind, span: Span) -> Self {
        Self { kind, span }
    }
}

impl Display for ElabError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match &self.kind {
            ElabErrorKind::ExpectedRoot => write!(f, "expected a root-level declaration"),
            ElabErrorKind::UndefinedVariable(name) => write!(f, "undefined variable `{name}`"),
            ElabErrorKind::UndefinedConstructor(name) => {
                write!(f, "undefined constructor `{name}`")
            }
            ElabErrorKind::TypeMismatch { .. } => write!(f, "type mismatch"),
            ElabErrorKind::UnsupportedSyntax(_) => write!(f, "unsupported syntax"),
            ElabErrorKind::NotAFunction(_) => write!(f, "expected a function"),
            ElabErrorKind::CannotProject(_, field) => write!(f, "no field `{field}` on this type"),
            ElabErrorKind::TypeExpected(_) => write!(f, "expected a type"),
            ElabErrorKind::NonExhaustiveMatch(_) => write!(f, "non-exhaustive match"),
            ElabErrorKind::NotInductive(_) => write!(f, "expected an inductive type"),
            ElabErrorKind::UnknownInductive(name) => write!(f, "unknown inductive type `{name}`"),
            ElabErrorKind::NotAConstructorType(_) => write!(f, "expected a constructor type"),
            ElabErrorKind::ImpossiblePattern { .. } => write!(f, "impossible pattern"),
            ElabErrorKind::MissingLangItem(item) => write!(f, "missing lang item `{item}`"),
        }
    }
}

#[derive(Debug)]
pub enum ElabErrorKind {
    ExpectedRoot,
    UndefinedVariable(String),
    UndefinedConstructor(String),
    TypeMismatch {
        expected: Term,
        reduced_to: Option<Term>,
        found: Term,
    },
    UnsupportedSyntax(SyntaxExpr),
    NotAFunction(Term),
    CannotProject(Term, String),
    TypeExpected(Term),
    NonExhaustiveMatch(Option<Term>),
    NotInductive(Term),
    UnknownInductive(QualifiedName),
    NotAConstructorType(Term),
    ImpossiblePattern {
        expected: Term,
        found: Term,
    },
    MissingLangItem(String),
}

impl miette::StdError for ElabError {}

impl Diagnostic for ElabError {
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        let code = match &self.kind {
            ElabErrorKind::ExpectedRoot => "E0200",
            ElabErrorKind::UndefinedVariable(_) => "E0201",
            ElabErrorKind::UndefinedConstructor(_) => "E0202",
            ElabErrorKind::TypeMismatch { .. } => "E0203",
            ElabErrorKind::UnsupportedSyntax(_) => "E0204",
            ElabErrorKind::NotAFunction(_) => "E0205",
            ElabErrorKind::CannotProject(_, _) => "E0206",
            ElabErrorKind::TypeExpected(_) => "E0207",
            ElabErrorKind::NonExhaustiveMatch(_) => "E0208",
            ElabErrorKind::NotInductive(_) => "E0209",
            ElabErrorKind::UnknownInductive(_) => "E0210",
            ElabErrorKind::NotAConstructorType(_) => "E0211",
            ElabErrorKind::ImpossiblePattern { .. } => "E0212",
            ElabErrorKind::MissingLangItem(_) => "E0213",
        };
        Some(Box::new(code))
    }

    fn severity(&self) -> Option<miette::Severity> {
        Some(miette::Severity::Error)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let label: String = match &self.kind {
            ElabErrorKind::ExpectedRoot => "not valid at the top level".into(),

            ElabErrorKind::UndefinedVariable(name) => format!("no binding found for `{name}`"),

            ElabErrorKind::UndefinedConstructor(name) => format!("`{name}` is not a constructor"),

            ElabErrorKind::TypeMismatch {
                expected, found, ..
            } => format!("expected `{expected}`, found `{found}`"),

            ElabErrorKind::UnsupportedSyntax(_) => "this syntax is not yet supported".into(),

            ElabErrorKind::NotAFunction(term) => format!("`{term}` is not a function"),

            ElabErrorKind::CannotProject(term, field) => format!("`{term}` has no field `{field}`"),

            ElabErrorKind::TypeExpected(term) => format!("`{term}` is not a type"),

            ElabErrorKind::NonExhaustiveMatch(Some(missing)) => {
                format!("missing case for `{missing}`")
            }

            ElabErrorKind::NonExhaustiveMatch(None) => "match is not exhaustive".into(),

            ElabErrorKind::NotInductive(term) => format!("`{term}` is not an inductive type"),

            ElabErrorKind::UnknownInductive(name) => {
                format!("`{name}` has not been declared as an inductive type")
            }

            ElabErrorKind::NotAConstructorType(term) => {
                format!("`{term}` is not a constructor type")
            }

            ElabErrorKind::ImpossiblePattern { expected, found } => {
                format!("pattern has type `{found}`, but scrutinee has type `{expected}`")
            }

            ElabErrorKind::MissingLangItem(item) => {
                format!("add `@[wired_in \"{item}\"]` to the relevant declaration")
            }
        };

        Some(Box::new(core::iter::once(LabeledSpan::new(
            Some(label),
            self.span.start,
            self.span.end.saturating_sub(self.span.start).max(1),
        ))))
    }

    fn help<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        match &self.kind {
            ElabErrorKind::TypeMismatch {
                expected,
                reduced_to,
                found,
            } => {
                if let Some(reduced) = reduced_to {
                    Some(Box::new(format!(
                        "`{expected}` reduces to `{reduced}`, which does not match `{found}`"
                    )))
                } else {
                    Some(Box::new(format!(
                        "the expected type is `{expected}` but the expression has type `{found}`"
                    )))
                }
            }
            ElabErrorKind::UndefinedVariable(_) | ElabErrorKind::UndefinedConstructor(_) => {
                Some(Box::new("check for typos or a missing import"))
            }

            ElabErrorKind::NonExhaustiveMatch(Some(missing)) => {
                Some(Box::new(format!("add a branch for `{missing}`")))
            }

            ElabErrorKind::NonExhaustiveMatch(None) => {
                Some(Box::new("add branches to cover all constructors"))
            }

            ElabErrorKind::NotAFunction(term) => Some(Box::new(format!(
                "`{term}` has a non-function type; remove the argument or change the definition"
            ))),

            ElabErrorKind::MissingLangItem(item) => Some(Box::new(format!(
                "`{item}` is required by the compiler but has not been wired in"
            ))),

            _ => None,
        }
    }
}
