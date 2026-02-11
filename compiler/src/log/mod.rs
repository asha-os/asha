pub mod pretty;

use alloc::string::String;
use miette::{Diagnostic, NamedSource};

#[derive(Debug)]
pub struct ErrorWithSource<'a, E: Diagnostic + ::core::fmt::Debug> {
    pub error: &'a E,
    pub source: &'a NamedSource<String>,
}

impl<E: Diagnostic + ::core::fmt::Debug> ::core::fmt::Display for ErrorWithSource<'_, E> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl<E: Diagnostic + ::core::fmt::Debug> miette::StdError for ErrorWithSource<'_, E> {}

impl<E: Diagnostic + ::core::fmt::Debug> Diagnostic for ErrorWithSource<'_, E> {
    fn code<'a>(&'a self) -> Option<alloc::boxed::Box<dyn ::core::fmt::Display + 'a>> {
        self.error.code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.error.severity()
    }

    fn help<'a>(&'a self) -> Option<alloc::boxed::Box<dyn ::core::fmt::Display + 'a>> {
        self.error.help()
    }

    fn labels(&self) -> Option<alloc::boxed::Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        self.error.labels()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(self.source)
    }
}
