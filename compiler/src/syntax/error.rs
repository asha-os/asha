extern crate alloc;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use miette::{Diagnostic, LabeledSpan, Severity, SourceSpan, StdError};

use crate::syntax::Span;
use crate::syntax::token::TokenKind;

impl From<Span> for SourceSpan {
    fn from(span: Span) -> Self {
        SourceSpan::new(span.start.into(), span.end - span.start)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub kind: LexErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexErrorKind {
    UnexpectedEndOfInput,
    InvalidToken,
    UnterminatedString,
    UnexpectedChar(char),
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            LexErrorKind::UnexpectedEndOfInput => write!(f, "unexpected end of input"),
            LexErrorKind::InvalidToken => write!(f, "invalid token"),
            LexErrorKind::UnterminatedString => write!(f, "unterminated string literal"),
            LexErrorKind::UnexpectedChar(c) => write!(f, "unexpected character `{}`", c),
        }
    }
}

impl StdError for LexError {}

impl Diagnostic for LexError {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        let code = match &self.kind {
            LexErrorKind::UnexpectedEndOfInput => "E0001",
            LexErrorKind::InvalidToken => "E0002",
            LexErrorKind::UnterminatedString => "E0003",
            LexErrorKind::UnexpectedChar(_) => "E0004",
        };
        Some(Box::new(code))
    }

    fn severity(&self) -> Option<Severity> {
        Some(Severity::Error)
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        let help: Option<&str> = match &self.kind {
            LexErrorKind::UnexpectedEndOfInput => {
                Some("the file ended unexpectedly, check for missing closing delimiters")
            }
            LexErrorKind::InvalidToken => {
                Some("this sequence of characters doesn't form a valid token")
            }
            LexErrorKind::UnterminatedString => Some("add a closing `\"` to terminate the string"),
            LexErrorKind::UnexpectedChar(c) => {
                if c.is_ascii_punctuation() {
                    return Some(Box::new(alloc::format!(
                        "`{}` is not a recognized operator or delimiter",
                        c
                    )));
                }
                None
            }
        };
        help.map(|s| Box::new(s) as Box<dyn fmt::Display>)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let label = match &self.kind {
            LexErrorKind::UnexpectedEndOfInput => "input ended here",
            LexErrorKind::InvalidToken => "invalid token",
            LexErrorKind::UnterminatedString => "string starts here but is never closed",
            LexErrorKind::UnexpectedChar(_) => "unexpected character",
        };
        Some(Box::new(core::iter::once(LabeledSpan::new(
            Some(String::from(label)),
            self.span.start,
            self.span.end - self.span.start,
        ))))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
    pub expected: Vec<TokenKind>,
    pub found: Option<TokenKind>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseErrorKind {
    UnexpectedToken,
    UnexpectedEndOfInput,
    UnclosedDelimiter {
        open: TokenKind,
        expected_close: TokenKind,
    },
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::LowerIdentifier => write!(f, "lowercase identifier"),
            TokenKind::UpperIdentifier => write!(f, "uppercase identifier"),
            TokenKind::Number => write!(f, "number"),
            TokenKind::String => write!(f, "string"),
            TokenKind::Equal => write!(f, "`=`"),
            TokenKind::Struct => write!(f, "`struct`"),
            TokenKind::Comma => write!(f, "`,`"),
            TokenKind::Colon => write!(f, "`:`"),
            TokenKind::LBrace => write!(f, "`{{`"),
            TokenKind::RBrace => write!(f, "`}}`"),
            TokenKind::LParen => write!(f, "`(`"),
            TokenKind::RParen => write!(f, "`)`"),
            TokenKind::LBracket => write!(f, "`[`"),
            TokenKind::RBracket => write!(f, "`]`"),
            TokenKind::Semicolon => write!(f, "`;`"),
            TokenKind::Arrow => write!(f, "`->`"),
            TokenKind::Product => write!(f, "`><`"),
            TokenKind::EndOfFile => write!(f, "end of file"),
            TokenKind::Def => write!(f, "`def`"),
            TokenKind::Let => write!(f, "`let`"),
            TokenKind::In => write!(f, "`in`"),
            TokenKind::Lambda => write!(f, "`\\` or `λ`"),
            TokenKind::FatArrow => write!(f, "`=>`"),
            TokenKind::Dot => write!(f, "`.`"),
            TokenKind::Underscore => write!(f, "`_`"),
        }
    }
}

fn format_expected(expected: &[TokenKind]) -> String {
    match expected.len() {
        0 => String::from("something else"),
        1 => alloc::format!("{}", expected[0]),
        2 => alloc::format!("{} or {}", expected[0], expected[1]),
        _ => {
            let mut s = String::new();
            for (i, tok) in expected.iter().enumerate() {
                if i == expected.len() - 1 {
                    s.push_str("or ");
                }
                s.push_str(&alloc::format!("{}", tok));
                if i < expected.len() - 2 {
                    s.push_str(", ");
                } else if i == expected.len() - 2 {
                    s.push(' ');
                }
            }
            s
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ParseErrorKind::UnexpectedToken => {
                if let Some(found) = &self.found {
                    write!(f, "unexpected {}", found)
                } else {
                    write!(f, "unexpected token")
                }
            }
            ParseErrorKind::UnexpectedEndOfInput => {
                write!(f, "unexpected end of input")
            }
            ParseErrorKind::UnclosedDelimiter { open, .. } => {
                write!(f, "unclosed {}", open)
            }
        }
    }
}

impl StdError for ParseError {}

impl Diagnostic for ParseError {
    fn code<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        let code = match &self.kind {
            ParseErrorKind::UnexpectedToken => "E0100",
            ParseErrorKind::UnexpectedEndOfInput => "E0101",
            ParseErrorKind::UnclosedDelimiter { .. } => "E0102",
        };
        Some(Box::new(code))
    }

    fn severity(&self) -> Option<Severity> {
        Some(Severity::Error)
    }

    fn help<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        match &self.kind {
            ParseErrorKind::UnexpectedToken => {
                if !self.expected.is_empty() {
                    Some(Box::new(alloc::format!(
                        "expected {}",
                        format_expected(&self.expected)
                    )))
                } else {
                    None
                }
            }
            ParseErrorKind::UnexpectedEndOfInput => {
                if !self.expected.is_empty() {
                    Some(Box::new(alloc::format!(
                        "expected {} before end of input",
                        format_expected(&self.expected)
                    )))
                } else {
                    Some(Box::new("the input ended unexpectedly"))
                }
            }
            ParseErrorKind::UnclosedDelimiter { expected_close, .. } => Some(Box::new(
                alloc::format!("add {} to close the delimiter", expected_close),
            )),
        }
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let label = match &self.kind {
            ParseErrorKind::UnexpectedToken => {
                if !self.expected.is_empty() {
                    alloc::format!("expected {}", format_expected(&self.expected))
                } else {
                    String::from("unexpected")
                }
            }
            ParseErrorKind::UnexpectedEndOfInput => String::from("input ended here"),
            ParseErrorKind::UnclosedDelimiter { open, .. } => {
                alloc::format!("this {} is never closed", open)
            }
        };
        Some(Box::new(core::iter::once(LabeledSpan::new(
            Some(label),
            self.span.start,
            self.span.end.saturating_sub(self.span.start).max(1),
        ))))
    }
}
