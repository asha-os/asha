pub mod error;
pub mod lexer;
pub mod parser;
pub mod token;
pub mod tree;

pub struct SourceFile<'a> {
    pub id: usize,
    pub name: &'a str,
    pub source: &'a [u8],
    pub package: Option<&'a str>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub file: usize,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(file: usize, start: usize, end: usize) -> Self {
        Self { file, start, end }
    }

    pub fn empty(file: usize, offset: usize) -> Self {
        Self {
            file,
            start: offset,
            end: offset,
        }
    }
}

impl SourceFile<'_> {
    pub fn line_col(&self, byte_offset: usize) -> (usize, usize) {
        let mut line = 1;
        let mut col = 1;
        for (i, &b) in self.source.iter().enumerate() {
            if i >= byte_offset {
                break;
            }
            if b == b'\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        (line, col)
    }
}

pub struct LexerCursor {
    pub file: usize,
    pub byte_offset: usize,
}

impl LexerCursor {
    pub fn new(file: usize) -> Self {
        Self {
            file,
            byte_offset: 0,
        }
    }

    pub fn advance(&mut self, bytes: usize) {
        self.byte_offset += bytes;
    }

    pub fn advance_char(&mut self, c: char) {
        self.byte_offset += c.len_utf8();
    }

    pub fn span_from(&self, start: usize) -> Span {
        Span::new(self.file, start, self.byte_offset)
    }
}

pub trait Spanned {
    fn span(&self) -> Span;
}

fn spanning<A: Spanned, B: Spanned>(a: &A, b: &B) -> Span {
    let span_a = a.span();
    let span_b = b.span();
    if span_a.file != span_b.file {
        panic!("Cannot span across different files");
    }
    Span::new(
        span_a.file,
        span_a.start.min(span_b.start),
        span_a.end.max(span_b.end),
    )
}
