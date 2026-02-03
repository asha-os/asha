pub mod lexer;
pub mod token;
pub mod error;

pub struct SourceFile<'a> {
    pub name: &'a str,
    pub source: &'a [u8],
    pub package: Option<&'a str>
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourcePos {
    pub file_index: usize,
    pub line: usize,
    pub column: usize,
    pub byte_offset: usize
}

pub struct SourceSpan {
    pub start: SourcePos,
    pub end: SourcePos
}