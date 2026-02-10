use crate::syntax::{Span, Spanned};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    pub lexeme: &'a [u8],
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    LowerIdentifier,
    UpperIdentifier,
    Number,
    String,
    Equal,
    Struct,
    Eval,
    Record,
    Comma,
    Colon,
    DoubleColon,
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Semicolon,
    Arrow,
    Product,
    EndOfFile,
    Def,
    Let,
    In,
    Lambda,
    FatArrow,
    Dot,
    Underscore,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenStream<'a> {
    pub tokens: &'a [Token<'a>],
    pub position: usize,
}

impl Spanned for Token<'_> {
    fn span(&self) -> Span {
        self.span
    }    
}