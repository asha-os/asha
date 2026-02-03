use crate::syntax::SourceSpan;

pub struct Token {
    pub lexeme: &'static str,
    pub kind: TokenKind,
    pub span: SourceSpan
}

pub enum TokenKind {
    Number,
    String
}

pub struct TokenStream {
    pub tokens: &'static [Token],
    pub position: usize    
}