use crate::syntax::{SourceFile, token::TokenStream};

pub enum TokenKind {
    Number,
    String
}

pub fn lex(source_file: SourceFile) -> TokenStream {
    todo!()
}