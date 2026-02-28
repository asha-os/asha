use crate::syntax::{
    LexerCursor, SourceFile, Span,
    error::{LexError, LexErrorKind},
    token::{Token, TokenKind},
};

fn decode_utf8_char(bytes: &[u8]) -> Option<char> {
    if bytes.is_empty() {
        return None;
    }
    let s = core::str::from_utf8(bytes).ok()?;
    s.chars().next()
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_alphabetic() || c.is_ascii_digit() || c == '_'
}

pub struct Lexer<'a> {
    source_file: &'a SourceFile<'a>,
    cursor: LexerCursor,
}

impl<'a> Lexer<'a> {
    pub fn new(source_file: &'a SourceFile<'a>) -> Self {
        Self {
            source_file,
            cursor: LexerCursor::new(source_file.id),
        }
    }

    pub fn read_all(&mut self, tokens: &mut [Token<'a>]) -> usize {
        let mut index = 0;
        while let Some(Ok(token)) = self.next() {
            if index < tokens.len() {
                tokens[index] = token;
                index += 1;
            } else {
                break;
            }
        }
        index
    }

    pub fn eoi_span(&self) -> Span {
        Span::empty(self.cursor.file, self.cursor.byte_offset)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token<'a>, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        let source = &self.source_file.source;

        while self.cursor.byte_offset < source.len() {
            match source[self.cursor.byte_offset] {
                b' ' | b'\t' | b'\r' | b'\n' => self.cursor.advance(1),
                _ => break,
            }
        }

        if self.cursor.byte_offset >= source.len() {
            return None;
        }

        let remaining = &source[self.cursor.byte_offset..];
        let current = decode_utf8_char(remaining)?;
        let start = self.cursor.byte_offset;

        match current {
            '0'..='9' => {
                while self.cursor.byte_offset < source.len() {
                    let c = source[self.cursor.byte_offset] as char;
                    if c.is_ascii_digit() {
                        self.cursor.advance(1);
                    } else {
                        break;
                    }
                }
                let lexeme = &source[start..self.cursor.byte_offset];

                Some(Ok(Token {
                    kind: TokenKind::Number,
                    lexeme,
                    span: self.cursor.span_from(start),
                }))
            }
            c if is_ident_start(c) && c != 'λ' && c != '_' => {
                let is_upper = c.is_uppercase();
                while self.cursor.byte_offset < source.len() {
                    let remaining = &source[self.cursor.byte_offset..];
                    if let Some(c) = decode_utf8_char(remaining) {
                        if is_ident_continue(c) {
                            self.cursor.advance_char(c);
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                let lexeme = &source[start..self.cursor.byte_offset];
                let kind = match lexeme {
                    b"struct" => TokenKind::Struct,
                    b"def" => TokenKind::Def,
                    b"let" => TokenKind::Let,
                    b"in" => TokenKind::In,
                    b"eval" => TokenKind::Eval,
                    b"alias" => TokenKind::Alias,
                    b"record" => TokenKind::Record,
                    b"extern" => TokenKind::Extern,
                    b"inductive" => TokenKind::Inductive,
                    b"class" => TokenKind::Class,
                    b"instance" => TokenKind::Instance,
                    _ if is_upper => TokenKind::UpperIdentifier,
                    _ => TokenKind::LowerIdentifier,
                };

                Some(Ok(Token {
                    kind,
                    lexeme,
                    span: self.cursor.span_from(start),
                }))
            }
            '"' => {
                self.cursor.advance(1);
                while self.cursor.byte_offset < source.len() {
                    let c = source[self.cursor.byte_offset] as char;
                    if c == '"' {
                        self.cursor.advance(1);
                        break;
                    } else {
                        self.cursor.advance(1);
                    }
                }
                let lexeme = &source[start..self.cursor.byte_offset];

                Some(Ok(Token {
                    kind: TokenKind::String,
                    lexeme,
                    span: self.cursor.span_from(start),
                }))
            }
            '@' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::At,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '=' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() && source[self.cursor.byte_offset] == b'>'
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::FatArrow,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else if self.cursor.byte_offset < source.len()
                    && source[self.cursor.byte_offset] == b'='
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::EqualEqual,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else {
                    Some(Ok(Token {
                        kind: TokenKind::Equal,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                }
            }
            '\\' | 'λ' => {
                self.cursor.advance_char(current);
                Some(Ok(Token {
                    kind: TokenKind::Lambda,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '.' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Dot,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '_' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() {
                    let remaining = &source[self.cursor.byte_offset..];
                    if let Some(c) = decode_utf8_char(remaining)
                        && is_ident_continue(c)
                    {
                        while self.cursor.byte_offset < source.len() {
                            let remaining = &source[self.cursor.byte_offset..];
                            if let Some(c) = decode_utf8_char(remaining) {
                                if is_ident_continue(c) {
                                    self.cursor.advance_char(c);
                                } else {
                                    break;
                                }
                            } else {
                                break;
                            }
                        }
                        let lexeme = &source[start..self.cursor.byte_offset];
                        return Some(Ok(Token {
                            kind: TokenKind::LowerIdentifier,
                            lexeme,
                            span: self.cursor.span_from(start),
                        }));
                    }
                }
                Some(Ok(Token {
                    kind: TokenKind::Underscore,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            ',' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Comma,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            ':' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() && source[self.cursor.byte_offset] == b':'
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::DoubleColon,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else {
                    Some(Ok(Token {
                        kind: TokenKind::Colon,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                }
            }
            '{' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::LBrace,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '}' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::RBrace,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '(' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::LParen,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            ')' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::RParen,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            ';' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Semicolon,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '[' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::LBracket,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            ']' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::RBracket,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '-' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() && source[self.cursor.byte_offset] == b'>'
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::Arrow,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else {
                    Some(Ok(Token {
                        kind: TokenKind::Minus,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                }
            }
            '→' => {
                self.cursor.advance_char('→');
                Some(Ok(Token {
                    kind: TokenKind::Arrow,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '>' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() && source[self.cursor.byte_offset] == b'<'
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::Product,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else if self.cursor.byte_offset < source.len()
                    && source[self.cursor.byte_offset] == b'='
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::GreaterEqual,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else {
                    Some(Ok(Token {
                        kind: TokenKind::Greater,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                }
            }
            '×' => {
                self.cursor.advance_char('×');
                Some(Ok(Token {
                    kind: TokenKind::Product,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '+' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Plus,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '*' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Star,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '/' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Slash,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '|' => {
                self.cursor.advance(1);
                Some(Ok(Token {
                    kind: TokenKind::Pipe,
                    lexeme: &source[start..self.cursor.byte_offset],
                    span: self.cursor.span_from(start),
                }))
            }
            '!' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() && source[self.cursor.byte_offset] == b'='
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::BangEqual,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else {
                    Some(Err(LexError {
                        kind: LexErrorKind::UnexpectedChar('!'),
                        span: self.cursor.span_from(start),
                    }))
                }
            }
            '<' => {
                self.cursor.advance(1);
                if self.cursor.byte_offset < source.len() && source[self.cursor.byte_offset] == b'='
                {
                    self.cursor.advance(1);
                    Some(Ok(Token {
                        kind: TokenKind::LessEqual,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                } else {
                    Some(Ok(Token {
                        kind: TokenKind::Less,
                        lexeme: &source[start..self.cursor.byte_offset],
                        span: self.cursor.span_from(start),
                    }))
                }
            }
            u => {
                self.cursor.advance_char(u);
                Some(Err(LexError {
                    kind: LexErrorKind::UnexpectedChar(u),
                    span: self.cursor.span_from(start),
                }))
            }
        }
    }
}
