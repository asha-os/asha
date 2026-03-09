extern crate alloc;

use alloc::vec::Vec;

use crate::syntax::{
    Span,
    error::{ParseError, ParseErrorKind},
    kind::SyntaxKind,
    token::{Token, TokenKind},
};

use cstree::build::{Checkpoint, GreenNodeBuilder, NodeCache};
use cstree::green::GreenNode;
use cstree::interning::TokenInterner;

fn to_sk(kind: TokenKind) -> SyntaxKind {
    match kind {
        TokenKind::LowerIdentifier => SyntaxKind::LowerIdent,
        TokenKind::UpperIdentifier => SyntaxKind::UpperIdent,
        TokenKind::Number => SyntaxKind::Number,
        TokenKind::String => SyntaxKind::StringLit,
        TokenKind::Equal => SyntaxKind::Equal,
        TokenKind::Struct => SyntaxKind::StructKw,
        TokenKind::Eval => SyntaxKind::EvalKw,
        TokenKind::Record => SyntaxKind::RecordKw,
        TokenKind::Extern => SyntaxKind::ExternKw,
        TokenKind::Inductive => SyntaxKind::InductiveKw,
        TokenKind::Class => SyntaxKind::ClassKw,
        TokenKind::Instance => SyntaxKind::InstanceKw,
        TokenKind::Comma => SyntaxKind::Comma,
        TokenKind::Colon => SyntaxKind::Colon,
        TokenKind::DoubleColon => SyntaxKind::DoubleColon,
        TokenKind::LBrace => SyntaxKind::LBrace,
        TokenKind::RBrace => SyntaxKind::RBrace,
        TokenKind::LParen => SyntaxKind::LParen,
        TokenKind::RParen => SyntaxKind::RParen,
        TokenKind::LBracket => SyntaxKind::LBracket,
        TokenKind::RBracket => SyntaxKind::RBracket,
        TokenKind::Semicolon => SyntaxKind::Semicolon,
        TokenKind::Arrow => SyntaxKind::Arrow,
        TokenKind::Product => SyntaxKind::Product,
        TokenKind::EndOfFile => SyntaxKind::Error,
        TokenKind::Def => SyntaxKind::DefKw,
        TokenKind::At => SyntaxKind::At,
        TokenKind::Alias => SyntaxKind::AliasKw,
        TokenKind::Let => SyntaxKind::LetKw,
        TokenKind::In => SyntaxKind::InKw,
        TokenKind::Lambda => SyntaxKind::Lambda,
        TokenKind::FatArrow => SyntaxKind::FatArrow,
        TokenKind::Dot => SyntaxKind::Dot,
        TokenKind::Underscore => SyntaxKind::Underscore,
        TokenKind::Plus => SyntaxKind::Plus,
        TokenKind::Minus => SyntaxKind::Minus,
        TokenKind::Pipe => SyntaxKind::Pipe,
        TokenKind::Star => SyntaxKind::Star,
        TokenKind::Slash => SyntaxKind::Slash,
        TokenKind::EqualEqual => SyntaxKind::EqualEqual,
        TokenKind::BangEqual => SyntaxKind::BangEqual,
        TokenKind::Less => SyntaxKind::Less,
        TokenKind::Greater => SyntaxKind::Greater,
        TokenKind::LessEqual => SyntaxKind::LessEqual,
        TokenKind::GreaterEqual => SyntaxKind::GreaterEqual,
        TokenKind::Whitespace => SyntaxKind::Whitespace,
        TokenKind::Theorem => SyntaxKind::TheoremKw,
        TokenKind::Match => SyntaxKind::MatchKw,
    }
}

fn tok_text(lexeme: &[u8]) -> &str {
    core::str::from_utf8(lexeme).unwrap_or("")
}

struct Parser<'a> {
    tokens: &'a [Token<'a>],
    pos: usize,
    file: usize,
    errors: Vec<ParseError>,
    builder: GreenNodeBuilder<'static, 'static, SyntaxKind>,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token<'a>], file: usize) -> Self {
        Self {
            tokens,
            pos: 0,
            file,
            errors: Vec::new(),
            builder: GreenNodeBuilder::new(),
        }
    }

    /// Emit all consecutive whitespace tokens into the current green node.
    fn eat_trivia(&mut self) {
        while self.pos < self.tokens.len() && self.tokens[self.pos].kind == TokenKind::Whitespace {
            let tok = &self.tokens[self.pos];
            self.builder.token(SyntaxKind::Whitespace, tok_text(tok.lexeme));
            self.pos += 1;
        }
    }

    /// Peek at the nth (0-indexed) non-trivia token kind from current position.
    fn peek_nth(&self, n: usize) -> TokenKind {
        let mut count = 0;
        let mut i = self.pos;
        while i < self.tokens.len() {
            if self.tokens[i].kind != TokenKind::Whitespace {
                if count == n {
                    return self.tokens[i].kind;
                }
                count += 1;
            }
            i += 1;
        }
        TokenKind::EndOfFile
    }

    fn peek(&self) -> TokenKind {
        self.peek_nth(0)
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.peek() == kind
    }

    /// Return the span of the next non-trivia token (for error messages).
    fn current_span(&self) -> Span {
        let mut i = self.pos;
        while i < self.tokens.len() && self.tokens[i].kind == TokenKind::Whitespace {
            i += 1;
        }
        if i < self.tokens.len() {
            self.tokens[i].span
        } else {
            Span::empty(self.file, self.tokens.last().map_or(0, |t| t.span.end))
        }
    }

    /// Eat trivia, then consume and emit the next token into the green tree.
    fn bump(&mut self) {
        self.eat_trivia();
        let tok = self.tokens[self.pos];
        self.builder.token(to_sk(tok.kind), tok_text(tok.lexeme));
        self.pos += 1;
    }

    /// Eat trivia + consume if the next token matches `kind`.
    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) { self.bump(); true } else { false }
    }

    /// Eat trivia + consume the next token, emitting an error if it doesn't match.
    fn expect(&mut self, kind: TokenKind) {
        if self.eat(kind) {
            return;
        }
        let span = self.current_span();
        let found = if self.peek() != TokenKind::EndOfFile {
            Some(self.peek())
        } else {
            None
        };
        self.errors.push(ParseError {
            kind: if found.is_some() {
                ParseErrorKind::UnexpectedToken
            } else {
                ParseErrorKind::UnexpectedEndOfInput
            },
            span,
            expected: alloc::vec![kind],
            found,
        });
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        self.eat_trivia();
        self.builder.start_node(kind);
    }

    fn finish_node(&mut self) {
        self.builder.finish_node();
    }

    fn checkpoint(&mut self) -> Checkpoint {
        self.eat_trivia();
        self.builder.checkpoint()
    }

    fn start_node_at(&mut self, cp: Checkpoint, kind: SyntaxKind) {
        self.builder.start_node_at(cp, kind);
    }
}

pub struct ParseOutput {
    pub green: GreenNode,
    pub cache: NodeCache<'static, TokenInterner>,
    pub errors: Vec<ParseError>,
}

pub fn parse(tokens: &[Token], file: usize) -> ParseOutput {
    let mut p = Parser::new(tokens, file);

    p.start_node(SyntaxKind::SourceFile);
    parse_source_file(&mut p);
    // Eat trailing trivia so it's part of the tree
    p.eat_trivia();
    p.finish_node();

    let (green, cache) = p.builder.finish();
    ParseOutput {
        green,
        cache: cache.unwrap(),
        errors: p.errors,
    }
}

fn parse_source_file(p: &mut Parser) {
    while !p.at(TokenKind::EndOfFile) {
        if !parse_declaration(p) {
            if !p.at(TokenKind::EndOfFile) {
                let span = p.current_span();
                p.bump();
                p.errors.push(ParseError {
                    kind: ParseErrorKind::UnexpectedToken,
                    span,
                    expected: Vec::new(),
                    found: Some(p.peek()),
                });
            }
        }
    }
}

/// Parse a declaration. Returns true if a declaration was parsed.
fn parse_declaration(p: &mut Parser) -> bool {
    let cp = p.checkpoint();
    let has_attrs = parse_attributes(p);

    match p.peek() {
        TokenKind::Def | TokenKind::Theorem => {
            p.start_node_at(cp, SyntaxKind::DefDecl);
            parse_def(p);
            p.finish_node();
        }
        TokenKind::Eval => {
            p.start_node_at(cp, SyntaxKind::EvalDecl);
            parse_eval(p);
            p.finish_node();
        }
        TokenKind::Record => {
            p.start_node_at(cp, SyntaxKind::RecordDecl);
            parse_record(p);
            p.finish_node();
        }
        TokenKind::Extern => {
            p.start_node_at(cp, SyntaxKind::ExternDecl);
            parse_extern(p);
            p.finish_node();
        }
        TokenKind::Inductive => {
            p.start_node_at(cp, SyntaxKind::InductiveDecl);
            parse_inductive(p);
            p.finish_node();
        }
        TokenKind::Class => {
            p.start_node_at(cp, SyntaxKind::ClassDecl);
            parse_class(p);
            p.finish_node();
        }
        TokenKind::Instance => {
            p.start_node_at(cp, SyntaxKind::InstanceDecl);
            parse_instance(p);
            p.finish_node();
        }
        TokenKind::Alias => {
            p.start_node_at(cp, SyntaxKind::AliasDecl);
            parse_alias(p);
            p.finish_node();
        }
        _ => {
            if has_attrs {
                let span = p.current_span();
                p.errors.push(ParseError {
                    kind: ParseErrorKind::UnexpectedToken,
                    span,
                    expected: Vec::new(),
                    found: Some(p.peek()),
                });
            }
            return false;
        }
    }
    true
}

// ── Attributes ──────────────────────────────────────────────────────────

/// Parse attributes. Returns true if any were found.
fn parse_attributes(p: &mut Parser) -> bool {
    if !p.at(TokenKind::At) {
        return false;
    }
    while p.at(TokenKind::At) {
        p.start_node(SyntaxKind::Attribute);
        p.bump();
        p.expect(TokenKind::LBracket);
        p.bump(); // name (LowerIdentifier)
        while !p.at(TokenKind::RBracket) && !p.at(TokenKind::EndOfFile) {
            parse_expr_atom(p);
        }
        p.expect(TokenKind::RBracket);
        p.finish_node();
    }
    true
}

fn parse_def(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::LowerIdentifier);
    parse_binders(p);
    p.expect(TokenKind::Colon);
    parse_expr(p);
    parse_def_body(p);
}

fn parse_def_body(p: &mut Parser) {
    if p.at(TokenKind::Equal) {
        p.start_node(SyntaxKind::DefBody);
        p.bump();
        parse_expr(p);
        p.finish_node();
    } else if p.at(TokenKind::Pipe) {
        p.start_node(SyntaxKind::PatternMatchArms);
        parse_pattern_match_arms(p);
        p.finish_node();
    } else {
        let span = p.current_span();
        p.errors.push(ParseError {
            kind: ParseErrorKind::UnexpectedToken,
            span,
            expected: alloc::vec![TokenKind::Equal, TokenKind::Pipe],
            found: Some(p.peek()),
        });
    }
}

fn parse_pattern_match_arms(p: &mut Parser) {
    while p.at(TokenKind::Pipe) {
        p.start_node(SyntaxKind::PatternMatchArm);
        p.bump();
        parse_comma_separated_patterns(p);
        p.expect(TokenKind::FatArrow);
        parse_expr(p);
        p.finish_node();
    }
}

fn parse_comma_separated_patterns(p: &mut Parser) {
    parse_pattern(p);
    while p.at(TokenKind::Comma) {
        p.bump();
        parse_pattern(p);
    }
}

fn parse_eval(p: &mut Parser) {
    p.bump();
    parse_expr(p);
    p.expect(TokenKind::Semicolon);
}

fn parse_record(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::UpperIdentifier);
    parse_binders(p);
    p.expect(TokenKind::LBrace);
    parse_record_fields(p);
    p.eat(TokenKind::Comma);
    p.expect(TokenKind::RBrace);
}

fn parse_record_fields(p: &mut Parser) {
    while p.at(TokenKind::LowerIdentifier) || p.at(TokenKind::At) {
        p.start_node(SyntaxKind::RecordField);
        parse_attributes(p);
        p.expect(TokenKind::LowerIdentifier);
        p.expect(TokenKind::Colon);
        parse_expr(p);
        p.finish_node();
        if !p.at(TokenKind::Comma) { break; }
        p.bump();
    }
}

fn parse_extern(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::LowerIdentifier);
    p.expect(TokenKind::Colon);
    parse_expr(p);
}

fn parse_inductive(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::UpperIdentifier);
    parse_binders(p);
    if p.at(TokenKind::Colon) {
        p.bump();
        parse_expr(p);
    }
    p.expect(TokenKind::LBrace);
    parse_inductive_constructors(p);
    p.eat(TokenKind::Comma);
    p.expect(TokenKind::RBrace);
}

fn parse_inductive_constructors(p: &mut Parser) {
    while p.at(TokenKind::LowerIdentifier) {
        p.start_node(SyntaxKind::InductiveCtor);
        p.bump();
        parse_binders(p);
        if p.at(TokenKind::Colon) {
            p.bump();
            parse_expr(p);
        }
        p.finish_node();
        if !p.at(TokenKind::Comma) { break; }
        p.bump();
    }
}

fn parse_class(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::UpperIdentifier);
    parse_binders(p);
    p.expect(TokenKind::LBrace);
    parse_record_fields(p);
    p.eat(TokenKind::Comma);
    p.expect(TokenKind::RBrace);
}

fn parse_instance(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::LowerIdentifier);
    parse_binders(p);
    p.expect(TokenKind::Colon);
    parse_expr(p);
    p.expect(TokenKind::LBrace);
    parse_instance_members(p);
    p.eat(TokenKind::Comma);
    p.expect(TokenKind::RBrace);
}

fn parse_instance_members(p: &mut Parser) {
    while p.at(TokenKind::LowerIdentifier) {
        p.start_node(SyntaxKind::InstanceMember);
        p.bump();
        p.expect(TokenKind::Equal);
        parse_expr(p);
        p.finish_node();
        if !p.at(TokenKind::Comma) { break; }
        p.bump();
    }
}

fn parse_alias(p: &mut Parser) {
    p.bump();
    p.expect(TokenKind::UpperIdentifier);
    parse_binders(p);
    if p.at(TokenKind::Colon) {
        p.bump();
        parse_expr(p);
    }
    p.expect(TokenKind::Equal);
    parse_expr(p);
}

fn parse_binders(p: &mut Parser) {
    while try_parse_binder(p) {}
}

fn try_parse_binder(p: &mut Parser) -> bool {
    match p.peek() {
        TokenKind::LParen => try_parse_delimited_binder(
            p, TokenKind::LParen, TokenKind::RParen, SyntaxKind::ExplicitBinder,
        ),
        TokenKind::LBrace => try_parse_delimited_binder(
            p, TokenKind::LBrace, TokenKind::RBrace, SyntaxKind::ImplicitBinder,
        ),
        TokenKind::LBracket => try_parse_delimited_binder(
            p, TokenKind::LBracket, TokenKind::RBracket, SyntaxKind::InstanceBinder,
        ),
        _ => false,
    }
}

fn try_parse_delimited_binder(
    p: &mut Parser,
    open: TokenKind,
    close: TokenKind,
    node_kind: SyntaxKind,
) -> bool {
    if p.peek_nth(0) == open
        && p.peek_nth(1) == TokenKind::LowerIdentifier
        && p.peek_nth(2) == TokenKind::Colon
        && scan_for_close_before_comma(p, open, close)
    {
        p.start_node(node_kind);
        p.bump();
        p.bump();
        p.bump();
        parse_expr(p);
        p.expect(close);
        p.finish_node();
        true
    } else {
        false
    }
}

/// Scan ahead for a matching `close` before any top-level comma.
fn scan_for_close_before_comma(p: &Parser, open: TokenKind, close: TokenKind) -> bool {
    let mut depth = 0;
    let mut i = p.pos;
    while i < p.tokens.len() {
        let kind = p.tokens[i].kind;
        if kind == TokenKind::Whitespace { i += 1; continue; }
        if kind == open { depth += 1; }
        else if kind == close {
            depth -= 1;
            if depth == 0 { return true; }
        } else if kind == TokenKind::Comma && depth == 1 {
            return false;
        }
        i += 1;
    }
    false
}

fn parse_pattern(p: &mut Parser) {
    match p.peek() {
        TokenKind::Underscore => {
            p.start_node(SyntaxKind::WildcardPat);
            p.bump();
            p.finish_node();
        }
        TokenKind::LParen => {
            let cp = p.checkpoint();
            p.bump();
            let mut count = 0;
            if !p.at(TokenKind::RParen) {
                parse_pattern(p);
                count += 1;
                while p.at(TokenKind::Comma) {
                    p.bump();
                    parse_pattern(p);
                    count += 1;
                }
            }
            p.expect(TokenKind::RParen);
            if count != 1 {
                p.start_node_at(cp, SyntaxKind::TuplePat);
                p.finish_node();
            }
        }
        TokenKind::UpperIdentifier | TokenKind::LowerIdentifier => {
            let cp = p.checkpoint();
            let is_upper = p.peek() == TokenKind::UpperIdentifier;
            let has_namespace = p.peek_nth(1) == TokenKind::DoubleColon;
            parse_qualified_name(p);
            if is_upper || has_namespace {
                p.start_node_at(cp, SyntaxKind::CtorPat);
                while is_pattern_atom_start(p.peek()) {
                    parse_pattern_atom(p);
                }
                p.finish_node();
            } else {
                p.start_node_at(cp, SyntaxKind::VarPat);
                p.finish_node();
            }
        }
        _ => {
            let span = p.current_span();
            p.start_node(SyntaxKind::WildcardPat);
            p.finish_node();
            p.errors.push(ParseError {
                kind: ParseErrorKind::UnexpectedToken,
                span,
                expected: Vec::new(),
                found: Some(p.peek()),
            });
        }
    }
}

fn is_pattern_atom_start(kind: TokenKind) -> bool {
    matches!(kind, TokenKind::Underscore | TokenKind::LParen | TokenKind::UpperIdentifier | TokenKind::LowerIdentifier)
}

fn parse_pattern_atom(p: &mut Parser) {
    match p.peek() {
        TokenKind::Underscore => {
            p.start_node(SyntaxKind::WildcardPat);
            p.bump();
            p.finish_node();
        }
        TokenKind::LParen => {
            let cp = p.checkpoint();
            p.bump();
            let mut count = 0;
            if !p.at(TokenKind::RParen) {
                parse_pattern(p);
                count += 1;
                while p.at(TokenKind::Comma) {
                    p.bump();
                    parse_pattern(p);
                    count += 1;
                }
            }
            p.expect(TokenKind::RParen);
            if count != 1 {
                p.start_node_at(cp, SyntaxKind::TuplePat);
                p.finish_node();
            }
        }
        TokenKind::UpperIdentifier | TokenKind::LowerIdentifier => {
            let cp = p.checkpoint();
            let is_upper = p.peek() == TokenKind::UpperIdentifier;
            let has_namespace = p.peek_nth(1) == TokenKind::DoubleColon;
            parse_qualified_name(p);
            if is_upper || has_namespace {
                p.start_node_at(cp, SyntaxKind::CtorPat);
                // In atom position, no recursive args
                p.finish_node();
            } else {
                p.start_node_at(cp, SyntaxKind::VarPat);
                p.finish_node();
            }
        }
        _ => {
            let span = p.current_span();
            p.start_node(SyntaxKind::WildcardPat);
            p.finish_node();
            p.errors.push(ParseError {
                kind: ParseErrorKind::UnexpectedToken,
                span,
                expected: Vec::new(),
                found: Some(p.peek()),
            });
        }
    }
}

fn parse_expr(p: &mut Parser) {
    match p.peek() {
        TokenKind::Lambda => { parse_lambda(p); return; }
        TokenKind::Let => { parse_let(p); return; }
        _ => {}
    }

    // Pi / Sigma: binder followed by -> or ><
    if let Some(is_pi) = pi_or_sigma_ahead(p) {
        let node_kind = if is_pi { SyntaxKind::PiExpr } else { SyntaxKind::SigmaExpr };
        p.start_node(node_kind);
        try_parse_binder(p);
        p.bump(); // -> or ><
        parse_expr(p);
        p.finish_node();
        return;
    }

    // cmp > add > mul > app > proj > atom
    let cp = p.checkpoint();
    parse_cmp(p);

    if p.at(TokenKind::Arrow) {
        p.start_node_at(cp, SyntaxKind::ArrowExpr);
        p.bump();
        parse_expr(p);
        p.finish_node();
    } else if p.at(TokenKind::Product) {
        p.start_node_at(cp, SyntaxKind::SigmaExpr);
        p.bump();
        parse_expr(p);
        p.finish_node();
    }
}

/// Pure lookahead: checks if a Pi (`->`) or Sigma (`><`) binder expression follows.
fn pi_or_sigma_ahead(p: &Parser) -> Option<bool> {
    let open = p.peek();
    let close = match open {
        TokenKind::LParen => TokenKind::RParen,
        TokenKind::LBrace => TokenKind::RBrace,
        TokenKind::LBracket => TokenKind::RBracket,
        _ => return None,
    };
    if p.peek_nth(1) != TokenKind::LowerIdentifier || p.peek_nth(2) != TokenKind::Colon {
        return None;
    }
    if !scan_for_close_before_comma(p, open, close) {
        return None;
    }
    let close_idx = find_close_raw(p, open, close)?;
    let mut i = close_idx + 1;
    while i < p.tokens.len() && p.tokens[i].kind == TokenKind::Whitespace {
        i += 1;
    }
    if i >= p.tokens.len() { return None; }
    match p.tokens[i].kind {
        TokenKind::Arrow => Some(true),
        TokenKind::Product => Some(false),
        _ => None,
    }
}

fn find_close_raw(p: &Parser, open: TokenKind, close: TokenKind) -> Option<usize> {
    let mut depth = 0;
    let mut i = p.pos;
    while i < p.tokens.len() {
        let kind = p.tokens[i].kind;
        if kind == open { depth += 1; }
        else if kind == close {
            depth -= 1;
            if depth == 0 { return Some(i); }
        }
        i += 1;
    }
    None
}

fn parse_lambda(p: &mut Parser) {
    p.start_node(SyntaxKind::LambdaExpr);
    p.bump(); // λ or \
    let mut has_binder = false;
    while try_parse_binder(p) {
        has_binder = true;
    }
    if !has_binder {
        let span = p.current_span();
        p.errors.push(ParseError {
            kind: ParseErrorKind::UnexpectedToken,
            span,
            expected: alloc::vec![TokenKind::LParen, TokenKind::LBrace, TokenKind::LBracket],
            found: Some(p.peek()),
        });
    }
    p.expect(TokenKind::FatArrow);
    parse_expr(p);
    p.finish_node();
}

fn parse_let(p: &mut Parser) {
    p.start_node(SyntaxKind::LetExpr);
    p.bump(); // let
    p.expect(TokenKind::LowerIdentifier);
    if p.at(TokenKind::Colon) {
        p.bump();
        parse_expr(p);
    }
    p.expect(TokenKind::Equal);
    parse_expr(p);
    p.expect(TokenKind::In);
    parse_expr(p);
    p.finish_node();
}

fn parse_cmp(p: &mut Parser) {
    let cp = p.checkpoint();
    parse_add(p);
    match p.peek() {
        TokenKind::EqualEqual | TokenKind::BangEqual | TokenKind::LessEqual
        | TokenKind::GreaterEqual | TokenKind::Less | TokenKind::Greater => {
            p.start_node_at(cp, SyntaxKind::InfixExpr);
            p.bump();
            parse_add(p);
            p.finish_node();
        }
        _ => {}
    }
}

fn parse_add(p: &mut Parser) {
    let cp = p.checkpoint();
    parse_mul(p);
    while matches!(p.peek(), TokenKind::Plus | TokenKind::Minus) {
        p.start_node_at(cp, SyntaxKind::InfixExpr);
        p.bump();
        parse_mul(p);
        p.finish_node();
    }
}

fn parse_mul(p: &mut Parser) {
    let cp = p.checkpoint();
    parse_app(p);
    while matches!(p.peek(), TokenKind::Star | TokenKind::Slash) {
        p.start_node_at(cp, SyntaxKind::InfixExpr);
        p.bump();
        parse_app(p);
        p.finish_node();
    }
}

fn parse_app(p: &mut Parser) {
    let cp = p.checkpoint();
    parse_proj(p);
    while is_atom_start(p.peek()) {
        p.start_node_at(cp, SyntaxKind::AppExpr);
        parse_proj(p);
        p.finish_node();
    }
}

fn parse_proj(p: &mut Parser) {
    let cp = p.checkpoint();
    parse_expr_atom(p);
    while p.at(TokenKind::Dot) {
        p.start_node_at(cp, SyntaxKind::ProjExpr);
        p.bump();
        p.expect(TokenKind::LowerIdentifier);
        p.finish_node();
    }
}

fn is_atom_start(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::LowerIdentifier
            | TokenKind::UpperIdentifier
            | TokenKind::Number
            | TokenKind::String
            | TokenKind::Underscore
            | TokenKind::LParen
            | TokenKind::LBracket
    )
}

fn parse_expr_atom(p: &mut Parser) {
    match p.peek() {
        TokenKind::Number => {
            p.start_node(SyntaxKind::LitExpr);
            p.bump();
            p.finish_node();
        }
        TokenKind::String => {
            p.start_node(SyntaxKind::LitExpr);
            p.bump();
            p.finish_node();
        }
        TokenKind::Underscore => {
            p.start_node(SyntaxKind::HoleExpr);
            p.bump();
            p.finish_node();
        }
        TokenKind::LParen => {
            let cp = p.checkpoint();
            p.bump();
            let mut count = 0;
            if !p.at(TokenKind::RParen) {
                parse_expr(p);
                count += 1;
                while p.at(TokenKind::Comma) {
                    p.bump();
                    parse_expr(p);
                    count += 1;
                }
            }
            p.expect(TokenKind::RParen);
            match count {
                0 => {
                    p.start_node_at(cp, SyntaxKind::UnitExpr);
                    p.finish_node();
                }
                1 => {}
                _ => {
                    p.start_node_at(cp, SyntaxKind::TupleExpr);
                    p.finish_node();
                }
            }
        }
        TokenKind::LBracket => {
            p.start_node(SyntaxKind::ArrayExpr);
            p.bump();
            if !p.at(TokenKind::RBracket) {
                parse_expr(p);
                while p.at(TokenKind::Comma) {
                    p.bump();
                    parse_expr(p);
                }
            }
            p.expect(TokenKind::RBracket);
            p.finish_node();
        }
        TokenKind::LowerIdentifier | TokenKind::UpperIdentifier => {
            let cp = p.checkpoint();
            let is_upper = p.peek() == TokenKind::UpperIdentifier;
            parse_qualified_name(p);
            if is_upper {
                p.start_node_at(cp, SyntaxKind::CtorExpr);
                p.finish_node();
            } else {
                p.start_node_at(cp, SyntaxKind::VarExpr);
                p.finish_node();
            }
        }
        _ => {
            let span = p.current_span();
            let found = if p.peek() != TokenKind::EndOfFile { Some(p.peek()) } else { None };
            p.errors.push(ParseError {
                kind: if found.is_some() { ParseErrorKind::UnexpectedToken } else { ParseErrorKind::UnexpectedEndOfInput },
                span,
                expected: Vec::new(),
                found,
            });
            // Emit a hole as error recovery
            p.start_node(SyntaxKind::HoleExpr);
            if p.pos < p.tokens.len() && p.tokens[p.pos].kind != TokenKind::Whitespace {
                p.bump();
            }
            p.finish_node();
        }
    }
}

/// Emit tokens for a qualified name.
fn parse_qualified_name(p: &mut Parser) {
    p.bump();

    while p.at(TokenKind::DoubleColon) {
        p.bump();
        if p.at(TokenKind::LowerIdentifier) || p.at(TokenKind::UpperIdentifier) {
            p.bump();
        } else {
            break;
        }
    }
}
