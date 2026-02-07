extern crate alloc;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use chumsky::{input::Input, prelude::*};

use crate::{spine::Literal, syntax::{
    Span,
    error::{ParseError, ParseErrorKind},
    token::{Token, TokenKind},
    tree::{SyntaxBinder, SyntaxExpr as Expr},
}};

impl chumsky::span::Span for Span {
    type Offset = usize;
    type Context = usize; // file index

    fn new(context: Self::Context, range: core::ops::Range<Self::Offset>) -> Self {
        Span {
            file: context,
            start: range.start,
            end: range.end,
        }
    }

    fn context(&self) -> Self::Context {
        self.file
    }

    fn start(&self) -> Self::Offset {
        self.start
    }

    fn end(&self) -> Self::Offset {
        self.end
    }
}

type ParserInput<'a> = chumsky::input::MappedInput<'a, Token<'a>, Span, &'a [(Token<'a>, Span)]>;

type ParserExtra<'a> = extra::Err<Rich<'a, Token<'a>, Span>>;

fn just_token<'a>(
    kind: TokenKind,
) -> impl Parser<'a, ParserInput<'a>, Token<'a>, ParserExtra<'a>> + Clone {
    any().filter(move |t: &Token| t.kind == kind)
}

fn lexeme_to_string(lexeme: &[u8]) -> String {
    String::from_utf8_lossy(lexeme).into_owned()
}

pub fn parse<'a>(
    tokens: &'a [(Token<'a>, Span)],
    eoi_span: Span,
) -> (Option<Expr>, Vec<ParseError>) {
    let input = tokens.split_token_span(eoi_span);

    let parser = program();

    let (output, errors) = parser.parse(input).into_output_errors();
    let errors = errors.into_iter().map(rich_to_parse_error).collect();

    (output, errors)
}

fn program<'a>() -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    let mut expr = Recursive::declare();

    let def = def_parser(expr.clone());

    expr.define(expr_impl(expr.clone()));

    let defs = def.repeated().collect();
    defs.map(Expr::Root)
}

fn def_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    just_token(TokenKind::Def)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then(
            binder(expr.clone())
                .repeated()
                .collect()
                .then_ignore(just_token(TokenKind::Colon))
                .then(expr.clone())
                .then_ignore(just_token(TokenKind::Equal))
                .then(expr),
        )
        .map(|(name, ((binders, ret_type), body))| Expr::Def {
            name: lexeme_to_string(name.lexeme),
            binders,
            return_type: Box::new(ret_type),
            body: Box::new(body),
        })
}

fn binder<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, SyntaxBinder, ParserExtra<'a>> + Clone {
    let explicit = just_token(TokenKind::LParen)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::RParen))
        .map(|(name, ty)| SyntaxBinder::Explicit(lexeme_to_string(name.lexeme), Box::new(ty)));

    let implicit = just_token(TokenKind::LBrace)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::RBrace))
        .map(|(name, ty)| SyntaxBinder::Implicit(lexeme_to_string(name.lexeme), Box::new(ty)));

    let instance = just_token(TokenKind::LBracket)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr)
        .then_ignore(just_token(TokenKind::RBracket))
        .map(|(name, ty)| SyntaxBinder::Instance(lexeme_to_string(name.lexeme), Box::new(ty)));

    choice((explicit, implicit, instance))
}

fn expr_impl<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    let atom = expr_atom(expr.clone());

    let app = atom.clone().foldl(atom.clone().repeated(), |lhs, rhs| {
        Expr::App(Box::new(lhs), Box::new(rhs))
    });

    let proj = app.clone().foldl(
        just_token(TokenKind::Dot)
            .ignore_then(just_token(TokenKind::LowerIdentifier))
            .repeated(),
        |lhs, field| Expr::Proj(Box::new(lhs), lexeme_to_string(field.lexeme)),
    );

    let arrow_or_product = proj
        .clone()
        .then(
            choice((
                just_token(TokenKind::Arrow).to(true),
                just_token(TokenKind::Product).to(false),
            ))
            .then(expr.clone())
            .or_not(),
        )
        .map(|(lhs, rest)| match rest {
            None => lhs,
            Some((true, rhs)) => Expr::Arrow(Box::new(lhs), Box::new(rhs)),
            Some((false, rhs)) => Expr::Sigma(
                SyntaxBinder::Explicit(String::from("_"), Box::new(lhs)),
                Box::new(rhs),
            ),
        });

    let pi = binder(expr.clone())
        .then_ignore(just_token(TokenKind::Arrow))
        .then(expr.clone())
        .map(|(binder, body)| Expr::Pi(binder, Box::new(body)));

    let sigma = binder(expr.clone())
        .then_ignore(just_token(TokenKind::Product))
        .then(expr.clone())
        .map(|(binder, body)| Expr::Sigma(binder, Box::new(body)));

    let lambda = just_token(TokenKind::Lambda)
        .ignore_then(binder(expr.clone()).repeated().at_least(1).collect())
        .then_ignore(just_token(TokenKind::FatArrow))
        .then(expr.clone())
        .map(|(binders, body)| Expr::Lambda {
            binders,
            body: Box::new(body),
        });

    let let_typed = just_token(TokenKind::Let)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::Equal))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::In))
        .then(expr.clone())
        .map(|(((name, ty), value), body)| Expr::Let {
            name: lexeme_to_string(name.lexeme),
            type_ann: Some(Box::new(ty)),
            value: Box::new(value),
            body: Box::new(body),
        });

    let let_untyped = just_token(TokenKind::Let)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Equal))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::In))
        .then(expr)
        .map(|((name, value), body)| Expr::Let {
            name: lexeme_to_string(name.lexeme),
            type_ann: None,
            value: Box::new(value),
            body: Box::new(body),
        });

    choice((lambda, let_typed, let_untyped, pi, sigma, arrow_or_product))
}

fn expr_atom<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    let var = just_token(TokenKind::LowerIdentifier).map(|t| Expr::Var(lexeme_to_string(t.lexeme)));

    let constructor = just_token(TokenKind::UpperIdentifier)
        .map(|t| Expr::Constructor(lexeme_to_string(t.lexeme)));

    let number = just_token(TokenKind::Number).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let n = s.parse::<u64>().unwrap_or(0);
        Expr::Lit(Literal::Nat(n))
    });

    let string = just_token(TokenKind::String).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let inner = if s.len() >= 2 { &s[1..s.len() - 1] } else { &s };
        Expr::Lit(Literal::Str(String::from(inner)))
    });

    let hole = just_token(TokenKind::Underscore).map(|_| Expr::Hole);

    let tuple_or_grouped = just_token(TokenKind::LParen)
        .ignore_then(
            expr.clone()
                .separated_by(just_token(TokenKind::Comma))
                .collect::<Vec<_>>(),
        )
        .then_ignore(just_token(TokenKind::RParen))
        .map(|items| {
            if items.len() == 1 {
                items.into_iter().next().unwrap()
            } else {
                Expr::Tuple(items)
            }
        });

    choice((var, constructor, number, string, hole, tuple_or_grouped))
}

fn rich_to_parse_error(err: Rich<'_, Token<'_>, Span>) -> ParseError {
    let span = *err.span();
    let found = err.found().map(|t| t.kind);
    let expected: Vec<TokenKind> = err
        .expected()
        .filter_map(|e| match e {
            chumsky::error::RichPattern::Token(t) => Some(t.into_inner().kind),
            chumsky::error::RichPattern::Label(_) => None,
            chumsky::error::RichPattern::EndOfInput => None,
            _ => None,
        })
        .collect();

    ParseError {
        kind: if found.is_none() {
            ParseErrorKind::UnexpectedEndOfInput
        } else {
            ParseErrorKind::UnexpectedToken
        },
        span,
        expected,
        found,
    }
}
