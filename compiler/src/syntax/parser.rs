extern crate alloc;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use chumsky::{input::Input, prelude::*};

use crate::syntax::{
    Span,
    error::{ParseError, ParseErrorKind},
    token::{Token, TokenKind},
    tree::{Binder, Literal, TypeExpr},
};

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
    let mut type_expr = Recursive::declare();
    let mut expr = Recursive::declare();

    let def = def_def(type_expr.clone(), expr.clone());

    type_expr.define(type_expr_impl(type_expr.clone()));
    expr.define(expr_impl(type_expr.clone(), expr.clone()));

    let exprs = def.repeated().collect();
    exprs.map(|exprs| mk_expr(crate::syntax::tree::ExprKind::Root(exprs)))
}

fn def_def<'a>(
    type_expr: impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone,
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    just_token(TokenKind::Def)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then(
            binder(type_expr.clone())
                .repeated()
                .collect()
                .then_ignore(just_token(TokenKind::Colon))
                .then(type_expr)
                .then_ignore(just_token(TokenKind::Equal))
                .then(expr),
        )
        .map(|(name, ((binders, ret_type), body))| {
            mk_expr(crate::syntax::tree::ExprKind::Def {
                name: lexeme_to_string(name.lexeme),
                binders,
                return_type: ret_type,
                body: Box::new(body),
            })
        })
}

fn type_expr_impl<'a>(
    type_expr: impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone {
    let atom = type_atom(type_expr.clone());

    let app = atom.clone().foldl(atom.clone().repeated(), |lhs, rhs| {
        TypeExpr::App(Box::new(lhs), Box::new(rhs))
    });
    let binder = binder(type_expr.clone());

    let pi = binder
        .clone()
        .then_ignore(just_token(TokenKind::Arrow))
        .then(type_expr.clone())
        .map(|(binder, body)| TypeExpr::Pi(binder, Box::new(body)));

    let sigma = binder
        .then_ignore(just_token(TokenKind::Product))
        .then(type_expr.clone())
        .map(|(binder, body)| TypeExpr::Sigma(binder, Box::new(body)));

    let arrow_or_product = app.clone().foldl(
        choice((
            just_token(TokenKind::Arrow).to(true),
            just_token(TokenKind::Product).to(false),
        ))
        .then(app.clone())
        .repeated(),
        |lhs, (is_arrow, rhs)| {
            if is_arrow {
                TypeExpr::Arrow(Box::new(lhs), Box::new(rhs))
            } else {
                TypeExpr::Sigma(
                    Binder::Explicit(String::from("_"), Box::new(lhs)),
                    Box::new(rhs),
                )
            }
        },
    );

    choice((pi, sigma, arrow_or_product))
}

fn binder<'a>(
    type_expr: impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Binder, ParserExtra<'a>> + Clone {
    let explicit = just_token(TokenKind::LParen)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(type_expr.clone())
        .then_ignore(just_token(TokenKind::RParen))
        .map(|(name, ty)| Binder::Explicit(lexeme_to_string(name.lexeme), Box::new(ty)));

    let implicit = just_token(TokenKind::LBrace)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(type_expr.clone())
        .then_ignore(just_token(TokenKind::RBrace))
        .map(|(name, ty)| Binder::Implicit(lexeme_to_string(name.lexeme), Box::new(ty)));

    let instance = just_token(TokenKind::LBracket)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(type_expr)
        .then_ignore(just_token(TokenKind::RBracket))
        .map(|(name, ty)| Binder::Instance(lexeme_to_string(name.lexeme), Box::new(ty)));

    choice((explicit, implicit, instance))
}

fn type_atom<'a>(
    type_expr: impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone {
    let var =
        just_token(TokenKind::LowerIdentifier).map(|t| TypeExpr::Var(lexeme_to_string(t.lexeme)));

    let constructor = just_token(TokenKind::UpperIdentifier)
        .map(|t| TypeExpr::Constructor(lexeme_to_string(t.lexeme)));

    let number = just_token(TokenKind::Number).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let n = s.parse::<u64>().unwrap_or(0);
        TypeExpr::Lit(Literal::Nat(n))
    });

    let string = just_token(TokenKind::String).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let inner = if s.len() >= 2 { &s[1..s.len() - 1] } else { &s };
        TypeExpr::Lit(Literal::String(String::from(inner)))
    });

    let tuple_or_grouped = just_token(TokenKind::LParen)
        .ignore_then(
            type_expr
                .clone()
                .separated_by(just_token(TokenKind::Comma))
                .collect::<Vec<_>>(),
        )
        .then_ignore(just_token(TokenKind::RParen))
        .map(|items| {
            if items.len() == 1 {
                items.into_iter().next().unwrap()
            } else {
                TypeExpr::Tuple(items)
            }
        });

    choice((var, constructor, number, string, tuple_or_grouped))
}

fn expr_impl<'a>(
    type_expr: impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone,
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    let atom = expr_atom(type_expr.clone(), expr.clone());

    let app = atom.clone().foldl(atom.clone().repeated(), |lhs, rhs| {
        mk_expr(crate::syntax::tree::ExprKind::App(
            Box::new(lhs),
            Box::new(rhs),
        ))
    });

    let proj = app.foldl(
        just_token(TokenKind::Dot)
            .ignore_then(just_token(TokenKind::LowerIdentifier))
            .repeated(),
        |lhs, idx| {
            let s = lexeme_to_string(idx.lexeme);
            mk_expr(crate::syntax::tree::ExprKind::Proj(Box::new(lhs), s))
        },
    );

    let lambda = just_token(TokenKind::Lambda)
        .ignore_then(binder(type_expr.clone()).repeated().at_least(1).collect())
        .then_ignore(just_token(TokenKind::FatArrow))
        .then(expr.clone())
        .map(|(binders, body)| {
            mk_expr(crate::syntax::tree::ExprKind::Lambda {
                binders,
                body: Box::new(body),
            })
        });

    let let_typed = just_token(TokenKind::Let)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(type_expr.clone())
        .then_ignore(just_token(TokenKind::Equal))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::In))
        .then(expr.clone())
        .map(|(((name, ty), value), body)| {
            mk_expr(crate::syntax::tree::ExprKind::Let {
                name: lexeme_to_string(name.lexeme),
                type_ann: Some(ty),
                value: Box::new(value),
                body: Box::new(body),
            })
        });

    let let_untyped = just_token(TokenKind::Let)
        .ignore_then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Equal))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::In))
        .then(expr.clone())
        .map(|((name, value), body)| {
            mk_expr(crate::syntax::tree::ExprKind::Let {
                name: lexeme_to_string(name.lexeme),
                type_ann: None,
                value: Box::new(value),
                body: Box::new(body),
            })
        });

    choice((lambda, let_typed, let_untyped, proj))
}

fn expr_atom<'a>(
    _type_expr: impl Parser<'a, ParserInput<'a>, TypeExpr, ParserExtra<'a>> + Clone,
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    let var = just_token(TokenKind::LowerIdentifier).map(|t| {
        mk_expr(crate::syntax::tree::ExprKind::Var(lexeme_to_string(
            t.lexeme,
        )))
    });

    let constructor = just_token(TokenKind::UpperIdentifier).map(|t| {
        mk_expr(crate::syntax::tree::ExprKind::Constructor(
            lexeme_to_string(t.lexeme),
        ))
    });

    let number = just_token(TokenKind::Number).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let n = s.parse::<u64>().unwrap_or(0);
        mk_expr(crate::syntax::tree::ExprKind::Lit(Literal::Nat(n)))
    });

    let string = just_token(TokenKind::String).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let inner = if s.len() >= 2 { &s[1..s.len() - 1] } else { &s };
        mk_expr(crate::syntax::tree::ExprKind::Lit(Literal::String(
            String::from(inner),
        )))
    });

    let hole =
        just_token(TokenKind::Underscore).map(|_| mk_expr(crate::syntax::tree::ExprKind::Hole));

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
                mk_expr(crate::syntax::tree::ExprKind::Tuple(items))
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

type Expr = crate::syntax::tree::Expr<crate::syntax::tree::Parsed>;

fn mk_expr(kind: crate::syntax::tree::ExprKind<crate::syntax::tree::Parsed>) -> Expr {
    Expr { ann: (), kind }
}
