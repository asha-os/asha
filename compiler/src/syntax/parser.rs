extern crate alloc;

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;
use chumsky::{input::Input, prelude::*};

use crate::{
    spine::Literal,
    syntax::{
        Span, Spanned,
        error::{ParseError, ParseErrorKind},
        spanning,
        token::{Token, TokenKind},
        tree::{SyntaxBinder, SyntaxExpr as Expr},
    },
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
    let mut expr = Recursive::declare();

    let def = choice((
        def_parser(expr.clone()),
        eval_parser(expr.clone()),
        record_parser(expr.clone()),
        extern_parser(expr.clone()),
        inductive_parser(expr.clone()),
    ));

    expr.define(expr_impl(expr.clone()));

    let defs = def.repeated().collect();
    defs.map(Expr::Root)
}

fn record_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    just_token(TokenKind::Record)
        .then(just_token(TokenKind::UpperIdentifier))
        .then(
            binder(expr.clone())
                .repeated()
                .collect::<Vec<_>>()
                .then_ignore(just_token(TokenKind::LBrace))
                .then(record_fields_parser(expr))
                .then_ignore(just_token(TokenKind::Comma).or_not())
                .then(just_token(TokenKind::RBrace)),
        )
        .map(
            |((record_tok, name_tok), ((binders, fields), rbraces))| Expr::Record {
                span: spanning(&record_tok, &rbraces),
                name: lexeme_to_string(name_tok.lexeme),
                binders,
                fields,
            },
        )
}

fn record_fields_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> {
    just_token(TokenKind::LowerIdentifier)
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr)
        .separated_by(just_token(TokenKind::Comma))
        .collect::<Vec<_>>()
        .map(|fields| {
            fields
                .into_iter()
                .map(|(name, ty)| Expr::RecordField {
                    span: spanning(&name, &ty),
                    name: lexeme_to_string(name.lexeme),
                    type_ann: Box::new(ty),
                })
                .collect()
        })
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
            span: spanning(&name, &body),
            name: lexeme_to_string(name.lexeme),
            binders,
            return_type: Box::new(ret_type),
            body: Box::new(body),
        })
}

fn inductive_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    just_token(TokenKind::Inductive)
        .then(just_token(TokenKind::UpperIdentifier))
        .then(
            binder(expr.clone())
                .repeated()
                .collect::<Vec<_>>()
                .then_ignore(just_token(TokenKind::LBrace))
                .then(inductive_constructors_parser(expr))
                .then_ignore(just_token(TokenKind::Comma).or_not())
                .then(just_token(TokenKind::RBrace)),
        )
        .map(
            |((inductive_tok, name_tok), ((binders, constructors), rbraces))| Expr::Inductive {
                span: spanning(&inductive_tok, &rbraces),
                name: lexeme_to_string(name_tok.lexeme),
                binders,
                constructors,
            },
        )
}

fn inductive_constructors_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Vec<Expr>, ParserExtra<'a>> {
    just_token(TokenKind::LowerIdentifier)
        .then(
            binder(expr.clone())
                .repeated()
                .collect::<Vec<_>>()
                .then(
                    just_token(TokenKind::Colon)
                        .ignore_then(expr.clone())
                        .or_not(),
                )
        )
        .separated_by(just_token(TokenKind::Comma))
        .collect::<Vec<_>>()
        .map(|constructors| {
            constructors
                .into_iter()
                .map(|(name, (binders, ty))| Expr::InductiveConstructor {
                    span: name.span, // todo: extend this
                    name: lexeme_to_string(name.lexeme),
                    binders,
                    type_ann: ty.map(Box::new),
                })
                .collect()
        })
}

fn eval_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    just_token(TokenKind::Eval)
        .then(expr)
        .then_ignore(just_token(TokenKind::Semicolon))
        .map(|(tok, expr)| Expr::Eval {
            span: spanning(&tok, &expr),
            expr: Box::new(expr),
        })
}

fn extern_parser<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> {
    just_token(TokenKind::Extern)
        .then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr)
        .map(|((extern_tok, name), ty)| Expr::Extern {
            span: spanning(&extern_tok, &ty),
            name: lexeme_to_string(name.lexeme),
            type_ann: Box::new(ty),
        })
}

fn binder<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, SyntaxBinder, ParserExtra<'a>> + Clone {
    let explicit = just_token(TokenKind::LParen)
        .then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr.clone())
        .then(just_token(TokenKind::RParen))
        .map(|(((lparen, name), ty), rparen)| {
            SyntaxBinder::Explicit(
                spanning(&lparen, &rparen),
                lexeme_to_string(name.lexeme),
                Box::new(ty),
            )
        });

    let implicit = just_token(TokenKind::LBrace)
        .then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr.clone())
        .then(just_token(TokenKind::RBrace))
        .map(|(((lbrace, name), ty), rbrace)| {
            SyntaxBinder::Implicit(
                spanning(&lbrace, &rbrace),
                lexeme_to_string(name.lexeme),
                Box::new(ty),
            )
        });

    let instance = just_token(TokenKind::LBracket)
        .then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr)
        .then(just_token(TokenKind::RBracket))
        .map(|(((lbracket, name), ty), rbracket)| {
            SyntaxBinder::Instance(
                spanning(&lbracket, &rbracket),
                lexeme_to_string(name.lexeme),
                Box::new(ty),
            )
        });

    choice((explicit, implicit, instance))
}

fn expr_impl<'a>(
    expr: impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, ParserInput<'a>, Expr, ParserExtra<'a>> + Clone {
    let atom = expr_atom(expr.clone());

    let app = atom
        .clone()
        .foldl(atom.clone().repeated(), |lhs, rhs| Expr::App {
            span: spanning(&lhs, &rhs),
            fun: Box::new(lhs),
            arg: Box::new(rhs),
        });

    let proj = app.clone().foldl(
        just_token(TokenKind::Dot)
            .ignore_then(just_token(TokenKind::LowerIdentifier))
            .repeated(),
        |lhs, field| Expr::Proj {
            span: spanning(&lhs, &field),
            value: Box::new(lhs),
            field: lexeme_to_string(field.lexeme),
        },
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
            Some((true, rhs)) => Expr::Arrow {
                span: spanning(&lhs, &rhs),
                param_type: Box::new(lhs),
                return_type: Box::new(rhs),
            },
            Some((false, rhs)) => Expr::Sigma {
                span: spanning(&lhs, &rhs),
                binder: SyntaxBinder::Explicit(lhs.span(), String::from("_"), Box::new(lhs)),
                codomain: Box::new(rhs),
            },
        });

    let pi = binder(expr.clone())
        .then_ignore(just_token(TokenKind::Arrow))
        .then(expr.clone())
        .map(|(binder, body)| Expr::Pi {
            span: spanning(&binder, &body),
            binder,
            codomain: Box::new(body),
        });

    let sigma = binder(expr.clone())
        .then_ignore(just_token(TokenKind::Product))
        .then(expr.clone())
        .map(|(binder, body)| Expr::Sigma {
            span: spanning(&binder, &body),
            binder,
            codomain: Box::new(body),
        });

    let lambda = just_token(TokenKind::Lambda)
        .then(binder(expr.clone()).repeated().at_least(1).collect())
        .then_ignore(just_token(TokenKind::FatArrow))
        .then(expr.clone())
        .map(|((lambda, binders), body)| Expr::Lambda {
            span: spanning(&lambda, &body),
            binders,
            body: Box::new(body),
        });

    let let_typed = just_token(TokenKind::Let)
        .then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Colon))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::Equal))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::In))
        .then(expr.clone())
        .map(|((((let_, name), ty), value), body)| Expr::Let {
            span: spanning(&let_, &body),
            name: lexeme_to_string(name.lexeme),
            type_ann: Some(Box::new(ty)),
            value: Box::new(value),
            body: Box::new(body),
        });

    let let_untyped = just_token(TokenKind::Let)
        .then(just_token(TokenKind::LowerIdentifier))
        .then_ignore(just_token(TokenKind::Equal))
        .then(expr.clone())
        .then_ignore(just_token(TokenKind::In))
        .then(expr)
        .map(|(((let_, name), value), body)| Expr::Let {
            span: spanning(&let_, &body),
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
    let ident = choice((
        just_token(TokenKind::LowerIdentifier),
        just_token(TokenKind::UpperIdentifier),
    ));

    let qualified = ident
        .clone()
        .then(
            just_token(TokenKind::DoubleColon)
                .ignore_then(ident.clone())
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .map(|(first, rest)| {
            let mut namespace = alloc::vec![lexeme_to_string(first.lexeme)];
            let last = rest.last().unwrap();
            let span = spanning(&first, last);
            let is_upper = last.kind == TokenKind::UpperIdentifier;
            for tok in &rest[..rest.len() - 1] {
                namespace.push(lexeme_to_string(tok.lexeme));
            }
            let member = lexeme_to_string(last.lexeme);
            if is_upper {
                Expr::Constructor {
                    name: member,
                    namespace,
                    span,
                }
            } else {
                Expr::Var {
                    namespace,
                    member,
                    span,
                }
            }
        });

    let var = just_token(TokenKind::LowerIdentifier).map(|t| Expr::Var {
        namespace: Vec::new(),
        member: lexeme_to_string(t.lexeme),
        span: t.span,
    });

    let constructor = just_token(TokenKind::UpperIdentifier).map(|t| Expr::Constructor {
        name: lexeme_to_string(t.lexeme),
        namespace: Vec::new(),
        span: t.span,
    });

    let number = just_token(TokenKind::Number).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let n = s.parse::<u64>().unwrap_or(0);
        Expr::Lit {
            value: Literal::Nat(n),
            span: t.span,
        }
    });

    let string = just_token(TokenKind::String).map(|t| {
        let s = lexeme_to_string(t.lexeme);
        let inner = if s.len() >= 2 { &s[1..s.len() - 1] } else { &s };
        Expr::Lit {
            value: Literal::Str(String::from(inner)),
            span: t.span,
        }
    });

    let hole = just_token(TokenKind::Underscore).map(|t| Expr::Hole(t.span));

    let tuple_or_grouped = just_token(TokenKind::LParen)
        .then(
            expr.clone()
                .separated_by(just_token(TokenKind::Comma))
                .collect::<Vec<_>>(),
        )
        .then(just_token(TokenKind::RParen))
        .map(|((lparen, items), rparen)| {
            match items.len() {
                0 => Expr::Unit(spanning(&lparen, &rparen)),
                1 => items.into_iter().next().unwrap(),
                _ => Expr::Tuple {
                    elements: items,
                    span: spanning(&lparen, &rparen),
                }
            }
        });

    let array = just_token(TokenKind::LBracket)
        .then(
            expr.clone()
                .separated_by(just_token(TokenKind::Comma))
                .collect(),
        )
        .then(just_token(TokenKind::RBracket))
        .map(|((lbracket, items), rbracket)| Expr::Array {
            elements: items,
            span: spanning(&lbracket, &rbracket),
        });

    choice((
        qualified,
        var,
        constructor,
        number,
        string,
        hole,
        tuple_or_grouped,
        array,
    ))
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
