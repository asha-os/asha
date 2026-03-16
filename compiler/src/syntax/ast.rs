extern crate alloc;

use alloc::string::String;
use alloc::vec::Vec;

use cstree::syntax::{ResolvedNode, ResolvedToken};
use cstree::util::NodeOrToken;

use crate::spine::Literal;
use crate::syntax::Span;
use crate::syntax::kind::SyntaxKind;

pub type SyntaxNodeR = ResolvedNode<SyntaxKind>;
pub type SyntaxTokenR = ResolvedToken<SyntaxKind>;

fn node_span(node: &SyntaxNodeR, file: usize) -> Span {
    let range = node.text_range();
    Span::new(file, range.start().into(), range.end().into())
}

fn token_text(token: &SyntaxTokenR) -> &str {
    token.text()
}

fn find_token<'a>(node: &'a SyntaxNodeR, kind: SyntaxKind) -> Option<&'a SyntaxTokenR> {
    node.children_with_tokens()
        .filter_map(|el| match el {
            NodeOrToken::Token(t) => Some(t),
            _ => None,
        })
        .find(|t| t.kind() == kind)
}

fn child_nodes(node: &SyntaxNodeR) -> impl Iterator<Item = &SyntaxNodeR> {
    node.children()
}

fn first_child_of_kind(node: &SyntaxNodeR, kind: SyntaxKind) -> Option<&SyntaxNodeR> {
    node.children().find(|c| c.kind() == kind)
}

fn ident_parts(node: &SyntaxNodeR) -> (Vec<String>, Option<&str>) {
    let idents: Vec<&SyntaxTokenR> = node
        .children_with_tokens()
        .filter_map(|el| match el {
            NodeOrToken::Token(t) => Some(t),
            _ => None,
        })
        .filter(|t| t.kind() == SyntaxKind::LowerIdent || t.kind() == SyntaxKind::UpperIdent)
        .collect();

    if idents.is_empty() {
        return (Vec::new(), None);
    }

    let last = idents.last().unwrap();
    let namespace: Vec<String> = idents[..idents.len() - 1]
        .iter()
        .map(|t| String::from(token_text(t)))
        .collect();
    (namespace, Some(token_text(last)))
}

fn is_expr_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::VarExpr
            | SyntaxKind::CtorExpr
            | SyntaxKind::AppExpr
            | SyntaxKind::LambdaExpr
            | SyntaxKind::LetExpr
            | SyntaxKind::LitExpr
            | SyntaxKind::TupleExpr
            | SyntaxKind::ProjExpr
            | SyntaxKind::HoleExpr
            | SyntaxKind::UnitExpr
            | SyntaxKind::ArrowExpr
            | SyntaxKind::ArrayExpr
            | SyntaxKind::PiExpr
            | SyntaxKind::SigmaExpr
            | SyntaxKind::InfixExpr
            | SyntaxKind::RecordLitExpr
            | SyntaxKind::MatchExpr
    )
}

#[allow(dead_code)]
fn is_pattern_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::VarPat
            | SyntaxKind::CtorPat
            | SyntaxKind::WildcardPat
            | SyntaxKind::TuplePat
            | SyntaxKind::LitPat
    )
}

macro_rules! ast_node {
    ($name:ident, $kind:ident) => {
        #[derive(Debug)]
        pub struct $name<'a>(pub(crate) &'a SyntaxNodeR);

        impl<'a> $name<'a> {
            pub fn span(&self, file: usize) -> Span {
                node_span(self.0, file)
            }
        }

        impl<'a> From<&'a SyntaxNodeR> for $name<'a> {
            fn from(node: &'a SyntaxNodeR) -> Self {
                debug_assert_eq!(node.kind(), SyntaxKind::$kind);
                Self(node)
            }
        }
    };
}

ast_node!(SourceFile, SourceFile);

impl<'a> SourceFile<'a> {
    pub fn declarations(&self) -> impl Iterator<Item = Decl<'a>> {
        child_nodes(self.0).filter_map(Decl::cast)
    }
}

#[derive(Debug)]
pub enum Decl<'a> {
    Def(DefDecl<'a>),
    Eval(EvalDecl<'a>),
    Record(RecordDecl<'a>),
    Extern(ExternDecl<'a>),
    Inductive(InductiveDecl<'a>),
    Class(ClassDecl<'a>),
    Instance(InstanceDecl<'a>),
    Alias(AliasDecl<'a>),
}

impl<'a> Decl<'a> {
    fn cast(node: &'a SyntaxNodeR) -> Option<Self> {
        match node.kind() {
            SyntaxKind::DefDecl => Some(Decl::Def(DefDecl(node))),
            SyntaxKind::EvalDecl => Some(Decl::Eval(EvalDecl(node))),
            SyntaxKind::RecordDecl => Some(Decl::Record(RecordDecl(node))),
            SyntaxKind::ExternDecl => Some(Decl::Extern(ExternDecl(node))),
            SyntaxKind::InductiveDecl => Some(Decl::Inductive(InductiveDecl(node))),
            SyntaxKind::ClassDecl => Some(Decl::Class(ClassDecl(node))),
            SyntaxKind::InstanceDecl => Some(Decl::Instance(InstanceDecl(node))),
            SyntaxKind::AliasDecl => Some(Decl::Alias(AliasDecl(node))),
            _ => None,
        }
    }

    pub fn span(&self, file: usize) -> Span {
        match self {
            Decl::Def(d) => d.span(file),
            Decl::Eval(d) => d.span(file),
            Decl::Record(d) => d.span(file),
            Decl::Extern(d) => d.span(file),
            Decl::Inductive(d) => d.span(file),
            Decl::Class(d) => d.span(file),
            Decl::Instance(d) => d.span(file),
            Decl::Alias(d) => d.span(file),
        }
    }
}

ast_node!(DefDecl, DefDecl);
ast_node!(EvalDecl, EvalDecl);
ast_node!(RecordDecl, RecordDecl);
ast_node!(ExternDecl, ExternDecl);
ast_node!(InductiveDecl, InductiveDecl);
ast_node!(ClassDecl, ClassDecl);
ast_node!(InstanceDecl, InstanceDecl);
ast_node!(AliasDecl, AliasDecl);

impl<'a> DefDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn return_type(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }

    pub fn body(&self) -> Option<DefBody<'a>> {
        if let Some(arms) = first_child_of_kind(self.0, SyntaxKind::PatternMatchArms) {
            return Some(DefBody::PatternMatch(PatternMatchArms(arms)));
        }
        if let Some(body_node) = first_child_of_kind(self.0, SyntaxKind::DefBody) {
            let expr = child_nodes(body_node)
                .find(|c| is_expr_kind(c.kind()))
                .and_then(Expr::cast);
            return expr.map(DefBody::Expr);
        }
        None
    }
}

impl<'a> EvalDecl<'a> {
    pub fn expr(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> RecordDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::UpperIdent).map(token_text)
    }

    pub fn attributes(&self) -> impl Iterator<Item = Attribute<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::Attribute)
            .map(Attribute)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn fields(&self) -> impl Iterator<Item = RecordField<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::RecordField)
            .map(RecordField)
    }
}

impl<'a> ExternDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> InductiveDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::UpperIdent).map(token_text)
    }

    pub fn attributes(&self) -> impl Iterator<Item = Attribute<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::Attribute)
            .map(Attribute)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn index_type(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }

    pub fn constructors(&self) -> impl Iterator<Item = InductiveCtor<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::InductiveCtor)
            .map(InductiveCtor)
    }
}

impl<'a> ClassDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::UpperIdent).map(token_text)
    }

    pub fn attributes(&self) -> impl Iterator<Item = Attribute<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::Attribute)
            .map(Attribute)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn members(&self) -> impl Iterator<Item = RecordField<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::RecordField)
            .map(RecordField)
    }
}

impl<'a> InstanceDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }

    pub fn members(&self) -> impl Iterator<Item = InstanceMember<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::InstanceMember)
            .map(InstanceMember)
    }
}

impl<'a> AliasDecl<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent)
            .or_else(|| find_token(self.0, SyntaxKind::UpperIdent))
            .map(token_text)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        let mut exprs = child_nodes(self.0).filter(|c| is_expr_kind(c.kind()));
        let first = exprs.next()?;
        let second = exprs.next();
        if second.is_some() {
            Expr::cast(first)
        } else {
            None
        }
    }

    pub fn value(&self) -> Option<Expr<'a>> {
        let mut exprs = child_nodes(self.0).filter(|c| is_expr_kind(c.kind()));
        let first = exprs.next()?;
        let second = exprs.next();
        Expr::cast(second.unwrap_or(first))
    }
}

#[derive(Debug)]
pub enum DefBody<'a> {
    Expr(Expr<'a>),
    PatternMatch(PatternMatchArms<'a>),
}

ast_node!(PatternMatchArms, PatternMatchArms);

impl<'a> PatternMatchArms<'a> {
    pub fn arms(&self) -> impl Iterator<Item = PatternMatchArm<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::PatternMatchArm)
            .map(PatternMatchArm)
    }
}

ast_node!(PatternMatchArm, PatternMatchArm);

impl<'a> PatternMatchArm<'a> {
    pub fn patterns(&self) -> impl Iterator<Item = Pattern<'a>> {
        child_nodes(self.0).filter_map(Pattern::cast)
    }

    /// The right-hand side expression (after `=>`).
    pub fn rhs(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .last()
            .and_then(Expr::cast)
    }
}

ast_node!(Attribute, Attribute);

impl<'a> Attribute<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn args(&self) -> impl Iterator<Item = Expr<'a>> {
        child_nodes(self.0).filter_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

ast_node!(RecordField, RecordField);

impl<'a> RecordField<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn attributes(&self) -> impl Iterator<Item = Attribute<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::Attribute)
            .map(Attribute)
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

ast_node!(InstanceMember, InstanceMember);

impl<'a> InstanceMember<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn value(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

ast_node!(InductiveCtor, InductiveCtor);

impl<'a> InductiveCtor<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

#[derive(Debug)]
pub enum Binder<'a> {
    Explicit(ExplicitBinder<'a>),
    Implicit(ImplicitBinder<'a>),
    Instance(InstanceBinder<'a>),
}

impl<'a> Binder<'a> {
    fn cast(node: &'a SyntaxNodeR) -> Option<Self> {
        match node.kind() {
            SyntaxKind::ExplicitBinder => Some(Binder::Explicit(ExplicitBinder(node))),
            SyntaxKind::ImplicitBinder => Some(Binder::Implicit(ImplicitBinder(node))),
            SyntaxKind::InstanceBinder => Some(Binder::Instance(InstanceBinder(node))),
            _ => None,
        }
    }

    pub fn name(&self) -> Option<&str> {
        match self {
            Binder::Explicit(b) => b.name(),
            Binder::Implicit(b) => b.name(),
            Binder::Instance(b) => b.name(),
        }
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        match self {
            Binder::Explicit(b) => b.type_ann(),
            Binder::Implicit(b) => b.type_ann(),
            Binder::Instance(b) => b.type_ann(),
        }
    }

    pub fn span(&self, file: usize) -> Span {
        match self {
            Binder::Explicit(b) => b.span(file),
            Binder::Implicit(b) => b.span(file),
            Binder::Instance(b) => b.span(file),
        }
    }
}

ast_node!(ExplicitBinder, ExplicitBinder);
ast_node!(ImplicitBinder, ImplicitBinder);
ast_node!(InstanceBinder, InstanceBinder);

impl<'a> ExplicitBinder<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }
    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> ImplicitBinder<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }
    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> InstanceBinder<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }
    pub fn type_ann(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

#[derive(Debug)]
pub enum Expr<'a> {
    Var(VarExpr<'a>),
    Ctor(CtorExpr<'a>),
    App(AppExpr<'a>),
    Lambda(LambdaExpr<'a>),
    Let(LetExpr<'a>),
    Lit(LitExpr<'a>),
    Tuple(TupleExpr<'a>),
    Proj(ProjExpr<'a>),
    Hole(HoleExpr<'a>),
    Unit(UnitExpr<'a>),
    Arrow(ArrowExpr<'a>),
    Array(ArrayExpr<'a>),
    Pi(PiExpr<'a>),
    Sigma(SigmaExpr<'a>),
    Infix(InfixExpr<'a>),
    RecordLit(RecordLitExpr<'a>),
    Match(MatchExpr<'a>),
}

impl<'a> Expr<'a> {
    pub fn cast(node: &'a SyntaxNodeR) -> Option<Self> {
        match node.kind() {
            SyntaxKind::VarExpr => Some(Expr::Var(VarExpr(node))),
            SyntaxKind::CtorExpr => Some(Expr::Ctor(CtorExpr(node))),
            SyntaxKind::AppExpr => Some(Expr::App(AppExpr(node))),
            SyntaxKind::LambdaExpr => Some(Expr::Lambda(LambdaExpr(node))),
            SyntaxKind::LetExpr => Some(Expr::Let(LetExpr(node))),
            SyntaxKind::LitExpr => Some(Expr::Lit(LitExpr(node))),
            SyntaxKind::TupleExpr => Some(Expr::Tuple(TupleExpr(node))),
            SyntaxKind::ProjExpr => Some(Expr::Proj(ProjExpr(node))),
            SyntaxKind::HoleExpr => Some(Expr::Hole(HoleExpr(node))),
            SyntaxKind::UnitExpr => Some(Expr::Unit(UnitExpr(node))),
            SyntaxKind::ArrowExpr => Some(Expr::Arrow(ArrowExpr(node))),
            SyntaxKind::ArrayExpr => Some(Expr::Array(ArrayExpr(node))),
            SyntaxKind::PiExpr => Some(Expr::Pi(PiExpr(node))),
            SyntaxKind::SigmaExpr => Some(Expr::Sigma(SigmaExpr(node))),
            SyntaxKind::InfixExpr => Some(Expr::Infix(InfixExpr(node))),
            SyntaxKind::RecordLitExpr => Some(Expr::RecordLit(RecordLitExpr(node))),
            SyntaxKind::MatchExpr => Some(Expr::Match(MatchExpr(node))),
            _ => None,
        }
    }

    pub fn span(&self, file: usize) -> Span {
        node_span(self.syntax(), file)
    }

    fn syntax(&self) -> &SyntaxNodeR {
        match self {
            Expr::Var(e) => e.0,
            Expr::Ctor(e) => e.0,
            Expr::App(e) => e.0,
            Expr::Lambda(e) => e.0,
            Expr::Let(e) => e.0,
            Expr::Lit(e) => e.0,
            Expr::Tuple(e) => e.0,
            Expr::Proj(e) => e.0,
            Expr::Hole(e) => e.0,
            Expr::Unit(e) => e.0,
            Expr::Arrow(e) => e.0,
            Expr::Array(e) => e.0,
            Expr::Pi(e) => e.0,
            Expr::Sigma(e) => e.0,
            Expr::Infix(e) => e.0,
            Expr::RecordLit(e) => e.0,
            Expr::Match(e) => e.0,
        }
    }
}

ast_node!(VarExpr, VarExpr);
ast_node!(CtorExpr, CtorExpr);
ast_node!(AppExpr, AppExpr);
ast_node!(LambdaExpr, LambdaExpr);
ast_node!(LetExpr, LetExpr);
ast_node!(LitExpr, LitExpr);
ast_node!(TupleExpr, TupleExpr);
ast_node!(ProjExpr, ProjExpr);
ast_node!(HoleExpr, HoleExpr);
ast_node!(UnitExpr, UnitExpr);
ast_node!(ArrowExpr, ArrowExpr);
ast_node!(ArrayExpr, ArrayExpr);
ast_node!(PiExpr, PiExpr);
ast_node!(SigmaExpr, SigmaExpr);
ast_node!(InfixExpr, InfixExpr);
ast_node!(RecordLitExpr, RecordLitExpr);
ast_node!(MatchExpr, MatchExpr);

impl<'a> VarExpr<'a> {
    pub fn qualified_parts(&self) -> (Vec<String>, &str) {
        let (ns, name) = ident_parts(self.0);
        (ns, name.unwrap_or(""))
    }
}

impl<'a> CtorExpr<'a> {
    pub fn qualified_parts(&self) -> (Vec<String>, &str) {
        let (ns, name) = ident_parts(self.0);
        (ns, name.unwrap_or(""))
    }
}

impl<'a> AppExpr<'a> {
    pub fn fun(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .find(|c| is_expr_kind(c.kind()))
            .and_then(Expr::cast)
    }

    pub fn arg(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .nth(1)
            .and_then(Expr::cast)
    }
}

impl<'a> LambdaExpr<'a> {
    pub fn binders(&self) -> impl Iterator<Item = Binder<'a>> {
        child_nodes(self.0).filter_map(Binder::cast)
    }

    pub fn body(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .last()
            .and_then(Expr::cast)
    }
}

impl<'a> LetExpr<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }

    pub fn type_ann(&self) -> Option<Expr<'a>> {
        let exprs: Vec<_> = child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .collect();
        if exprs.len() == 3 {
            Expr::cast(exprs[0])
        } else {
            None
        }
    }

    pub fn value(&self) -> Option<Expr<'a>> {
        let exprs: Vec<_> = child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .collect();
        if exprs.len() == 3 {
            Expr::cast(exprs[1])
        } else if exprs.len() >= 2 {
            Expr::cast(exprs[0])
        } else {
            None
        }
    }

    pub fn body(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .last()
            .and_then(Expr::cast)
    }
}

impl<'a> LitExpr<'a> {
    pub fn literal(&self) -> Option<Literal> {
        if let Some(tok) = find_token(self.0, SyntaxKind::Number) {
            let text = token_text(tok);
            text.parse::<u64>().ok().map(Literal::Nat)
        } else if let Some(tok) = find_token(self.0, SyntaxKind::StringLit) {
            let text = token_text(tok);
            let inner = if text.len() >= 2 {
                &text[1..text.len() - 1]
            } else {
                text
            };
            Some(Literal::Str(String::from(inner)))
        } else {
            None
        }
    }
}

impl<'a> TupleExpr<'a> {
    pub fn elements(&self) -> impl Iterator<Item = Expr<'a>> {
        child_nodes(self.0).filter_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> ProjExpr<'a> {
    pub fn value(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .find(|c| is_expr_kind(c.kind()))
            .and_then(Expr::cast)
    }

    pub fn field(&self) -> Option<&str> {
        self.0
            .children_with_tokens()
            .filter_map(|el| match el {
                NodeOrToken::Token(t) if t.kind() == SyntaxKind::LowerIdent => Some(t),
                _ => None,
            })
            .last()
            .map(token_text)
    }
}

impl<'a> ArrowExpr<'a> {
    pub fn param_type(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .find(|c| is_expr_kind(c.kind()))
            .and_then(Expr::cast)
    }

    pub fn return_type(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .nth(1)
            .and_then(Expr::cast)
    }
}

impl<'a> ArrayExpr<'a> {
    pub fn elements(&self) -> impl Iterator<Item = Expr<'a>> {
        child_nodes(self.0).filter_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> PiExpr<'a> {
    pub fn binder(&self) -> Option<Binder<'a>> {
        child_nodes(self.0).find_map(Binder::cast)
    }

    pub fn codomain(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }
}

impl<'a> SigmaExpr<'a> {
    /// Returns the binder if this is a dependent sigma (`(x : A) >< B`).
    /// For non-dependent sigmas (`A >< B`)
    pub fn binder(&self) -> Option<Binder<'a>> {
        child_nodes(self.0).find_map(Binder::cast)
    }

    /// Returns the first expr child. For non-dependent sigma, this is the LHS type.
    pub fn lhs(&self) -> Option<Expr<'a>> {
        child_nodes(self.0).find_map(|c| {
            if is_expr_kind(c.kind()) {
                Expr::cast(c)
            } else {
                None
            }
        })
    }

    /// Returns the codomain/RHS. For dependent sigma, this is the expr child.
    pub fn codomain(&self) -> Option<Expr<'a>> {
        let has_binder = child_nodes(self.0).any(|c| Binder::cast(c).is_some());
        if has_binder {
            child_nodes(self.0).find_map(|c| {
                if is_expr_kind(c.kind()) {
                    Expr::cast(c)
                } else {
                    None
                }
            })
        } else {
            child_nodes(self.0)
                .filter(|c| is_expr_kind(c.kind()))
                .nth(1)
                .and_then(Expr::cast)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InfixOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
}

impl<'a> InfixExpr<'a> {
    pub fn lhs(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .find(|c| is_expr_kind(c.kind()))
            .and_then(Expr::cast)
    }

    pub fn rhs(&self) -> Option<Expr<'a>> {
        child_nodes(self.0)
            .filter(|c| is_expr_kind(c.kind()))
            .nth(1)
            .and_then(Expr::cast)
    }

    pub fn op(&self) -> Option<InfixOp> {
        self.0
            .children_with_tokens()
            .filter_map(|el| match el {
                NodeOrToken::Token(t) => Some(t),
                _ => None,
            })
            .find_map(|t| match t.kind() {
                SyntaxKind::Plus => Some(InfixOp::Add),
                SyntaxKind::Minus => Some(InfixOp::Sub),
                SyntaxKind::Star => Some(InfixOp::Mul),
                SyntaxKind::Slash => Some(InfixOp::Div),
                SyntaxKind::Equal => Some(InfixOp::Eq),
                SyntaxKind::EqualEqual => Some(InfixOp::Eq),
                SyntaxKind::BangEqual => Some(InfixOp::Neq),
                SyntaxKind::Less => Some(InfixOp::Lt),
                SyntaxKind::Greater => Some(InfixOp::Gt),
                SyntaxKind::LessEqual => Some(InfixOp::Leq),
                SyntaxKind::GreaterEqual => Some(InfixOp::Geq),
                _ => None,
            })
    }
}

impl<'a> RecordLitExpr<'a> {
    pub fn fields(&self) -> impl Iterator<Item = RecordField<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::RecordField)
            .map(RecordField)
    }
}

impl<'a> MatchExpr<'a> {
    pub fn scrutinees(&self) -> impl Iterator<Item = Expr<'a>> {
        child_nodes(self.0)
            .take_while(|c| c.kind() != SyntaxKind::PatternMatchArm)
            .filter_map(|c| {
                if is_expr_kind(c.kind()) {
                    Expr::cast(c)
                } else {
                    None
                }
            })
    }

    pub fn arms(&self) -> impl Iterator<Item = PatternMatchArm<'a>> {
        child_nodes(self.0)
            .filter(|c| c.kind() == SyntaxKind::PatternMatchArm)
            .map(PatternMatchArm)
    }
}

#[derive(Debug)]
pub enum Pattern<'a> {
    Var(VarPat<'a>),
    Ctor(CtorPat<'a>),
    Wildcard(WildcardPat<'a>),
    Tuple(TuplePat<'a>),
    Lit(LitPat<'a>),
}

impl<'a> Pattern<'a> {
    fn cast(node: &'a SyntaxNodeR) -> Option<Self> {
        match node.kind() {
            SyntaxKind::VarPat => Some(Pattern::Var(VarPat(node))),
            SyntaxKind::CtorPat => Some(Pattern::Ctor(CtorPat(node))),
            SyntaxKind::WildcardPat => Some(Pattern::Wildcard(WildcardPat(node))),
            SyntaxKind::TuplePat => Some(Pattern::Tuple(TuplePat(node))),
            SyntaxKind::LitPat => Some(Pattern::Lit(LitPat(node))),
            _ => None,
        }
    }

    pub fn span(&self, file: usize) -> Span {
        node_span(self.syntax(), file)
    }

    fn syntax(&self) -> &SyntaxNodeR {
        match self {
            Pattern::Var(p) => p.0,
            Pattern::Ctor(p) => p.0,
            Pattern::Wildcard(p) => p.0,
            Pattern::Tuple(p) => p.0,
            Pattern::Lit(p) => p.0,
        }
    }
}

ast_node!(VarPat, VarPat);
ast_node!(CtorPat, CtorPat);
ast_node!(WildcardPat, WildcardPat);
ast_node!(TuplePat, TuplePat);
ast_node!(LitPat, LitPat);

impl<'a> VarPat<'a> {
    pub fn name(&self) -> Option<&str> {
        find_token(self.0, SyntaxKind::LowerIdent).map(token_text)
    }
}

impl<'a> CtorPat<'a> {
    pub fn qualified_parts(&self) -> (Vec<String>, &str) {
        let (ns, name) = ident_parts(self.0);
        (ns, name.unwrap_or(""))
    }

    pub fn args(&self) -> impl Iterator<Item = Pattern<'a>> {
        child_nodes(self.0).filter_map(Pattern::cast)
    }
}

impl<'a> TuplePat<'a> {
    pub fn elements(&self) -> impl Iterator<Item = Pattern<'a>> {
        child_nodes(self.0).filter_map(Pattern::cast)
    }
}

impl<'a> LitPat<'a> {
    pub fn literal(&self) -> Option<Literal> {
        if let Some(tok) = find_token(self.0, SyntaxKind::Number) {
            let text = token_text(tok);
            text.parse::<u64>().ok().map(Literal::Nat)
        } else if let Some(tok) = find_token(self.0, SyntaxKind::StringLit) {
            let text = token_text(tok);
            let inner = if text.len() >= 2 {
                &text[1..text.len() - 1]
            } else {
                text
            };
            Some(Literal::Str(String::from(inner)))
        } else {
            None
        }
    }
}
