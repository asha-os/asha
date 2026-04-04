use core::fmt::Display;

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec::Vec,
};

use crate::{
    elaboration::{Declaration, Environment},
    spine::{BinderInfo, Level, Term},
};

impl Display for Environment {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for decl in self.decls.values() {
            writeln!(f, "{decl}")?;
        }
        Ok(())
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Declaration::Definition {
                name, type_, value, ..
            } => {
                write!(f, "def {} : {} = {}", name.to_string(), type_, value)
            }
            Declaration::Constructor { name, type_, .. } => {
                write!(f, "constructor {} : {}", name.to_string(), type_)
            }
            Declaration::Opaque { name, type_, .. } => {
                write!(f, "opaque {} : {}", name.to_string(), type_)
            }
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", pretty_term(self))
    }
}

#[must_use]
pub fn pretty_term(term: &Term) -> String {
    pretty_term_prec(term, 0)
}

/// Pretty-print a term with a precedence level to control parenthesisation
#[must_use]
fn pretty_term_prec(term: &Term, prec: u8) -> String {
    let s = match term {
        Term::MVar(_) => "?_".into(),
        Term::BVar(i) => format!("b{i}"),
        Term::FVar(name) => format!("{}", name),
        Term::Const(qname) => qname.to_string(),

        Term::App(_, _) => {
            let (head, args) = collect_spine(term);
            let head_str = pretty_term_prec(head, 1);
            let args_str: String = args
                .iter()
                .map(|a| format!(" {}", pretty_term_prec(a, 1)))
                .collect();
            format!("{head_str}{args_str}")
        }

        Term::Pi(binder_info, param, body) => {
            let param_str = pretty_term_prec(param, 0);
            let body_str = pretty_term_prec(body, 0);
            match binder_info {
                BinderInfo::Explicit => format!("{param_str} -> {body_str}"),
                BinderInfo::Implicit => format!("{{{param_str}}} -> {body_str}"),
                BinderInfo::InstanceImplicit => format!("[{param_str}] -> {body_str}"),
                BinderInfo::StrictImplicit => format!("{{{{{param_str}}}}} -> {body_str}"),
            }
        }

        Term::Lam(binder_info, param, body) => {
            let param_str = pretty_term_prec(param, 0);
            let body_str = pretty_term_prec(body, 0);
            match binder_info {
                BinderInfo::Explicit => format!("λ {param_str} => {body_str}"),
                BinderInfo::Implicit => format!("λ {{{param_str}}} => {body_str}"),
                BinderInfo::InstanceImplicit => format!("λ [{param_str}] => {body_str}"),
                BinderInfo::StrictImplicit => format!("λ {{{{{param_str}}}}} => {body_str}"),
            }
        }

        Term::Sigma(binder_info, param, body) => {
            let param_str = pretty_term_prec(param, 0);
            let body_str = pretty_term_prec(body, 0);
            match binder_info {
                BinderInfo::Explicit => format!("({param_str} × {body_str})"),
                _ => format!("{param_str} × {body_str}"),
            }
        }

        Term::Sort(level) => match level {
            Level::Zero => "Prop".into(),
            Level::Succ(inner) if **inner == Level::Zero => "Type".into(),
            other => format!("Type({other})"),
        },

        Term::Let(ty, value, body) => format!(
            "let _ : {} := {} in {}",
            pretty_term_prec(ty, 0),
            pretty_term_prec(value, 0),
            pretty_term_prec(body, 0),
        ),

        Term::Lit(crate::spine::Literal::Nat(n)) => format!("{n}"),
        Term::Lit(crate::spine::Literal::Str(s)) => format!("\"{s}\""),

        Term::Unit => "()".to_string(),
    };

    if prec >= 1 && needs_parens(term) {
        format!("({s})")
    } else {
        s
    }
}

/// Returns true for terms that need parentheses when used as a function argument.
fn needs_parens(term: &Term) -> bool {
    match term {
        Term::MVar(_)
        | Term::BVar(_)
        | Term::FVar(_)
        | Term::Const(_)
        | Term::Lit(_)
        | Term::Unit => false,
        Term::Sort(Level::Zero) => false,
        Term::Sort(Level::Succ(inner)) if **inner == Level::Zero => false,
        _ => true,
    }
}

/// Decomposes an application spine
fn collect_spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut cur = term;
    while let Term::App(f, a) = cur {
        args.push(a.as_ref());
        cur = f;
    }
    args.reverse();
    (cur, args)
}

impl Display for Level {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", DisplayableLevel::from(self))
    }
}

impl Display for DisplayableLevel {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DisplayableLevel::Nth(n) => write!(f, "{n}"),
            DisplayableLevel::Max(l1, l2) => write!(f, "max({l1}, {l2})"),
            DisplayableLevel::IMax(l1, l2) => write!(f, "imax({l1}, {l2})"),
            DisplayableLevel::MVar(name) => write!(f, "m{name}"),
            DisplayableLevel::Param(name) => write!(f, "{name}"),
        }
    }
}

enum DisplayableLevel {
    Nth(u64),
    Max(Box<DisplayableLevel>, Box<DisplayableLevel>),
    IMax(Box<DisplayableLevel>, Box<DisplayableLevel>),
    MVar(usize),
    Param(String),
}

impl From<&Level> for DisplayableLevel {
    fn from(level: &Level) -> Self {
        match level {
            Level::Zero => DisplayableLevel::Nth(0),
            Level::Succ(l) => match DisplayableLevel::from(l.as_ref()) {
                DisplayableLevel::Nth(n) => DisplayableLevel::Nth(n + 1),
                other => DisplayableLevel::Max(Box::new(other), Box::new(DisplayableLevel::Nth(0))),
            },
            Level::Max(l1, l2) => DisplayableLevel::Max(
                Box::new(DisplayableLevel::from(l1.as_ref())),
                Box::new(DisplayableLevel::from(l2.as_ref())),
            ),
            Level::IMax(l1, l2) => DisplayableLevel::IMax(
                Box::new(DisplayableLevel::from(l1.as_ref())),
                Box::new(DisplayableLevel::from(l2.as_ref())),
            ),
            Level::MVar(unique) => DisplayableLevel::MVar(unique.id),
            Level::Param(qname) => DisplayableLevel::Param(qname.to_string()),
        }
    }
}
