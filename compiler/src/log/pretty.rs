use core::fmt::Display;

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
};

use crate::{
    elaboration::{Declaration, Environment},
    module::name::QualifiedName,
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
                write!(f, "def {} : {} = {}", name.display().unwrap(), type_, value)
            }
            Declaration::Constructor { name, type_, .. } => {
                write!(f, "constructor {} : {}", name.display().unwrap(), type_)
            }
            Declaration::Opaque { name, type_, .. } => {
                write!(f, "opaque {} : {}", name.display().unwrap(), type_)
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
    match term {
        Term::MVar(_) => "✸".into(),
        Term::BVar(de_bruijn_index) => format!("b{de_bruijn_index}"),
        Term::FVar(unique) => unique.display_name.clone().map_or_else(
            || format!("f{}", unique.id),
            |name| format!("'{name}'"),
        ),
        Term::Const(qname) => qname.display().unwrap().to_string(),
        Term::App(func, arg) => format!("{} ({})", pretty_term(func), pretty_term(arg)),
        Term::Pi(binder_info, param, body) => {
            let binder_str = binder_surrounding(*binder_info, &pretty_term(param));
            format!("{} -> {}", binder_str, pretty_term(body))
        }
        Term::Lam(binder_info, param, body) => {
            let binder_str = binder_surrounding(*binder_info, &pretty_term(param));
            format!("λ {}. {}", binder_str, pretty_term(body))
        }
        Term::Sigma(binder_info, param, body) => {
            let binder_str = binder_surrounding(*binder_info, &pretty_term(param));
            format!("{} × {}", binder_str, pretty_term(body))
        }
        Term::Sort(level) => format!("Type({level})"),
        Term::Let(binding, value, body) => format!(
            "let {} = {} in {}",
            pretty_term(binding),
            pretty_term(value),
            pretty_term(body)
        ),
        Term::Lit(lit) => format!("{lit:?}"),
        Term::Unit => "()".to_string(),
    }
}

fn binder_surrounding(binder_info: BinderInfo, str: &str) -> String {
    match binder_info {
        BinderInfo::Explicit => format!("({str})"),
        BinderInfo::Implicit => format!("{{{str}}}"),
        BinderInfo::InstanceImplicit => format!("[{str}]"),
        BinderInfo::StrictImplicit => format!("{{{{{str}}}}}"),
    }
}

impl Display for QualifiedName {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.display().unwrap_or("<unknown>"))
    }
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
        }
    }
}

enum DisplayableLevel {
    Nth(u64),
    Max(Box<DisplayableLevel>, Box<DisplayableLevel>),
    IMax(Box<DisplayableLevel>, Box<DisplayableLevel>),
    MVar(usize),
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
        }
    }
}
