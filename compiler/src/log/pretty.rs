use core::fmt::Display;

use alloc::{format, string::{String, ToString}};

use crate::{elaboration::{Declaration, Environment}, spine::{BinderInfo, Term}};

impl Display for Environment {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for (_, decl) in &self.decls {
            writeln!(f, "{}", decl)?;
        }
        Ok(())
    }    
}

impl Display for Declaration {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Declaration::Definition { name, type_, value } => {
                write!(f, "def {} : {} := {}", name.display().unwrap(), type_, value)
            },
            Declaration::Constructor { name, type_ } => {
                write!(f, "constructor {} : {}", name.display().unwrap(), type_)
            }
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", pretty_term(self))
    }
}

pub fn pretty_term(term: &Term) -> String {
    match term {
        Term::MVar(unique) => format!("m{}", unique.id),
        Term::BVar(de_bruijn_index) => format!("b{}", de_bruijn_index),
        Term::FVar(unique) => format!("f{}", unique.id),
        Term::Const(qname) => qname.display().unwrap().to_string(),
        Term::App(func, arg) => format!("({} {})", pretty_term(func), pretty_term(arg)),
        Term::Pi(binder_info, param, body) => {
            let binder_str = binder_surrounding(binder_info, pretty_term(param));
            format!("Pi {} -> {}", binder_str, pretty_term(body))
        }
        Term::Lam(binder_info, param, body) => {
            let binder_str = binder_surrounding(binder_info, pretty_term(param));
            format!("λ {}. {}", binder_str, pretty_term(body))
        },
        Term::Sigma(binder_info, param, body) => {
            let binder_str = binder_surrounding(binder_info, pretty_term(param));
            format!("Σ {} × {}", binder_str, pretty_term(body))
        },
        Term::Sort(level) => format!("Type({:?})", level),
        Term::Let(binding, value, body) => format!("(let {} = {} in {})", pretty_term(binding), pretty_term(value), pretty_term(body)),
        Term::Lit(lit) => format!("{:?}", lit),
    }
}

fn binder_surrounding(binder_info: &BinderInfo, str: String) -> String {
    match binder_info {
        BinderInfo::Explicit => format!("({})", str),
        BinderInfo::Implicit => format!("{{{}}}", str),
        BinderInfo::InstanceImplicit => format!("[{}]", str),
        BinderInfo::StrictImplicit => format!("{{{{{}}}}}", str),
    }
}