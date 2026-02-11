use alloc::boxed::Box;

use crate::{module::unique::Unique, spine::Term};

pub fn instantiate(term: &Term, replacement: &Term) -> Term {
    instantiate_at(term, replacement, 0)
}

fn instantiate_at(term: &Term, replacement: &Term, depth: usize) -> Term {
    match term {
        Term::BVar(i) => {
            if *i == depth {
                shift(replacement, depth)
            } else if *i > depth {
                Term::BVar(i - 1)
            } else {
                Term::BVar(*i)
            }
        }
        Term::Unit
        | Term::Const(_)
        | Term::FVar(_)
        | Term::MVar(_)
        | Term::Lit(_)
        | Term::Sort(_) => term.clone(),
        Term::App(f, a) => Term::App(
            Box::new(instantiate_at(f, replacement, depth)),
            Box::new(instantiate_at(a, replacement, depth)),
        ),
        Term::Lam(info, ty, body) => Term::Lam(
            info.clone(),
            Box::new(instantiate_at(ty, replacement, depth)),
            Box::new(instantiate_at(body, replacement, depth + 1)),
        ),
        Term::Pi(info, ty, body) => Term::Pi(
            info.clone(),
            Box::new(instantiate_at(ty, replacement, depth)),
            Box::new(instantiate_at(body, replacement, depth + 1)),
        ),
        Term::Sigma(info, ty, body) => Term::Sigma(
            info.clone(),
            Box::new(instantiate_at(ty, replacement, depth)),
            Box::new(instantiate_at(body, replacement, depth + 1)),
        ),
        Term::Let(ty, val, body) => Term::Let(
            Box::new(instantiate_at(ty, replacement, depth)),
            Box::new(instantiate_at(val, replacement, depth)),
            Box::new(instantiate_at(body, replacement, depth + 1)),
        ),
    }
}

fn shift(term: &Term, amount: usize) -> Term {
    if amount == 0 {
        return term.clone();
    }
    shift_at(term, amount, 0)
}

fn shift_at(term: &Term, amount: usize, depth: usize) -> Term {
    match term {
        Term::BVar(i) => {
            if *i >= depth {
                Term::BVar(i + amount)
            } else {
                Term::BVar(*i)
            }
        }

        Term::Unit
        | Term::Const(_)
        | Term::FVar(_)
        | Term::MVar(_)
        | Term::Lit(_)
        | Term::Sort(_) => term.clone(),

        Term::App(f, a) => Term::App(
            Box::new(shift_at(f, amount, depth)),
            Box::new(shift_at(a, amount, depth)),
        ),
        Term::Lam(info, ty, body) => Term::Lam(
            info.clone(),
            Box::new(shift_at(ty, amount, depth)),
            Box::new(shift_at(body, amount, depth + 1)),
        ),
        Term::Pi(info, ty, body) => Term::Pi(
            info.clone(),
            Box::new(shift_at(ty, amount, depth)),
            Box::new(shift_at(body, amount, depth + 1)),
        ),
        Term::Sigma(info, ty, body) => Term::Sigma(
            info.clone(),
            Box::new(shift_at(ty, amount, depth)),
            Box::new(shift_at(body, amount, depth + 1)),
        ),
        Term::Let(ty, val, body) => Term::Let(
            Box::new(shift_at(ty, amount, depth)),
            Box::new(shift_at(val, amount, depth)),
            Box::new(shift_at(body, amount, depth + 1)),
        ),
    }
}

pub fn abstract_fvar(term: &Term, fvar: Unique) -> Term {
    abstract_fvar_at(term, fvar, 0)
}

fn abstract_fvar_at(term: &Term, fvar: Unique, depth: usize) -> Term {
    match term {
        Term::FVar(u) if *u == fvar => Term::BVar(depth),

        Term::BVar(i) => {
            if *i >= depth {
                Term::BVar(i + 1)
            } else {
                Term::BVar(*i)
            }
        }

        Term::Unit
        | Term::Const(_)
        | Term::FVar(_)
        | Term::MVar(_)
        | Term::Lit(_)
        | Term::Sort(_) => term.clone(),

        Term::App(f, a) => Term::App(
            Box::new(abstract_fvar_at(f, fvar.clone(), depth)),
            Box::new(abstract_fvar_at(a, fvar, depth)),
        ),
        Term::Lam(info, ty, body) => Term::Lam(
            info.clone(),
            Box::new(abstract_fvar_at(ty, fvar.clone(), depth)),
            Box::new(abstract_fvar_at(body, fvar, depth + 1)),
        ),
        Term::Pi(info, ty, body) => Term::Pi(
            info.clone(),
            Box::new(abstract_fvar_at(ty, fvar.clone(), depth)),
            Box::new(abstract_fvar_at(body, fvar, depth + 1)),
        ),
        Term::Sigma(info, ty, body) => Term::Sigma(
            info.clone(),
            Box::new(abstract_fvar_at(ty, fvar.clone(), depth)),
            Box::new(abstract_fvar_at(body, fvar, depth + 1)),
        ),
        Term::Let(ty, val, body) => Term::Let(
            Box::new(abstract_fvar_at(ty, fvar.clone(), depth)),
            Box::new(abstract_fvar_at(val, fvar.clone(), depth)),
            Box::new(abstract_fvar_at(body, fvar, depth + 1)),
        ),
    }
}
