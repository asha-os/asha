use alloc::{boxed::Box, vec::Vec};

use crate::{
    module::{name::QualifiedName, unique::Unique},
    spine::Term,
};

/// Substitutes `replacement` for `BVar(0)` in `term` (beta reduction).
///
/// After substitution, all remaining bound variable indices above 0 are decremented
/// by one (since one binder has been consumed), and free variables inside `replacement`
/// are shifted up to account for the binding depth at the substitution site.
pub fn instantiate(term: &Term, replacement: &Term) -> Term {
    instantiate_at(term, replacement, 0)
}

/// Recursive worker for [`instantiate`]. `depth` tracks how many binders we've
/// traversed into. `BVar(depth)` is the target for substitution at each level.
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

/// Shifts all free De Bruijn indices in `term` up by `amount`.
///
/// A "free" index is one that refers beyond the current binding depth. Indices
/// bound by enclosing binders within `term` itself are left unchanged. This is
/// used by [`instantiate`] to adjust the replacement term when substituting
/// under binders.
fn shift(term: &Term, amount: usize) -> Term {
    if amount == 0 {
        return term.clone();
    }
    shift_at(term, amount, 0)
}

/// Recursive worker for [`shift`]. Only indices `>= depth` are shifted.
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

/// Abstracts a free variable out of a term, converting `FVar(fvar)` into `BVar(0)`.
///
/// This is the inverse of [`instantiate`]: it closes over a free variable to create
/// a term suitable for use as the body of a `Lam`, `Pi`, or `Sigma`. Existing bound
/// variable indices at or above the current depth are shifted up by one to make room
/// for the new binder.
pub fn abstract_fvar(term: &Term, fvar: Unique) -> Term {
    abstract_fvar_at(term, fvar, 0)
}

/// Recursive worker for [`abstract_fvar`]. `depth` is the De Bruijn index that
/// `fvar` will be mapped to at the current binding level.
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

/// Replaces all occurrences of `fvar` in `term` with `replacement`.
pub fn replace_fvar(term: &Term, fvar: &Unique, replacement: &Term) -> Term {
    match term {
        Term::FVar(u) if *u == *fvar => replacement.clone(),

        Term::Unit
        | Term::BVar(_)
        | Term::Const(_)
        | Term::FVar(_)
        | Term::MVar(_)
        | Term::Lit(_)
        | Term::Sort(_) => term.clone(),

        Term::App(f, a) => Term::App(
            Box::new(replace_fvar(f, fvar, replacement)),
            Box::new(replace_fvar(a, fvar, replacement)),
        ),
        Term::Lam(info, ty, body) => Term::Lam(
            info.clone(),
            Box::new(replace_fvar(ty, fvar, replacement)),
            Box::new(replace_fvar(body, fvar, replacement)),
        ),
        Term::Pi(info, ty, body) => Term::Pi(
            info.clone(),
            Box::new(replace_fvar(ty, fvar, replacement)),
            Box::new(replace_fvar(body, fvar, replacement)),
        ),
        Term::Sigma(info, ty, body) => Term::Sigma(
            info.clone(),
            Box::new(replace_fvar(ty, fvar, replacement)),
            Box::new(replace_fvar(body, fvar, replacement)),
        ),
        Term::Let(ty, val, body) => Term::Let(
            Box::new(replace_fvar(ty, fvar, replacement)),
            Box::new(replace_fvar(val, fvar, replacement)),
            Box::new(replace_fvar(body, fvar, replacement)),
        ),
    }
}

/// Collects the head constant and arguments from an application spine
fn collect_app_spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut current = term;
    while let Term::App(f, a) = current {
        args.push(a.as_ref());
        current = f.as_ref();
    }
    args.reverse();
    (current, args)
}

/// Replaces recursive calls in a term
pub fn replace_rec_call(
    term: &Term,
    fn_name: &QualifiedName,
    structural_arg: &Unique,
    replacement: &Term,
) -> Term {
    if let Term::App(_, last_arg) = term {
        if let Term::FVar(u) = last_arg.as_ref() {
            if *u == *structural_arg {
                let (head, _) = collect_app_spine(term);
                if let Term::Const(name) = head {
                    if name == fn_name {
                        return replacement.clone();
                    }
                }
            }
        }
    }

    match term {
        Term::Unit
        | Term::BVar(_)
        | Term::Const(_)
        | Term::FVar(_)
        | Term::MVar(_)
        | Term::Lit(_)
        | Term::Sort(_) => term.clone(),

        Term::App(f, a) => Term::App(
            Box::new(replace_rec_call(f, fn_name, structural_arg, replacement)),
            Box::new(replace_rec_call(a, fn_name, structural_arg, replacement)),
        ),
        Term::Lam(info, ty, body) => Term::Lam(
            info.clone(),
            Box::new(replace_rec_call(ty, fn_name, structural_arg, replacement)),
            Box::new(replace_rec_call(body, fn_name, structural_arg, replacement)),
        ),
        Term::Pi(info, ty, body) => Term::Pi(
            info.clone(),
            Box::new(replace_rec_call(ty, fn_name, structural_arg, replacement)),
            Box::new(replace_rec_call(body, fn_name, structural_arg, replacement)),
        ),
        Term::Sigma(info, ty, body) => Term::Sigma(
            info.clone(),
            Box::new(replace_rec_call(ty, fn_name, structural_arg, replacement)),
            Box::new(replace_rec_call(body, fn_name, structural_arg, replacement)),
        ),
        Term::Let(ty, val, body) => Term::Let(
            Box::new(replace_rec_call(ty, fn_name, structural_arg, replacement)),
            Box::new(replace_rec_call(val, fn_name, structural_arg, replacement)),
            Box::new(replace_rec_call(body, fn_name, structural_arg, replacement)),
        ),
    }
}
