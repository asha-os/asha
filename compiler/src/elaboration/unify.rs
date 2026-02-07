use alloc::boxed::Box;

use crate::{
    elaboration::{ElabState, reduce::whnf},
    module::unique::Unique,
    spine::{Level, Term},
};

pub fn is_def_eq(state: &mut ElabState, a: &Term, b: &Term) -> bool {
    if structural_eq(a, b) {
        return true;
    }

    let a = instantiate_mvars(state, &a);
    let b = instantiate_mvars(state, &b);

    if structural_eq(&a, &b) {
        return true;
    }

    if try_assign_mvar(state, &a, &b) {
        return true;
    }
    if try_assign_mvar(state, &b, &a) {
        return true;
    }

    let a = whnf(state, &a);
    let b = whnf(state, &b);

    if try_assign_mvar(state, &a, &b) {
        return true;
    }
    if try_assign_mvar(state, &b, &a) {
        return true;
    }

    structural_eq(&a, &b)
}

fn structural_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::BVar(i), Term::BVar(j)) => i == j,
        (Term::FVar(u1), Term::FVar(u2)) => u1 == u2,
        (Term::MVar(u1), Term::MVar(u2)) => u1 == u2,
        (Term::Lit(l1), Term::Lit(l2)) => l1 == l2,
        (Term::Sort(l1), Term::Sort(l2)) => structural_eq_level(l1, l2),
        (Term::App(f1, a1), Term::App(f2, a2)) => structural_eq(f1, f2) && structural_eq(a1, a2),
        (Term::Lam(_, ty1, b1), Term::Lam(_, ty2, b2)) => {
            structural_eq(ty1, ty2) && structural_eq(b1, b2)
        }
        (Term::Pi(_, ty1, b1), Term::Pi(_, ty2, b2)) => {
            structural_eq(ty1, ty2) && structural_eq(b1, b2)
        }
        (Term::Sigma(_, ty1, b1), Term::Sigma(_, ty2, b2)) => {
            structural_eq(ty1, ty2) && structural_eq(b1, b2)
        }
        (Term::Let(ty1, v1, b1), Term::Let(ty2, v2, b2)) => {
            structural_eq(ty1, ty2) && structural_eq(v1, v2) && structural_eq(b1, b2)
        }
        _ => false,
    }
}

fn structural_eq_level(a: &Level, b: &Level) -> bool {
    match (a, b) {
        (Level::Zero, Level::Zero) => true,
        (Level::Succ(a), Level::Succ(b)) => structural_eq_level(a, b),
        (Level::Max(a1, a2), Level::Max(b1, b2)) => {
            structural_eq_level(a1, b1) && structural_eq_level(a2, b2)
        }
        (Level::IMax(a1, a2), Level::IMax(b1, b2)) => {
            structural_eq_level(a1, b1) && structural_eq_level(a2, b2)
        }
        (Level::MVar(u1), Level::MVar(u2)) => u1 == u2,
        _ => false,
    }
}

fn instantiate_mvars(state: &ElabState, term: &Term) -> Term {
    match term {
        Term::MVar(u) => {
            if let Some(val) = state.mctx.get_assignment(u.clone()) {
                instantiate_mvars(state, val)
            } else {
                term.clone()
            }
        }
        Term::BVar(_) | Term::FVar(_) | Term::Lit(_) => term.clone(),
        Term::Sort(l) => Term::Sort(instantiate_mvars_level(state, l)),
        Term::App(f, a) => Term::App(
            Box::new(instantiate_mvars(state, f)),
            Box::new(instantiate_mvars(state, a)),
        ),
        Term::Lam(info, ty, body) => Term::Lam(
            info.clone(),
            Box::new(instantiate_mvars(state, ty)),
            Box::new(instantiate_mvars(state, body)),
        ),
        Term::Pi(info, ty, body) => Term::Pi(
            info.clone(),
            Box::new(instantiate_mvars(state, ty)),
            Box::new(instantiate_mvars(state, body)),
        ),
        Term::Sigma(info, ty, body) => Term::Sigma(
            info.clone(),
            Box::new(instantiate_mvars(state, ty)),
            Box::new(instantiate_mvars(state, body)),
        ),
        Term::Let(ty, val, body) => Term::Let(
            Box::new(instantiate_mvars(state, ty)),
            Box::new(instantiate_mvars(state, val)),
            Box::new(instantiate_mvars(state, body)),
        ),
    }
}

fn instantiate_mvars_level(state: &ElabState, level: &Level) -> Level {
    match level {
        Level::Zero => Level::Zero,
        Level::Succ(l) => Level::Succ(Box::new(instantiate_mvars_level(state, l))),
        Level::Max(l1, l2) => Level::Max(
            Box::new(instantiate_mvars_level(state, l1)),
            Box::new(instantiate_mvars_level(state, l2)),
        ),
        Level::IMax(l1, l2) => Level::IMax(
            Box::new(instantiate_mvars_level(state, l1)),
            Box::new(instantiate_mvars_level(state, l2)),
        ),
        Level::MVar(u) => {
            // todo: create their table
            Level::MVar(u.clone())
        }
    }
}

fn try_assign_mvar(state: &mut ElabState, a: &Term, b: &Term) -> bool {
    let mvar_a = match a {
        Term::MVar(u) => u.clone(),
        _ => return false,
    };

    if state.mctx.is_assigned(mvar_a.clone()) {
        return false;
    }

    if occurs_in(mvar_a.clone(), b) {
        return false;
    }

    state.mctx.assign(mvar_a, b.clone());
    return true;
}

fn occurs_in(mvar: Unique, term: &Term) -> bool {
    match term {
        Term::MVar(u) => *u == mvar,
        Term::BVar(_) => false,
        Term::FVar(_) => false,
        Term::Lit(_) => false,
        Term::Sort(l) => occurs_in_level(mvar, l),
        Term::App(f, a) => occurs_in(mvar.clone(), f) || occurs_in(mvar, a),
        Term::Lam(_, ty, body) => occurs_in(mvar.clone(), ty) || occurs_in(mvar, body),
        Term::Pi(_, ty, body) => occurs_in(mvar.clone(), ty) || occurs_in(mvar, body),
        Term::Sigma(_, ty, body) => occurs_in(mvar.clone(), ty) || occurs_in(mvar, body),
        Term::Let(ty, val, body) => {
            occurs_in(mvar.clone(), ty) || occurs_in(mvar.clone(), val) || occurs_in(mvar, body)
        }
    }
}

fn occurs_in_level(mvar: Unique, level: &Level) -> bool {
    match level {
        Level::Zero => false,
        Level::Succ(l) => occurs_in_level(mvar, l),
        Level::Max(l1, l2) => occurs_in_level(mvar.clone(), l1) || occurs_in_level(mvar, l2),
        Level::IMax(l1, l2) => occurs_in_level(mvar.clone(), l1) || occurs_in_level(mvar, l2),
        Level::MVar(u) => *u == mvar,
    }
}
