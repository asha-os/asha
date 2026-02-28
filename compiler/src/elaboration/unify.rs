use crate::{
    elaboration::{ElabState, reduce::whnf},
    module::unique::Unique,
    spine::{Level, Term},
};

/// Checks whether two terms are definitionally equal, potentially solving metavariable
/// constraints in the process.
///
/// Returns `true` if the terms can be made equal (possibly by assigning metavariables),
/// `false` otherwise. Assigned metavariables are recorded in `state.mctx`.
pub fn is_def_eq(state: &mut ElabState, a: &Term, b: &Term) -> bool {
    if structural_eq(a, b) {
        return true;
    }

    let a = instantiate_mvars(state, a);
    let b = instantiate_mvars(state, b);

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

    match (&a, &b) {
        (Term::App(f1, a1), Term::App(f2, a2)) => {
            is_def_eq(state, f1, f2) && is_def_eq(state, a1, a2)
        }
        (Term::Lam(_, ty1, b1), Term::Lam(_, ty2, b2))
        | (Term::Pi(_, ty1, b1), Term::Pi(_, ty2, b2))
        | (Term::Sigma(_, ty1, b1), Term::Sigma(_, ty2, b2)) => {
            is_def_eq(state, ty1, ty2) && is_def_eq(state, b1, b2)
        }
        (Term::Let(ty1, v1, b1), Term::Let(ty2, v2, b2)) => {
            is_def_eq(state, ty1, ty2) && is_def_eq(state, v1, v2) && is_def_eq(state, b1, b2)
        }
        _ => structural_eq(&a, &b),
    }
}

/// Checks pure syntactic equality between two terms without any reduction or
/// metavariable solving. Two terms are structurally equal when they have the
/// exact same shape and all leaves (indices, names, literals, levels) match.
fn structural_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::BVar(i), Term::BVar(j)) => i == j,
        (Term::FVar(u1), Term::FVar(u2)) | (Term::MVar(u1), Term::MVar(u2)) => u1 == u2,
        (Term::Lit(l1), Term::Lit(l2)) => l1 == l2,
        (Term::Sort(l1), Term::Sort(l2)) => structural_eq_level(l1, l2),
        (Term::App(f1, a1), Term::App(f2, a2)) => structural_eq(f1, f2) && structural_eq(a1, a2),
        (Term::Const(n1), Term::Const(n2)) => n1 == n2,
        (Term::Lam(_, ty1, b1), Term::Lam(_, ty2, b2))
        | (Term::Pi(_, ty1, b1), Term::Pi(_, ty2, b2))
        | (Term::Sigma(_, ty1, b1), Term::Sigma(_, ty2, b2)) => {
            structural_eq(ty1, ty2) && structural_eq(b1, b2)
        }
        (Term::Let(ty1, v1, b1), Term::Let(ty2, v2, b2)) => {
            structural_eq(ty1, ty2) && structural_eq(v1, v2) && structural_eq(b1, b2)
        }
        (Term::Unit, Term::Unit) => true,
        _ => false,
    }
}

/// Structural equality for universe levels.
fn structural_eq_level(a: &Level, b: &Level) -> bool {
    match (a, b) {
        (Level::Zero, Level::Zero) => true,
        (Level::Succ(a), Level::Succ(b)) => structural_eq_level(a, b),
        (Level::Max(a1, a2), Level::Max(b1, b2)) | (Level::IMax(a1, a2), Level::IMax(b1, b2)) => {
            structural_eq_level(a1, b1) && structural_eq_level(a2, b2)
        }
        (Level::MVar(u1), Level::MVar(u2)) => u1 == u2,
        _ => false,
    }
}

/// Deeply replaces all assigned metavariables in a term with their values.
///
/// Recursively traverses the term, and whenever an `MVar` is encountered that
/// has been assigned in `state.mctx`, substitutes its value (and recurses into
/// that value to handle chains of assignments).
fn instantiate_mvars(state: &ElabState, term: &Term) -> Term {
    match term {
        Term::MVar(u) => {
            if let Some(val) = state.mctx.get_assignment(u) {
                instantiate_mvars(state, val)
            } else {
                term.clone()
            }
        }
        Term::Unit | Term::Const(_) | Term::BVar(_) | Term::FVar(_) | Term::Lit(_) => term.clone(),
        Term::Sort(l) => Term::Sort(instantiate_mvars_level(l)),
        Term::App(f, a) => Term::mk_app(instantiate_mvars(state, f), instantiate_mvars(state, a)),
        Term::Lam(info, ty, body) => Term::mk_lam(
            *info,
            instantiate_mvars(state, ty),
            instantiate_mvars(state, body),
        ),
        Term::Pi(info, ty, body) => Term::mk_pi(
            *info,
            instantiate_mvars(state, ty),
            instantiate_mvars(state, body),
        ),
        Term::Sigma(info, ty, body) => Term::mk_sigma(
            *info,
            instantiate_mvars(state, ty),
            instantiate_mvars(state, body),
        ),
        Term::Let(ty, val, body) => Term::mk_let(
            instantiate_mvars(state, ty),
            instantiate_mvars(state, val),
            instantiate_mvars(state, body),
        ),
    }
}

/// Instantiates assigned metavariables within universe levels.
fn instantiate_mvars_level(level: &Level) -> Level {
    match level {
        Level::Zero => Level::Zero,
        Level::Succ(l) => Level::Succ(instantiate_mvars_level(l).boxed()),
        Level::Max(l1, l2) => Level::Max(
            instantiate_mvars_level(l1).boxed(),
            instantiate_mvars_level(l2).boxed(),
        ),
        Level::IMax(l1, l2) => Level::IMax(
            instantiate_mvars_level(l1).boxed(),
            instantiate_mvars_level(l2).boxed(),
        ),
        Level::MVar(u) => {
            // todo: create their table
            Level::MVar(u.clone())
        }
    }
}

/// Attempts to assign metavariable `a` to the value `b`.
///
/// Succeeds only when `a` is an unassigned `MVar` and `b` does not contain `a`.
fn try_assign_mvar(state: &mut ElabState, a: &Term, b: &Term) -> bool {
    let mvar_a = match a {
        Term::MVar(u) => u.clone(),
        _ => return false,
    };

    if state.mctx.is_assigned(&mvar_a) {
        return false;
    }

    if occurs_in(&mvar_a, b) {
        return false;
    }

    state.mctx.assign(mvar_a, b.clone());
    true
}

/// Checks whether `mvar` occurs anywhere inside `term`. Used as the occurs check
/// during metavariable assignment to prevent infinite types.
fn occurs_in(mvar: &Unique, term: &Term) -> bool {
    match term {
        Term::MVar(u) => u == mvar,
        Term::BVar(_) | Term::FVar(_) | Term::Lit(_) | Term::Const(_) | Term::Unit => false,
        Term::Sort(l) => occurs_in_level(mvar, l),
        Term::App(f, a) => occurs_in(mvar, f) || occurs_in(mvar, a),
        Term::Lam(_, ty, body) | Term::Pi(_, ty, body) | Term::Sigma(_, ty, body) => {
            occurs_in(mvar, ty) || occurs_in(mvar, body)
        }
        Term::Let(ty, val, body) => {
            occurs_in(mvar, ty) || occurs_in(mvar, val) || occurs_in(mvar, body)
        }
    }
}

/// Occurs check for universe levels.
fn occurs_in_level(mvar: &Unique, level: &Level) -> bool {
    match level {
        Level::Zero => false,
        Level::Succ(l) => occurs_in_level(mvar, l),
        Level::Max(l1, l2) | Level::IMax(l1, l2) => {
            occurs_in_level(mvar, l1) || occurs_in_level(mvar, l2)
        }
        Level::MVar(u) => u == mvar,
    }
}
