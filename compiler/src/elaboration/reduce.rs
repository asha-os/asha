use crate::{
    elaboration::{ElabState, subst},
    module::name::QualifiedName,
    spine::Term,
};

/// Reduces a term to weak head normal form.
///
/// Only the outermost redexes are contracted: beta redexes (`App(Lam, arg)`),
/// let-bindings, and assigned metavariables. All other term forms are returned
/// as-is, since their head is already in normal form.
pub fn whnf(state: &ElabState, term: &Term) -> Term {
    match term {
        Term::App(f, arg) => {
            let f = whnf(state, f);
            match &f {
                Term::Lam(_, _, body) => whnf(state, &subst::instantiate(body, arg)),
                _ => Term::mk_app(f, *arg.clone()),
            }
        }

        Term::Let(_, val, body) => whnf(state, &subst::instantiate(body, val)),

        Term::MVar(u) => match state.mctx.get_assignment(u.clone()) {
            Some(val) => whnf(state, val),
            None => term.clone(),
        },

        _ => term.clone(),
    }
}

/// Extracts the head constant from a (possibly applied) term.
///
/// Recursively peels off applications: `f a b c` yields `f`. Returns `Some`
/// only if the head is a `Term::Const`. Used to identify which record or
/// inductive type a value belongs to during projection elaboration.
pub fn head_const(term: &Term) -> Option<&QualifiedName> {
    match term {
        Term::Const(name) => Some(name),
        Term::App(fun, _) => head_const(fun),
        _ => None,
    }
}

/// Checks if a field type is recursive
pub fn is_recursive_field(field_ty: &Term, inductive_name: &QualifiedName) -> bool {
    match field_ty {
        Term::Const(name) => name == inductive_name,
        Term::App(fun, _) => match &**fun {
            Term::Const(name) => name == inductive_name,
            _ => false,
        },
        _ => false,
    }
}
