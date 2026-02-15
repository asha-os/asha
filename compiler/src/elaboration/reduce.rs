use alloc::boxed::Box;

use crate::{
    elaboration::{ElabState, subst}, module::name::QualifiedName, spine::Term
};

pub fn whnf(state: &ElabState, term: &Term) -> Term {
    match term {
        Term::App(f, arg) => {
            let f = whnf(state, f);
            match &f {
                Term::Lam(_, _, body) => whnf(state, &subst::instantiate(body, arg)),
                _ => Term::App(Box::new(f), arg.clone()),
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

pub fn head_const(term: &Term) -> Option<&QualifiedName> {
    match term {
        Term::Const(name) => Some(name),
        Term::App(fun, _) => head_const(fun),
        _ => None,
    }
}
