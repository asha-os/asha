use alloc::vec::Vec;

use crate::{
    elaboration::{Declaration, ElabState, subst},
    module::name::QualifiedName,
    spine::{Literal, Term},
};

/// Reduces a term to weak head normal form.
#[must_use]
pub fn whnf(state: &ElabState, term: &Term) -> Term {
    match term {
        Term::App(f, arg) => {
            let f = whnf(state, f);
            if let Term::Lam(_, _, body) = &f {
                whnf(state, &subst::instantiate(body, arg))
            } else {
                let app = Term::mk_app(f, *arg.clone());
                if let Some(reduced) = try_iota(state, &app) {
                    whnf(state, &reduced)
                } else {
                    app
                }
            }
        }

        Term::Let(_, val, body) => whnf(state, &subst::instantiate(body, val)),

        Term::MVar(u) => match state.mctx.get_assignment(u) {
            Some(val) => whnf(state, val),
            None => term.clone(),
        },

        Term::Const(name) => {
            if let Some(Declaration::Definition { value, .. }) = state.env.lookup(name) {
                whnf(state, &value.clone())
            } else {
                term.clone()
            }
        }

        _ => term.clone(),
    }
}

/// Collects the spine of an application into `(head, [arg0, arg1, argN])`.
fn collect_args(term: &Term) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut cur = term;
    while let Term::App(f, a) = cur {
        args.push(a.as_ref());
        cur = f;
    }
    args.reverse();
    (cur, args)
}

/// Converts a Nat literal to its constructor representation.
fn nat_lit_to_ctor(state: &ElabState, n: u64) -> Option<Term> {
    let nat_name = state.lang_items.get_nat()?;
    let ind = state.env.lookup_inductive(nat_name)?;

    // We identify zero and succ by their field count
    let mut zero_ctor = None;
    let mut succ_ctor = None;

    for ctor_name in &ind.constructors {
        let ctor_decl = state.env.lookup(ctor_name)?;
        let ctor_type = ctor_decl.type_();

        let mut ty = ctor_type.clone();
        for _ in 0..ind.num_params {
            if let Term::Pi(_, _, body) = ty {
                ty = *body;
            }
        }
        let mut field_count = 0;
        while let Term::Pi(_, _, body) = ty {
            field_count += 1;
            ty = *body;
        }

        if field_count == 0 {
            zero_ctor = Some(ctor_name.clone());
        } else if field_count == 1 {
            succ_ctor = Some(ctor_name.clone());
        }
    }

    let zero_ctor = zero_ctor?;
    let succ_ctor = succ_ctor?;

    if n == 0 {
        Some(Term::Const(zero_ctor))
    } else {
        Some(Term::mk_app(
            Term::Const(succ_ctor),
            Term::Lit(Literal::Nat(n - 1)),
        ))
    }
}

/// Extracts field types from a constructor type, skipping inductive parameters
fn extract_field_types(ctor_type: &Term, num_params: usize, param_args: &[Term]) -> Vec<Term> {
    let mut current = ctor_type.clone();

    for i in 0..num_params {
        if let Term::Pi(_, _, body) = current {
            current = if i < param_args.len() {
                subst::instantiate(&body, &param_args[i])
            } else {
                *body
            };
        }
    }

    let mut field_types = Vec::new();
    while let Term::Pi(_, param_ty, body) = current {
        field_types.push(*param_ty);
        current = *body;
    }

    field_types
}

/// Attempts iota-reductionm
/// Returns `Some(reduced)` on success, `None` if reduction cannot fire.
fn try_iota(state: &ElabState, term: &Term) -> Option<Term> {
    let (head, args) = collect_args(term);

    let match_name = match head {
        Term::Const(n) => n,
        _ => return None,
    };

    let inductive = state.env.lookup_inductive(match_name)?;

    let num_params = inductive.num_params;
    let num_ctors = inductive.constructors.len();

    let expected_args = num_params + 2 + num_ctors;
    if args.len() < expected_args {
        return None;
    }

    let scrutinee_idx = num_params + 1;
    let scrutinee = whnf(state, args[scrutinee_idx]);

    // If the scrutinee is a Nat literal, convert it to constructor form
    let scrutinee = if let Term::Lit(Literal::Nat(n)) = &scrutinee {
        nat_lit_to_ctor(state, *n).unwrap_or(scrutinee)
    } else {
        scrutinee
    };

    let (ctor_head, ctor_field_args) = collect_args(&scrutinee);
    let ctor_name = match ctor_head {
        Term::Const(n) => n,
        _ => return None,
    };

    // Find which branch index this constructor corresponds to
    let branch_idx = inductive.constructors.iter().position(|c| c == ctor_name)?;

    let branch = args[num_params + 2 + branch_idx];

    // Look up the constructor's type to determine field types and which are recursive
    let ctor_decl = state.env.lookup(ctor_name)?;
    let ctor_type = ctor_decl.type_().clone();

    // Extract the actual type parameter arguments from the scrutinee's type position
    let param_args: Vec<Term> = (0..num_params).map(|i| args[i].clone()).collect();

    let field_types = extract_field_types(&ctor_type, num_params, &param_args);

    let inductive_name = inductive.name.clone();

    // Apply the branch to each field argument with ih for recursive fields
    let mut result = branch.clone();
    for (field_idx, field_type) in field_types.iter().enumerate() {
        let field_arg = ctor_field_args.get(field_idx).copied()?;
        result = Term::mk_app(result, field_arg.clone());

        // If this field is recursive, supply the induction hypothesis
        if is_recursive_field(field_type, &inductive_name) {
            let mut ih = Term::Const(match_name.clone());
            for i in 0..num_params {
                ih = Term::mk_app(ih, args[i].clone());
            }
            ih = Term::mk_app(ih, args[num_params].clone()); // motive
            ih = Term::mk_app(ih, field_arg.clone()); // sub-scrutinee
            for i in 0..num_ctors {
                ih = Term::mk_app(ih, args[num_params + 2 + i].clone());
            }
            result = Term::mk_app(result, ih);
        }
    }

    for extra in args.iter().skip(expected_args) {
        result = Term::mk_app(result, (*extra).clone());
    }

    Some(result)
}

/// Extracts the head constant from a (possibly applied) term.
///
/// Recursively peels off applications: `f a b c` yields `f`. Returns `Some`
/// only if the head is a `Term::Const`. Used to identify which record or
/// inductive type a value belongs to during projection elaboration.
#[must_use]
pub fn head_const(term: &Term) -> Option<&QualifiedName> {
    match term {
        Term::Const(name) => Some(name),
        Term::App(fun, _) => head_const(fun),
        _ => None,
    }
}

/// Checks if a field type is recursive
#[must_use]
pub fn is_recursive_field(field_ty: &Term, inductive_name: &QualifiedName) -> bool {
    match field_ty {
        Term::Const(name) => name == inductive_name,
        Term::App(fun, _) => head_const(fun).map_or(false, |n| n == inductive_name),
        _ => false,
    }
}
