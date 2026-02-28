use alloc::vec::Vec;
use api::println;

use crate::{
    elaboration::{
        ElabState,
        err::{ElabError, ElabErrorKind},
        reduce::{head_const, is_recursive_field, whnf},
        subst, unify,
    },
    module::{
        name::QualifiedName,
        unique::{Unique, UniqueGen},
    },
    spine::{BinderInfo, Literal, Term},
    syntax::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
/// A pattern in a pattern match, which can be a variable, a constructor with subpatterns, or a literal.
pub enum Pattern {
    Var(Option<Unique>),
    Constructor {
        ctor: QualifiedName,
        fields: Vec<Pattern>,
        type_: Term,
    },
    Lit(Literal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A scrutinee in a pattern match, consisting of a term to be matched and its type.
pub struct Scrutinee {
    pub term: Term,
    pub type_: Term,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A row in the pattern match matrix, consisting of a vector of patterns and a right-hand side term.
pub struct PatternRow {
    pub patterns: Vec<Pattern>,
    pub rhs: Term,
}

impl PatternRow {
    #[must_use] 
    pub fn new(patterns: Vec<Pattern>, rhs: Term) -> Self {
        Self { patterns, rhs }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A pattern match matrix, consisting of a vector of scrutinees, a vector of pattern rows,
/// and the expected return type of the match expression.
pub struct MatchProblem {
    pub scrutinees: Vec<Scrutinee>,
    pub rows: Vec<PatternRow>,
    pub return_type: Term,
    pub match_fn: Option<QualifiedName>,
}

impl MatchProblem {
    #[must_use] 
    pub fn new(
        scrutinees: Vec<Scrutinee>,
        rows: Vec<PatternRow>,
        return_type: Term,
        match_fn: Option<QualifiedName>,
    ) -> Self {
        Self {
            scrutinees,
            rows,
            return_type,
            match_fn,
        }
    }
}

/// Compiles a pattern match problem into a term that performs the pattern matching.
pub fn compile(
    state: &mut ElabState,
    problem: MatchProblem,
    span: Span,
) -> Result<Term, ElabError> {
    if problem.rows.is_empty() {
        return Err(ElabError::new(
            ElabErrorKind::NonExhaustiveMatch(None),
            span,
        ));
    }
    if problem.scrutinees.is_empty() {
        return Ok(problem.rows[0].rhs.clone());
    }
    let col = pick_column(&problem);
    // If the column is all variables, we can eliminate it and compile the smaller problem.
    if is_all_variables(&problem, col) {
        return compile(state, all_variables_elimination(problem, col), span);
    }

    // Otherwise, we split on constructors
    let type_ = whnf(state, &problem.scrutinees[col].type_);
    let inductive_name = head_const(&type_)
        .ok_or_else(|| ElabError::new(ElabErrorKind::NotInductive(type_.clone()), span))?;
    let inductive = state.env.lookup_inductive(inductive_name).ok_or_else(|| {
        ElabError::new(
            ElabErrorKind::UnknownInductive(inductive_name.clone()),
            span,
        )
    })?;

    let scrutinee = problem.scrutinees[col].term.clone();
    let num_params = inductive.num_params;
    let ctors = inductive.constructors.clone();
    let inductive_name = inductive.name.clone();
    let match_fn = inductive.match_fn.clone();
    let _ = inductive;

    let all_args = extract_all_args(&type_);
    let param_args = all_args
        .iter()
        .take(num_params)
        .cloned()
        .collect::<Vec<_>>();

    let scrutinee_type = problem.scrutinees[col].type_.clone();
    let motive_term = Term::mk_lam(
        BinderInfo::Explicit,
        scrutinee_type.clone(),
        problem.return_type.clone(),
    );

    let mut branches = Vec::new();
    for ctor_name in &ctors {
        let ctor_type = state.env.lookup(ctor_name).unwrap().type_().clone();
        let ctor_return_args =
            extract_return_type_args(&mut state.gen_, &ctor_type, num_params, &param_args);

        let saved_mctx = state.mctx.clone();
        let possible = ctor_return_args.len() == all_args.len()
            && ctor_return_args
                .iter()
                .zip(all_args.iter())
                .all(|(a, b)| unify::is_def_eq(state, a, b));
        state.mctx = saved_mctx;
        println!("ctor {:?} return args: {:?}", ctor_name, ctor_return_args);
        println!("scrutinee args: {:?}", all_args);
        println!("possible: {}", possible);

        if !possible {
            continue;
        }

        let field_types = extract_field_types(&ctor_type, num_params, &param_args);
        let arity = field_types.len();

        let (sub_problem, field_fvars) = specialize(
            &mut state.gen_,
            &problem,
            col,
            ctor_name,
            arity,
            &field_types,
        );

        let branch_body = compile(state, sub_problem, span)?;

        // Abstract field fvars and wrap with lambdas
        let mut result = branch_body;

        // First, wrap IH lambdas
        for (fvar, field_type) in field_fvars.iter().rev().zip(field_types.iter().rev()) {
            if is_recursive_field(field_type, &inductive_name) {
                let ih_fvar = state.gen_.fresh_unnamed();

                // Replace recursive calls on this field with the IH fvar
                if let Some(ref rec_fn) = problem.match_fn {
                    result = subst::replace_rec_call(
                        &result,
                        rec_fn,
                        fvar,
                        &Term::FVar(ih_fvar.clone()),
                    );
                }

                result = subst::abstract_fvar(&result, ih_fvar);
                result = Term::mk_lam(
                    BinderInfo::Explicit,
                    Term::mk_app(motive_term.clone(), Term::FVar(fvar.clone())),
                    result,
                );
            }
        }

        for (fvar, field_type) in field_fvars.iter().rev().zip(field_types.iter().rev()) {
            result = subst::abstract_fvar(&result, fvar.clone());
            result = Term::mk_lam(BinderInfo::Explicit, field_type.clone(), result);
        }
        branches.push(result);
    }

    let mut result = Term::mk_app(Term::mk_app(Term::Const(match_fn), motive_term), scrutinee);
    for branch in branches {
        result = Term::mk_app(result, branch);
    }

    Ok(result)
}

fn extract_all_args(ty: &Term) -> Vec<Term> {
    let mut args = Vec::new();
    let mut current = ty.clone();
    while let Term::App(f, a) = current {
        args.push(*a);
        current = *f;
    }
    args.reverse();
    args
}

/// Extracts the field types from a constructor's Pi type, skipping the inductive's parameters
/// and instantiating de Bruijn indices with the actual type arguments from the scrutinee.
fn extract_field_types(ctor_type: &Term, num_params: usize, type_args: &[Term]) -> Vec<Term> {
    let mut current = ctor_type.clone();
    // Skip inductive parameters
    for i in 0..num_params {
        if let Term::Pi(_, _, body) = current {
            current = if i < type_args.len() {
                subst::instantiate(&body, &type_args[i])
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

/// Extracts the return type arguments from a constructor's Pi type
fn extract_return_type_args(
    gen_: &mut UniqueGen,
    ctor_type: &Term,
    num_params: usize,
    param_args: &[Term],
) -> Vec<Term> {
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
    while let Term::Pi(_, _, body) = current {
        let mvar = Term::MVar(gen_.fresh_unnamed());
        current = subst::instantiate(&body, &mvar);
    }
    extract_all_args(&current)
}

/// Specializes the match problem for a specific constructor.
/// In simple terms, this is just the "constructor case" of the pattern match compilation algorithm, which
/// creates a new sub-problem where the chosen column is replaced by the constructor's field types, and the rows are filtered and transformed accordingly.
///
/// Returns the sub-problem and the fresh fvars created for the constructor's fields
fn specialize(
    gen_: &mut UniqueGen,
    problem: &MatchProblem,
    col: usize,
    ctor: &QualifiedName,
    ctor_arity: usize,
    field_types: &[Term],
) -> (MatchProblem, Vec<Unique>) {
    let mut new_scrutinees = Vec::new();
    let mut field_fvars = Vec::new();
    for field_type in field_types {
        let fvar = gen_.fresh_unnamed();
        field_fvars.push(fvar.clone());
        new_scrutinees.push(Scrutinee {
            term: Term::FVar(fvar),
            type_: field_type.clone(),
        });
    }
    for (i, s) in problem.scrutinees.iter().enumerate() {
        if i != col {
            new_scrutinees.push(s.clone());
        }
    }

    let mut new_rows = Vec::new();
    for row in &problem.rows {
        match &row.patterns[col] {
            Pattern::Constructor {
                ctor: c, fields, ..
            } if c == ctor => {
                let mut new_patterns = Vec::new();
                new_patterns.extend(fields.clone());
                for (i, p) in row.patterns.iter().enumerate() {
                    if i != col {
                        new_patterns.push(p.clone());
                    }
                }
                new_rows.push(PatternRow {
                    patterns: new_patterns,
                    rhs: row.rhs.clone(),
                });
            }
            Pattern::Var(fvar) => {
                let rhs = if let Some(fvar) = fvar {
                    let mut ctor_app = Term::Const(ctor.clone());
                    for field_fvar in &field_fvars {
                        ctor_app = Term::mk_app(ctor_app, Term::FVar(field_fvar.clone()));
                    }
                    subst::replace_fvar(&row.rhs, fvar, &ctor_app)
                } else {
                    row.rhs.clone()
                };
                let mut new_patterns = Vec::new();
                for _ in 0..ctor_arity {
                    new_patterns.push(Pattern::Var(None));
                }
                for (i, p) in row.patterns.iter().enumerate() {
                    if i != col {
                        new_patterns.push(p.clone());
                    }
                }
                new_rows.push(PatternRow {
                    patterns: new_patterns,
                    rhs,
                });
            }
            _ => {}
        }
    }

    let sub_problem = MatchProblem {
        scrutinees: new_scrutinees,
        rows: new_rows,
        return_type: problem.return_type.clone(),
        match_fn: problem.match_fn.clone(),
    };
    (sub_problem, field_fvars)
}

/// A heuristic to pick the first column for pattern matching.
fn pick_column(_problem: &MatchProblem) -> usize {
    0
}

/// Checks if all patterns in the given column are variables.
fn is_all_variables(problem: &MatchProblem, col: usize) -> bool {
    for row in &problem.rows {
        match &row.patterns[col] {
            Pattern::Var(_) => {},
            _ => return false,
        }
    }
    true
}

fn all_variables_elimination(problem: MatchProblem, col: usize) -> MatchProblem {
    let scrutinee = &problem.scrutinees[col];
    let mut new_rows = Vec::new();
    for row in problem.rows {
        let rhs = match &row.patterns[col] {
            Pattern::Var(Some(fvar)) => subst::replace_fvar(&row.rhs, fvar, &scrutinee.term),
            Pattern::Var(None) => row.rhs.clone(),
            _ => unreachable!(),
        };
        let mut new_patterns = row.patterns;
        new_patterns.remove(col);
        new_rows.push(PatternRow {
            patterns: new_patterns,
            rhs,
        });
    }
    MatchProblem {
        scrutinees: problem
            .scrutinees
            .into_iter()
            .enumerate()
            .filter_map(|(i, s)| if i == col { None } else { Some(s) })
            .collect(),
        rows: new_rows,
        return_type: problem.return_type,
        match_fn: problem.match_fn,
    }
}
