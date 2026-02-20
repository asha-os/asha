use alloc::{boxed::Box, vec::Vec};

use crate::{
    elaboration::{
        Environment,
        err::{ElabError, ElabErrorKind},
        reduce::{head_const, is_recursive_field},
        subst,
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
    Literal(Literal),
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
    env: &Environment,
    gen_: &mut UniqueGen,
    problem: MatchProblem,
    span: Span,
) -> Result<Term, ElabError> {
    if problem.scrutinees.is_empty() {
        return Ok(problem.rows[0].rhs.clone());
    }
    let col = pick_column(&problem);
    // If the column is all variables, we can eliminate it and compile the smaller problem.
    if is_all_variables(&problem, col) {
        return compile(env, gen_, all_variables_elimination(problem, col), span);
    }

    // Otherwise, we split on constructors
    let type_ = &problem.scrutinees[col].type_;
    let inductive = head_const(type_)
        .and_then(|name| env.lookup_inductive(name))
        .ok_or_else(|| ElabError::new(ElabErrorKind::NotInductive(type_.clone()), span))?;

    let scrutinee = problem.scrutinees[col].term.clone();
    let num_params = inductive.num_params;
    let ctors = inductive.constructors.clone();

    let type_args = extract_type_args(type_, num_params);

    let scrutinee_type = problem.scrutinees[col].type_.clone();
    let motive_term = Term::Lam(
        BinderInfo::Explicit,
        Box::new(scrutinee_type.clone()),
        Box::new(problem.return_type.clone()),
    );

    let mut branches = Vec::new();
    for ctor_name in &ctors {
        let ctor_type = env.lookup(ctor_name).unwrap().type_().clone();
        let field_types = extract_field_types(&ctor_type, num_params, &type_args);
        let arity = field_types.len();

        let (sub_problem, field_fvars) =
            specialize(gen_, &problem, col, ctor_name, arity, &field_types);

        if sub_problem.rows.is_empty() {
            return Err(ElabError::new(
                ElabErrorKind::NonExhaustiveMatch(Some(Term::Const(ctor_name.clone()))),
                span,
            ));
        }

        let branch_body = compile(env, gen_, sub_problem, span)?;

        // Abstract field fvars and wrap with lambdas
        let mut result = branch_body;

        // First, wrap IH lambdas
        let inductive_name = &inductive.name;
        for (fvar, field_type) in field_fvars.iter().rev().zip(field_types.iter().rev()) {
            if is_recursive_field(field_type, inductive_name) {
                let ih_fvar = gen_.fresh_unnamed();

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
                result = Term::Lam(
                    BinderInfo::Explicit,
                    Box::new(Term::App(
                        Box::new(motive_term.clone()),
                        Box::new(Term::FVar(fvar.clone())),
                    )),
                    Box::new(result),
                );
            }
        }

        for (fvar, field_type) in field_fvars.iter().rev().zip(field_types.iter().rev()) {
            result = subst::abstract_fvar(&result, fvar.clone());
            result = Term::Lam(
                BinderInfo::Explicit,
                Box::new(field_type.clone()),
                Box::new(result),
            );
        }
        branches.push(result);
    }

    let match_fn = inductive.match_fn.clone();
    let mut result = Term::App(
        Box::new(Term::App(
            Box::new(Term::Const(match_fn)),
            Box::new(motive_term),
        )),
        Box::new(scrutinee),
    );
    for branch in branches {
        result = Term::App(Box::new(result), Box::new(branch));
    }

    Ok(result)
}

/// Extracts the type arguments applied to an inductive .
fn extract_type_args(scrutinee_type: &Term, num_params: usize) -> Vec<Term> {
    let mut args = Vec::new();
    let mut current = scrutinee_type.clone();
    while let Term::App(f, a) = current {
        args.push(*a);
        current = *f;
    }
    args.reverse();
    args.truncate(num_params);
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
                        ctor_app =
                            Term::App(Box::new(ctor_app), Box::new(Term::FVar(field_fvar.clone())));
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
            Pattern::Var(_) => continue,
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
