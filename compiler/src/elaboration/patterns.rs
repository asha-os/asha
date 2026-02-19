use alloc::vec::Vec;
use api::println;

use crate::{
    elaboration::reduce::head_const,
    module::{name::QualifiedName, unique::Unique},
    spine::{Literal, Term},
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
/// A pattern match matrix, consisting of a vector of scrutinees and a vector of pattern rows.
pub struct MatchProblem {
    pub scrutinees: Vec<Scrutinee>,
    pub rows: Vec<PatternRow>,
}

impl MatchProblem {
    pub fn new(scrutinees: Vec<Scrutinee>, rows: Vec<PatternRow>) -> Self {
        Self { scrutinees, rows }
    }
}

/// Compiles a pattern match problem into a term that performs the pattern matching.
pub fn compile(problem: MatchProblem) -> Term {
    if problem.scrutinees.is_empty() {
        return problem.rows[0].rhs.clone();
    }

    let col = pick_column(&problem);
    // If the column is all variables, we can eliminate it and compile the smaller problem.
    if is_all_variables(&problem, col) {
        return compile(all_variables_elimination(problem, col));
    }

    let type_ = &problem.scrutinees[col].type_;
    let head_const = head_const(type_);
    println!("Head const: {}", head_const.unwrap());

    Term::Unit
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
    let mut new_rows = Vec::new();
    for row in problem.rows {
        match &row.patterns[col] {
            Pattern::Var(_) => {
                let mut new_patterns = row.patterns.clone();
                new_patterns.remove(col);
                new_rows.push(PatternRow {
                    patterns: new_patterns,
                    rhs: row.rhs,
                });
            }
            _ => unreachable!(),
        }
    }
    MatchProblem {
        scrutinees: problem
            .scrutinees
            .iter()
            .enumerate()
            .filter_map(|(i, scrutinee)| {
                if i == col {
                    None
                } else {
                    Some(scrutinee.clone())
                }
            })
            .collect(),
        rows: new_rows,
    }
}
