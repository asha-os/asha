use alloc::string::String;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ElabError {
    #[error("expected root")]
    ExpectedRoot,
    #[error("undefined variable `{0}`")]
    UndefinedVariable(String),
    #[error("type mismatch: expected `{expected:?}`, found `{found:?}`")]
    TypeMismatch { expected: crate::spine::Term, found: crate::spine::Term },
}