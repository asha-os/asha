use alloc::{boxed::Box};

use crate::{module::unique::Unique, syntax::tree::Literal};

pub enum Term {
    BVar(usize),
    FVar(Unique),
    MVar(Unique),
    App(Box<Term>, Box<Term>),
    Lam(Box<Term>),
    Pi(Box<Term>, Box<Term>),
    Sigma(Box<Term>, Box<Term>),
    Let(Box<Term>, Box<Term>, Box<Term>),
    Lit(Literal),
}