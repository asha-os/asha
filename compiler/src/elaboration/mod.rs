pub mod ctx;
pub mod err;
pub mod reduce;
pub mod subst;
pub mod unify;

use alloc::{string::String, vec::Vec};

use crate::{
    elaboration::{
        ctx::{LocalContext, MetavarContext},
        err::ElabError,
    },
    module::{
        ModuleId,
        unique::{Unique, UniqueGen},
    },
    spine::{BinderInfo, Term},
    syntax::tree::{SyntaxBinder, SyntaxExpr},
};

pub struct Environment {
    pub module_id: ModuleId,
    pub decls: Vec<Declaration>,
}

pub enum Declaration {
    Definition {
        name: String, // todo: qualified name
        type_: Term,
        value: Term,
    },
}

pub struct ElabState {
    pub env: Environment,
    pub gen_: UniqueGen,
    pub mctx: MetavarContext,
    pub lctx: LocalContext,
    pub errors: Vec<ElabError>,
}

impl ElabState {
    pub fn new(module: ModuleId) -> Self {
        Self {
            env: Environment {
                module_id: module.clone(),
                decls: Vec::new(),
            },
            gen_: UniqueGen::new(module),
            mctx: MetavarContext::new(),
            lctx: LocalContext { decls: Vec::new() },
            errors: Vec::new(),
        }
    }

    pub fn fresh_mvar(&mut self, type_: Term) -> Term {
        let u = self.mctx.fresh_mvar(type_, &self.lctx, &mut self.gen_);
        Term::MVar(u)
    }

    pub fn fresh_fvar(&mut self, name: String, type_: Term) -> (Unique, Term) {
        let u = self.lctx.push_binder(name, type_, &mut self.gen_);
        (u.clone(), Term::FVar(u))
    }

    fn erroneous_term(&mut self) -> Term {
        Term::MVar(self.gen_.fresh_unnamed())
    }

    pub fn elaborate_command(&mut self, cmd: &SyntaxExpr) {
        match cmd {
            SyntaxExpr::Def {
                name,
                binders,
                return_type,
                body,
            } => self.elaborate_def(name, binders, return_type, body),
            _ => todo!()
        }
    }

    fn elaborate_def(
        &mut self,
        name: &str,
        binders: &[SyntaxBinder],
        return_type: &SyntaxExpr,
        body: &SyntaxExpr,
    ) {
        let saved_lctx = self.lctx.clone();
        let mut binder_fvars: Vec<(Unique, BinderInfo, Term)> = Vec::new();

        for binder in binders {
            let (binder_name, binder_type_syntax, info) = match binder {
                SyntaxBinder::Explicit(n, ty) => (n, ty, BinderInfo::Explicit),
                SyntaxBinder::Implicit(n, ty) => (n, ty, BinderInfo::Implicit),
                SyntaxBinder::Instance(n, ty) => (n, ty, BinderInfo::InstanceImplicit),
            };
        }
    }

    fn elaborate_term(&mut self, syntax: &SyntaxExpr, expected_type: Option<&Term>) -> Term {
        let (term, inferred_type) = self.elaborate_term_inner(syntax);

        if let Some(expected) = expected_type {
            if !self.unify(&inferred_type, expected) {
                self.errors.push(ElabError::TypeMismatch {
                    expected: expected.clone(),
                    found: inferred_type,
                });
            }
        }

        term
    }

    fn elaborate_term_inner(&mut self, syntax: &SyntaxExpr) -> (Term, Term) {
        match syntax {
            SyntaxExpr::Var(name) => {
                if let Some(decl) = self.lctx.lookup_name(name) {
                    return (Term::FVar(decl.fvar.clone()), decl.type_.clone());
                }

                self.errors.push(ElabError::UndefinedVariable(name.clone()));
                (self.erroneous_term(), self.erroneous_term())
            }
            _ => todo!(),
        }
    }

    fn unify(&mut self, a: &Term, b: &Term) -> bool {
        unify::is_def_eq(self, a, b)
    }
}

pub fn elaborate_file(
    module_id: ModuleId,
    root: &SyntaxExpr,
) -> Result<Environment, Vec<ElabError>> {
    let mut state = ElabState::new(module_id);

    match root {
        SyntaxExpr::Root(commands) => {
            for cmd in commands {
                state.elaborate_command(cmd);
            }
        }
        _ => return Err(alloc::vec![ElabError::ExpectedRoot]),
    }

    if state.errors.is_empty() {
        Ok(state.env)
    } else {
        Err(state.errors)
    }
}
