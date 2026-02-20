use alloc::{collections::btree_map::BTreeMap, string::String, vec::Vec};

use crate::{
    module::unique::{Unique, UniqueGen},
    spine::Term,
};

#[derive(Debug, Clone)]
/// Represents a local declaration, which can be either a binder (with no value) or a let-binding (with a value)
pub struct LocalDecl {
    /// The unique identifier for this local declaration
    pub fvar: Unique,
    /// The type of the local declaration
    pub type_: Term,
    /// The value of the local declaration, if it is a let-binding. None if it is a binder.
    pub value: Option<Term>,
}

#[derive(Debug, Clone)]
/// Represents the local context, which is a stack of local declarations (binders and let-bindings)
pub struct LocalContext {
    /// The list of local declarations in this context. The last declaration is the most recently added one.
    pub decls: Vec<LocalDecl>,
}

impl LocalContext {
    pub fn new() -> Self {
        Self { decls: Vec::new() }
    }

    /// Pushes a new binder onto the local context. This creates a new unique variable for the binder and adds it to the context with its type.
    pub fn push_binder(&mut self, name: String, type_: Term, gen_: &mut UniqueGen) -> Unique {
        let fvar = gen_.fresh(name);
        self.decls.push(LocalDecl {
            fvar: fvar.clone(),
            type_,
            value: None,
        });
        fvar
    }

    /// Pushes a new let-binding onto the local context. This creates a new unique variable for the let-binding and adds it to the context with its type and value.
    pub fn push_let(
        &mut self,
        name: String,
        type_: Term,
        value: Term,
        gen_: &mut UniqueGen,
    ) -> Unique {
        let fvar = gen_.fresh(name);
        self.decls.push(LocalDecl {
            fvar: fvar.clone(),
            type_,
            value: Some(value),
        });
        fvar
    }

    /// Looks up a local declaration by its unique variable. Returns None if no such declaration exists in the context.
    pub fn lookup(&self, fvar: Unique) -> Option<&LocalDecl> {
        self.decls.iter().find(|d| d.fvar == fvar)
    }

    /// Looks up a local declaration by its display name. Returns None if no such declaration exists in the context. If multiple declarations have the same display name, the most recently added one is returned.
    pub fn lookup_name(&self, name: &str) -> Option<&LocalDecl> {
        self.decls
            .iter()
            .rfind(|d| d.fvar.display_name.as_deref() == Some(name))
    }
}

#[derive(Debug, Clone)]
/// Represents a metavariable declaration, which consists of the metavariable itself, its type, and the local context in which it was created.
pub struct MetavarDecl {
    /// The unique identifier for this metavariable
    pub mvar: Unique,
    /// The type of the metavariable
    pub type_: Term,
    /// The local context in which this metavariable was created
    pub lctx: LocalContext,
}

#[derive(Debug, Clone)]
/// Represents the metavariable context, which consists of a list of metavariable declarations and a mapping from metavariables to their assigned values (if any)
pub struct MetavarContext {
    /// The list of metavariable declarations in this context. The last declaration is the most recently added one.
    pub decls: Vec<MetavarDecl>,
    /// The mapping from metavariables to their assigned values (if any)
    pub assignments: BTreeMap<Unique, Term>,
}

impl MetavarContext {
    pub fn new() -> Self {
        Self {
            decls: Vec::new(),
            assignments: BTreeMap::new(),
        }
    }

    /// Creates a fresh metavariable with the given type and local context, adds it to the metavariable context, and returns its unique identifier
    pub fn fresh_mvar(&mut self, type_: Term, lctx: &LocalContext, gen_: &mut UniqueGen) -> Unique {
        let mvar = gen_.fresh_unnamed();
        self.decls.push(MetavarDecl {
            mvar: mvar.clone(),
            type_,
            lctx: lctx.clone(),
        });
        mvar
    }

    /// Assigns a value to a metavariable. Panics if the metavariable is already assigned.
    pub fn assign(&mut self, mvar: Unique, value: Term) {
        assert!(
            !self.assignments.contains_key(&mvar),
            "mvar already assigned"
        );
        self.assignments.insert(mvar, value);
    }

    /// Checks if a metavariable is assigned. Returns true if the metavariable has an assigned value, false otherwise.
    pub fn is_assigned(&self, mvar: Unique) -> bool {
        self.assignments.contains_key(&mvar)
    }

    /// Gets the assigned value of a metavariable. Returns None if the metavariable is not assigned.
    pub fn get_assignment(&self, mvar: Unique) -> Option<&Term> {
        self.assignments.get(&mvar)
    }

    /// Looks up a metavariable declaration by its unique identifier. Returns None if no such declaration exists in the context.
    pub fn lookup_decl(&self, mvar: Unique) -> Option<&MetavarDecl> {
        self.decls.iter().find(|d| d.mvar == mvar)
    }
}
