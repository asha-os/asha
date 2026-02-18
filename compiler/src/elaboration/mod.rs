//! # Elaboration
//!
//! The elaboration module is the core of the type checker. It transforms parsed syntax trees
//! ([`SyntaxExpr`]) into fully typed core terms ([`Term`]) while performing type inference,
//! unification, and implicit argument insertion.
//!
//! ## Architecture
//!
//! Elaboration is driven by [`ElabState`], which carries:
//! - A global [`Environment`] of declarations and externals
//! - A [`LocalContext`](ctx::LocalContext) of in-scope binders and let-bindings
//! - A [`MetavarContext`](ctx::MetavarContext) for unification variables (holes)
//! - A hierarchical [`Namespace`] tree for name resolution
//!
//! The main entry point is [`elaborate_file`], which processes a root syntax tree and produces
//! an [`Environment`] containing all elaborated declarations.
//!
//! ## Submodules
//!
//! - [`ctx`]: Local and metavariable context management
//! - [`err`]: Elaboration error types and diagnostics
//! - [`unify`]: Definitional equality checking and metavariable assignment
//! - [`reduce`]: Weak head normal form (WHNF) reduction
//! - [`subst`]: De Bruijn index substitution, shifting, and abstraction

pub mod ctx;
pub mod err;
pub mod patterns;
pub mod reduce;
pub mod subst;
pub mod unify;

use alloc::{
    boxed::Box,
    collections::btree_map::BTreeMap,
    format,
    string::{String, ToString},
    vec::Vec,
};
use api::println;

use crate::{
    elaboration::{
        ctx::{LocalContext, MetavarContext},
        err::{ElabError, ElabErrorKind},
        patterns::{MatchProblem, Pattern, PatternRow, Scrutinee},
        reduce::head_const,
    },
    module::{
        ModuleId,
        name::QualifiedName,
        prim::*,
        unique::{Unique, UniqueGen},
    },
    spine::{BinderInfo, Level, Literal, Term, uncurry},
    syntax::{
        Span, Spanned,
        tree::{
            DefBody, InductiveConstructor, InfixOp, PatternMatchArm, RecordField, SyntaxBinder,
            SyntaxExpr, SyntaxPattern, SyntaxTree, SyntaxTreeDeclaration,
        },
    },
};

/// A hierarchical namespace for name resolution.
///
/// Each namespace maps short display names to their [`QualifiedName`],
/// and may contain child namespaces. This forms a tree
/// that mirrors the module/record/class/inductive structure of the source program.
#[derive(Debug, Clone)]
pub struct Namespace {
    /// Top-level declarations visible in this namespace, keyed by display name.
    pub decls: BTreeMap<String, QualifiedName>,
    /// Child namespaces (e.g. record fields, class methods, inductive constructors).
    pub children: BTreeMap<String, Namespace>,
}

impl Namespace {
    pub fn new() -> Self {
        Self {
            decls: BTreeMap::new(),
            children: BTreeMap::new(),
        }
    }

    /// Looks up a declaration in this namespace by its display name.
    pub fn lookup_decl(&self, name: &str) -> Option<&QualifiedName> {
        self.decls.get(name)
    }

    /// Returns a direct child namespace by name.
    pub fn child(&self, name: &str) -> Option<&Namespace> {
        self.children.get(name)
    }

    /// Traverses a path of namespace segments, returning the namespace at the end.
    /// Returns `None` if any segment along the path does not exist.
    pub fn walk(&self, path: &[String]) -> Option<&Namespace> {
        let mut current = self;
        for segment in path {
            current = current.children.get(segment)?;
        }
        Some(current)
    }

    /// Resolves a qualified reference by walking the namespace `path` and then looking up `member`.
    pub fn resolve(&self, path: &[String], member: &str) -> Option<&QualifiedName> {
        self.walk(path)?.lookup_decl(member)
    }
}

/// The global elaboration environment.
///
/// Holds all declarations produced during elaboration, externally-provided primitive
/// types and operations, and the root namespace for name resolution.
#[derive(Debug, Clone)]
pub struct Environment {
    /// The module this environment belongs to.
    pub module_id: ModuleId,
    /// Externally-provided declarations. Maps name to its type.
    pub externals: BTreeMap<QualifiedName, Term>,
    /// All declarations elaborated in this module (definitions, constructors, etc.).
    pub decls: BTreeMap<QualifiedName, Declaration>,
    /// The root of the namespace tree for name resolution.
    pub root_namespace: Namespace,
}

impl Environment {
    /// Creates an environment pre-loaded with built-in primitive types and operations.
    ///
    /// Also populates the root namespace so these names are resolvable.
    pub fn pre_loaded(module_id: ModuleId) -> Self {
        // todo: review
        let mut externals = BTreeMap::new();
        externals.insert(PRIM_NAT, Term::Sort(Level::type0()));
        externals.insert(PRIM_STRING, Term::Sort(Level::type0()));
        externals.insert(PRIM_BOOL, Term::Sort(Level::type0()));
        externals.insert(PRIM_TRUE, Term::Const(PRIM_BOOL));
        externals.insert(PRIM_FALSE, Term::Const(PRIM_BOOL));
        externals.insert(
            PRIM_FIN,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Const(PRIM_NAT)),
                Box::new(Term::Sort(Level::type0())),
            ),
        );
        externals.insert(
            PRIM_ARRAY,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Sort(Level::type0())),
                Box::new(Term::Pi(
                    BinderInfo::Explicit,
                    Box::new(Term::Const(PRIM_NAT)),
                    Box::new(Term::Sort(Level::type0())),
                )),
            ),
        );
        externals.insert(
            PRIM_IO,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Sort(Level::type0())),
                Box::new(Term::Sort(Level::type0())),
            ),
        );
        // todo: remove these
        externals.insert(
            PRIM_ADD_FN,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Const(PRIM_NAT)),
                Box::new(Term::Pi(
                    BinderInfo::Explicit,
                    Box::new(Term::Const(PRIM_NAT)),
                    Box::new(Term::Const(PRIM_NAT)),
                )),
            ),
        );
        externals.insert(
            PRIM_GT_FN,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Const(PRIM_NAT)),
                Box::new(Term::Pi(
                    BinderInfo::Explicit,
                    Box::new(Term::Const(PRIM_NAT)),
                    Box::new(Term::Sort(Level::Zero)),
                )),
            ),
        );
        let mut root_namespace = Namespace::new();
        root_namespace.decls.insert("Nat".into(), PRIM_NAT);
        root_namespace.decls.insert("Str".into(), PRIM_STRING);
        root_namespace.decls.insert("Fin".into(), PRIM_FIN);
        root_namespace.decls.insert("Array".into(), PRIM_ARRAY);
        root_namespace.decls.insert("IO".into(), PRIM_IO);
        root_namespace.decls.insert("Bool".into(), PRIM_BOOL);
        root_namespace.children.insert(
            "Bool".into(),
            Namespace {
                decls: [("true".into(), PRIM_TRUE), ("false".into(), PRIM_FALSE)].into(),
                children: BTreeMap::new(),
            },
        );
        root_namespace.children.insert(
            "Add".into(),
            Namespace {
                decls: [("add".into(), PRIM_ADD_FN)].into(),
                children: BTreeMap::new(),
            },
        );
        root_namespace.children.insert(
            "Gt".into(),
            Namespace {
                decls: [("gt".into(), PRIM_GT_FN)].into(),
                children: BTreeMap::new(),
            },
        );
        Self {
            module_id,
            externals,
            decls: BTreeMap::new(),
            root_namespace,
        }
    }

    /// Looks up a declaration by its [`QualifiedName`]. Only searches module-local declarations,
    /// not externals.
    pub fn lookup(&self, name: &QualifiedName) -> Option<&Declaration> {
        self.decls.get(name)
    }

    /// Looks up the type of a name, searching both module-local declarations and externals.
    /// Returns the canonical [`QualifiedName`] and its type.
    pub fn lookup_type(&self, qname: &QualifiedName) -> Option<(&QualifiedName, &Term)> {
        self.decls
            .get(qname)
            .map(|decl| (decl.name(), decl.type_()))
            .or_else(|| self.externals.get_key_value(qname).map(|(n, t)| (n, t)))
    }
}

/// A top-level declaration in the elaborated environment.
#[derive(Debug, Clone)]
pub enum Declaration {
    /// A function or value definition with a known body.
    Definition {
        name: QualifiedName,
        type_: Term,
        value: Term,
        span: Span,
    },
    /// A declaration that has a type but no reducible body, they are opaque constants.
    Constructor {
        name: QualifiedName,
        type_: Term,
        span: Span,
    },
}

impl Declaration {
    /// Returns the declaration's [`QualifiedName`].
    pub fn name(&self) -> &QualifiedName {
        match self {
            Declaration::Definition { name, .. } => name,
            Declaration::Constructor { name, .. } => name,
        }
    }

    /// Returns the declaration's type.
    pub fn type_(&self) -> &Term {
        match self {
            Declaration::Definition { type_, .. } => type_,
            Declaration::Constructor { type_, .. } => type_,
        }
    }
}

/// The mutable state threaded through elaboration.
///
/// Combines the global environment, local context, metavariable context, unique name
/// generator, namespace tracking, and accumulated errors into a single state object
/// that is passed (as `&mut self`) to every elaboration method.
pub struct ElabState {
    /// The global environment containing all elaborated declarations and externals.
    pub env: Environment,
    /// Generator for fresh [`Unique`] identifiers (scoped to the current module).
    pub gen_: UniqueGen,
    /// Metavariable context: tracks unification variables and their assignments.
    pub mctx: MetavarContext,
    /// Local context: stack of in-scope binders and let-bindings.
    pub lctx: LocalContext,
    /// The namespace path currently being elaborated into (e.g. `["MyRecord"]`).
    pub current_namespace: Vec<String>,
    /// Namespaces that have been opened, making their declarations visible unqualified.
    pub open_namespaces: Vec<Vec<String>>,
    /// Errors accumulated during elaboration (reported at the end).
    pub errors: Vec<ElabError>,
}

impl ElabState {
    /// Creates a blank elaboration state with no pre-loaded primitives.
    pub fn new(module: ModuleId) -> Self {
        Self {
            env: Environment {
                module_id: module.clone(),
                externals: BTreeMap::new(),
                decls: BTreeMap::new(),
                root_namespace: Namespace::new(),
            },
            gen_: UniqueGen::new(module),
            mctx: MetavarContext::new(),
            lctx: LocalContext { decls: Vec::new() },
            current_namespace: Vec::new(),
            open_namespaces: Vec::new(),
            errors: Vec::new(),
        }
    }

    /// Creates an elaboration state pre-loaded with built-in primitive types and operators.
    pub fn pre_loaded(module: ModuleId) -> Self {
        let mut state = Self::new(module);
        state.env = Environment::pre_loaded(state.env.module_id.clone());
        state.open_namespaces.push(alloc::vec!["Bool".into()]);
        state
    }

    /// Creates a fresh metavariable (unification hole) with the given type, using
    /// the current local context. Returns it wrapped as `Term::MVar`.
    pub fn fresh_mvar(&mut self, type_: Term) -> Term {
        let u = self.mctx.fresh_mvar(type_, &self.lctx, &mut self.gen_);
        Term::MVar(u)
    }

    /// Creates a fresh free variable with the given display name and type, pushes it
    /// onto the local context, and returns both the [`Unique`] and `Term::FVar`.
    pub fn fresh_fvar(&mut self, name: String, type_: Term) -> (Unique, Term) {
        let u = self.lctx.push_binder(name, type_, &mut self.gen_);
        (u.clone(), Term::FVar(u))
    }

    /// Produces a throwaway metavariable term used as a placeholder after an error.
    fn erroneous_term(&mut self) -> Term {
        Term::MVar(self.gen_.fresh_unnamed())
    }

    /// Resolves a name to its [`QualifiedName`] and type using multi-level lookup:
    /// 1. If an explicit namespace path is given, look it up directly.
    /// 2. Try the current namespace (e.g. inside a record or class body).
    /// 3. Try each opened namespace in order.
    /// 4. Fall back to the root namespace.
    fn resolve_name(&self, namespace: &[String], member: &str) -> Option<(&QualifiedName, &Term)> {
        let ns = &self.env.root_namespace;

        if !namespace.is_empty() {
            return ns
                .resolve(namespace, member)
                .and_then(|qn| self.env.lookup_type(qn));
        }

        if !self.current_namespace.is_empty() {
            if let Some(qn) = ns.resolve(&self.current_namespace, member) {
                if let Some(result) = self.env.lookup_type(qn) {
                    return Some(result);
                }
            }
        }

        for opened in &self.open_namespaces {
            if let Some(qn) = ns.resolve(opened, member) {
                if let Some(result) = self.env.lookup_type(qn) {
                    return Some(result);
                }
            }
        }

        ns.lookup_decl(member)
            .and_then(|qn| self.env.lookup_type(qn))
    }

    /// Dispatches a top-level declaration to the appropriate elaboration handler.
    pub fn elaborate_declaration(&mut self, decl: &SyntaxTreeDeclaration) {
        match decl {
            SyntaxTreeDeclaration::Def {
                name,
                binders,
                return_type,
                body,
                span,
            } => self.elaborate_def(name, binders, return_type, body, *span),
            SyntaxTreeDeclaration::Record {
                name,
                binders,
                fields,
                span,
            } => self.elaborate_record(name, binders, fields, *span),
            SyntaxTreeDeclaration::Extern {
                name,
                type_ann,
                span,
            } => self.elaborate_extern(name, type_ann, *span),
            SyntaxTreeDeclaration::Inductive {
                name,
                binders,
                constructors,
                span,
            } => self.elaborate_inductive(name, binders, constructors, *span),
            SyntaxTreeDeclaration::Class {
                name,
                binders,
                members,
                span,
            } => self.elaborate_class(name, binders, members, *span),
            SyntaxTreeDeclaration::Instance { .. } => {
                // todo: implement instance elaboration
            }
            SyntaxTreeDeclaration::Eval { expr, .. } => {
                let term = self.elaborate_term(expr, None);
                println!("Evaluated term: {:#?}", &term);
            }
        }
    }

    /// Elaborates a sequence of binders (explicit, implicit, or instance-implicit),
    /// pushing each into the local context as a free variable.
    ///
    /// Returns a list of `(fvar, binder_info, elaborated_type)` triples, which can later
    /// be used by [`Self::abstract_binders`] to build Pi types.
    fn elaborate_binders(&mut self, binders: &[SyntaxBinder]) -> Vec<(Unique, BinderInfo, Term)> {
        let mut binder_fvars = Vec::new();
        for binder in binders {
            let (binder_name, binder_type_syntax, info) = match binder {
                SyntaxBinder::Explicit(_, n, ty) => (n, ty, BinderInfo::Explicit),
                SyntaxBinder::Implicit(_, n, ty) => (n, ty, BinderInfo::Implicit),
                SyntaxBinder::Instance(_, n, ty) => (n, ty, BinderInfo::InstanceImplicit),
            };
            let (elaborated_type, type_of_type) = self.elaborate_term_inner(binder_type_syntax);
            let normalized_type_of_type = reduce::whnf(self, &type_of_type);
            if !matches!(normalized_type_of_type, Term::Sort(_)) {
                self.errors.push(ElabError::new(
                    ElabErrorKind::TypeExpected(elaborated_type.clone()),
                    binder.span(),
                ));
            }
            let (fvar, _) = self.fresh_fvar(binder_name.clone(), elaborated_type.clone());
            binder_fvars.push((fvar, info, elaborated_type));
        }
        binder_fvars
    }

    /// Converts free variables introduced by [`Self::elaborate_binders`] back into bound
    /// variables by wrapping `term` in nested Pi types (right to left).
    ///
    /// For binders `(a, b, c)` and a term `T`, produces `Pi a. Pi b. Pi c. T`
    /// where each free variable is abstracted into the corresponding De Bruijn index.
    fn abstract_binders(binder_fvars: &[(Unique, BinderInfo, Term)], mut term: Term) -> Term {
        for (fvar, info, ty) in binder_fvars.iter().rev() {
            term = subst::abstract_fvar(&term, fvar.clone());
            term = Term::Pi(info.clone(), Box::new(ty.clone()), Box::new(term));
        }
        term
    }

    /// Elaborates a `def` declaration.
    ///
    /// 1. Generates a fresh [`QualifiedName`] for the definition.
    /// 2. Saves the local context, elaborates binders, return type, and body.
    /// 3. Abstracts the binders into a Pi type and lambda body.
    /// 4. Registers the definition in the environment and namespace.
    /// 5. Restores the local context.
    fn elaborate_def(
        &mut self,
        name: &str,
        binders: &[SyntaxBinder],
        return_type: &SyntaxExpr,
        body: &DefBody,
        span: Span,
    ) {
        let def_name = QualifiedName::User(self.gen_.fresh(name.to_string()));

        let saved_lctx = self.lctx.clone();
        let binder_fvars = self.elaborate_binders(binders);
        let elaborated_return_type = self.elaborate_term(return_type, None);
        let elaborated_body = match body {
            DefBody::Expr(body) => self.elaborate_term(body, Some(&elaborated_return_type)),
            DefBody::PatternMatch { arms, span } => {
                let (pattern_return_type, scrutinee_types) =
                    uncurry(elaborated_return_type.clone());
                let n = scrutinee_types.len();
                let scrutinees = scrutinee_types
                    .iter()
                    .enumerate()
                    .map(|(i, (_, ty))| Scrutinee {
                        term: Term::BVar(n - 1 - i),
                        type_: ty.clone(),
                    })
                    .collect::<Vec<_>>();
                let body = self.elaborate_pattern_match(
                    scrutinees,
                    arms,
                    Some(pattern_return_type),
                    *span,
                );

                let mut lambda = body;
                for (_, scrutinee_type) in scrutinee_types.iter().rev() {
                    lambda = Term::Lam(
                        BinderInfo::Explicit,
                        Box::new(scrutinee_type.clone()),
                        Box::new(lambda),
                    );
                }
                lambda
            }
        };

        let pi_type = Self::abstract_binders(&binder_fvars, elaborated_return_type);
        let mut value = elaborated_body;
        for (fvar, _, _) in binder_fvars.iter().rev() {
            value = subst::abstract_fvar(&value, fvar.clone());
        }

        self.env.decls.insert(
            def_name.clone(),
            Declaration::Definition {
                name: def_name.clone(),
                type_: pi_type,
                value,
                span,
            },
        );
        self.register_in_namespace(name, def_name);

        self.lctx = saved_lctx;
    }

    /// Elaborates a syntax expression into a core [`Term`], optionally checking it against
    /// an expected type. If the inferred type does not unify with the expected type,
    /// a [`ElabErrorKind::TypeMismatch`] is recorded.
    fn elaborate_term(&mut self, syntax: &SyntaxExpr, expected_type: Option<&Term>) -> Term {
        let (term, inferred_type) = self.elaborate_term_inner(syntax);

        if let Some(expected) = expected_type {
            if !self.unify(&inferred_type, expected) {
                self.errors.push(ElabError::new(
                    err::ElabErrorKind::TypeMismatch {
                        expected: expected.clone(),
                        found: inferred_type,
                    },
                    syntax.span(),
                ));
            }
        }

        term
    }

    /// Core term elaboration. Returns `(elaborated_term, inferred_type)`.
    ///
    /// Handles all expression forms and reports errors for unsupported syntax.
    fn elaborate_term_inner(&mut self, syntax: &SyntaxExpr) -> (Term, Term) {
        match syntax {
            SyntaxExpr::Var {
                namespace, member, ..
            } => {
                if namespace.is_empty() {
                    if let Some(decl) = self.lctx.lookup_name(member) {
                        return (Term::FVar(decl.fvar.clone()), decl.type_.clone());
                    }
                }

                if let Some((name, type_)) = self.resolve_name(namespace, member) {
                    return (Term::Const(name.clone()), type_.clone());
                }

                self.errors.push(ElabError::new(
                    ElabErrorKind::UndefinedVariable(member.clone()),
                    syntax.span(),
                ));
                (self.erroneous_term(), self.erroneous_term())
            }
            SyntaxExpr::Constructor { name, .. } if name == "Type" => (
                Term::Sort(Level::type0()),
                Term::Sort(Level::Succ(Box::new(Level::type0()))),
            ),
            SyntaxExpr::Constructor { name, .. } if name == "Prop" => {
                (Term::Sort(Level::Zero), Term::Sort(Level::type0()))
            }
            SyntaxExpr::Constructor {
                namespace, name, ..
            } => {
                if let Some((name, type_)) = self.resolve_name(namespace, name) {
                    return (Term::Const(name.clone()), type_.clone());
                }

                self.errors.push(ElabError::new(
                    ElabErrorKind::UndefinedConstructor(name.clone()),
                    syntax.span(),
                ));
                (self.erroneous_term(), self.erroneous_term())
            }
            SyntaxExpr::Lit { value, .. } => {
                let ty = match value {
                    crate::spine::Literal::Nat(_) => Term::Const(PRIM_NAT),
                    crate::spine::Literal::Str(_) => Term::Const(PRIM_STRING),
                };
                (Term::Lit(value.clone()), ty)
            }
            SyntaxExpr::Array {
                elements: elems, ..
            } => {
                let elem_type = if let Some(head) = elems.first() {
                    let (_term, head_ty) = self.elaborate_term_inner(head);
                    head_ty
                } else {
                    self.fresh_mvar(Term::Sort(Level::type0()))
                };
                let elems_len = elems.len() as u64;

                let array_type = Term::App(
                    Box::new(Term::App(
                        Box::new(Term::Const(PRIM_ARRAY)),
                        Box::new(elem_type.clone()),
                    )),
                    Box::new(Term::Lit(Literal::Nat(elems_len))),
                );
                let mut result = Term::Const(PRIM_ARRAY_NIL);
                let mut current_length = 0;
                let mut elems = elems.clone();
                elems.reverse();
                for elem in elems {
                    let elaborated_elem = self.elaborate_term(&elem, Some(&elem_type));
                    result = Term::App(
                        Box::new(Term::App(
                            Box::new(Term::App(
                                Box::new(Term::App(
                                    Box::new(Term::Const(PRIM_ARRAY_CONS)),
                                    Box::new(elem_type.clone()),
                                )),
                                Box::new(Term::Lit(Literal::Nat(current_length))),
                            )),
                            Box::new(elaborated_elem),
                        )),
                        Box::new(result),
                    );
                    current_length += 1;
                }
                (result, array_type)
            }
            SyntaxExpr::InfixOp { op, lhs, rhs, span } => {
                let (op_namespace, op_name) = match op {
                    InfixOp::Add => (PRIM_ADD_CLASS, PRIM_ADD_FN),
                    InfixOp::Sub => (PRIM_SUB_CLASS, PRIM_SUB_FN),
                    InfixOp::Mul => (PRIM_MUL_CLASS, PRIM_MUL_FN),
                    InfixOp::Div => (PRIM_DIV_CLASS, PRIM_DIV_FN),
                    InfixOp::Eq => (PRIM_BEQ_CLASS, PRIM_BEQ_FN),
                    InfixOp::Neq => (PRIM_BNEQ_CLASS, PRIM_BNEQ_FN),
                    InfixOp::Lt => (PRIM_LT_CLASS, PRIM_LT_FN),
                    InfixOp::Gt => (PRIM_GT_CLASS, PRIM_GT_FN),
                    InfixOp::Leq => (PRIM_LEQ_CLASS, PRIM_LEQ_FN),
                    InfixOp::Geq => (PRIM_GEQ_CLASS, PRIM_GEQ_FN),
                };
                let namespace_str = op_namespace.display().unwrap();
                let namespace = alloc::vec![namespace_str.to_string()];
                let member = op_name.display().unwrap().to_string();
                let var_term = self.elaborate_term(
                    &SyntaxExpr::Var {
                        namespace: namespace.clone(),
                        member: member.clone(),
                        span: *span,
                    },
                    None,
                );
                let (arg1, arg2_ty) = self.elaborate_term_inner(lhs);
                let arg2 = self.elaborate_term(rhs, Some(&arg2_ty));

                if let Some((_, expected_fn_type)) = self.resolve_name(&namespace, &member) {
                    let return_type = match expected_fn_type {
                        Term::Pi(_, _, body) => {
                            let after_arg1 = subst::instantiate(body, &arg1);
                            match after_arg1 {
                                Term::Pi(_, _, body2) => subst::instantiate(&body2, &arg2),
                                _ => {
                                    self.errors.push(ElabError::new(
                                        ElabErrorKind::NotAFunction(after_arg1),
                                        *span,
                                    ));
                                    self.erroneous_term()
                                }
                            }
                        }
                        _ => {
                            self.errors.push(ElabError::new(
                                ElabErrorKind::NotAFunction(expected_fn_type.clone()),
                                *span,
                            ));
                            self.erroneous_term()
                        }
                    };
                    let term = Term::App(
                        Box::new(Term::App(Box::new(var_term), Box::new(arg1))),
                        Box::new(arg2),
                    );
                    (term, return_type)
                } else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::UndefinedVariable(format!(
                            "{}::{}",
                            &namespace_str, &member
                        )),
                        *span,
                    ));
                    return (self.erroneous_term(), self.erroneous_term());
                }
            }
            SyntaxExpr::App { fun, arg, .. } => self.elaborate_app(syntax, fun, arg),
            SyntaxExpr::Proj { value, field, span } => {
                let (elaborated_value, value_type) = self.elaborate_term_inner(value);
                let normalized_value_type = reduce::whnf(self, &value_type);
                if let Some(record_name) = head_const(&normalized_value_type) {
                    let namespace = record_name.display().unwrap().to_string();
                    if let Some((proj_fn_name, proj_fn_type)) =
                        self.resolve_name(&[namespace.clone()], field)
                    {
                        let proj_fn_term = Term::Const(proj_fn_name.clone());
                        let (mut term, fn_type) = self.insert_implicit_args_until(
                            proj_fn_term,
                            proj_fn_type.clone(),
                            BinderInfo::InstanceImplicit,
                        );
                        match fn_type {
                            Term::Pi(_, _, body_ty) => {
                                let return_type = subst::instantiate(&body_ty, &elaborated_value);
                                term = Term::App(Box::new(term), Box::new(elaborated_value));
                                (term, return_type)
                            }
                            _ => {
                                self.errors.push(ElabError::new(
                                    ElabErrorKind::NotAFunction(fn_type),
                                    *span,
                                ));
                                (self.erroneous_term(), self.erroneous_term())
                            }
                        }
                    } else {
                        self.errors.push(ElabError::new(
                            ElabErrorKind::UndefinedVariable(format!("{}::{}", namespace, field)),
                            *span,
                        ));
                        (self.erroneous_term(), self.erroneous_term())
                    }
                } else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::CannotProject(elaborated_value, field.clone()),
                        *span,
                    ));
                    (self.erroneous_term(), self.erroneous_term())
                }
            }
            SyntaxExpr::Arrow {
                param_type,
                return_type,
                ..
            } => {
                let elaborated_param_type = self.elaborate_term(param_type, None);
                let elaborated_return_type = self.elaborate_term(return_type, None);
                (
                    Term::Pi(
                        BinderInfo::Explicit,
                        Box::new(elaborated_param_type.clone()),
                        Box::new(elaborated_return_type.clone()),
                    ),
                    Term::Sort(Level::type0()),
                )
            }
            SyntaxExpr::Lambda { binders, body, .. } => {
                let saved_lctx = self.lctx.clone();
                let binder_fvars = self.elaborate_binders(binders);
                let (elaborated_body, body_type) = self.elaborate_term_inner(body);
                let mut term = elaborated_body;
                let mut result_type = body_type;
                for (fvar, info, ty) in binder_fvars.iter().rev() {
                    term = subst::abstract_fvar(&term, fvar.clone());
                    term = Term::Lam(info.clone(), Box::new(ty.clone()), Box::new(term));
                    result_type = subst::abstract_fvar(&result_type, fvar.clone());
                    result_type =
                        Term::Pi(info.clone(), Box::new(ty.clone()), Box::new(result_type));
                }
                self.lctx = saved_lctx;
                (term, result_type)
            }
            SyntaxExpr::Unit { .. } => (Term::Unit, Term::Sort(Level::type0())),
            u => {
                self.errors.push(ElabError::new(
                    err::ElabErrorKind::UnsupportedSyntax(u.clone()),
                    syntax.span(),
                ));
                (self.erroneous_term(), self.erroneous_term())
            }
        }
    }

    /// Inserts fresh metavariables for all leading implicit and instance-implicit
    /// arguments, stopping at the first explicit parameter. Returns the updated term
    /// (with implicit args applied) and the remaining function type.
    fn insert_implicit_args(&mut self, term: Term, fn_type: Term) -> (Term, Term) {
        self.insert_implicit_args_until(term, fn_type, BinderInfo::Explicit)
    }

    /// Like [`Self::insert_implicit_args`], but stops at a specified [`BinderInfo`] kind
    /// rather than always stopping at `Explicit`. Used by projection elaboration to
    /// stop before instance-implicit parameters.
    fn insert_implicit_args_until(
        &mut self,
        mut term: Term,
        mut fn_type: Term,
        stop_at: BinderInfo,
    ) -> (Term, Term) {
        loop {
            fn_type = reduce::whnf(self, &fn_type);
            match &fn_type {
                Term::Pi(info, param_ty, body_ty) if info != &stop_at => {
                    let mvar = self.fresh_mvar(*param_ty.clone());
                    fn_type = subst::instantiate(body_ty, &mvar);
                    term = Term::App(Box::new(term), Box::new(mvar));
                }
                _ => break,
            };
        }
        (term, fn_type)
    }

    /// Elaborates a function application `fun arg`.
    ///
    /// First elaborates `fun`, inserts any implicit arguments, then elaborates
    /// `arg` against the expected parameter type and instantiates the return type.
    fn elaborate_app(
        &mut self,
        syntax: &SyntaxExpr,
        fun: &SyntaxExpr,
        arg: &SyntaxExpr,
    ) -> (Term, Term) {
        let (term, fn_type) = self.elaborate_term_inner(fun);
        let (term, fn_type) = self.insert_implicit_args(term, fn_type);

        match fn_type {
            Term::Pi(_info, param_ty, body_ty) => {
                let elaborated_arg = self.elaborate_term(arg, Some(&param_ty));
                let return_type = subst::instantiate(&body_ty, &elaborated_arg);
                (
                    Term::App(Box::new(term), Box::new(elaborated_arg)),
                    return_type,
                )
            }
            u => {
                self.errors.push(ElabError::new(
                    ElabErrorKind::NotAFunction(u),
                    syntax.span(),
                ));
                return (self.erroneous_term(), self.erroneous_term());
            }
        }
    }

    /// Checks whether two terms are definitionally equal, potentially assigning
    /// metavariables. Delegates to [`unify::is_def_eq`].
    fn unify(&mut self, a: &Term, b: &Term) -> bool {
        unify::is_def_eq(self, a, b)
    }

    /// Elaborates a `record` declaration.
    ///
    /// Creates the record type constant (typed as `Type`), a `new` constructor whose
    /// parameters are the record fields, and a projection function for each field
    /// (stored in a child namespace `RecordName.fieldName`).
    fn elaborate_record(
        &mut self,
        name: &str,
        binders: &[SyntaxBinder],
        fields: &[RecordField],
        span: Span,
    ) {
        let record_name = QualifiedName::User(self.gen_.fresh(name.to_string()));
        let mut child_ns = Namespace::new();

        let saved_lctx = self.lctx.clone();
        let binder_fvars = self.elaborate_binders(binders);
        let mut constructor_type = Term::Const(record_name.clone());
        for field in fields.iter().rev() {
            let field_name = QualifiedName::User(self.gen_.fresh(field.name.clone()));
            let field_type = self.elaborate_term(&field.type_ann, None);
            // todo: make this a def
            let field_def = Declaration::Constructor {
                name: field_name.clone(),
                type_: field_type.clone(),
                span: field.span,
            };

            self.env.decls.insert(field_name.clone(), field_def);
            child_ns.decls.insert(field.name.clone(), field_name);

            constructor_type = Term::Pi(
                BinderInfo::Explicit,
                Box::new(field_type),
                Box::new(constructor_type),
            );
        }

        let pi_type = Self::abstract_binders(&binder_fvars, Term::Sort(Level::type0()));
        let constructor_type = Self::abstract_binders(&binder_fvars, constructor_type);

        self.env.decls.insert(
            record_name.clone(),
            Declaration::Constructor {
                name: record_name.clone(),
                type_: pi_type,
                span,
            },
        );
        self.register_in_namespace(name, record_name.clone());

        let constructor_name = QualifiedName::User(self.gen_.fresh("new".to_string()));
        self.env.decls.insert(
            constructor_name.clone(),
            Declaration::Constructor {
                name: constructor_name.clone(),
                type_: constructor_type,
                span,
            },
        );
        child_ns.decls.insert("new".into(), constructor_name);
        let parent_ns = &mut self.env.root_namespace.children;
        if let Some(existing) = parent_ns.get_mut(name) {
            existing.decls.extend(child_ns.decls);
            existing.children.extend(child_ns.children);
        } else {
            parent_ns.insert(name.to_string(), child_ns);
        }

        self.lctx = saved_lctx;
    }

    /// Registers a declaration in the appropriate namespace (root or current).
    fn register_in_namespace(&mut self, display_name: &str, qname: QualifiedName) {
        let ns = if self.current_namespace.is_empty() {
            &mut self.env.root_namespace
        } else {
            let mut current = &mut self.env.root_namespace;
            for segment in &self.current_namespace {
                current = current
                    .children
                    .entry(segment.clone())
                    .or_insert_with(Namespace::new);
            }
            current
        };
        ns.decls.insert(display_name.into(), qname);
    }

    /// Elaborates an `extern` declaration: type-checks the annotation and registers
    /// it as an external (opaque) binding in the environment.
    fn elaborate_extern(&mut self, name: &str, type_ann: &SyntaxExpr, _span: Span) {
        let elaborated_type = self.elaborate_term(type_ann, None);
        let qname = QualifiedName::User(self.gen_.fresh(name.to_string()));
        self.env.externals.insert(qname.clone(), elaborated_type);
        self.register_in_namespace(name, qname);
    }

    /// Elaborates an `inductive` type declaration.
    ///
    /// Creates the inductive type constant (typed as `Type` after abstracting binders),
    /// then elaborates each constructor via [`Self::elaborate_inductive_constructors`],
    /// placing them in a child namespace `InductiveName::CtorName`.
    fn elaborate_inductive(
        &mut self,
        name: &str,
        binders: &[SyntaxBinder],
        constructors: &[InductiveConstructor],
        span: Span,
    ) {
        let name = QualifiedName::User(self.gen_.fresh(name.to_string()));
        let saved_lctx = self.lctx.clone();

        let binder_fvars = self.elaborate_binders(binders);
        let inductive_type = Self::abstract_binders(&binder_fvars, Term::Sort(Level::type0()));
        self.env.decls.insert(
            name.clone(),
            Declaration::Constructor {
                name: name.clone(),
                type_: inductive_type,
                span,
            },
        );

        self.register_in_namespace(&name.display().unwrap(), name.clone());
        let mut namespace = Namespace::new();
        self.elaborate_inductive_constructors(&mut namespace, &name, &binder_fvars, constructors);
        if let Some(existing) = self
            .env
            .root_namespace
            .children
            .get_mut(&name.display().unwrap().to_string())
        {
            existing.decls.extend(namespace.decls);
            existing.children.extend(namespace.children);
        } else {
            self.env
                .root_namespace
                .children
                .insert(name.display().unwrap().to_string(), namespace);
        }

        self.lctx = saved_lctx;
    }

    /// Elaborates each constructor of an inductive type.
    ///
    /// Each constructor gets its own binders, an optional explicit return type (defaulting
    /// to the inductive type itself), and has both the inductive's binders and its own
    /// binders abstracted into the final Pi type.
    fn elaborate_inductive_constructors(
        &mut self,
        inductive_namespace: &mut Namespace,
        inductive_name: &QualifiedName,
        binders: &[(Unique, BinderInfo, Term)],
        constructors: &[InductiveConstructor],
    ) {
        for constructor in constructors {
            let ctor_name = QualifiedName::User(self.gen_.fresh(constructor.name.to_string()));
            let saved_lctx = self.lctx.clone();

            let ctor_binder_fvars = self.elaborate_binders(&constructor.binders);

            let base_type = if let Some(type_ann) = &constructor.type_ann {
                self.elaborate_term(type_ann, None)
            } else {
                Term::Const(inductive_name.clone())
            };

            let constructor_type = Self::abstract_binders(
                binders,
                Self::abstract_binders(&ctor_binder_fvars, base_type),
            );

            self.env.decls.insert(
                ctor_name.clone(),
                Declaration::Constructor {
                    name: ctor_name.clone(),
                    type_: constructor_type,
                    span: constructor.span,
                },
            );

            inductive_namespace
                .decls
                .insert(constructor.name.clone(), ctor_name);
            self.lctx = saved_lctx;
        }
    }

    /// Elaborates a typeclass declaration.
    ///
    /// Creates the class type constant (typed as `Type`), then for each member field
    /// wraps its type in an instance-implicit parameter `[self : ClassName args] -> FieldType`,
    /// enabling typeclass-style dispatch. Members are placed in a child namespace
    /// `ClassName::memberName`.
    fn elaborate_class(
        &mut self,
        name_str: &str,
        binders: &[SyntaxBinder],
        members: &[RecordField],
        span: Span,
    ) {
        let name = QualifiedName::User(self.gen_.fresh(name_str.to_string()));
        let mut child_ns = Namespace::new();
        let saved_lctx = self.lctx.clone();

        let binder_fvars = self.elaborate_binders(binders);
        for member in members {
            let field_display_name = member.name.clone();
            let field_name = QualifiedName::User(self.gen_.fresh(member.name.clone()));
            let field_type = self.elaborate_term(&member.type_ann, None);
            let mut applied_class = Term::Const(name.clone());
            for (fvar, _, _) in &binder_fvars {
                applied_class =
                    Term::App(Box::new(applied_class), Box::new(Term::FVar(fvar.clone())));
            }
            let wrapped_type = Term::Pi(
                BinderInfo::InstanceImplicit,
                Box::new(applied_class),
                Box::new(field_type.clone()),
            );
            let wrapped_type = Self::abstract_binders(&binder_fvars, wrapped_type);
            // todo: make this a def
            let field_def = Declaration::Constructor {
                name: field_name.clone(),
                type_: wrapped_type.clone(),
                span: member.span,
            };
            self.env.decls.insert(field_name.clone(), field_def);
            child_ns.decls.insert(field_display_name, field_name);
        }

        let class_type = Self::abstract_binders(&binder_fvars, Term::Sort(Level::type0()));
        self.register_in_namespace(&name_str, name.clone());

        self.env.decls.insert(
            name.clone(),
            Declaration::Constructor {
                name: name.clone(),
                type_: class_type,
                span,
            },
        );
        let parent_ns = &mut self.env.root_namespace.children;
        if let Some(existing) = parent_ns.get_mut(name_str) {
            existing.decls.extend(child_ns.decls);
            existing.children.extend(child_ns.children);
        } else {
            parent_ns.insert(name_str.to_string(), child_ns);
        }
        println!(
            "Namespace after class elaboration: {:#?}",
            self.env.root_namespace
        );

        self.lctx = saved_lctx;
    }

    /// Elaborates a pattern match expression.
    ///
    /// Placeholder
    fn elaborate_pattern_match(
        &mut self,
        scrutinees: Vec<Scrutinee>,
        arms: &[PatternMatchArm],
        expected_type: Option<Term>,
        span: Span,
    ) -> Term {
        let rows = arms
            .iter()
            .map(|arm| {
                let patterns = arm
                    .patterns
                    .iter()
                    .enumerate()
                    .map(|(i, p)| {
                        let scrutinee_type = scrutinees[i].type_.clone();
                        self.elaborate_pattern(p, &scrutinee_type)
                    })
                    .collect();
                let rhs = self.elaborate_term(&arm.rhs, expected_type.as_ref());
                PatternRow::new(patterns, rhs)
            })
            .collect::<Vec<_>>();
        let problem = MatchProblem::new(scrutinees, rows);

        patterns::compile(problem)
    }

    fn elaborate_pattern(&mut self, pattern: &SyntaxPattern, expected_type: &Term) -> Pattern {
        match pattern {
            SyntaxPattern::Var(name, _) => {
                let (fvar, _type) = self.fresh_fvar(name.clone(), expected_type.clone());
                Pattern::Var(Some(fvar))
            }
            SyntaxPattern::Constructor {
                namespace,
                name,
                args,
                span,
            } => {
                let resolved = self.resolve_name(namespace, name);
                let Some((ctor_qname, ctor_type)) = resolved else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::UndefinedConstructor(name.clone()),
                        *span,
                    ));
                    return Pattern::Var(None);
                };
                let ctor_qname = ctor_qname.clone();
                let ctor_type = ctor_type.clone();

                let (_ctor_term, ctor_type) =
                    self.insert_implicit_args(Term::Const(ctor_qname.clone()), ctor_type);

                let mut current_type = reduce::whnf(self, &ctor_type);
                let mut arg_types = Vec::new();
                for _ in args.iter() {
                    match current_type {
                        Term::Pi(_, param_ty, body_ty) => {
                            arg_types.push(*param_ty);
                            current_type = reduce::whnf(self, &body_ty);
                        }
                        _ => {
                            self.errors.push(ElabError::new(
                                ElabErrorKind::NotAConstructorType(current_type.clone()),
                                *span,
                            ));
                            break;
                        }
                    }
                }
                if !self.unify(&current_type, expected_type) {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::TypeMismatch {
                            expected: expected_type.clone(),
                            found: current_type,
                        },
                        *span,
                    ));
                }

                let elaborated_args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        if i < arg_types.len() {
                            self.elaborate_pattern(arg, &arg_types[i])
                        } else {
                            Pattern::Var(None)
                        }
                    })
                    .collect::<Vec<_>>();
                Pattern::Constructor {
                    ctor: ctor_qname,
                    fields: elaborated_args,
                    type_: ctor_type,
                }
            }
            SyntaxPattern::Wildcard(_) => Pattern::Var(None),
            u => todo!("unsupported pattern: {:?}", u),
        }
    }
}

/// Entry point for elaboration: type-checks an entire source file.
///
/// Takes a module identifier and the parsed [`SyntaxTree`] and produces either
/// a fully elaborated [`Environment`] or a list of accumulated [`ElabError`]s.
pub fn elaborate_file(
    module_id: ModuleId,
    tree: &SyntaxTree,
) -> Result<Environment, Vec<ElabError>> {
    let mut state = ElabState::pre_loaded(module_id);

    for decl in &tree.declarations {
        state.elaborate_declaration(decl);
    }

    if state.errors.is_empty() {
        Ok(state.env)
    } else {
        Err(state.errors)
    }
}
