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
pub mod metadata;
pub mod patterns;
pub mod reduce;
pub mod subst;
pub mod unify;

use core::slice;

use alloc::{
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
        metadata::InductiveMetadata,
        patterns::{MatchProblem, Pattern, PatternRow, Scrutinee},
        reduce::{head_const, is_recursive_field},
    },
    module::{ModuleId, name::Name, unique::UniqueGen},
    spine::{BinderInfo, Level, Literal, Term, uncurry},
    syntax::{
        Span,
        ast::{
            self, AliasDecl, Attribute, Binder, ClassDecl, Decl, DefBody, DefDecl, Expr,
            ExternDecl, InductiveCtor, InductiveDecl, InfixOp, PatternMatchArm, RecordDecl,
            SourceFile, SyntaxNodeR,
        },
    },
};

/// A hierarchical namespace for name resolution.
///
/// Each namespace maps short display names to their [`Name`],
/// and may contain child namespaces. This forms a tree
/// that mirrors the module/record/class/inductive structure of the source program.
#[derive(Debug, Clone)]
pub struct Namespace {
    /// Top-level declarations visible in this namespace, keyed by display name.
    pub decls: BTreeMap<String, Name>,
    /// Child namespaces (e.g. record fields, class methods, inductive constructors).
    pub children: BTreeMap<String, Namespace>,
}

impl Namespace {
    #[must_use]
    pub fn new() -> Self {
        Self {
            decls: BTreeMap::new(),
            children: BTreeMap::new(),
        }
    }

    /// Looks up a declaration in this namespace by its display name.
    #[must_use]
    pub fn lookup_decl(&self, name: &str) -> Option<&Name> {
        self.decls.get(name)
    }

    /// Returns a direct child namespace by name.
    #[must_use]
    pub fn child(&self, name: &str) -> Option<&Namespace> {
        self.children.get(name)
    }

    /// Traverses a path of namespace segments, returning the namespace at the end.
    /// Returns `None` if any segment along the path does not exist.
    #[must_use]
    pub fn walk(&self, path: &[String]) -> Option<&Namespace> {
        let mut current = self;
        for segment in path {
            current = current.children.get(segment)?;
        }
        Some(current)
    }

    /// Resolves a qualified reference by walking the namespace `path` and then looking up `member`.
    #[must_use]
    pub fn resolve(&self, path: &[String], member: &str) -> Option<&Name> {
        self.walk(path)?.lookup_decl(member)
    }
}

impl Default for Namespace {
    fn default() -> Self {
        Self::new()
    }
}

/// The registry of built-in primitive types, operations, and type class instances.
pub struct LanguageItems(BTreeMap<String, Name>);

impl Default for LanguageItems {
    fn default() -> Self {
        Self::new()
    }
}

impl LanguageItems {
    #[must_use]
    pub fn new() -> Self {
        Self(BTreeMap::new())
    }

    pub fn insert(&mut self, name: &str, qname: Name) {
        self.0.insert(name.to_string(), qname);
    }

    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Name> {
        self.0.get(name)
    }

    #[must_use]
    pub fn get_string(&self) -> Option<&Name> {
        self.get("string")
    }

    #[must_use]
    pub fn get_nat(&self) -> Option<&Name> {
        self.get("nat")
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
    pub externals: BTreeMap<Name, Term>,
    /// All declarations elaborated in this module (definitions, constructors, etc.).
    pub decls: BTreeMap<Name, Declaration>,
    /// All aliases, maps them to their elaborated values and types
    pub aliases: BTreeMap<Name, (Term, Term)>,
    /// The root of the namespace tree for name resolution.
    pub root_namespace: Namespace,
    /// Metadata for inductive types.
    pub inductives: BTreeMap<Name, InductiveMetadata>,
    /// Reverse lookup of match functions to inductive name
    pub match_fns: BTreeMap<Name, Name>,
}

impl Environment {
    /// Looks up a declaration by its [`Name`]. Only searches module-local declarations,
    /// not externals.
    #[must_use]
    pub fn lookup(&self, name: &Name) -> Option<&Declaration> {
        self.decls.get(name)
    }

    /// Looks up the type of a name, searching both module-local declarations and externals.
    /// Returns the canonical [`Name`] and its type.
    #[must_use]
    pub fn lookup_type(&self, qname: &Name) -> Option<(&Name, &Term)> {
        self.decls
            .get(qname)
            .map(|decl| (decl.name(), decl.type_()))
            .or_else(|| self.externals.get_key_value(qname))
    }

    /// Looks up an alias by its [`Name`].
    /// Returns the elaborated value and its type.
    #[must_use]
    pub fn lookup_alias(&self, qname: &Name) -> Option<(&Term, &Term)> {
        self.aliases.get(qname).map(|(value, type_)| (value, type_))
    }

    /// Looks up an inductive type's metadata by its qualified name.
    #[must_use]
    pub fn lookup_inductive(&self, qname: &Name) -> Option<&InductiveMetadata> {
        self.inductives.get(qname)
    }
}

/// A top-level declaration in the elaborated environment.
#[derive(Debug, Clone)]
pub enum Declaration {
    /// A function or value definition with a known body.
    Definition {
        name: Name,
        type_: Term,
        value: Term,
        span: Span,
    },
    /// A declaration that has a type but no reducible body, they are opaque constants.
    Constructor { name: Name, type_: Term, span: Span },
    /// A forward-declared definition whose body we don't want to unfold for some reason.
    Opaque { name: Name, type_: Term, span: Span },
}

impl Declaration {
    /// Returns the declaration's [`Name`].
    #[must_use]
    pub fn name(&self) -> &Name {
        match self {
            Declaration::Definition { name, .. }
            | Declaration::Constructor { name, .. }
            | Declaration::Opaque { name, .. } => name,
        }
    }

    /// Returns the declaration's type.
    #[must_use]
    pub fn type_(&self) -> &Term {
        match self {
            Declaration::Definition { type_, .. }
            | Declaration::Constructor { type_, .. }
            | Declaration::Opaque { type_, .. } => type_,
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
    /// Mapping of built-in primitive names to their qualified names in the environment.
    pub lang_items: LanguageItems,
    /// Source file ID for span computation from CST nodes.
    pub file: usize,
}

impl ElabState {
    /// Creates a blank elaboration state with no pre-loaded primitives.
    #[must_use]
    pub fn new(module: ModuleId, file: usize) -> Self {
        Self {
            env: Environment {
                module_id: module.clone(),
                externals: BTreeMap::new(),
                decls: BTreeMap::new(),
                aliases: BTreeMap::new(),
                root_namespace: Namespace::new(),
                inductives: BTreeMap::new(),
                match_fns: BTreeMap::new(),
            },
            gen_: UniqueGen::new(module),
            mctx: MetavarContext::new(),
            lctx: LocalContext { decls: Vec::new() },
            current_namespace: Vec::new(),
            open_namespaces: Vec::new(),
            errors: Vec::new(),
            lang_items: LanguageItems::new(),
            file,
        }
    }

    /// Creates a fresh metavariable (unification hole) with the given type, using
    /// the current local context. Returns it wrapped as `Term::MVar`.
    pub fn fresh_mvar(&mut self, type_: Term) -> Term {
        let u = self.mctx.fresh_mvar(type_, &self.lctx, &mut self.gen_);
        Term::MVar(u)
    }

    /// Creates a fresh free variable with the given display name and type, pushes it
    /// onto the local context, and returns both the [`Unique`] and `Term::FVar`.
    pub fn fresh_fvar(&mut self, name: String, type_: Term) -> (Name, Term) {
        let name = self.lctx.push_binder(name, type_, &mut self.gen_);
        (name.clone(), Term::FVar(name))
    }

    /// Produces a throwaway metavariable term used as a placeholder after an error.
    fn erroneous_term(&mut self) -> Term {
        Term::MVar(self.gen_.fresh_unnamed())
    }

    /// Resolves a name to its [`Name`] and type using multi-level lookup:
    /// 1. If an explicit namespace path is given, look it up directly.
    /// 2. Try the current namespace (e.g. inside a record or class body).
    /// 3. Try each opened namespace in order.
    /// 4. Fall back to the root namespace.
    fn resolve_name(&self, namespace: &[String], member: &str) -> Option<(&Name, &Term)> {
        let ns = &self.env.root_namespace;

        if !namespace.is_empty() {
            return ns
                .resolve(namespace, member)
                .and_then(|qn| self.env.lookup_type(qn));
        }

        if !self.current_namespace.is_empty()
            && let Some(qn) = ns.resolve(&self.current_namespace, member)
            && let Some(result) = self.env.lookup_type(qn)
        {
            return Some(result);
        }

        for opened in &self.open_namespaces {
            if let Some(qn) = ns.resolve(opened, member)
                && let Some(result) = self.env.lookup_type(qn)
            {
                return Some(result);
            }
        }

        ns.lookup_decl(member)
            .and_then(|qn| self.env.lookup_type(qn))
    }

    fn resolve_alias(&self, namespace: &[String], member: &str) -> Option<(&Name, &Term, &Term)> {
        let ns = &self.env.root_namespace;

        if !namespace.is_empty() {
            return ns
                .resolve(namespace, member)
                .and_then(|qn| self.env.lookup_alias(qn).map(|(val, ty)| (qn, val, ty)));
        }

        if !self.current_namespace.is_empty()
            && let Some(qn) = ns.resolve(&self.current_namespace, member)
            && let Some((val, ty)) = self.env.lookup_alias(qn)
        {
            return Some((qn, val, ty));
        }

        for opened in &self.open_namespaces {
            if let Some(qn) = ns.resolve(opened, member)
                && let Some((val, ty)) = self.env.lookup_alias(qn)
            {
                return Some((qn, val, ty));
            }
        }

        ns.lookup_decl(member)
            .and_then(|qn| self.env.lookup_alias(qn).map(|(val, ty)| (qn, val, ty)))
    }

    /// Dispatches a top-level declaration to the appropriate elaboration handler.
    pub fn elaborate_declaration(&mut self, decl: &Decl) {
        match decl {
            Decl::Def(d) => self.elaborate_def(d),
            Decl::Record(d) => self.elaborate_record(d),
            Decl::Extern(d) => self.elaborate_extern(d),
            Decl::Inductive(d) => self.elaborate_inductive(d),
            Decl::Class(d) => self.elaborate_class(d),
            Decl::Instance(_) => {
                // todo: implement instance elaboration
            }
            Decl::Alias(d) => self.elaborate_alias(d),
            Decl::Eval(d) => {
                if let Some(expr) = d.expr() {
                    let term = self.elaborate_term(&expr, None);
                    println!("Evaluated term: {:#?}", &term);
                }
            }
        }
    }

    /// Elaborates a sequence of binders (explicit, implicit, or instance-implicit),
    /// pushing each into the local context as a free variable.
    ///
    /// Returns a list of `(fvar, binder_info, elaborated_type)` triples, which can later
    /// be used by [`Self::abstract_binders`] to build Pi types.
    fn elaborate_binders_iter<'a, I>(&mut self, binders: I) -> Vec<(Name, BinderInfo, Term)>
    where
        I: Iterator<Item = Binder<'a>>,
    {
        binders.map(|b| self.elaborate_binder(&b)).collect()
    }

    fn elaborate_binder(&mut self, binder: &Binder) -> (Name, BinderInfo, Term) {
        let info = match binder {
            Binder::Explicit(_) => BinderInfo::Explicit,
            Binder::Implicit(_) => BinderInfo::Implicit,
            Binder::Instance(_) => BinderInfo::InstanceImplicit,
        };
        let binder_name = binder.name().unwrap_or("_").to_string();
        let binder_type_expr = binder.type_ann();
        let (elaborated_type, type_of_type) = if let Some(ty) = binder_type_expr {
            self.elaborate_term_inner(&ty)
        } else {
            let m = self.fresh_mvar(Term::type0());
            (m.clone(), Term::type0())
        };
        let normalized_type_of_type = reduce::whnf(self, &type_of_type);
        if !matches!(normalized_type_of_type, Term::Sort(_)) {
            self.errors.push(ElabError::new(
                ElabErrorKind::TypeExpected(elaborated_type.clone()),
                binder.span(self.file),
            ));
        }
        let (fvar, _) = self.fresh_fvar(binder_name, elaborated_type.clone());
        (fvar, info, elaborated_type)
    }

    /// Converts free variables introduced by [`Self::elaborate_binders`] back into bound
    /// variables by wrapping `term` in nested Pi types (right to left).
    ///
    /// For binders `(a, b, c)` and a term `T`, produces `Pi a. Pi b. Pi c. T`
    /// where each free variable is abstracted into the corresponding De Bruijn index.
    fn abstract_binders(binder_fvars: &[(Name, BinderInfo, Term)], mut term: Term) -> Term {
        for (fvar, info, ty) in binder_fvars.iter().rev() {
            term = subst::abstract_fvar(&term, fvar.clone());
            term = Term::mk_pi(*info, ty.clone(), term);
        }
        term
    }

    fn abstract_binders_lam(binder_fvars: &[(Name, BinderInfo, Term)], mut term: Term) -> Term {
        for (fvar, info, ty) in binder_fvars.iter().rev() {
            term = subst::abstract_fvar(&term, fvar.clone());
            term = Term::mk_lam(*info, ty.clone(), term);
        }
        term
    }

    /// Elaborates a `def` declaration.
    ///
    /// 1. Generates a fresh [`Name`] for the definition.
    /// 2. Saves the local context, elaborates binders, return type, and body.
    /// 3. Abstracts the binders into a Pi type and lambda body.
    /// 4. Registers the definition in the environment and namespace.
    /// 5. Restores the local context.
    fn elaborate_def(&mut self, d: &DefDecl) {
        let name = d.name().unwrap_or("_");
        let span = d.span(self.file);
        let def_name = self.gen_.fresh_name(name.to_string());

        let saved_lctx = self.lctx.clone();
        let binder_fvars = self.elaborate_binders_iter(d.binders());
        let return_type_expr = d.return_type();
        let elaborated_return_type = if let Some(rt) = &return_type_expr {
            self.elaborate_term(rt, None)
        } else {
            self.fresh_mvar(Term::type0())
        };
        let pi_type = Self::abstract_binders(&binder_fvars, elaborated_return_type.clone());

        let body = d.body();
        let is_pattern_match = matches!(&body, Some(DefBody::PatternMatch(_)));

        let elaborated_body = match &body {
            Some(DefBody::Expr(body_expr)) => {
                self.elaborate_term(body_expr, Some(&elaborated_return_type))
            }
            Some(DefBody::PatternMatch(arms_node)) => {
                let arms_span = arms_node.span(self.file);
                // Pre-register as Opaque so recursive calls resolve during body elaboration
                self.env.decls.insert(
                    def_name.clone(),
                    Declaration::Opaque {
                        name: def_name.clone(),
                        type_: pi_type.clone(),
                        span: arms_span,
                    },
                );
                self.register_in_namespace(name, def_name.clone());

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

                let arms: Vec<_> = arms_node.arms().collect();
                let body = self.elaborate_pattern_match(
                    scrutinees,
                    &arms,
                    pattern_return_type,
                    Some(def_name.clone()),
                    arms_span,
                );

                let mut lambda = body;
                for (_, scrutinee_type) in scrutinee_types.iter().rev() {
                    lambda = Term::mk_lam(BinderInfo::Explicit, scrutinee_type.clone(), lambda);
                }
                lambda
            }
            None => self.erroneous_term(),
        };

        let elaborated_return_type = unify::instantiate_mvars(self, &elaborated_return_type);
        let pi_type = Self::abstract_binders(&binder_fvars, elaborated_return_type);

        let mut value = unify::instantiate_mvars(self, &elaborated_body);
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
        if !is_pattern_match {
            self.register_in_namespace(name, def_name);
        }

        self.lctx = saved_lctx;
    }

    /// Elaborates a syntax expression into a core [`Term`], optionally checking it against
    /// an expected type. If the inferred type does not unify with the expected type,
    /// a [`ElabErrorKind::TypeMismatch`] is recorded.
    fn elaborate_term(&mut self, syntax: &Expr, expected_type: Option<&Term>) -> Term {
        let (term, inferred_type) = self.elaborate_term_inner(syntax);

        let (term, inferred_type) = if expected_type.is_some() {
            self.insert_implicit_args(term, inferred_type)
        } else {
            (term, inferred_type)
        };

        if let Some(expected) = expected_type
            && !self.unify(&inferred_type, expected)
        {
            let reduced_to = {
                let reduced = reduce::whnf(self, expected);
                if &reduced != expected {
                    Some(reduced)
                } else {
                    None
                }
            };
            self.errors.push(ElabError::new(
                err::ElabErrorKind::TypeMismatch {
                    expected: expected.clone(),
                    reduced_to,
                    found: inferred_type,
                },
                syntax.span(self.file),
            ));
        }

        term
    }

    /// Core term elaboration. Returns `(elaborated_term, inferred_type)`.
    ///
    /// Handles all expression forms and reports errors for unsupported syntax.
    fn elaborate_term_inner(&mut self, syntax: &Expr) -> (Term, Term) {
        let span = syntax.span(self.file);
        match syntax {
            Expr::Var(v) => {
                let (namespace, member) = v.qualified_parts();
                if namespace.is_empty()
                    && let Some(decl) = self.lctx.lookup_name(member)
                {
                    return (Term::FVar(decl.fvar.clone()), decl.type_.clone());
                }

                if let Some((name, type_)) = self.resolve_name(&namespace, member) {
                    return (Term::Const(name.clone()), type_.clone());
                }

                self.errors.push(ElabError::new(
                    ElabErrorKind::UndefinedVariable(member.to_string()),
                    span,
                ));
                (self.erroneous_term(), self.erroneous_term())
            }
            Expr::Ctor(c) => {
                let (namespace, name) = c.qualified_parts();
                if name == "Type" {
                    let u = self.gen_.fresh_unnamed();
                    let level = Level::MVar(u);
                    return (Term::Sort(level.clone()), Term::Sort(level.succ()));
                }
                if name == "Prop" {
                    return (Term::Sort(Level::Zero), Term::type0());
                }

                if let Some((qn, type_)) = self.resolve_name(&namespace, name) {
                    return (Term::Const(qn.clone()), type_.clone());
                }

                if let Some((_, val, type_)) = self.resolve_alias(&namespace, name) {
                    return (val.clone(), type_.clone());
                }

                self.errors.push(ElabError::new(
                    ElabErrorKind::UndefinedConstructor(name.to_string()),
                    span,
                ));
                (self.erroneous_term(), self.erroneous_term())
            }
            Expr::Lit(lit) => {
                let value = lit.literal().unwrap_or(Literal::Nat(0));
                let ty = match &value {
                    Literal::Nat(_) => self.get_lang_item_or_error("nat", span),
                    Literal::Str(_) => self.get_lang_item_or_error("string", span),
                };
                (Term::Lit(value), ty)
            }
            Expr::Array(arr) => {
                let elems: Vec<_> = arr.elements().collect();
                let elem_type = if let Some(head) = elems.first() {
                    let (_term, head_ty) = self.elaborate_term_inner(head);
                    head_ty
                } else {
                    self.fresh_mvar(Term::type0())
                };
                let elems_len = elems.len() as u64;
                let array_lang_item = self.get_lang_item_or_error("array", span);
                let array_nil_lang_item = self.get_lang_item_or_error("array_nil", span);
                let array_cons_lang_item = self.get_lang_item_or_error("array_cons", span);

                let array_type = Term::mk_app(
                    Term::mk_app(array_lang_item, elem_type.clone()),
                    Term::Lit(Literal::Nat(elems_len)),
                );
                let mut result = array_nil_lang_item.clone();
                for (current_length, elem) in elems.into_iter().rev().enumerate() {
                    let elaborated_elem = self.elaborate_term(&elem, Some(&elem_type));
                    result = Term::mk_app(
                        Term::mk_app(
                            Term::mk_app(
                                Term::mk_app(array_cons_lang_item.clone(), elem_type.clone()),
                                Term::Lit(Literal::Nat(current_length as u64)),
                            ),
                            elaborated_elem,
                        ),
                        result,
                    );
                }
                (result, array_type)
            }
            Expr::Infix(infix) => {
                let op = infix.op().unwrap_or(InfixOp::Add);
                let op_fn_li = match op {
                    InfixOp::Add => "add",
                    InfixOp::Sub => "sub",
                    InfixOp::Mul => "mul",
                    InfixOp::Div => "div",
                    InfixOp::Eq => "types.eq",
                    InfixOp::Neq => "neq",
                    InfixOp::Lt => "lt",
                    InfixOp::Leq => "leq",
                    InfixOp::Gt => "gt",
                    InfixOp::Geq => "geq",
                };
                let Some(op_fn_name) = self.lang_items.get(op_fn_li).cloned() else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::MissingLangItem(op_fn_li.to_string()),
                        span,
                    ));
                    return (self.erroneous_term(), self.erroneous_term());
                };
                let op_fn = Term::Const(op_fn_name.clone());

                let lhs = infix.lhs();
                let rhs = infix.rhs();
                let (arg1, arg1_ty) = if let Some(l) = &lhs {
                    self.elaborate_term_inner(l)
                } else {
                    (self.erroneous_term(), self.erroneous_term())
                };
                let (arg2, arg2_ty) = if let Some(r) = &rhs {
                    self.elaborate_term_inner(r)
                } else {
                    (self.erroneous_term(), self.erroneous_term())
                };

                if let Some((_, expected_fn_type)) = self.env.lookup_type(&op_fn_name) {
                    self.make_app(
                        op_fn,
                        expected_fn_type.clone(),
                        alloc::vec![(arg1, arg1_ty), (arg2, arg2_ty)],
                        span,
                    )
                } else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::UndefinedVariable(op_fn_li.to_string()),
                        span,
                    ));
                    (self.erroneous_term(), self.erroneous_term())
                }
            }
            Expr::App(app) => {
                let fun = app.fun();
                let arg = app.arg();
                if let (Some(f), Some(a)) = (&fun, &arg) {
                    self.elaborate_app(syntax, f, a)
                } else {
                    (self.erroneous_term(), self.erroneous_term())
                }
            }
            Expr::Proj(proj) => {
                let value_expr = proj.value();
                let field = proj.field().unwrap_or("");
                let (elaborated_value, value_type) = if let Some(v) = &value_expr {
                    self.elaborate_term_inner(v)
                } else {
                    (self.erroneous_term(), self.erroneous_term())
                };
                let normalized_value_type = reduce::whnf(self, &value_type);
                if let Some(record_name) = head_const(&normalized_value_type) {
                    let namespace = record_name.to_string();
                    if let Some((proj_fn_name, proj_fn_type)) =
                        self.resolve_name(slice::from_ref(&namespace), field)
                    {
                        let proj_fn_term = Term::Const(proj_fn_name.clone());
                        let (mut term, fn_type) = self.insert_implicit_args_until(
                            proj_fn_term,
                            proj_fn_type.clone(),
                            BinderInfo::InstanceImplicit,
                        );
                        if let Term::Pi(_, _, body_ty) = fn_type {
                            let return_type = subst::instantiate(&body_ty, &elaborated_value);
                            term = Term::mk_app(term, elaborated_value);
                            (term, return_type)
                        } else {
                            self.errors
                                .push(ElabError::new(ElabErrorKind::NotAFunction(fn_type), span));
                            (self.erroneous_term(), self.erroneous_term())
                        }
                    } else {
                        self.errors.push(ElabError::new(
                            ElabErrorKind::UndefinedVariable(format!("{namespace}::{field}")),
                            span,
                        ));
                        (self.erroneous_term(), self.erroneous_term())
                    }
                } else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::CannotProject(elaborated_value, field.to_string()),
                        span,
                    ));
                    (self.erroneous_term(), self.erroneous_term())
                }
            }
            Expr::Arrow(arrow) => {
                let param = arrow.param_type();
                let ret = arrow.return_type();
                let elaborated_param_type = if let Some(p) = &param {
                    self.elaborate_term(p, None)
                } else {
                    self.erroneous_term()
                };
                let elaborated_return_type = if let Some(r) = &ret {
                    self.elaborate_term(r, None)
                } else {
                    self.erroneous_term()
                };
                (
                    Term::mk_pi(
                        BinderInfo::Explicit,
                        elaborated_param_type,
                        elaborated_return_type,
                    ),
                    Term::type0(),
                )
            }
            Expr::Lambda(lam) => {
                let saved_lctx = self.lctx.clone();
                let binder_fvars = self.elaborate_binders_iter(lam.binders());
                let body_expr = lam.body();
                let (elaborated_body, body_type) = if let Some(b) = &body_expr {
                    self.elaborate_term_inner(b)
                } else {
                    (self.erroneous_term(), self.erroneous_term())
                };
                let mut term = elaborated_body;
                let mut result_type = body_type;
                for (fvar, info, ty) in binder_fvars.iter().rev() {
                    term = subst::abstract_fvar(&term, fvar.clone());
                    term = Term::mk_lam(*info, ty.clone(), term);
                    result_type = subst::abstract_fvar(&result_type, fvar.clone());
                    result_type = Term::mk_pi(*info, ty.clone(), result_type);
                }
                self.lctx = saved_lctx;
                (term, result_type)
            }
            Expr::Unit(_) => (Term::Unit, Term::type0()),
            Expr::Pi(pi) => {
                let binder = pi.binder();
                let codomain_expr = pi.codomain();
                let (fvar, info, elaborated_binder_type) = if let Some(b) = &binder {
                    self.elaborate_binder(b)
                } else {
                    let mvar = self.fresh_mvar(Term::type0());
                    let (fvar, _) = self.fresh_fvar("_".to_string(), mvar);
                    (fvar, BinderInfo::Explicit, self.erroneous_term())
                };
                let (elaborated_codomain, codomain_type) = if let Some(c) = &codomain_expr {
                    self.elaborate_term_inner(c)
                } else {
                    (self.erroneous_term(), self.erroneous_term())
                };
                let normalized_codomain_type = reduce::whnf(self, &codomain_type);
                if !matches!(normalized_codomain_type, Term::Sort(_)) {
                    if let Some(c) = &codomain_expr {
                        self.errors.push(ElabError::new(
                            ElabErrorKind::TypeExpected(elaborated_codomain.clone()),
                            c.span(self.file),
                        ));
                    }
                }
                let abstracted_body = subst::abstract_fvar(&elaborated_codomain, fvar.clone());
                let pi_type = Term::mk_pi(info, elaborated_binder_type.clone(), abstracted_body);
                (pi_type, Term::type0())
            }
            _ => {
                self.errors
                    .push(ElabError::new(err::ElabErrorKind::UnsupportedSyntax, span));
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
                    term = Term::mk_app(term, mvar);
                }
                _ => break,
            }
        }
        (term, fn_type)
    }

    /// Elaborates a function application `fun arg`.
    ///
    /// First elaborates `fun`, inserts any implicit arguments, then elaborates
    /// `arg` against the expected parameter type and instantiates the return type.
    fn elaborate_app(&mut self, syntax: &Expr, fun: &Expr, arg: &Expr) -> (Term, Term) {
        let (term, fn_type) = self.elaborate_term_inner(fun);
        let (term, fn_type) = self.insert_implicit_args(term, fn_type);

        match fn_type {
            Term::Pi(_info, param_ty, body_ty) => {
                let elaborated_arg = self.elaborate_term(arg, Some(&param_ty));
                let return_type = subst::instantiate(&body_ty, &elaborated_arg);
                (Term::mk_app(term, elaborated_arg), return_type)
            }
            u => {
                self.errors.push(ElabError::new(
                    ElabErrorKind::NotAFunction(u),
                    syntax.span(self.file),
                ));
                (self.erroneous_term(), self.erroneous_term())
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
    fn elaborate_record(&mut self, d: &RecordDecl) {
        let name = d.name().unwrap_or("_");
        let span = d.span(self.file);
        let record_name = self.gen_.fresh_name(name.to_string());
        let mut child_ns = Namespace::new();

        let saved_lctx = self.lctx.clone();
        let attributes: Vec<_> = d.attributes().collect();
        let binder_fvars = self.elaborate_binders_iter(d.binders());
        self.register_inductive_type(
            &attributes,
            name,
            &record_name,
            &binder_fvars,
            Term::type0(),
            span,
        );

        let fields: Vec<_> = d.fields().collect();
        let mut field_data: Vec<(String, Name, Term)> = Vec::new();
        for field in &fields {
            let field_name = field.name().unwrap_or("_").to_string();
            let field_qname = self.gen_.fresh_name(field_name.clone());
            let field_type = if let Some(ty) = field.type_ann() {
                self.elaborate_term(&ty, None)
            } else {
                self.erroneous_term()
            };
            field_data.push((field_name, field_qname, field_type));
        }

        let mut constructor_type = Term::Const(record_name.clone());
        for (fvar, _, _) in &binder_fvars {
            constructor_type = Term::mk_app(constructor_type, Term::FVar(fvar.clone()));
        }
        for (_, _, field_type) in field_data.iter().rev() {
            constructor_type =
                Term::mk_pi(BinderInfo::Explicit, field_type.clone(), constructor_type);
        }
        let constructor_type = Self::abstract_binders(&binder_fvars, constructor_type);
        let constructor = self.register_constructor("new", constructor_type, &mut child_ns, span);

        self.register_inductive(
            name,
            record_name.clone(),
            &binder_fvars,
            alloc::vec![constructor],
            child_ns,
            span,
        );

        let all_field_types: Vec<Term> = field_data.iter().map(|(_, _, ty)| ty.clone()).collect();
        let match_fn = self
            .env
            .lookup_inductive(&record_name)
            .unwrap()
            .match_fn
            .clone();
        for (field_index, (field_display_name, field_qname, field_type)) in
            field_data.into_iter().enumerate()
        {
            let field_def = self.elaborate_field_definition(
                &field_qname,
                &record_name,
                &match_fn,
                &all_field_types,
                field_index,
                &field_type,
                &binder_fvars,
                span,
            );
            self.env.decls.insert(field_qname.clone(), field_def);
            let record_ns = self.env.root_namespace.children.get_mut(name).unwrap();
            record_ns.decls.insert(field_display_name, field_qname);
        }

        self.lctx = saved_lctx;
    }

    /// Registers a declaration in the appropriate namespace (root or current).
    fn register_in_namespace(&mut self, display_name: &str, qname: Name) {
        let ns = if self.current_namespace.is_empty() {
            &mut self.env.root_namespace
        } else {
            let mut current = &mut self.env.root_namespace;
            for segment in &self.current_namespace {
                current = current.children.entry(segment.clone()).or_default();
            }
            current
        };
        ns.decls.insert(display_name.into(), qname);
    }

    /// Elaborates an `extern` declaration: type-checks the annotation and registers
    /// it as an external (opaque) binding in the environment.
    fn elaborate_extern(&mut self, d: &ExternDecl) {
        let name = d.name().unwrap_or("_");
        let elaborated_type = if let Some(ty) = d.type_ann() {
            self.elaborate_term(&ty, None)
        } else {
            self.erroneous_term()
        };
        let qname = self.gen_.fresh_name(name.to_string());
        self.env.externals.insert(qname.clone(), elaborated_type);
        self.register_in_namespace(name, qname);
    }

    /// Elaborates an `inductive` type declaration.
    ///
    /// Creates the inductive type constant (typed as `Type` after abstracting binders),
    /// then elaborates each constructor via [`Self::elaborate_inductive_constructors`],
    /// placing them in a child namespace `InductiveName::CtorName`.
    /// Registers the type declaration for an inductive and adds it to the namespace
    fn register_inductive_type(
        &mut self,
        attributes: &[Attribute],
        name: &str,
        ind_name: &Name,
        binder_fvars: &[(Name, BinderInfo, Term)],
        index_type: Term,
        span: Span,
    ) {
        let inductive_type = Self::abstract_binders(binder_fvars, index_type);
        self.env.decls.insert(
            ind_name.clone(),
            Declaration::Constructor {
                name: ind_name.clone(),
                type_: inductive_type,
                span,
            },
        );
        self.optionally_register_lang_item(ind_name, attributes);
        self.register_in_namespace(name, ind_name.clone());
    }

    /// Creates a constructor, registers it, and inserts it into the given namespace
    fn register_constructor(
        &mut self,
        display_name: &str,
        type_: Term,
        namespace: &mut Namespace,
        span: Span,
    ) -> (Name, Term) {
        let ctor_name = self.gen_.fresh_name(display_name.to_string());
        self.env.decls.insert(
            ctor_name.clone(),
            Declaration::Constructor {
                name: ctor_name.clone(),
                type_: type_.clone(),
                span,
            },
        );
        namespace
            .decls
            .insert(display_name.into(), ctor_name.clone());
        (ctor_name, type_)
    }

    /// Registers the match function, merges the child namespace, and creates inductive metadata
    fn register_inductive(
        &mut self,
        name: &str,
        ind_name: Name,
        binder_fvars: &[(Name, BinderInfo, Term)],
        constructors: Vec<(Name, Term)>,
        mut namespace: Namespace,
        span: Span,
    ) {
        let (constructor_names, constructor_types): (Vec<_>, Vec<_>) =
            constructors.into_iter().unzip();

        let match_fn_name = self.gen_.fresh_name("match".into());
        let match_fn_type = self.generate_match_fn_type(
            &ind_name,
            binder_fvars,
            &constructor_names,
            &constructor_types,
        );
        self.env.decls.insert(
            match_fn_name.clone(),
            Declaration::Constructor {
                name: match_fn_name.clone(),
                type_: match_fn_type,
                span,
            },
        );
        namespace
            .decls
            .insert("match".into(), match_fn_name.clone());

        let display_name = name.to_string();
        if let Some(existing) = self.env.root_namespace.children.get_mut(&display_name) {
            existing.decls.extend(namespace.decls);
            existing.children.extend(namespace.children);
        } else {
            self.env
                .root_namespace
                .children
                .insert(display_name, namespace);
        }

        let metadata = InductiveMetadata {
            name: ind_name.clone(),
            num_params: binder_fvars.len(),
            num_indices: 0, // todo
            constructors: constructor_names,
            match_fn: match_fn_name.clone(),
            is_recursive: false, // todo
        };
        self.env
            .match_fns
            .insert(match_fn_name.clone(), ind_name.clone());
        self.env.inductives.insert(match_fn_name, metadata.clone());
        self.env.inductives.insert(ind_name, metadata);
    }

    fn elaborate_inductive(&mut self, d: &InductiveDecl) {
        let name = d.name().unwrap_or("_");
        let span = d.span(self.file);
        let ind_name = self.gen_.fresh_name(name.to_string());
        let saved_lctx = self.lctx.clone();

        let attributes: Vec<_> = d.attributes().collect();
        let binder_fvars = self.elaborate_binders_iter(d.binders());
        let index_type = if let Some(index_ty) = d.index_type() {
            self.elaborate_term(&index_ty, None)
        } else {
            Term::type0()
        };
        self.register_inductive_type(
            &attributes,
            name,
            &ind_name,
            &binder_fvars,
            index_type,
            span,
        );

        let mut namespace = Namespace::new();
        let constructors: Vec<_> = d.constructors().collect();
        let constructor_data = self.elaborate_inductive_constructors(
            &mut namespace,
            &ind_name,
            &binder_fvars,
            &constructors,
        );

        self.register_inductive(
            name,
            ind_name,
            &binder_fvars,
            constructor_data,
            namespace,
            span,
        );
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
        inductive_name: &Name,
        binders: &[(Name, BinderInfo, Term)],
        constructors: &[InductiveCtor],
    ) -> Vec<(Name, Term)> {
        let mut constructor_data = Vec::new();
        for constructor in constructors {
            let ctor_display_name = constructor.name().unwrap_or("_").to_string();
            let ctor_name = self.gen_.fresh_name(ctor_display_name.clone());
            let saved_lctx = self.lctx.clone();
            let ctor_binder_fvars = self.elaborate_binders_iter(constructor.binders());

            let base_type = if let Some(type_ann) = constructor.type_ann() {
                self.elaborate_term(&type_ann, None)
            } else {
                Term::Const(inductive_name.clone())
            };

            let base_type = unify::instantiate_mvars(self, &base_type);

            // Inductive parameters are always implicit in constructor types
            let implicit_binders: Vec<_> = binders
                .iter()
                .map(|(u, _, ty)| (u.clone(), BinderInfo::Implicit, ty.clone()))
                .collect();
            let constructor_type = Self::abstract_binders(
                &implicit_binders,
                Self::abstract_binders(&ctor_binder_fvars, base_type),
            );

            let ctor_span = constructor.span(self.file);
            self.env.decls.insert(
                ctor_name.clone(),
                Declaration::Constructor {
                    name: ctor_name.clone(),
                    type_: constructor_type.clone(),
                    span: ctor_span,
                },
            );

            inductive_namespace
                .decls
                .insert(ctor_display_name, ctor_name.clone());
            self.lctx = saved_lctx;
            constructor_data.push((ctor_name, constructor_type));
        }
        constructor_data
    }

    /// Elaborates a typeclass declaration.
    ///
    /// Creates the class type constant (typed as `Type`), then for each member field
    /// wraps its type in an instance-implicit parameter `[self : ClassName args] -> FieldType`,
    /// enabling typeclass-style dispatch. Members are placed in a child namespace
    /// `ClassName::memberName`.
    fn elaborate_class(&mut self, d: &ClassDecl) {
        let name_str = d.name().unwrap_or("_");
        let span = d.span(self.file);
        let name = self.gen_.fresh_name(name_str.to_string());
        let mut child_ns = Namespace::new();
        let saved_lctx = self.lctx.clone();

        let attributes: Vec<_> = d.attributes().collect();
        let binder_fvars = self.elaborate_binders_iter(d.binders());
        self.register_inductive_type(
            &attributes,
            name_str,
            &name,
            &binder_fvars,
            Term::type0(),
            span,
        );
        let mut constructor_type = Term::Const(name.clone());
        for (fvar, _, _) in &binder_fvars {
            constructor_type = Term::mk_app(constructor_type, Term::FVar(fvar.clone()));
        }
        let members: Vec<_> = d.members().collect();
        for member in members.iter().rev() {
            let field_display_name = member.name().unwrap_or("_").to_string();
            let field_name = self.gen_.fresh_name(field_display_name.clone());
            let field_type = if let Some(ty) = member.type_ann() {
                self.elaborate_term(&ty, None)
            } else {
                self.erroneous_term()
            };

            let mut applied_class = Term::Const(name.clone());
            for (fvar, _, _) in &binder_fvars {
                applied_class = Term::mk_app(applied_class, Term::FVar(fvar.clone()));
            }
            let wrapped_type = Term::mk_pi(
                BinderInfo::InstanceImplicit,
                applied_class,
                field_type.clone(),
            );
            let implicit_binders = binder_fvars
                .iter()
                .map(|(u, _, ty)| (u.clone(), BinderInfo::Implicit, ty.clone()))
                .collect::<Vec<_>>();
            let wrapped_type = Self::abstract_binders(&implicit_binders, wrapped_type);
            let member_span = member.span(self.file);
            let field_def = Declaration::Constructor {
                name: field_name.clone(),
                type_: wrapped_type.clone(),
                span: member_span,
            };
            self.env.decls.insert(field_name.clone(), field_def);
            let member_attrs: Vec<_> = member.attributes().collect();
            self.optionally_register_lang_item(&field_name, &member_attrs);
            child_ns.decls.insert(field_display_name, field_name);

            constructor_type = Term::mk_pi(BinderInfo::Explicit, field_type, constructor_type);
        }

        let constructor_type = Self::abstract_binders(&binder_fvars, constructor_type);

        let constructor = self.register_constructor("new", constructor_type, &mut child_ns, span);

        self.register_inductive(
            name_str,
            name,
            &binder_fvars,
            alloc::vec![constructor],
            child_ns,
            span,
        );

        self.lctx = saved_lctx;
    }

    /// Elaborates a pattern match expression to a core term.
    ///
    /// 1. Builds a motive from the scrutinee types
    /// 2. Elaborates each pattern in each arm against the corresponding scrutinee type
    /// 3. Specializes the expected return type for each arm by applying the motive
    /// 4. Elaborates the right-hand side of each arm against the specialized expected type.
    /// 5. Compiles the resulting pattern matrix into a core term via `patterns::compile`
    fn elaborate_pattern_match(
        &mut self,
        scrutinees: Vec<Scrutinee>,
        arms: &[PatternMatchArm],
        expected_type: Term,
        match_fn: Option<Name>,
        span: Span,
    ) -> Term {
        let mut motive = expected_type.clone();
        for s in scrutinees.iter().rev() {
            motive = Term::mk_lam(BinderInfo::Explicit, s.type_.clone(), motive);
        }

        let rows = arms
            .iter()
            .map(|arm| {
                let arm_patterns: Vec<_> = arm.patterns().collect();
                let patterns: Vec<Pattern> = arm_patterns
                    .iter()
                    .enumerate()
                    .filter_map(|(i, p)| {
                        scrutinees
                            .get(i)
                            .map(|scrutinee| self.elaborate_pattern(p, &scrutinee.type_))
                    })
                    .collect();

                let mut specialized = motive.clone();
                for pat in &patterns {
                    specialized = Term::mk_app(specialized, self.pattern_to_term(pat));
                }
                let specialized = reduce::whnf(self, &specialized);
                let rhs_expr = arm.rhs();
                let rhs = if let Some(r) = &rhs_expr {
                    self.elaborate_term(r, Some(&specialized))
                } else {
                    self.erroneous_term()
                };
                PatternRow::new(patterns, rhs)
            })
            .collect::<Vec<_>>();
        let problem = MatchProblem::new(scrutinees, rows, expected_type, match_fn);

        match patterns::compile(self, problem, span) {
            Ok(term) => term,
            Err(err) => {
                self.errors.push(err);
                self.erroneous_term()
            }
        }
    }

    /// Builds a core [`Term`] from an elaborated [`Pattern`].
    fn pattern_to_term(&mut self, pattern: &Pattern) -> Term {
        match pattern {
            Pattern::Var(Some(fvar)) => Term::FVar(fvar.clone()),
            Pattern::Var(None) => {
                let u = self.gen_.fresh_anonymous();
                Term::FVar(u)
            }
            Pattern::Constructor { ctor, fields, .. } => {
                let mut term = Term::Const(ctor.clone());
                for field in fields {
                    term = Term::mk_app(term, self.pattern_to_term(field));
                }
                term
            }
            Pattern::Lit(lit) => Term::Lit(lit.clone()),
        }
    }

    fn elaborate_pattern(&mut self, pattern: &ast::Pattern, expected_type: &Term) -> Pattern {
        let span = pattern.span(self.file);
        match pattern {
            ast::Pattern::Var(v) => {
                let name = v.name().unwrap_or("_").to_string();
                let (fvar, _type) = self.fresh_fvar(name, expected_type.clone());
                Pattern::Var(Some(fvar))
            }
            ast::Pattern::Ctor(c) => {
                let (namespace, name) = c.qualified_parts();
                let resolved = self.resolve_name(&namespace, name);
                let Some((ctor_qname, ctor_type)) = resolved else {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::UndefinedConstructor(name.to_string()),
                        span,
                    ));
                    return Pattern::Var(None);
                };
                let ctor_qname = ctor_qname.clone();
                let ctor_type_before = ctor_type.clone();

                // Insert implicit arguments for the constructor type
                let (_ctor_term, ctor_type) =
                    self.insert_implicit_args(Term::Const(ctor_qname.clone()), ctor_type.clone());
                let num_implicits = count_leading_implicits(&ctor_type_before);

                let args: Vec<_> = c.args().collect();
                let mut current_type = reduce::whnf(self, &ctor_type);
                let mut arg_types = Vec::new();
                for _ in &args {
                    if let Term::Pi(_, param_ty, body_ty) = current_type {
                        arg_types.push(*param_ty);
                        current_type = reduce::whnf(self, &body_ty);
                    } else {
                        self.errors.push(ElabError::new(
                            ElabErrorKind::NotAConstructorType(current_type.clone()),
                            span,
                        ));
                        break;
                    }
                }
                // Unify the innermost type (which is the constructor itself after all applications)
                // to the expected type of the pattern
                if !self.unify(&current_type, expected_type) {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::ImpossiblePattern {
                            expected: expected_type.clone(),
                            found: current_type.clone(),
                        },
                        span,
                    ));
                }

                // Elaborate each pattern argument against the corresponding parameter type
                let elaborated_args = args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, arg)| {
                        arg_types
                            .get(i)
                            .map(|arg_type| self.elaborate_pattern(arg, arg_type))
                    })
                    .collect::<Vec<_>>();

                let mut all_fields = Vec::new();
                for _ in 0..num_implicits {
                    all_fields.push(Pattern::Var(None));
                }
                all_fields.extend(elaborated_args);

                Pattern::Constructor {
                    ctor: ctor_qname,
                    fields: all_fields,
                    type_: ctor_type,
                }
            }
            ast::Pattern::Wildcard(_) => Pattern::Var(None),
            ast::Pattern::Lit(lit) => {
                let value = lit.literal().unwrap_or(Literal::Nat(0));
                Pattern::Lit(value)
            }
            _ => {
                self.errors
                    .push(ElabError::new(ElabErrorKind::UnsupportedSyntax, span));
                Pattern::Var(None)
            }
        }
    }

    /// Generates the type of the match/elimination function for an inductive type.
    fn generate_match_fn_type(
        &mut self,
        inductive_name: &Name,
        binder_fvars: &[(Name, BinderInfo, Term)],
        constructor_names: &[Name],
        constructors_types: &[Term],
    ) -> Term {
        let motive_type = Term::mk_pi(
            BinderInfo::Explicit,
            Term::Const(inductive_name.clone()),
            Term::type0(),
        );
        let (motive_fvar, _) = self.fresh_fvar("_motive".into(), motive_type.clone());
        let motive = Term::FVar(motive_fvar.clone());

        let (scrutinee_fvar, _) =
            self.fresh_fvar("_scrut".into(), Term::Const(inductive_name.clone()));

        let mut branch_types = Vec::new();
        for (ctor_name, ctor_type) in constructor_names.iter().zip(constructors_types.iter()) {
            let branch_type = Self::build_branch_type(
                ctor_name,
                inductive_name,
                ctor_type,
                binder_fvars.len(),
                &motive,
            );
            branch_types.push(branch_type);
        }

        let mut result = Term::mk_app(motive.clone(), Term::FVar(scrutinee_fvar.clone()));

        for branch_type in branch_types.iter().rev() {
            result = Term::mk_pi(BinderInfo::Explicit, branch_type.clone(), result);
        }

        result = subst::abstract_fvar(&result, scrutinee_fvar);
        result = Term::mk_pi(
            BinderInfo::Explicit,
            Term::Const(inductive_name.clone()),
            result,
        );

        result = subst::abstract_fvar(&result, motive_fvar);
        result = Term::mk_pi(BinderInfo::Explicit, motive_type, result);

        for (_, info, ty) in binder_fvars.iter().rev() {
            result = Term::mk_pi(*info, ty.clone(), result);
        }

        result
    }

    /// Builds the branch type for a single constructor in the match function.
    fn build_branch_type(
        ctor_name: &Name,
        inductive_name: &Name,
        ctor_type: &Term,
        num_params: usize,
        motive: &Term,
    ) -> Term {
        // Skip inductive parameters
        let mut current = ctor_type.clone();
        for _ in 0..num_params {
            if let Term::Pi(_, _, body) = current {
                current = *body;
            }
        }

        let mut field_binders = Vec::new();
        while let Term::Pi(info, param_ty, body) = current {
            field_binders.push((info, *param_ty));
            current = *body;
        }

        let num_fields = field_binders.len();

        let recursive_fields: Vec<usize> = field_binders
            .iter()
            .enumerate()
            .filter(|(_, (_, ty))| is_recursive_field(ty, inductive_name))
            .map(|(i, _)| i)
            .collect();
        let num_ihs = recursive_fields.len();

        let mut ctor_app = Term::Const(ctor_name.clone());
        for i in 0..num_fields {
            ctor_app = Term::mk_app(ctor_app, Term::BVar(num_ihs + num_fields - 1 - i));
        }

        let mut result = Term::mk_app(motive.clone(), ctor_app);

        // Wrap IH binders (k is current binders, field_idx is the position of the recursive field in the constructor type)
        for (k, &field_idx) in recursive_fields.iter().enumerate().rev() {
            // The field sits at depth: k + (num_fields - 1 - field_idx)
            let field_ref = Term::BVar(k + num_fields - 1 - field_idx);
            let ih_ty = Term::mk_app(motive.clone(), field_ref);
            result = Term::mk_pi(BinderInfo::Explicit, ih_ty, result);
        }

        // Wrap field binders
        for (info, field_type) in field_binders.iter().rev() {
            result = Term::mk_pi(*info, field_type.clone(), result);
        }
        result
    }

    /// Generates a field projection definition for a record type
    fn elaborate_field_definition(
        &mut self,
        field_name: &Name,
        record_name: &Name,
        match_fn: &Name,
        all_field_types: &[Term],
        field_index: usize,
        field_type: &Term,
        binder_fvars: &[(Name, BinderInfo, Term)],
        span: Span,
    ) -> Declaration {
        let num_fields = all_field_types.len();

        let mut applied_record = Term::Const(record_name.clone());
        for (fvar, _, _) in binder_fvars {
            applied_record = Term::mk_app(applied_record, Term::FVar(fvar.clone()));
        }

        let mut branch = Term::BVar(num_fields - 1 - field_index);
        for ft in all_field_types.iter().rev() {
            branch = Term::mk_lam(BinderInfo::Explicit, ft.clone(), branch);
        }

        // Build the motive: λ (_ : R params) => field_type
        let motive = Term::mk_lam(
            BinderInfo::Explicit,
            applied_record.clone(),
            field_type.clone(),
        );

        // Scrutinee is the free variable for the record argument
        let scrutinee_fvar = self.gen_.fresh_anonymous();
        let scrutinee = Term::FVar(scrutinee_fvar.clone());

        // Build: match_fn motive scrutinee branch
        let body = Term::mk_app(
            Term::mk_app(
                Term::mk_app(Term::Const(match_fn.clone()), motive),
                scrutinee,
            ),
            branch,
        );

        // Wrap in λ (x : R params) => body
        let value = subst::abstract_fvar(&body, scrutinee_fvar.clone());
        let value = Term::mk_lam(BinderInfo::Explicit, applied_record.clone(), value);

        let mut value = value;
        for (fvar, info, ty) in binder_fvars.iter().rev() {
            value = subst::abstract_fvar(&value, fvar.clone());
            value = Term::mk_lam(*info, ty.clone(), value);
        }

        // Build the type: {params} -> R params -> field_type
        let proj_type = Term::mk_pi(BinderInfo::Explicit, applied_record, field_type.clone());
        let proj_type = Self::abstract_binders(binder_fvars, proj_type);

        Declaration::Definition {
            name: field_name.clone(),
            type_: proj_type,
            value,
            span,
        }
    }

    fn elaborate_alias(&mut self, d: &AliasDecl) {
        let name_str = d.name().unwrap_or("_");
        let span = d.span(self.file);
        let name = self.gen_.fresh_name(name_str.to_string());
        let saved_lctx = self.lctx.clone();
        let binder_fvars = self.elaborate_binders_iter(d.binders());

        let elaborated_type_ann = if let Some(type_ann) = d.type_ann() {
            let ty = self.elaborate_term(&type_ann, None);
            Some(Self::abstract_binders(&binder_fvars, ty))
        } else {
            None
        };
        let value_expr = d.value();
        let (elaborated_value, value_type) = if let Some(v) = &value_expr {
            self.elaborate_term_inner(v)
        } else {
            (self.erroneous_term(), self.erroneous_term())
        };
        if let Some(type_ann) = &elaborated_type_ann
            && !self.unify(type_ann, &value_type)
        {
            let reduced_to = {
                let reduced = reduce::whnf(self, type_ann);
                if &reduced != type_ann {
                    Some(reduced)
                } else {
                    None
                }
            };
            self.errors.push(ElabError::new(
                ElabErrorKind::TypeMismatch {
                    expected: type_ann.clone(),
                    reduced_to,
                    found: value_type.clone(),
                },
                span,
            ));
        }

        let final_type = if let Some(type_ann) = elaborated_type_ann {
            type_ann
        } else {
            Self::abstract_binders(&binder_fvars, value_type.clone())
        };
        let final_value = Self::abstract_binders_lam(&binder_fvars, elaborated_value.clone());
        self.register_in_namespace(name.to_string().as_str(), name.clone());
        self.env
            .aliases
            .insert(name.clone(), (final_value, final_type));

        self.lctx = saved_lctx;
    }

    /// Retrieves a language item by name, returning an error if it's not found
    fn get_lang_item_or_error(&mut self, item: &str, span: Span) -> Term {
        if let Some(li_name) = self.lang_items.get(item) {
            Term::Const(li_name.clone())
        } else {
            self.errors.push(ElabError::new(
                ElabErrorKind::MissingLangItem(item.to_string()),
                span,
            ));
            self.erroneous_term()
        }
    }

    /// Checks for a `#[wired_in("item_name")]` attribute and, if found, registers the given name as the implementation of that lang item
    fn optionally_register_lang_item(&mut self, name: &Name, attributes: &[Attribute]) {
        for attr in attributes {
            if attr.name() == Some("wired_in") {
                if let Some(arg) = attr.args().next() {
                    if let Expr::Lit(lit) = &arg {
                        if let Some(Literal::Str(item_name)) = lit.literal() {
                            self.lang_items.insert(&item_name, name.clone());
                        }
                    }
                }
            }
        }
    }

    /// Given a base function and its type, applies leading implicit arguments until reaching an explicit parameter
    /// Then, with the provided arguments and their types, abstracts over all binders (both implicit and explicit) to produce a final lambda term and its type
    fn make_app(
        &mut self,
        base_fn: Term,
        base_fn_type: Term,
        args: Vec<(Term, Term)>,
        span: Span,
    ) -> (Term, Term) {
        let (term_with_implicits, fn_type_after_implicits) =
            self.insert_implicit_args_until(base_fn, base_fn_type, BinderInfo::Explicit);

        let mut term = term_with_implicits;
        let mut result_type = fn_type_after_implicits;

        for (arg, arg_ty) in args.into_iter().rev() {
            term = Term::mk_app(term, arg);
            result_type = if let Term::Pi(_, param_ty, body_ty) = result_type {
                if !self.unify(&param_ty, &arg_ty) {
                    let reduced_to = {
                        let reduced = reduce::whnf(self, &param_ty);
                        if reduced != *param_ty {
                            Some(reduced)
                        } else {
                            None
                        }
                    };
                    self.errors.push(ElabError::new(
                        ElabErrorKind::TypeMismatch {
                            expected: *param_ty.clone(),
                            reduced_to,
                            found: arg_ty.clone(),
                        },
                        span,
                    ));
                }
                *body_ty
            } else {
                self.errors.push(ElabError::new(
                    ElabErrorKind::NotAFunction(result_type.clone()),
                    span,
                ));
                return (self.erroneous_term(), self.erroneous_term());
            };
        }

        (term, result_type)
    }
}

/// Entry point for elaboration: type-checks an entire source file.
///
/// Takes a module identifier and the parsed [`SyntaxTree`] and produces either
/// a fully elaborated [`Environment`] or a list of accumulated [`ElabError`]s.
pub fn elaborate_file(
    module_id: ModuleId,
    root: &SyntaxNodeR,
    file: usize,
) -> Result<Environment, Vec<ElabError>> {
    let mut state = ElabState::new(module_id, file);
    let source_file = SourceFile::from(root);

    for decl in source_file.declarations() {
        state.elaborate_declaration(&decl);
    }

    if state.errors.is_empty() {
        Ok(state.env)
    } else {
        Err(state.errors)
    }
}

fn count_leading_implicits(ty: &Term) -> usize {
    let mut count = 0;
    let mut current = ty;
    while let Term::Pi(info, _, body) = current {
        if *info == BinderInfo::Explicit {
            break;
        }
        count += 1;
        current = body;
    }
    count
}
