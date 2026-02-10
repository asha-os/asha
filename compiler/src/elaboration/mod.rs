pub mod ctx;
pub mod err;
pub mod reduce;
pub mod subst;
pub mod unify;

use alloc::{
    boxed::Box,
    collections::btree_map::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};
use api::println;

use crate::{
    elaboration::{
        ctx::{LocalContext, MetavarContext},
        err::{ElabError, ElabErrorKind},
    },
    log::pretty::pretty_term,
    module::{
        ModuleId,
        name::QualifiedName,
        prim::{PRIM_ARRAY, PRIM_ARRAY_CONS, PRIM_ARRAY_NIL, PRIM_FIN, PRIM_NAT, PRIM_STRING},
        unique::{Unique, UniqueGen},
    },
    spine::{BinderInfo, Level, Literal, Term},
    syntax::{
        Span, Spanned,
        tree::{SyntaxBinder, SyntaxExpr},
    },
};

#[derive(Debug, Clone)]
pub struct Namespace {
    pub decls: BTreeMap<String, QualifiedName>,
    pub children: BTreeMap<String, Namespace>,
}

impl Namespace {
    pub fn new() -> Self {
        Self {
            decls: BTreeMap::new(),
            children: BTreeMap::new(),
        }
    }

    pub fn lookup_decl(&self, name: &str) -> Option<&QualifiedName> {
        self.decls.get(name)
    }

    pub fn child(&self, name: &str) -> Option<&Namespace> {
        self.children.get(name)
    }

    pub fn walk(&self, path: &[String]) -> Option<&Namespace> {
        let mut current = self;
        for segment in path {
            current = current.children.get(segment)?;
        }
        Some(current)
    }

    pub fn resolve(&self, path: &[String], member: &str) -> Option<&QualifiedName> {
        self.walk(path)?.lookup_decl(member)
    }
}

#[derive(Debug, Clone)]
pub struct Environment {
    pub module_id: ModuleId,
    pub externals: BTreeMap<QualifiedName, Term>,
    pub decls: BTreeMap<QualifiedName, Declaration>,
    pub root_namespace: Namespace,
}

impl Environment {
    // todo: review
    pub fn pre_loaded(module_id: ModuleId) -> Self {
        let mut externals = BTreeMap::new();
        externals.insert(PRIM_NAT, Term::Sort(Level::Zero));
        externals.insert(PRIM_STRING, Term::Sort(Level::Zero));
        externals.insert(
            PRIM_FIN,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Const(PRIM_NAT)),
                Box::new(Term::Sort(Level::Zero)),
            ),
        );
        externals.insert(
            PRIM_ARRAY,
            Term::Pi(
                BinderInfo::Explicit,
                Box::new(Term::Sort(Level::Zero)),
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
        Self {
            module_id,
            externals,
            decls: BTreeMap::new(),
            root_namespace,
        }
    }

    pub fn lookup(&self, name: &QualifiedName) -> Option<&Declaration> {
        self.decls.get(name)
    }

    pub fn lookup_type(&self, qname: &QualifiedName) -> Option<(&QualifiedName, &Term)> {
        self.decls
            .get(qname)
            .map(|decl| (decl.name(), decl.type_()))
            .or_else(|| self.externals.get_key_value(qname).map(|(n, t)| (n, t)))
    }
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Definition {
        name: QualifiedName,
        type_: Term,
        value: Term,
        span: Span,
    },
    Constructor {
        name: QualifiedName,
        type_: Term,
        span: Span,
    },
}

impl Declaration {
    pub fn name(&self) -> &QualifiedName {
        match self {
            Declaration::Definition { name, .. } => name,
            Declaration::Constructor { name, .. } => name,
        }
    }

    pub fn type_(&self) -> &Term {
        match self {
            Declaration::Definition { type_, .. } => type_,
            Declaration::Constructor { type_, .. } => type_,
        }
    }
}

pub struct ElabState {
    pub env: Environment,
    pub gen_: UniqueGen,
    pub mctx: MetavarContext,
    pub lctx: LocalContext,
    pub current_namespace: Vec<String>,
    pub open_namespaces: Vec<Vec<String>>,
    pub errors: Vec<ElabError>,
}

impl ElabState {
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

    pub fn pre_loaded(module: ModuleId) -> Self {
        let mut state = Self::new(module);
        state.env = Environment::pre_loaded(state.env.module_id.clone());
        state
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

    pub fn elaborate_command(&mut self, cmd: &SyntaxExpr) {
        match cmd {
            SyntaxExpr::Def {
                name,
                binders,
                return_type,
                body,
                span,
            } => self.elaborate_def(name, binders, return_type, body, *span),
            SyntaxExpr::Record {
                name,
                binders,
                fields,
                span,
            } => self.elaborate_record(name, binders, fields, *span),
            SyntaxExpr::Eval { expr, .. } => {
                let term = self.elaborate_term(expr, None);
                println!("Evaluated term: {:#?}", pretty_term(&term));
            }
            _ => (),
        }
    }

    fn elaborate_def(
        &mut self,
        name: &str,
        binders: &[SyntaxBinder],
        return_type: &SyntaxExpr,
        body: &SyntaxExpr,
        span: Span,
    ) {
        let def_name = QualifiedName::User(self.gen_.fresh(name.to_string()));

        let saved_lctx = self.lctx.clone();
        let mut binder_fvars: Vec<(Unique, BinderInfo, Term)> = Vec::new();

        for binder in binders {
            let (binder_name, binder_type_syntax, info) = match binder {
                SyntaxBinder::Explicit(_, n, ty) => (n, ty, BinderInfo::Explicit),
                SyntaxBinder::Implicit(_, n, ty) => (n, ty, BinderInfo::Implicit),
                SyntaxBinder::Instance(_, n, ty) => (n, ty, BinderInfo::InstanceImplicit),
            };
            let elaborated_type = self.elaborate_term(binder_type_syntax, None);
            let (fvar, _) = self.fresh_fvar(binder_name.clone(), elaborated_type.clone());
            binder_fvars.push((fvar, info, elaborated_type));
        }
        let elaborated_return_type = self.elaborate_term(return_type, None);
        let elaborated_body = self.elaborate_term(body, Some(&elaborated_return_type));

        let mut pi_type = elaborated_return_type;
        let mut value = elaborated_body;
        for (fvar, info, ty) in binder_fvars.into_iter().rev() {
            pi_type = subst::abstract_fvar(&pi_type, fvar.clone());
            value = subst::abstract_fvar(&value, fvar);

            pi_type = Term::Pi(info, Box::new(ty), Box::new(pi_type));
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
                Term::Sort(Level::Zero),
                Term::Sort(Level::Succ(Box::new(Level::Zero))),
            ),
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
                    self.fresh_mvar(Term::Sort(Level::Zero))
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
            SyntaxExpr::App { fun, arg, .. } => {
                let (mut term, mut fn_type) = self.elaborate_term_inner(fun);

                loop {
                    fn_type = reduce::whnf(self, &fn_type);
                    match &fn_type {
                        Term::Pi(info, param_ty, body_ty) if info != &BinderInfo::Explicit => {
                            let mvar = self.fresh_mvar(*param_ty.clone());
                            fn_type = subst::instantiate(body_ty, &mvar);
                            term = Term::App(Box::new(term), Box::new(mvar));
                        }
                        _ => break,
                    };
                }

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
            u => {
                self.errors.push(ElabError::new(
                    err::ElabErrorKind::UnsupportedSyntax(u.clone()),
                    syntax.span(),
                ));
                (self.erroneous_term(), self.erroneous_term())
            }
        }
    }

    fn unify(&mut self, a: &Term, b: &Term) -> bool {
        unify::is_def_eq(self, a, b)
    }

    fn elaborate_record(
        &mut self,
        name: &str,
        binders: &[SyntaxBinder],
        fields: &[SyntaxExpr],
        span: Span,
    ) {
        let record_name = QualifiedName::User(self.gen_.fresh(name.to_string()));
        // todo: remove code duplication
        let saved_lctx = self.lctx.clone();
        let mut binder_fvars: Vec<(Unique, BinderInfo, Term)> = Vec::new();

        for binder in binders {
            let (binder_name, binder_type_syntax, info) = match binder {
                SyntaxBinder::Explicit(_, n, ty) => (n, ty, BinderInfo::Explicit),
                SyntaxBinder::Implicit(_, n, ty) => (n, ty, BinderInfo::Implicit),
                SyntaxBinder::Instance(_, n, ty) => (n, ty, BinderInfo::InstanceImplicit),
            };
            let elaborated_type = self.elaborate_term(binder_type_syntax, None);
            let (fvar, _) = self.fresh_fvar(binder_name.clone(), elaborated_type.clone());
            binder_fvars.push((fvar, info, elaborated_type));
        }
        let mut field_types: Vec<(String, Term)> = Vec::new();
        for field in fields {
            match field {
                SyntaxExpr::RecordField { name, type_ann, .. } => {
                    let elaborated_type = self.elaborate_term(type_ann, None);
                    field_types.push((name.clone(), elaborated_type));
                }
                _ => {
                    self.errors.push(ElabError::new(
                        ElabErrorKind::UnsupportedSyntax(field.clone()),
                        field.span(),
                    ));
                }
            }
        }

        let mut pi_type = Term::Sort(Level::Zero);
        for (fvar, info, ty) in binder_fvars.into_iter().rev() {
            pi_type = subst::abstract_fvar(&pi_type, fvar.clone());
            pi_type = Term::Pi(info, Box::new(ty), Box::new(pi_type));
        }
        println!("Elaborated record '{}' with type: {}", name, &pi_type);

        self.env.decls.insert(
            record_name.clone(),
            Declaration::Constructor {
                name: record_name.clone(),
                type_: pi_type,
                span,
            },
        );
        self.register_in_namespace(name, record_name);

        self.lctx = saved_lctx;
    }

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
}

pub fn elaborate_file(
    module_id: ModuleId,
    root: &SyntaxExpr,
) -> Result<Environment, Vec<ElabError>> {
    let mut state = ElabState::pre_loaded(module_id);

    match root {
        SyntaxExpr::Root(commands) => {
            for cmd in commands {
                state.elaborate_command(cmd);
            }
        }
        _ => panic!("expected a root syntax expression"),
    }

    if state.errors.is_empty() {
        Ok(state.env)
    } else {
        Err(state.errors)
    }
}
