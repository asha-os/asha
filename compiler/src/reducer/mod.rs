use alloc::format;
use api::println;

use crate::{
    elaboration::{Declaration, Environment, reduce::try_iota, subst},
    spine::Term,
};

pub struct Reducer {
    env: Environment,
}

impl Reducer {
    pub fn new(env: Environment) -> Self {
        Self { env }
    }

    pub fn run(&self) {
        let main = self.env.main_fn.as_ref().expect("No main function found");
        let main_decl = self
            .env
            .decls
            .get(&main)
            .expect("Main function not found in environment");
        let result = self.reduce(main_decl);
        println!("Result of main: {}", result);
    }

    pub fn reduce(&self, decl: &Declaration) -> Term {
        match decl {
            Declaration::Definition {
                name, type_, value, ..
            } => {
                println!("Running definition: {}", name);
                self.eval(value.clone())
            }
            Declaration::Constructor { name, type_, .. } => {
                panic!("Cannot run constructor declaration: {}", name);
            }
            Declaration::Opaque { name, type_, .. } => {
                panic!("Cannot run opaque declaration: {}", name);
            }
            Declaration::Recursor { name, .. } => {
                panic!("Cannot run recursor without arguments: {}", name);
            }
        }
    }

    pub fn eval(&self, term: Term) -> Term {
        match term {
            Term::App(fun, arg) => {
                let function = self.eval(*fun);
                let argument = self.eval(*arg);
                if let Term::Lam(_, _, body) = function {
                    self.eval(subst::instantiate(&body, &argument))
                } else {
                    let app = Term::mk_app(function, argument);
                    if let Some(reduced) = try_iota(&self.env, &app) {
                        self.eval(reduced)
                    } else {
                        app
                    }
                }
            }
            Term::Const(qname) => {
                let decl = self
                    .env
                    .decls
                    .get(&qname)
                    .expect(&format!("Undefined constant: {}", qname));
                match decl {
                    Declaration::Definition { value, .. } => self.eval(value.clone()),
                    _ => Term::Const(qname),
                }
            }
            _ => term,
        }
    }
}
