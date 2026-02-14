#![no_std]
#![no_main]

use alloc::string::{String, ToString};
use api::{
    exit,
    io::{fs::MappedFile, stdin::Args},
    println,
};
use miette::{GraphicalReportHandler, GraphicalTheme, NamedSource};

use crate::{
    log::ErrorWithSource,
    syntax::{SourceFile, lexer::Lexer, parser::parse},
};

extern crate alloc;
extern crate common;
extern crate runtime;

pub mod elaboration;
pub mod log;
pub mod module;
pub mod spine;
pub mod syntax;

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    let args = Args::get();
    if args.is_none() {
        println!("You must provide a source file as an argument.");
        exit(1);
    }
    let mut args = args.unwrap();
    if args.len() < 2 {
        println!("You must provide a source file as an argument.");
        exit(1);
    }

    let _program_name = args.next();
    let source_file = args.next().unwrap();
    println!("Opening file: {}", &source_file);

    if let Some(file) = MappedFile::open(&source_file) {
        println!("Read {} bytes from file:", file.len());
        let source_file = SourceFile {
            id: 0,
            name: &source_file,
            source: file.as_bytes(),
            package: None,
        };
        let mut lexer = Lexer::new(&source_file);

        let mut tokens = alloc::vec::Vec::new();
        let mut lex_errors = alloc::vec::Vec::new();
        for result in &mut lexer {
            match result {
                Ok(token) => tokens.push((token, token.span)),
                Err(err) => lex_errors.push(err),
            }
        }

        let handler = GraphicalReportHandler::new_themed(GraphicalTheme::unicode());
        let source_str = ::core::str::from_utf8(file.as_bytes()).unwrap_or("<invalid utf8>");
        let named_source = NamedSource::new(source_file.name, String::from(source_str));

        for err in &lex_errors {
            let mut output = String::new();
            let err_with_source = ErrorWithSource {
                error: err,
                source: &named_source,
            };
            if handler.render_report(&mut output, &err_with_source).is_ok() {
                println!("{}", output);
            }
        }

        let eoi_span = lexer.eoi_span();
        let (ast, errors) = parse(&tokens, eoi_span);

        for err in &errors {
            let mut output = String::new();
            let err_with_source = ErrorWithSource {
                error: err,
                source: &named_source,
            };
            if handler.render_report(&mut output, &err_with_source).is_ok() {
                println!("{}", output);
            }
        }

        match ast {
            Some(tree) => {
                println!("AST produced for module {}: {:#?}", source_file.name, tree);
                let module_id = source_file.name.to_string();
                println!("Elaborating module {}...", module_id);
                match elaboration::elaborate_file(module_id, &tree) {
                    Ok(elab) => println!("Elaboration successful:\n{}", elab),
                    Err(errs) => {
                        println!("Elaboration failed with {} error(s):", errs.len());
                        for err in &errs {
                            let mut output = String::new();
                            let err_with_source = ErrorWithSource {
                                error: err,
                                source: &named_source,
                            };
                            if handler.render_report(&mut output, &err_with_source).is_ok() {
                                println!("{}", output);
                            }
                        }
                    }
                }
            }
            None if errors.is_empty() && lex_errors.is_empty() => println!("No AST produced"),
            None => {}
        }

        exit(0);
    } else {
        println!("File not found!");
        exit(1);
    }
}
