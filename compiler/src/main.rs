#![no_std]
#![no_main]

use alloc::string::String;
use miette::{Diagnostic, NamedSource, NarratableReportHandler};
use api::{
    io::{fs::MappedFile, stdin::Args},
    println,
};

use crate::syntax::{SourceFile, lexer::Lexer, parser::parse};

extern crate alloc;
extern crate common;
extern crate runtime;

pub mod module;
pub mod elaboration;
pub mod syntax;
pub mod spine;

#[derive(Debug)]
struct ErrorWithSource<'a, E: Diagnostic + ::core::fmt::Debug> {
    error: &'a E,
    source: &'a NamedSource<String>,
}

impl<E: Diagnostic + ::core::fmt::Debug> ::core::fmt::Display for ErrorWithSource<'_, E> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl<E: Diagnostic + ::core::fmt::Debug> miette::StdError for ErrorWithSource<'_, E> {}

impl<E: Diagnostic + ::core::fmt::Debug> Diagnostic for ErrorWithSource<'_, E> {
    fn code<'a>(&'a self) -> Option<alloc::boxed::Box<dyn ::core::fmt::Display + 'a>> {
        self.error.code()
    }

    fn severity(&self) -> Option<miette::Severity> {
        self.error.severity()
    }

    fn help<'a>(&'a self) -> Option<alloc::boxed::Box<dyn ::core::fmt::Display + 'a>> {
        self.error.help()
    }

    fn labels(&self) -> Option<alloc::boxed::Box<dyn Iterator<Item = miette::LabeledSpan> + '_>> {
        self.error.labels()
    }

    fn source_code(&self) -> Option<&dyn miette::SourceCode> {
        Some(self.source)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> i32 {
    let args = Args::get();
    if args.is_none() {
        println!("You must provide a source file as an argument.");
        return 1;
    }    
    let mut args = args.unwrap();
    if args.len() < 2 {
        println!("You must provide a source file as an argument.");
        return 1;
    }

    let _program_name = args.next();
    let source_file = String::from_utf16_lossy(args.next().unwrap().as_utf16());
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

        let handler = NarratableReportHandler::new();
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
            Some(tree) => println!("Parsed: {:?}", tree),
            None if errors.is_empty() && lex_errors.is_empty() => println!("No AST produced"),
            None => {}
        }

        return 0;
    } else {
        println!("File not found!");
        return 1;
    }
}
