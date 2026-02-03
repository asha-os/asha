#![no_std]
#![no_main]

use raph_api::{io::fs::MappedFile, println};

extern crate raph_common;
extern crate raph_runtime;

pub mod syntax;

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> i32 {
    println!("Hello, World!");

    if let Some(file) = MappedFile::open("test_program") {
        println!("Read {} bytes from file:", file.len());
        if let Some(text) = file.as_str() {
            println!("Source: {}", text);
        } else {
            println!("<invalid utf-8>");
        }
        return 0;
    } else {
        println!("File not found!");
        return 1;
    }
}
