#![no_std]
#![no_main]

extern crate alloc;
extern crate common;
extern crate runtime;

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    loop {}
}