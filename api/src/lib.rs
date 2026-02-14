#![cfg_attr(target_os = "asha", no_std)]

pub mod io;

use core::panic::PanicInfo;

pub fn exit(code: i32) -> ! {
    #[cfg(not(target_os = "asha"))]
    std::process::exit(code);

    #[cfg(target_os = "asha")]
    loop {}
}    

pub fn abort(_info: &PanicInfo) -> ! {
    exit(1);
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ({
        $crate::io::stdout::print(format_args!($($arg)*));
    })
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ({
        $crate::io::stdout::print(format_args!($($arg)*));
        $crate::io::stdout::print(format_args!("\n"));
    })
}
