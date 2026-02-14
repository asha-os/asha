#![no_std]

#[cfg(target_os = "asha")]
use core::panic::PanicInfo;

#[cfg(target_os = "asha")]
use talc::{ErrOnOom, Talc, Talck};

#[global_allocator]
#[cfg(target_os = "asha")]
pub static ALLOCATOR: Talck<spin::Mutex<()>, ErrOnOom> = Talc::new(ErrOnOom).lock();

#[panic_handler]
#[cfg(target_os = "asha")]
fn panic(info: &PanicInfo) -> ! {
    api::abort(info)
}

#[cfg(all(not(target_os = "asha"), target_os = "windows"))]
#[link(name = "ucrt")]
unsafe extern "C" {}
