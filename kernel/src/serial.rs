use core::sync::atomic::{AtomicUsize, Ordering};

pub struct Serial;

static SERIAL_BASE: AtomicUsize = AtomicUsize::new(0);

#[cfg(target_arch = "x86_64")]
pub fn init_serial(_base: usize) {
    unsafe {
        core::arch::asm!(
            "mov dx, 0x3F8+1",
            "mov al, 0x00",
            "out dx, al",
            "mov dx, 0x3F8+3",
            "mov al, 0x80",
            "out dx, al",
            "mov dx, 0x3F8+0",
            "mov al, 0x03",
            "out dx, al",
            "mov dx, 0x3F8+1",
            "mov al, 0x00",
            "out dx, al",
            "mov dx, 0x3F8+3",
            "mov al, 0x03",
            "out dx, al",
        );
    }
}

#[cfg(target_arch = "aarch64")]
pub fn init_serial(base: usize) {
    SERIAL_BASE.store(base, Ordering::Relaxed);
}

#[cfg(target_arch = "x86_64")]
fn serial_write_byte(b: u8) {
    unsafe {
        core::arch::asm!(
            "mov dx, 0x3FD",
            "2: in al, dx",
            "test al, 0x20",
            "jz 2b",
            "mov dx, 0x3F8",
            "mov al, {0}",
            "out dx, al",
            in(reg_byte) b,
            out("al") _,
            out("dx") _,
        );
    }
}

#[cfg(target_arch = "aarch64")]
fn serial_write_byte(b: u8) {
    let base = SERIAL_BASE.load(Ordering::Relaxed);
    let uartdr = base;

    unsafe {
        core::ptr::write_volatile(uartdr as *mut u32, b as u32);
    }
}

impl core::fmt::Write for Serial {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for b in s.bytes() {
            serial_write_byte(b);
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        core::fmt::write(&mut crate::serial::Serial, format_args!($($arg)*)).unwrap();
    };
}

#[macro_export]
macro_rules! println {
    () => {
        crate::print!("\n");
    };
    ($($arg:tt)*) => {
        crate::print!("{}\n", format_args!($($arg)*));
    };
}
