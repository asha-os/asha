use core::sync::atomic::{AtomicUsize, Ordering};

#[cfg(target_arch = "aarch64")]
pub mod gic;
#[cfg(target_arch = "x86_64")]
pub mod pic;

pub fn init_interrupts(gicd_base: usize, gicc_base: usize) {
    #[cfg(target_arch = "aarch64")]
    gic::init_gic(gicd_base, gicc_base);
    #[cfg(target_arch = "x86_64")]
    {
        let _ = (gicd_base, gicc_base);
        pic::init_pic();
        pic::register_interrupt_handlers();
    }
}

static mut KEY_BUFFER: [u8; 256] = [0; 256];
static WRITE_POS: AtomicUsize = AtomicUsize::new(0);
static READ_POS: AtomicUsize = AtomicUsize::new(0);

pub fn push_scancode(scancode: u8) {
    let w = WRITE_POS.load(Ordering::Relaxed);
    unsafe { KEY_BUFFER[w & 0xFF] = scancode };
    WRITE_POS.store(w.wrapping_add(1), Ordering::Release);
}

pub fn pop_scancode() -> Option<u8> {
    let r = READ_POS.load(Ordering::Relaxed);
    let w = WRITE_POS.load(Ordering::Acquire);
    if r == w {
        return None;
    }
    let code = unsafe { KEY_BUFFER[r & 0xFF] };
    READ_POS.store(r.wrapping_add(1), Ordering::Relaxed);
    Some(code)
}
