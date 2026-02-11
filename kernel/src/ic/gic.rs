#[cfg(target_arch = "aarch64")]
use core::ptr;

pub fn init_gic(gicd_base: usize, gicc_base: usize) {
    unsafe {
        ptr::write_volatile((gicd_base + 0x000) as *mut u32, 1);
        // Enable CPU interface
        ptr::write_volatile((gicc_base + 0x000) as *mut u32, 1);
        // Set priority mask (accept all priorities)
        ptr::write_volatile((gicc_base + 0x004) as *mut u32, 0xFF);
    }
}

pub fn acknowledge_interrupt(gicc_base: usize) -> u32 {
    unsafe { ptr::read_volatile((gicc_base + 0x00C) as *const u32) }
}

pub fn end_interrupt(gicc_base: usize, id: u32) {
    unsafe { ptr::write_volatile((gicc_base + 0x010) as *mut u32, id) };
}
