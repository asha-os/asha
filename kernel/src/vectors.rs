use core::arch::global_asm;
use core::sync::atomic::{AtomicUsize, Ordering};

static GICC_BASE: AtomicUsize = AtomicUsize::new(0);

pub fn init_vectors(gicc_base: usize) {
    GICC_BASE.store(gicc_base, Ordering::Relaxed);
    unsafe {
        core::arch::asm!(
            "adr {tmp}, {table}",
            "msr vbar_el1, {tmp}",
            tmp = out(reg) _,
            table = sym VECTOR_TABLE,
        );
    }
}

pub fn enable_interrupts() {
    unsafe {
        core::arch::asm!("msr daifclr, #0xf");
    }
}

extern "C" fn irq_handler() {
    let gicc = GICC_BASE.load(Ordering::Relaxed);
    let iar = crate::ic::gic::acknowledge_interrupt(gicc);
    let irq_id = iar & 0x3FF;

    match irq_id {
        1023 => {}
        _ => {
            crate::println!("IRQ: {}", irq_id);
        }
    }

    crate::ic::gic::end_interrupt(gicc, iar);
}

extern "C" fn sync_handler() {
    let esr: u64;
    let elr: u64;
    unsafe {
        core::arch::asm!("mrs {}, esr_el1", out(reg) esr);
        core::arch::asm!("mrs {}, elr_el1", out(reg) elr);
    }
    crate::println!("SYNC exception: ESR=0x{:x} ELR=0x{:x}", esr, elr);
    loop {
        core::hint::spin_loop();
    }
}

extern "C" fn default_handler() {
    crate::println!("Unhandled exception");
    loop {
        core::hint::spin_loop();
    }
}

global_asm!(
    ".section .vectors, \"ax\"",
    ".balign 0x800",
    "VECTOR_TABLE:",

    // Synchronous
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    bl {default_handler}",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // IRQ
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    bl {default_handler}",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // FIQ
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    bl {default_handler}",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // SError
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    bl {default_handler}",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // Synchronous
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    stp x0, x1, [sp, #-16]!",
    "    stp x2, x3, [sp, #-16]!",
    "    stp x4, x5, [sp, #-16]!",
    "    stp x6, x7, [sp, #-16]!",
    "    stp x8, x9, [sp, #-16]!",
    "    stp x10, x11, [sp, #-16]!",
    "    stp x12, x13, [sp, #-16]!",
    "    stp x14, x15, [sp, #-16]!",
    "    stp x16, x17, [sp, #-16]!",
    "    stp x18, x19, [sp, #-16]!",
    "    stp x20, x21, [sp, #-16]!",
    "    stp x22, x23, [sp, #-16]!",
    "    stp x24, x25, [sp, #-16]!",
    "    stp x26, x27, [sp, #-16]!",
    "    stp x28, x29, [sp, #-16]!",
    "    bl {sync_handler}",
    "    ldp x28, x29, [sp], #16",
    "    ldp x26, x27, [sp], #16",
    "    ldp x24, x25, [sp], #16",
    "    ldp x22, x23, [sp], #16",
    "    ldp x20, x21, [sp], #16",
    "    ldp x18, x19, [sp], #16",
    "    ldp x16, x17, [sp], #16",
    "    ldp x14, x15, [sp], #16",
    "    ldp x12, x13, [sp], #16",
    "    ldp x10, x11, [sp], #16",
    "    ldp x8, x9, [sp], #16",
    "    ldp x6, x7, [sp], #16",
    "    ldp x4, x5, [sp], #16",
    "    ldp x2, x3, [sp], #16",
    "    ldp x0, x1, [sp], #16",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // IRQ
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    stp x0, x1, [sp, #-16]!",
    "    stp x2, x3, [sp, #-16]!",
    "    stp x4, x5, [sp, #-16]!",
    "    stp x6, x7, [sp, #-16]!",
    "    stp x8, x9, [sp, #-16]!",
    "    stp x10, x11, [sp, #-16]!",
    "    stp x12, x13, [sp, #-16]!",
    "    stp x14, x15, [sp, #-16]!",
    "    stp x16, x17, [sp, #-16]!",
    "    stp x18, x19, [sp, #-16]!",
    "    stp x20, x21, [sp, #-16]!",
    "    stp x22, x23, [sp, #-16]!",
    "    stp x24, x25, [sp, #-16]!",
    "    stp x26, x27, [sp, #-16]!",
    "    stp x28, x29, [sp, #-16]!",
    "    bl {irq_handler}",
    "    ldp x28, x29, [sp], #16",
    "    ldp x26, x27, [sp], #16",
    "    ldp x24, x25, [sp], #16",
    "    ldp x22, x23, [sp], #16",
    "    ldp x20, x21, [sp], #16",
    "    ldp x18, x19, [sp], #16",
    "    ldp x16, x17, [sp], #16",
    "    ldp x14, x15, [sp], #16",
    "    ldp x12, x13, [sp], #16",
    "    ldp x10, x11, [sp], #16",
    "    ldp x8, x9, [sp], #16",
    "    ldp x6, x7, [sp], #16",
    "    ldp x4, x5, [sp], #16",
    "    ldp x2, x3, [sp], #16",
    "    ldp x0, x1, [sp], #16",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // FIQ
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    bl {default_handler}",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    // SError
    ".balign 0x80",
    "    stp x29, x30, [sp, #-16]!",
    "    bl {default_handler}",
    "    ldp x29, x30, [sp], #16",
    "    eret",

    ".balign 0x80",
    "    b .",
    ".balign 0x80",
    "    b .",
    ".balign 0x80",
    "    b .",
    ".balign 0x80",
    "    b .",

    ".balign 0x80",
    "    b .",
    ".balign 0x80",
    "    b .",
    ".balign 0x80",
    "    b .",
    ".balign 0x80",
    "    b .",

    sync_handler = sym sync_handler,
    irq_handler = sym irq_handler,
    default_handler = sym default_handler,
);

unsafe extern "C" {
    static VECTOR_TABLE: u8;
}
