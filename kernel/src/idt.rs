use core::ptr::addr_of;

pub fn enable_interrupts() {
    unsafe {
        core::arch::asm!("sti");
    }
}

pub unsafe fn set_handler(vector: u8, handler: u64) {
    unsafe {
        IDT[vector as usize] = IdtEntry::new(handler, 0x08, 0, 0x8E);
    }
}

pub struct InterruptStackFrame {
    pub rip: u64,
    pub cs: u64,
    pub rflags: u64,
    pub rsp: u64,
    pub ss: u64,
}

pub unsafe fn init_idt() {
    let descriptor = IdtDescriptor {
        limit: (core::mem::size_of::<[IdtEntry; 256]>() - 1) as u16,
        base: addr_of!(IDT) as u64,
    };

    unsafe {
        core::arch::asm!(
            "lidt [{}]",
            in(reg) &descriptor,
        )
    };
}

#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
struct IdtEntry {
    offset_low: u16,
    selector: u16,
    ist: u8,
    type_attrs: u8,
    offset_mid: u16,
    offset_high: u32,
    zero: u32,
}

impl IdtEntry {
    const fn new(offset: u64, selector: u16, ist: u8, type_attrs: u8) -> Self {
        IdtEntry {
            offset_low: offset as u16,
            selector,
            ist,
            type_attrs,
            offset_mid: (offset >> 16) as u16,
            offset_high: (offset >> 32) as u32,
            zero: 0,
        }
    }

    const fn missing() -> Self {
        IdtEntry {
            offset_low: 0,
            selector: 0,
            ist: 0,
            type_attrs: 0,
            offset_mid: 0,
            offset_high: 0,
            zero: 0,
        }
    }
}

#[repr(C, packed)]
struct IdtDescriptor {
    limit: u16,
    base: u64,
}

static mut IDT: [IdtEntry; 256] = [IdtEntry::missing(); 256];

#[macro_export]
macro_rules! define_interrupt_handler {
    ($stub_name:ident, $handler:ident) => {
        #[unsafe(naked)]
        pub extern "C" fn $stub_name() {
            core::arch::naked_asm!(
                "push rax",
                "push rbx",
                "push rcx",
                "push rdx",
                "push rsi",
                "push rdi",
                "push rbp",
                "push r8",
                "push r9",
                "push r10",
                "push r11",
                "push r12",
                "push r13",
                "push r14",
                "push r15",

                "call {handler}",

                "pop r15",
                "pop r14",
                "pop r13",
                "pop r12",
                "pop r11",
                "pop r10",
                "pop r9",
                "pop r8",
                "pop rbp",
                "pop rdi",
                "pop rsi",
                "pop rdx",
                "pop rcx",
                "pop rbx",
                "pop rax",

                "iretq",

                handler = sym $handler,
            )
        }
    };
}
