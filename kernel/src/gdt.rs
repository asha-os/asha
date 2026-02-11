#[repr(C, packed)]
struct GdtEntry(u64);

impl GdtEntry {
    const fn null() -> Self {
        GdtEntry(0)
    }

    const fn kernel_code() -> Self {
        GdtEntry(0x00AF9A000000FFFF)
    }

    const fn kernel_data() -> Self {
        GdtEntry(0x00CF92000000FFFF)
    }
}

#[repr(C, packed)]
struct GdtDescriptor {
    limit: u16,
    base: u64,
}

static GDT: [GdtEntry; 3] = [
    GdtEntry::null(),
    GdtEntry::kernel_code(),
    GdtEntry::kernel_data(),
];

const KERNEL_CS: u16 = 0x08;
const KERNEL_DS: u16 = 0x10;

pub unsafe fn init_gdt() {
    let descriptor = GdtDescriptor {
        limit: (core::mem::size_of_val(&GDT) - 1) as u16,
        base: GDT.as_ptr() as u64,
    };

    unsafe {
        core::arch::asm!(
            "lgdt [{}]",
            "push {}",
            "lea {tmp}, [rip + 2f]",
            "push {tmp}",
            "retfq",
            "2:",
            "mov ds, {ds:x}",
            "mov es, {ds:x}",
            "mov fs, {ds:x}",
            "mov gs, {ds:x}",
            "mov ss, {ds:x}",
            in(reg) &descriptor,
            in(reg) KERNEL_CS as u64,
            ds = in(reg) KERNEL_DS as u64,
            tmp = lateout(reg) _,
        )
    };
}
