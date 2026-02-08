#![no_std]
#![no_main]

use crate::{
    idt::{enable_interrupts, init_idt},
    pic::init_pic, text::{TextWriter, color::{Color, ColorCode}},
};

extern crate alloc;
extern crate common;
extern crate runtime;

pub mod heap;
pub mod idt;
pub mod pic;
pub mod text;

#[repr(C)]
pub struct MemoryMapInfo {
    pub entries: *const u8,
    pub entry_count: usize,
    pub entry_size: usize,
}

#[repr(C)]
#[derive(Clone)]
pub struct FramebufferInfo {
    pub base: u64,
    pub size: usize,
    pub width: u32,
    pub height: u32,
    pub stride: u32,
    pub pixel_format: u32,
}

impl FramebufferInfo {
    pub fn bytes_per_pixel(&self) -> usize {
        4
    }
    pub fn width(&self) -> usize {
        self.width as usize
    }
    pub fn height(&self) -> usize {
        self.height as usize
    }
    pub fn stride(&self) -> usize {
        self.stride as usize
    }
}

#[repr(C)]
pub struct BootInfo {
    pub memory_map: MemoryMapInfo,
    pub framebuffer: FramebufferInfo,
}

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

unsafe fn init_gdt() {
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

#[unsafe(no_mangle)]
pub extern "C" fn _start(boot_info: *const BootInfo) -> ! {
    unsafe {
        init_gdt();
        init_idt();
    };
    init_pic();
    enable_interrupts();
    pic::register_interrupt_handlers();

    let info = unsafe { &*boot_info };
    let (free_region, free_size) = find_free_region(&info.memory_map);
    heap::init_heap(free_region, free_size);

    let fb_buffer = unsafe {
        core::slice::from_raw_parts_mut(
            info.framebuffer.base as *mut u8,
            info.framebuffer.size,
        )
    };
    let mut text_writer = TextWriter::new_framebuffer_writer(
        fb_buffer,
        info.framebuffer.clone(),
        ColorCode::new(Color::White, Color::Black)
    );
    text_writer.write_string("Hello, world!");
    text_writer.new_line();
    text_writer.write_string("Welcome!");

    loop {}
}

#[repr(C)]
struct MemoryDescriptor {
    type_: u32,
    physical_start: u64,
    virtual_start: u64,
    number_of_pages: u64,
    attribute: u64,
}

fn find_free_region(memory_map: &MemoryMapInfo) -> (*mut u8, usize) {
    let mut largest_region = core::ptr::null_mut();
    let mut largest_size = 0;
    for i in 0..memory_map.entry_count {
        let entry_addr = memory_map.entries as usize + i * memory_map.entry_size;
        let desc = unsafe { &*(entry_addr as *const MemoryDescriptor) };
        if desc.type_ == 7 {
            let region_start = desc.physical_start as *mut u8;
            let region_size = (desc.number_of_pages * 4096) as usize;
            if region_size > largest_size {
                largest_size = region_size;
                largest_region = region_start;
            }
        }
    }
    (largest_region, largest_size)
}
