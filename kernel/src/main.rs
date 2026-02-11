#![no_std]
#![no_main]

use alloc::string::{String, ToString};

use crate::{
    ic::{init_interrupts, pop_scancode},
    serial::init_serial,
    tty::{
        Tty,
        color::{Color, ColorCode},
        writer::TextWriter,
    },
};

extern crate alloc;
extern crate common;
extern crate runtime;

#[cfg(target_arch = "x86_64")]
pub mod gdt;
pub mod heap;
pub mod ic;
#[cfg(target_arch = "x86_64")]
pub mod idt;
pub mod serial;
pub mod tty;
#[cfg(target_arch = "aarch64")]
pub mod vectors;

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
    pub serial_base: u64,
    pub gicd_base: u64,
    pub gicc_base: u64,
}

#[unsafe(no_mangle)]
pub extern "C" fn _start(boot_info: *const BootInfo) -> ! {
    let info = unsafe { &*boot_info };

    #[cfg(target_arch = "x86_64")]
    unsafe {
        gdt::init_gdt();
        idt::init_idt();
    }
    #[cfg(target_arch = "aarch64")]
    vectors::init_vectors(info.gicc_base as usize);

    init_serial(info.serial_base as usize);
    init_interrupts(info.gicd_base as usize, info.gicc_base as usize);

    #[cfg(target_arch = "x86_64")]
    idt::enable_interrupts();
    #[cfg(target_arch = "aarch64")]
    vectors::enable_interrupts();

    println!("Serial initialized.");
    println!(
        "FB: base=0x{:x} size={} {}x{} stride={} fmt={}",
        info.framebuffer.base,
        info.framebuffer.size,
        info.framebuffer.width,
        info.framebuffer.height,
        info.framebuffer.stride,
        info.framebuffer.pixel_format,
    );
    let (free_region, free_size) = find_free_region(&info.memory_map);
    heap::init_heap(free_region, free_size);

    let fb_buffer = unsafe {
        core::slice::from_raw_parts_mut(info.framebuffer.base as *mut u8, info.framebuffer.size)
    };
    let text_writer = TextWriter::new_framebuffer_writer(fb_buffer, info.framebuffer.clone());
    let mut tty = Tty::new(text_writer, ColorCode::new(Color::White, Color::Black));
    tty.set_shell_prompt("> ".to_string(), ColorCode::new(Color::Green, Color::Black));
    loop {
        if let Some(scancode) = pop_scancode() {
            if let Some(command) = tty.handle_input(scancode) {
                let command = String::from_utf8_lossy(&command);
                println!("Command entered: {}", command);
            }
        }
    }
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
