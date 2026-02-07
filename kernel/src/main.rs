#![no_std]
#![no_main]

extern crate alloc;
extern crate common;
extern crate runtime;

#[repr(C)]
pub struct MemoryMapInfo {
    pub entries: *const u8,
    pub entry_count: usize,
    pub entry_size: usize,
}

#[repr(C)]
pub struct FramebufferInfo {
    pub base: u64,
    pub size: usize,
    pub width: u32,
    pub height: u32,
    pub stride: u32,
    pub pixel_format: u32,
}

#[repr(C)]
pub struct BootInfo {
    pub memory_map: MemoryMapInfo,
    pub framebuffer: FramebufferInfo,
}

#[unsafe(no_mangle)]
pub extern "C" fn _start(_boot_info: *const BootInfo) -> ! {
    loop {}
}
