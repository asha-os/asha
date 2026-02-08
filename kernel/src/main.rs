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
pub extern "C" fn _start(boot_info: *const BootInfo) -> ! {
    let info = unsafe { &*boot_info };
    let fb = info.framebuffer.base as *mut u32;
    let pixels = (info.framebuffer.stride * info.framebuffer.height) as usize;
    for i in 0..pixels {
        unsafe {
            *fb.add(i) = 0x0000FF00;
        }
    }

    loop {}
}
