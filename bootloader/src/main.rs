#![no_std]
#![no_main]

use r_efi::efi;
use r_efi::protocols::file;
use r_efi::protocols::graphics_output;
use r_efi::protocols::simple_file_system;

const KERNEL_LOAD_ADDR: u64 = 0x100000; // 1 MB

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
pub extern "efiapi" fn efi_main(
    image_handle: efi::Handle,
    system_table: *mut efi::SystemTable,
) -> efi::Status {
    let st = unsafe { &*system_table };
    let bs = unsafe { &*st.boot_services };
    let con_out = unsafe { &mut *st.con_out };

    print(con_out, "Booting...\r\n");

    let mut fs_ptr: *mut core::ffi::c_void = core::ptr::null_mut();
    let mut fs_guid = simple_file_system::PROTOCOL_GUID;
    let status = unsafe { (bs.locate_protocol)(&mut fs_guid, core::ptr::null_mut(), &mut fs_ptr) };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to locate SimpleFileSystem\r\n");
        return status;
    }
    let fs = fs_ptr as *mut simple_file_system::Protocol;

    let mut root: *mut file::Protocol = core::ptr::null_mut();
    let status = unsafe { ((*fs).open_volume)(fs, &mut root) };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to open volume\r\n");
        return status;
    }

    let mut kernel_file: *mut file::Protocol = core::ptr::null_mut();
    let kernel_path: [u16; 11] = [
        'k' as u16, 'e' as u16, 'r' as u16, 'n' as u16, 'e' as u16, 'l' as u16, '.' as u16,
        'b' as u16, 'i' as u16, 'n' as u16, 0u16,
    ];
    let status = unsafe {
        ((*root).open)(
            root,
            &mut kernel_file,
            kernel_path.as_ptr() as *mut efi::Char16,
            file::MODE_READ,
            0,
        )
    };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to open kernel.bin\r\n");
        return status;
    }

    let mut info_buf = [0u8; 256];
    let mut info_size = info_buf.len();
    let mut info_id = file::INFO_ID;
    let status = unsafe {
        ((*kernel_file).get_info)(
            kernel_file,
            &mut info_id,
            &mut info_size,
            info_buf.as_mut_ptr() as *mut core::ffi::c_void,
        )
    };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to get kernel file info\r\n");
        return status;
    }
    let file_info = unsafe { &*(info_buf.as_ptr() as *const file::Info) };
    let kernel_size = file_info.file_size as usize;

    let kernel_ptr = KERNEL_LOAD_ADDR as *mut u8;
    let pages = (kernel_size + 0xFFF) / 0x1000;
    let mut addr = KERNEL_LOAD_ADDR;
    let status =
        unsafe { (bs.allocate_pages)(efi::ALLOCATE_ADDRESS, efi::LOADER_DATA, pages, &mut addr) };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to allocate memory for kernel\r\n");
        return status;
    }

    let mut read_size = kernel_size;
    let status = unsafe {
        ((*kernel_file).read)(
            kernel_file,
            &mut read_size,
            kernel_ptr as *mut core::ffi::c_void,
        )
    };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to read kernel\r\n");
        return status;
    }

    unsafe { ((*kernel_file).close)(kernel_file) };
    unsafe { ((*root).close)(root) };

    print(con_out, "Kernel loaded.\r\n");

    let mut gop_ptr: *mut core::ffi::c_void = core::ptr::null_mut();
    let mut gop_guid = graphics_output::PROTOCOL_GUID;
    let status =
        unsafe { (bs.locate_protocol)(&mut gop_guid, core::ptr::null_mut(), &mut gop_ptr) };
    let framebuffer = if status == efi::Status::SUCCESS {
        let gop = unsafe { &*(gop_ptr as *mut graphics_output::Protocol) };
        let mode = unsafe { &*gop.mode };
        let mode_info = unsafe { &*mode.info };
        FramebufferInfo {
            base: mode.frame_buffer_base,
            size: mode.frame_buffer_size,
            width: mode_info.horizontal_resolution,
            height: mode_info.vertical_resolution,
            stride: mode_info.pixels_per_scan_line,
            pixel_format: mode_info.pixel_format,
        }
    } else {
        print(con_out, "Warning: no GOP framebuffer\r\n");
        FramebufferInfo {
            base: 0,
            size: 0,
            width: 0,
            height: 0,
            stride: 0,
            pixel_format: 0,
        }
    };

    print(con_out, "Exiting boot services...\r\n");

    let mut boot_info_ptr: *mut core::ffi::c_void = core::ptr::null_mut();
    let status = unsafe {
        (bs.allocate_pool)(
            efi::LOADER_DATA,
            core::mem::size_of::<BootInfo>(),
            &mut boot_info_ptr,
        )
    };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to allocate BootInfo\r\n");
        return status;
    }
    let boot_info = boot_info_ptr as *mut BootInfo;

    let mut mmap_size: usize = 0;
    let mut mmap_key: usize = 0;
    let mut desc_size: usize = 0;
    let mut desc_version: u32 = 0;

    unsafe {
        (bs.get_memory_map)(
            &mut mmap_size,
            core::ptr::null_mut(),
            &mut mmap_key,
            &mut desc_size,
            &mut desc_version,
        )
    };

    mmap_size += 2 * desc_size;
    let mut mmap_buf: *mut core::ffi::c_void = core::ptr::null_mut();
    let status = unsafe { (bs.allocate_pool)(efi::LOADER_DATA, mmap_size, &mut mmap_buf) };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to allocate memory map buffer\r\n");
        return status;
    }

    let status = unsafe {
        (bs.get_memory_map)(
            &mut mmap_size,
            mmap_buf as *mut efi::MemoryDescriptor,
            &mut mmap_key,
            &mut desc_size,
            &mut desc_version,
        )
    };
    if status != efi::Status::SUCCESS {
        print(con_out, "Failed to get memory map\r\n");
        return status;
    }

    let entry_count = mmap_size / desc_size;

    unsafe {
        (*boot_info).memory_map = MemoryMapInfo {
            entries: mmap_buf as *const u8,
            entry_count,
            entry_size: desc_size,
        };
        (*boot_info).framebuffer = framebuffer;
    }

    let status = unsafe { (bs.exit_boot_services)(image_handle, mmap_key) };
    if status != efi::Status::SUCCESS {
        loop {}
    }

    #[cfg(target_arch = "x86_64")]
    let entry: extern "sysv64" fn(*const BootInfo) -> ! =
        unsafe { core::mem::transmute(kernel_ptr) };
    #[cfg(target_arch = "aarch64")] // todo: this is probably wrong
    let entry: extern "C" fn(*const BootInfo) -> ! = unsafe { core::mem::transmute(kernel_ptr) };

    entry(boot_info);
}

fn print(con_out: &mut efi::protocols::simple_text_output::Protocol, s: &str) {
    for c in s.chars() {
        let buf = [c as u16, 0u16];
        unsafe {
            (con_out.output_string)(con_out, buf.as_ptr() as *mut efi::Char16);
        }
    }
}

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
