#![no_std]

pub mod io;

use core::panic::PanicInfo;

pub fn abort(_info: &PanicInfo) -> ! {
    #[cfg(target_os = "windows")]
    unsafe {
        windows::ExitProcess(1);
    }

    #[cfg(not(target_os = "windows"))]
    loop {}
}

#[cfg(target_os = "windows")]
pub(crate) mod windows {
    use core::ffi::c_void;

    pub type HANDLE = *mut c_void;
    pub type DWORD = u32;
    pub type BOOL = i32;

    pub const STD_OUTPUT_HANDLE: DWORD = -11i32 as DWORD;
    pub const INVALID_HANDLE_VALUE: HANDLE = -1isize as HANDLE;
    pub const GENERIC_READ: DWORD = 0x80000000;
    pub const OPEN_EXISTING: DWORD = 3;
    pub const PAGE_READONLY: DWORD = 0x02;
    pub const FILE_MAP_READ: DWORD = 0x04;

    unsafe extern "system" {
        pub fn GetStdHandle(nStdHandle: DWORD) -> HANDLE;
        pub fn WriteConsoleW(
            hConsoleOutput: HANDLE,
            lpBuffer: *const u16,
            nNumberOfCharsToWrite: DWORD,
            lpNumberOfCharsWritten: *mut DWORD,
            lpReserved: *mut c_void,
        ) -> BOOL;
        pub fn ExitProcess(uExitCode: u32) -> !;
        pub fn CreateFileA(
            lpFileName: *const u8,
            dwDesiredAccess: DWORD,
            dwShareMode: DWORD,
            lpSecurityAttributes: *mut c_void,
            dwCreationDisposition: DWORD,
            dwFlagsAndAttributes: DWORD,
            hTemplateFile: *mut c_void,
        ) -> HANDLE;
        pub fn ReadFile(
            hFile: HANDLE,
            lpBuffer: *mut u8,
            nNumberOfBytesToRead: DWORD,
            lpNumberOfBytesRead: *mut DWORD,
            lpOverlapped: *mut c_void,
        ) -> BOOL;
        pub fn CloseHandle(hObject: HANDLE) -> BOOL;
        pub fn GetFileSizeEx(hFile: HANDLE, lpFileSize: *mut i64) -> BOOL;
        pub fn CreateFileMappingA(
            hFile: HANDLE,
            lpFileMappingAttributes: *mut c_void,
            flProtect: DWORD,
            dwMaximumSizeHigh: DWORD,
            dwMaximumSizeLow: DWORD,
            lpName: *const u8,
        ) -> HANDLE;
        pub fn MapViewOfFile(
            hFileMappingObject: HANDLE,
            dwDesiredAccess: DWORD,
            dwFileOffsetHigh: DWORD,
            dwFileOffsetLow: DWORD,
            dwNumberOfBytesToMap: usize,
        ) -> *mut c_void;
        pub fn UnmapViewOfFile(lpBaseAddress: *const c_void) -> BOOL;
        pub fn GetCommandLineW() -> *const u16;
        pub fn CommandLineToArgvW(lpCmdLine: *const u16, pNumArgs: *mut i32) -> *mut *mut u16;
        pub fn LocalFree(hMem: *mut c_void) -> *mut c_void;
    }

    pub fn write_stdout(s: &[u8]) {
        unsafe {
            let handle = GetStdHandle(STD_OUTPUT_HANDLE);
            let mut written: DWORD = 0;

            let str = core::str::from_utf8_unchecked(s);
            let mut buf = [0u16; 1024];
            let mut pos = 0;

            for ch in str.chars() {
                let mut tmp = [0u16; 2];
                let encoded = ch.encode_utf16(&mut tmp);
                for &unit in encoded.iter() {
                    if pos >= buf.len() {
                        WriteConsoleW(
                            handle,
                            buf.as_ptr(),
                            pos as DWORD,
                            &mut written,
                            core::ptr::null_mut(),
                        );
                        pos = 0;
                    }
                    buf[pos] = unit;
                    pos += 1;
                }
            }

            if pos > 0 {
                WriteConsoleW(
                    handle,
                    buf.as_ptr(),
                    pos as DWORD,
                    &mut written,
                    core::ptr::null_mut(),
                );
            }
        }
    }
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => ({
        $crate::io::stdout::print(format_args!($($arg)*));
    })
}

#[macro_export]
macro_rules! println {
    () => ($crate::print!("\n"));
    ($($arg:tt)*) => ({
        $crate::io::stdout::print(format_args!($($arg)*));
        $crate::io::stdout::print(format_args!("\n"));
    })
}
