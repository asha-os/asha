#[cfg(target_os = "windows")]
use crate::windows::{CommandLineToArgvW, GetCommandLineW, LocalFree};

#[cfg(target_os = "windows")]
pub struct Args {
    argv: *mut *mut u16,
    argc: i32,
    current: i32,
}

#[cfg(target_os = "windows")]
impl Args {
    pub fn get() -> Option<Self> {
        unsafe {
            let cmd_line = GetCommandLineW();
            if cmd_line.is_null() {
                return None;
            }

            let mut argc: i32 = 0;
            let argv = CommandLineToArgvW(cmd_line, &mut argc);
            if argv.is_null() {
                return None;
            }

            Some(Args {
                argv,
                argc,
                current: 0,
            })
        }
    }

    pub fn len(&self) -> usize {
        self.argc as usize
    }

    pub fn is_empty(&self) -> bool {
        self.argc == 0
    }
}

#[cfg(target_os = "windows")]
impl Iterator for Args {
    type Item = Arg;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current >= self.argc {
            return None;
        }

        let ptr = unsafe { *self.argv.offset(self.current as isize) };
        self.current += 1;

        Some(Arg { ptr })
    }
}

#[cfg(target_os = "windows")]
impl Drop for Args {
    fn drop(&mut self) {
        unsafe {
            LocalFree(self.argv as *mut _);
        }
    }
}

#[cfg(target_os = "windows")]
pub struct Arg {
    ptr: *mut u16,
}

#[cfg(target_os = "windows")]
impl Arg {
    pub fn len_utf16(&self) -> usize {
        let mut len = 0;
        unsafe {
            while *self.ptr.offset(len as isize) != 0 {
                len += 1;
            }
        }
        len
    }

    pub fn as_utf16(&self) -> &[u16] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len_utf16()) }
    }

    pub fn to_utf8<'a>(&self, buf: &'a mut [u8]) -> Option<&'a str> {
        let utf16 = self.as_utf16();
        let mut pos = 0;

        for &code_unit in utf16 {
            if code_unit < 0x80 {
                if pos >= buf.len() {
                    return None;
                }
                buf[pos] = code_unit as u8;
                pos += 1;
            } else if code_unit < 0x800 {
                if pos + 1 >= buf.len() {
                    return None;
                }
                buf[pos] = (0xC0 | (code_unit >> 6)) as u8;
                buf[pos + 1] = (0x80 | (code_unit & 0x3F)) as u8;
                pos += 2;
            } else {
                if pos + 2 >= buf.len() {
                    return None;
                }
                buf[pos] = (0xE0 | (code_unit >> 12)) as u8;
                buf[pos + 1] = (0x80 | ((code_unit >> 6) & 0x3F)) as u8;
                buf[pos + 2] = (0x80 | (code_unit & 0x3F)) as u8;
                pos += 3;
            }
        }

        core::str::from_utf8(&buf[..pos]).ok()
    }
}

#[cfg(not(target_os = "windows"))]
pub struct Args;

#[cfg(not(target_os = "windows"))]
impl Args {
    pub fn get() -> Option<Self> {
        None
    }
}

#[cfg(not(target_os = "windows"))]
impl Iterator for Args {
    type Item = ();
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}
