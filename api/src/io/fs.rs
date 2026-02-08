#[cfg(target_os = "windows")]
use core::ptr;

#[cfg(target_os = "windows")]
use crate::windows::{
    CloseHandle, CreateFileA, CreateFileMappingA, FILE_MAP_READ, GENERIC_READ, GetFileSizeEx,
    HANDLE, INVALID_HANDLE_VALUE, MapViewOfFile, OPEN_EXISTING, PAGE_READONLY, UnmapViewOfFile,
};

pub struct MappedFile {
    #[cfg(target_os = "windows")]
    file_handle: HANDLE,
    #[cfg(target_os = "windows")]
    mapping_handle: HANDLE,
    #[cfg(target_os = "windows")]
    ptr: *const u8,
    #[cfg(target_os = "windows")]
    len: usize,
}

impl MappedFile {
    #[cfg(target_os = "windows")]
    pub fn open(path: &str) -> Option<Self> {
        let mut path_buf = [0u8; 260];
        if path.len() >= path_buf.len() {
            return None;
        }
        path_buf[..path.len()].copy_from_slice(path.as_bytes());
        path_buf[path.len()] = 0;

        unsafe {
            let file_handle = CreateFileA(
                path_buf.as_ptr(),
                GENERIC_READ,
                1,
                ptr::null_mut(),
                OPEN_EXISTING,
                0,
                ptr::null_mut(),
            );

            if file_handle == INVALID_HANDLE_VALUE {
                return None;
            }

            let mut size: i64 = 0;
            if GetFileSizeEx(file_handle, &mut size) == 0 {
                CloseHandle(file_handle);
                return None;
            }

            let len = size as usize;
            if len == 0 {
                CloseHandle(file_handle);
                return Some(MappedFile {
                    file_handle: ptr::null_mut(),
                    mapping_handle: ptr::null_mut(),
                    ptr: ptr::null(),
                    len: 0,
                });
            }

            let mapping_handle = CreateFileMappingA(
                file_handle,
                ptr::null_mut(),
                PAGE_READONLY,
                0,
                0,
                ptr::null(),
            );

            if mapping_handle.is_null() {
                CloseHandle(file_handle);
                return None;
            }

            let ptr = MapViewOfFile(mapping_handle, FILE_MAP_READ, 0, 0, 0);

            if ptr.is_null() {
                CloseHandle(mapping_handle);
                CloseHandle(file_handle);
                return None;
            }

            Some(MappedFile {
                file_handle,
                mapping_handle,
                ptr: ptr as *const u8,
                len,
            })
        }
    }

    #[cfg(not(target_os = "windows"))]
    pub fn open(_path: &str) -> Option<Self> {
        None
    }

    #[cfg(target_os = "windows")]
    pub fn as_bytes(&self) -> &[u8] {
        if self.ptr.is_null() {
            &[]
        } else {
            unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
        }
    }

    #[cfg(not(target_os = "windows"))]
    pub fn as_bytes(&self) -> &[u8] {
        &[]
    }

    pub fn as_str(&self) -> Option<&str> {
        core::str::from_utf8(self.as_bytes()).ok()
    }

    pub fn len(&self) -> usize {
        #[cfg(target_os = "windows")]
        return self.len;
        #[cfg(not(target_os = "windows"))]
        return 0;
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(target_os = "windows")]
impl Drop for MappedFile {
    fn drop(&mut self) {
        unsafe {
            if !self.ptr.is_null() {
                UnmapViewOfFile(self.ptr as *const _);
            }
            if !self.mapping_handle.is_null() {
                CloseHandle(self.mapping_handle);
            }
            if !self.file_handle.is_null() {
                CloseHandle(self.file_handle);
            }
        }
    }
}
