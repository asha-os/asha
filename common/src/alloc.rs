use core::alloc::{GlobalAlloc, Layout};

pub struct Allocator;

impl Allocator {
    pub const fn new() -> Self {
        Self
    }
}

unsafe impl GlobalAlloc for Allocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { alloc_impl(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { dealloc_impl(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        unsafe { realloc_impl(ptr, layout, new_size) }
    }
}

#[cfg(target_os = "windows")]
mod windows {
    use core::alloc::Layout;
    use core::ffi::c_void;

    type HANDLE = *mut c_void;
    type DWORD = u32;

    unsafe extern "system" {
        fn GetProcessHeap() -> HANDLE;
        fn HeapAlloc(hHeap: HANDLE, dwFlags: DWORD, dwBytes: usize) -> *mut c_void;
        fn HeapReAlloc(
            hHeap: HANDLE,
            dwFlags: DWORD,
            lpMem: *mut c_void,
            dwBytes: usize,
        ) -> *mut c_void;
        fn HeapFree(hHeap: HANDLE, dwFlags: DWORD, lpMem: *mut c_void) -> i32;
    }

    pub unsafe fn alloc_impl(layout: Layout) -> *mut u8 {
        let heap = unsafe { GetProcessHeap() };
        if heap.is_null() {
            return core::ptr::null_mut();
        }

        let size = layout.size();
        let align = layout.align();

        if align <= 8 {
            unsafe { HeapAlloc(heap, 0, size) as *mut u8 }
        } else {
            let total = size + align + core::mem::size_of::<*mut u8>();
            let raw = unsafe { HeapAlloc(heap, 0, total) as *mut u8 };
            if raw.is_null() {
                return core::ptr::null_mut();
            }

            let raw_addr = raw as usize;
            let aligned_addr =
                (raw_addr + core::mem::size_of::<*mut u8>() + align - 1) & !(align - 1);
            let aligned = aligned_addr as *mut u8;

            unsafe {
                let ptr_storage = (aligned as *mut *mut u8).sub(1);
                *ptr_storage = raw;
            }

            aligned
        }
    }

    pub unsafe fn dealloc_impl(ptr: *mut u8, layout: Layout) {
        let heap = unsafe { GetProcessHeap() };
        if heap.is_null() || ptr.is_null() {
            return;
        }

        let align = layout.align();

        let raw = if align <= 8 {
            ptr
        } else {
            unsafe {
                let ptr_storage = (ptr as *mut *mut u8).sub(1);
                *ptr_storage
            }
        };

        unsafe { HeapFree(heap, 0, raw as *mut c_void) };
    }

    pub unsafe fn realloc_impl(ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let align = layout.align();

        if align > 8 {
            let new_layout = match Layout::from_size_align(new_size, align) {
                Ok(l) => l,
                Err(_) => return core::ptr::null_mut(),
            };
            let new_ptr = unsafe { alloc_impl(new_layout) };
            if !new_ptr.is_null() {
                let copy_size = if layout.size() < new_size {
                    layout.size()
                } else {
                    new_size
                };
                unsafe { core::ptr::copy_nonoverlapping(ptr, new_ptr, copy_size) };
                unsafe { dealloc_impl(ptr, layout) };
            }
            return new_ptr;
        }

        let heap = unsafe { GetProcessHeap() };
        if heap.is_null() {
            return core::ptr::null_mut();
        }

        unsafe { HeapReAlloc(heap, 0, ptr as *mut c_void, new_size) as *mut u8 }
    }
}

#[cfg(target_os = "windows")]
use windows::{alloc_impl, dealloc_impl, realloc_impl};

#[cfg(not(target_os = "windows"))]
unsafe fn alloc_impl(_layout: Layout) -> *mut u8 {
    core::ptr::null_mut()
}

#[cfg(not(target_os = "windows"))]
unsafe fn dealloc_impl(_ptr: *mut u8, _layout: Layout) {}

#[cfg(not(target_os = "windows"))]
unsafe fn realloc_impl(_ptr: *mut u8, _layout: Layout, _new_size: usize) -> *mut u8 {
    core::ptr::null_mut()
}
