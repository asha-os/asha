use talc::Span;

pub fn init_heap(free_region: *mut u8, free_size: usize) {
    let span = Span::from_base_size(free_region, free_size);
    unsafe {
        runtime::ALLOCATOR.lock().claim(span).unwrap();
    }
}
