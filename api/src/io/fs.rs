#[cfg(not(target_os = "asha"))]
pub struct MappedFile {
    data: Vec<u8>,
}

#[cfg(not(target_os = "asha"))]
impl MappedFile {
    pub fn open(path: &str) -> Option<Self> {
        let data = std::fs::read(path).ok()?;
        Some(MappedFile { data })
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    pub fn as_str(&self) -> Option<&str> {
        core::str::from_utf8(&self.data).ok()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

#[cfg(target_os = "asha")]
pub struct MappedFile;

#[cfg(target_os = "asha")]
impl MappedFile {
    pub fn open(_path: &str) -> Option<Self> {
        None
    }

    pub fn as_bytes(&self) -> &[u8] {
        &[]
    }

    pub fn as_str(&self) -> Option<&str> {
        None
    }

    pub fn len(&self) -> usize {
        0
    }

    pub fn is_empty(&self) -> bool {
        true
    }
}
