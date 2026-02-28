use alloc::string::String;

use crate::module::ModuleId;

#[derive(Debug, Clone)]
pub struct Unique {
    pub id: usize,
    pub module_id: ModuleId,
    pub display_name: Option<String>,
}

impl Unique {
    #[must_use] 
    pub const fn new(id: usize, module_id: ModuleId, display_name: Option<String>) -> Self {
        Self {
            id,
            module_id,
            display_name,
        }
    }

    #[must_use] 
    pub fn unnamed(id: usize, module_id: ModuleId) -> Self {
        Self {
            id,
            module_id,
            display_name: None,
        }
    }
}

impl PartialEq for Unique {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.module_id == other.module_id
    }
}

impl Eq for Unique {}

impl PartialOrd for Unique {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Unique {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match self.module_id.cmp(&other.module_id) {
            core::cmp::Ordering::Equal => self.id.cmp(&other.id),
            ord => ord,
        }
    }
}

#[derive(Debug)]
pub struct UniqueGen {
    module_id: ModuleId,
    next: usize,
}

impl UniqueGen {
    #[must_use] 
    pub fn new(module_id: ModuleId) -> Self {
        Self { module_id, next: 0 }
    }

    pub fn fresh(&mut self, name: String) -> Unique {
        let id = self.next;
        self.next += 1;
        Unique::new(id, self.module_id.clone(), Some(name))
    }

    pub fn fresh_unnamed(&mut self) -> Unique {
        let id = self.next;
        self.next += 1;
        Unique::unnamed(id, self.module_id.clone())
    }
}
