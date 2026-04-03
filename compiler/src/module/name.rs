use alloc::string::String;

use crate::module::unique::Unique;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Name {
    pub id: Unique,
    pub name: String,
}

impl Name {
    pub fn new(id: Unique, name: String) -> Self {
        Self { id, name }
    }
}
