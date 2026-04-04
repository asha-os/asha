use alloc::string::String;

use crate::module::unique::Unique;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Name {
    Explicit(Unique, String),
    Anonymous(Unique),
}

impl core::fmt::Display for Name {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Name::Explicit(_, name) => write!(f, "{}", name),
            Name::Anonymous(_) => write!(f, "_"),
        }
    }
}

impl Name {
    pub fn id(&self) -> &Unique {
        match self {
            Name::Explicit(id, _) => id,
            Name::Anonymous(id) => id,
        }
    }
}
