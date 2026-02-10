use crate::module::unique::Unique;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum QualifiedName {
    User(Unique),
    Intrinsic(IntrinsicName),
}

impl QualifiedName {
    pub fn display(&self) -> Option<&str> {
        match self {
            QualifiedName::User(u) => u.display_name.as_deref(),
            QualifiedName::Intrinsic(i) => Some(i.name()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntrinsicName {
    Nat,
    Str,
    Fin,
    Array,
    ArrayNil,
    ArrayCons,
}

impl IntrinsicName {
    pub fn name(&self) -> &str {
        match self {
            IntrinsicName::Nat => "Nat",
            IntrinsicName::Str => "Str",
            IntrinsicName::Fin => "Fin",
            IntrinsicName::Array => "Array",
            IntrinsicName::ArrayNil => "Array.nil",
            IntrinsicName::ArrayCons => "Array.cons",
        }
    }
}
