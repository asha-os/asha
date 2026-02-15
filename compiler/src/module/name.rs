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
    Bool,
    True,
    False,
    Array,
    ArrayNil,
    ArrayCons,
    IO,
    AddClass,
    AddFn,
    SubClass,
    SubFn,
    MulClass,
    MulFn,
    DivClass,
    DivFn,
    BEqClass,
    BEqFn,
    BNeqClass,
    BNeqFn,
    LtClass,
    LtFn,
    LeqClass,
    LeqFn,
    GeqClass,
    GeqFn,
    GtClass,
    GtFn,
}

impl IntrinsicName {
    pub fn name(&self) -> &str {
        match self {
            IntrinsicName::Nat => "Nat",
            IntrinsicName::Bool => "Bool",
            IntrinsicName::True => "True",
            IntrinsicName::False => "False",
            IntrinsicName::Str => "Str",
            IntrinsicName::Fin => "Fin",
            IntrinsicName::Array => "Array",
            IntrinsicName::ArrayNil => "Array.nil",
            IntrinsicName::ArrayCons => "Array.cons",
            IntrinsicName::IO => "IO",
            IntrinsicName::AddClass => "Add",
            IntrinsicName::AddFn => "add",
            IntrinsicName::SubClass => "Sub",
            IntrinsicName::SubFn => "sub",
            IntrinsicName::MulClass => "Mul",
            IntrinsicName::MulFn => "mul",
            IntrinsicName::DivClass => "Div",
            IntrinsicName::DivFn => "div",
            IntrinsicName::BEqClass => "BEq",
            IntrinsicName::BEqFn => "beq",
            IntrinsicName::BNeqClass => "BNeq",
            IntrinsicName::BNeqFn => "bneq",
            IntrinsicName::LtClass => "Lt",
            IntrinsicName::LtFn => "lt",
            IntrinsicName::LeqClass => "Leq",
            IntrinsicName::LeqFn => "leq",
            IntrinsicName::GeqClass => "Geq",
            IntrinsicName::GeqFn => "geq",
            IntrinsicName::GtClass => "Gt",
            IntrinsicName::GtFn => "gt",
        }
    }
}
