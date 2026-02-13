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
    IO,
    HAdd,
    Add,
    HSub,
    Sub,
    HMul,
    Mul,
    HDiv,
    Div,
    BEq,
    Eq,
    BNeq,
    Neq,
    HLt,
    Lt,
    HLeq,
    Leq,
    HGeq,
    Geq,
    HGt,
    Gt,
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
            IntrinsicName::IO => "IO",
            IntrinsicName::HAdd => "HAdd",
            IntrinsicName::HSub => "HSub",
            IntrinsicName::HMul => "HMul",
            IntrinsicName::HDiv => "HDiv",
            IntrinsicName::BEq => "BEq",
            IntrinsicName::BNeq => "BNeq",
            IntrinsicName::HLt => "HLt",
            IntrinsicName::HLeq => "HLeq",
            IntrinsicName::HGeq => "HGeq",
            IntrinsicName::HGt => "HGt",
            IntrinsicName::Add => "add",
            IntrinsicName::Sub => "sub",
            IntrinsicName::Mul => "mul",
            IntrinsicName::Div => "div",
            IntrinsicName::Eq => "eq",
            IntrinsicName::Neq => "neq",
            IntrinsicName::Lt => "lt",
            IntrinsicName::Leq => "leq",
            IntrinsicName::Geq => "geq",
            IntrinsicName::Gt => "gt",
        }
    }
}
