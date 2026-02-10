use crate::module::name::{IntrinsicName, QualifiedName};

pub const PRIM_NAT: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::Nat);
pub const PRIM_FIN: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::Fin);
pub const PRIM_STRING: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::Str);
pub const PRIM_ARRAY: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::Array);
pub const PRIM_ARRAY_NIL: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::ArrayNil);
pub const PRIM_ARRAY_CONS: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::ArrayCons);
pub const PRIM_IO: QualifiedName = QualifiedName::Intrinsic(IntrinsicName::IO);