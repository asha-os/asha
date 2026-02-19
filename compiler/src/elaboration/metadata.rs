use alloc::vec::Vec;

use crate::module::name::QualifiedName;

#[derive(Debug, Clone)]
pub struct InductiveMetadata {
    pub name: QualifiedName,
    pub num_params: usize,
    pub num_indices: usize,
    pub constructors: Vec<QualifiedName>,
    pub match_fn: QualifiedName,
    pub is_recursive: bool,
}
