use alloc::vec::Vec;

use crate::module::name::Name;

#[derive(Debug, Clone)]
pub struct InductiveMetadata {
    pub name: Name,
    pub num_params: usize,
    pub num_indices: usize,
    pub constructors: Vec<Name>,
    pub match_fn: Name,
    pub is_recursive: bool,
}
