use super::node::NodeIndex;
use crate::datatypes::Attributes;

pub type EdgeIndex = usize;

#[derive(Debug, Clone)]
pub struct Edge {
    pub source_index: NodeIndex,
    pub target_index: NodeIndex,
    pub attributes: Attributes,
}

impl Edge {
    pub fn new(source_index: NodeIndex, target_index: NodeIndex, attributes: Attributes) -> Self {
        Edge {
            source_index,
            target_index,
            attributes,
        }
    }
}
