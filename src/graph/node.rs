use super::edge::EdgeIndex;
use crate::datatypes::{AttributeKey, Attributes};
use std::collections::HashSet;

pub type NodeIndex = AttributeKey;

#[derive(Debug, Clone)]
pub struct Node {
    pub incoming_edges: HashSet<EdgeIndex>,
    pub outgoing_edges: HashSet<EdgeIndex>,
    pub attributes: Attributes,
}

impl Node {
    pub fn new(attributes: Attributes) -> Self {
        Node {
            incoming_edges: HashSet::new(),
            outgoing_edges: HashSet::new(),
            attributes,
        }
    }
}
