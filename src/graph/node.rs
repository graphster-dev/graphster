use super::edge::EdgeIndex;
use crate::{
    datatypes::{AttributeKey, Attributes},
    from_marker::{FromMarker, IntoMarker},
    ref_wrapper::RefWrapper,
};
use std::{collections::HashSet, fmt::Display};

/// A wrapper around `AttributeKey` that represents the index of a node in a graph.
///
/// The `NodeIndex` struct is used to uniquely identify nodes within a graph.
/// It provides conversions from various types into `NodeIndex` for convenience.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::*;
///
/// let index: NodeIndex = "node1".into();
/// let key = AttributeKey::String("node1".to_string());
/// assert_eq!(index, NodeIndex::from("node1"));
/// assert_eq!(index, NodeIndex::from(key));
/// ```
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(transparent)]
pub struct NodeIndex(pub AttributeKey);

impl<T: Into<AttributeKey>> From<T> for NodeIndex {
    fn from(value: T) -> Self {
        Self(value.into())
    }
}

impl<T: IntoMarker<AttributeKey>> FromMarker<T> for NodeIndex {}
impl FromMarker<AttributeKey> for NodeIndex {}

impl Display for NodeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NodeIndex({})", self.0)
    }
}

pub type NodeIndexRef<'a> = RefWrapper<'a, NodeIndex>;

impl<'a, T: Into<NodeIndex> + IntoMarker<NodeIndex>> From<T> for NodeIndexRef<'a> {
    fn from(value: T) -> Self {
        Self::Owned(value.into())
    }
}

pub struct NodeIndices<'a>(Box<dyn Iterator<Item = &'a NodeIndex> + 'a>);

impl<'a> Iterator for NodeIndices<'a> {
    type Item = &'a NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub(crate) trait IntoNodeIndices<'a> {
    fn into_node_indices(self) -> NodeIndices<'a>;
}

impl<'a, T> IntoNodeIndices<'a> for T
where
    T: Iterator<Item = &'a NodeIndex> + 'a,
{
    fn into_node_indices(self) -> NodeIndices<'a> {
        NodeIndices(Box::new(self))
    }
}

/// Represents a node in a graph with optional attributes and connections to other nodes.
///
/// The `Node` struct contains sets of incoming and outgoing edges, as well as a collection
/// of attributes associated with the node.
#[derive(Debug, Clone)]
pub struct Node {
    pub incoming_edges: HashSet<EdgeIndex>,
    pub outgoing_edges: HashSet<EdgeIndex>,
    pub attributes: Attributes,
}

impl Node {
    pub(crate) fn new(attributes: Attributes) -> Self {
        Node {
            incoming_edges: HashSet::new(),
            outgoing_edges: HashSet::new(),
            attributes,
        }
    }
}

impl From<Attributes> for Node {
    fn from(value: Attributes) -> Self {
        Self::new(value)
    }
}

pub type NodeTuple = (NodeIndex, Attributes);

pub trait IntoNodeTuple {
    fn into_node_tuple(self) -> NodeTuple;
}

impl<N: Into<NodeIndex>, A: Into<Attributes>> IntoNodeTuple for (N, A) {
    fn into_node_tuple(self) -> NodeTuple {
        (self.0.into(), self.1.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_node_index_from() {
        // Testing with one AttributeKey type should be enough
        assert_eq!(
            NodeIndex::from(false),
            NodeIndex(AttributeKey::Boolean(false))
        );
    }

    #[test]
    fn test_node_index_display() {
        // Testing with one AttributeKey type should be enough
        assert_eq!(format!("{}", NodeIndex::from(false)), "NodeIndex(false)");
    }

    #[test]
    fn test_node_index_ref_from() {
        // Testing with one AttributeKey type should be enough
        assert_eq!(
            NodeIndexRef::from(false),
            NodeIndexRef::Owned(NodeIndex::from(false))
        );
    }

    #[test]
    fn test_node_new() {
        let attributes = Attributes::new();
        let node = Node::new(attributes.clone());
        assert_eq!(node.incoming_edges, HashSet::new());
        assert_eq!(node.outgoing_edges, HashSet::new());
        assert_eq!(node.attributes, attributes);
    }

    #[test]
    fn test_node_from() {
        let attributes = Attributes::new();
        let node = Node::from(attributes.clone());
        assert_eq!(node.incoming_edges, HashSet::new());
        assert_eq!(node.outgoing_edges, HashSet::new());
        assert_eq!(node.attributes, attributes);
    }

    #[test]
    fn test_into_node_tuple() {
        let index: NodeIndex = 0.into();
        let attributes = Attributes::new();
        let tuple = (index.clone(), attributes.clone()).into_node_tuple();
        assert_eq!(tuple.0, index);
        assert_eq!(tuple.1, attributes);
    }
}
