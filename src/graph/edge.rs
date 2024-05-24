use super::node::NodeIndex;
use crate::{datatypes::Attributes, ref_wrapper::RefWrapper};
use std::{collections::hash_set, fmt::Display, iter};

/// A wrapper around `usize` that represents the index of an edge in a graph.
///
/// The `EdgeIndex` struct is used to uniquely identify edges within a graph.
/// It provides conversions to and from `usize` for convenience.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::EdgeIndex;
///
/// let index: EdgeIndex = 1.into();
/// let usize_index: usize = index.into();
///
/// assert_eq!(index, EdgeIndex::from(1));
/// assert_eq!(usize_index, 1);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[repr(transparent)]
pub struct EdgeIndex(pub usize);

impl From<usize> for EdgeIndex {
    fn from(value: usize) -> Self {
        Self(value)
    }
}

impl From<EdgeIndex> for usize {
    fn from(value: EdgeIndex) -> Self {
        value.0
    }
}

impl Display for EdgeIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "EdgeIndex({})", self.0)
    }
}

pub type EdgeIndexRef<'a> = RefWrapper<'a, EdgeIndex>;

impl<'a> From<usize> for EdgeIndexRef<'a> {
    fn from(value: usize) -> Self {
        EdgeIndexRef::Owned(value.into())
    }
}

pub enum EdgeDirection {
    Incoming,
    Outgoing,
    Any,
}

impl Default for EdgeDirection {
    fn default() -> Self {
        Self::Any
    }
}

pub enum EdgeIndices<'a> {
    Iter(hash_set::Iter<'a, EdgeIndex>),
    Chain(iter::Chain<hash_set::Iter<'a, EdgeIndex>, hash_set::Iter<'a, EdgeIndex>>),
}

impl<'a> Iterator for EdgeIndices<'a> {
    type Item = &'a EdgeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            EdgeIndices::Iter(iter) => iter.next(),
            EdgeIndices::Chain(iter) => iter.next(),
        }
    }
}

impl<'a> From<hash_set::Iter<'a, EdgeIndex>> for EdgeIndices<'a> {
    fn from(value: hash_set::Iter<'a, EdgeIndex>) -> Self {
        Self::Iter(value)
    }
}

impl<'a> From<iter::Chain<hash_set::Iter<'a, EdgeIndex>, hash_set::Iter<'a, EdgeIndex>>>
    for EdgeIndices<'a>
{
    fn from(
        value: iter::Chain<hash_set::Iter<'a, EdgeIndex>, hash_set::Iter<'a, EdgeIndex>>,
    ) -> Self {
        Self::Chain(value)
    }
}

/// Represents an edge in a graph, connecting two nodes with optional attributes.
///
/// The `Edge` struct contains indices of the source and target nodes, as well as a collection
/// of attributes associated with the edge.
/// ```
#[derive(Debug, Clone)]
pub struct Edge {
    pub source_index: NodeIndex,
    pub target_index: NodeIndex,
    pub attributes: Attributes,
}

impl Edge {
    pub(crate) fn new(
        source_index: NodeIndex,
        target_index: NodeIndex,
        attributes: Attributes,
    ) -> Self {
        Edge {
            source_index,
            target_index,
            attributes,
        }
    }
}

impl<N1: Into<NodeIndex>, N2: Into<NodeIndex>, A: Into<Attributes>> From<(N1, N2, A)> for Edge {
    fn from(value: (N1, N2, A)) -> Self {
        Self::new(value.0.into(), value.1.into(), value.2.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_edge_index_from() {
        assert_eq!(EdgeIndex::from(0_usize), EdgeIndex(0_usize));
        assert_eq!(usize::from(EdgeIndex(0_usize)), 0_usize);
    }

    #[test]
    fn test_edge_index_display() {
        assert_eq!(format!("{}", EdgeIndex(0_usize)), "EdgeIndex(0)");
    }

    #[test]
    fn test_edge_index_ref_from() {
        assert_eq!(
            EdgeIndexRef::from(0_usize),
            EdgeIndexRef::Owned(EdgeIndex(0_usize))
        );
    }

    #[test]
    fn test_edge_new() {
        let source_index: NodeIndex = 0.into();
        let target_index: NodeIndex = 1.into();
        let attributes = Attributes::new();
        let edge = Edge::new(
            source_index.clone(),
            target_index.clone(),
            attributes.clone(),
        );

        assert_eq!(edge.source_index, source_index);
        assert_eq!(edge.target_index, target_index);
        assert_eq!(edge.attributes, attributes);
    }

    #[test]
    fn test_edge_from() {
        let source_index: NodeIndex = 0.into();
        let target_index: NodeIndex = 1.into();
        let attributes = Attributes::new();
        let edge = Edge::from((
            source_index.clone(),
            target_index.clone(),
            attributes.clone(),
        ));

        assert_eq!(edge.source_index, source_index);
        assert_eq!(edge.target_index, target_index);
        assert_eq!(edge.attributes, attributes);
    }
}
