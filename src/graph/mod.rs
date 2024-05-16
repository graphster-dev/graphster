mod edge;
mod node;

use crate::{datatypes::Attributes, GraphsterError};
use edge::{Edge, EdgeIndex};
use node::{Node, NodeIndex};
use std::{collections::HashMap, sync::atomic::AtomicUsize};

pub struct DataGraph {
    nodes: HashMap<NodeIndex, Node>,
    edges: HashMap<usize, Edge>,
    edge_index_counter: AtomicUsize,
}

impl DataGraph {
    pub fn new() -> Self {
        DataGraph {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            edge_index_counter: AtomicUsize::new(0),
        }
    }

    pub fn add_node(&mut self, index: impl Into<NodeIndex>, attributes: impl Into<Attributes>) {
        let node = Node::new(attributes.into());

        self.nodes.insert(index.into(), node);
    }

    pub fn add_edge(
        &mut self,
        source_index: impl Into<NodeIndex>,
        target_index: impl Into<NodeIndex>,
        attributes: impl Into<Attributes>,
    ) -> Result<EdgeIndex, GraphsterError> {
        let edge_index = self
            .edge_index_counter
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);

        let source_index = source_index.into();
        let target_index = target_index.into();

        let source_node = self
            .nodes
            .get_mut(&source_index)
            .ok_or(GraphsterError::NodeNotFound(format!(
                "Node with index {:?} not found",
                source_index
            )))?;
        source_node.outgoing_edges.insert(edge_index);

        let target_node = self
            .nodes
            .get_mut(&target_index)
            .ok_or(GraphsterError::NodeNotFound(format!(
                "Node with index {:?} not found",
                target_index,
            )))?;
        target_node.incoming_edges.insert(edge_index);

        let edge = Edge::new(source_index, target_index.into(), attributes.into());

        self.edges.insert(edge_index, edge);

        Ok(edge_index)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_add_node() {
        let mut graph = DataGraph::new();

        graph.add_node(0, Attributes::new());

        assert_eq!(graph.nodes.len(), 1);
    }

    #[test]
    fn test_add_edge() {
        let mut graph = DataGraph::new();

        graph.add_node(0, Attributes::new());
        graph.add_node(1, Attributes::new());

        graph.add_edge(0, 1, Attributes::new()).unwrap();

        assert_eq!(graph.edges.len(), 1);
    }
}
