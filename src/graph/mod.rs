mod edge;
mod node;
#[cfg(feature = "polars")]
#[cfg_attr(docsrs, doc(cfg(feature = "polars")))]
mod polars;

#[cfg(feature = "polars")]
pub use self::polars::{EdgesDataFrame, NodesDataFrame};
pub use self::{
    edge::{EdgeDirection, EdgeIndex},
    node::NodeIndex,
};
use crate::{
    errors::{GraphsterError, GraphsterResult},
    prelude::Attributes,
};
use edge::{Edge, EdgeIndexRef, EdgeIndices};
use itertools::Itertools;
use node::{IntoNodeIndices, IntoNodeTuple, Node, NodeIndexRef, NodeIndices};
use rayon::prelude::*;
use std::{collections::HashMap, sync::atomic::AtomicUsize};

/// A graph data structure that supports rapid data manipulation, analysis, and processing.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::*;
/// use std::collections::HashMap;
///
/// let mut graph = DataGraph::new();
///
/// // Add a node with an index of 0 and some attributes
/// graph.add_node(0, Attributes::from([("foo", "bar")])).unwrap();
///
/// // Add another node with an index of 1
/// graph.add_node(1, HashMap::from([("bar", "foo")])).unwrap();
///
/// // Add an edge between node 0 and node 1
/// graph.add_edge(0, 1, Attributes::from([("foo", "bar")])).unwrap();
///
/// // Get the number of nodes in the graph
/// let node_count = graph.node_count();
/// assert_eq!(node_count, 2);
///
/// // Get the number of edges in the graph
/// let edge_count = graph.edge_count();
/// assert_eq!(edge_count, 1);
/// ```
#[derive(Debug)]
pub struct DataGraph {
    nodes: HashMap<NodeIndex, Node>,
    edges: HashMap<EdgeIndex, Edge>,
    edge_index_counter: AtomicUsize,
}

impl DataGraph {
    /// Creates a new empty graph.
    ///
    /// Returns a new `DataGraph` instance with no nodes or edges.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let graph = DataGraph::new();
    ///
    /// assert_eq!(graph.node_count(), 0);
    /// assert_eq!(graph.edge_count(), 0);
    /// ```
    pub fn new() -> Self {
        DataGraph {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            edge_index_counter: AtomicUsize::new(0),
        }
    }

    /// Creates a new graph from an iterator of nodes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let nodes = vec![
    ///     (0, Attributes::from([("foo", "bar")])),
    ///     (1, Attributes::from([("bar", "foo")])),
    /// ];
    /// let graph = DataGraph::from_nodes(nodes);
    ///
    /// assert_eq!(graph.node_count(), 2);
    /// assert_eq!(graph.edge_count(), 0);
    /// ```
    pub fn from_nodes<N, T>(nodes: N) -> Self
    where
        N: IntoParallelIterator<Item = T>,
        T: IntoNodeTuple,
    {
        let nodes = nodes
            .into_par_iter()
            .map(|node| {
                let node = node.into_node_tuple();

                (node.0, node.1.into())
            })
            .collect::<HashMap<NodeIndex, Node>>();

        DataGraph {
            nodes,
            edges: HashMap::new(),
            edge_index_counter: AtomicUsize::new(0),
        }
    }

    /// Creates a new graph from an iterator of nodes and an iterator of edges.
    ///
    /// This function returns a `GraphsterResult` because it can fail if a source or target node
    /// referenced in an edge doesn't exist in the provided nodes iterator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let nodes = vec![
    ///     (0, Attributes::from([("foo", "bar")])),
    ///     (1, Attributes::from([("bar", "foo")])),
    /// ];
    /// let edges = vec![(0, 1, Attributes::from([("foo", "bar")]))];
    ///
    /// let graph = DataGraph::from_nodes_and_edges(nodes, edges).unwrap();
    ///
    /// assert_eq!(graph.node_count(), 2);
    /// assert_eq!(graph.edge_count(), 1);
    /// ```
    pub fn from_nodes_and_edges<N, NT, E, ET>(nodes: N, edges: E) -> GraphsterResult<Self>
    where
        N: IntoParallelIterator<Item = NT>,
        NT: IntoNodeTuple,
        E: IntoParallelIterator<Item = ET>,
        ET: Into<Edge>,
    {
        let nodes_mapping = nodes
            .into_par_iter()
            .map(|node| {
                let node = node.into_node_tuple();

                (node.0, node.1.into())
            })
            .collect::<HashMap<NodeIndex, Node>>();

        let edge_index_counter = AtomicUsize::new(0);

        let edges = edges
            .into_par_iter()
            .map(|edge| {
                let edge = edge.into();

                if !nodes_mapping.contains_key(&edge.source_index) {
                    return Err(GraphsterError::NodeNotFound {
                        node_index: edge.source_index,
                    });
                }

                if !nodes_mapping.contains_key(&edge.target_index) {
                    return Err(GraphsterError::NodeNotFound {
                        node_index: edge.target_index,
                    });
                }

                let edge_index = edge_index_counter
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    .into();

                Ok((edge_index, edge))
            })
            .collect::<GraphsterResult<_>>()?;

        Ok(DataGraph {
            nodes: nodes_mapping,
            edges,
            edge_index_counter,
        })
    }

    /// Adds a new node to the graph with the specified index and attributes.
    ///
    /// If a node with the same index already exists in the graph, this function returns
    /// an error of type `GraphsterError::NodeAlreadyExists`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// graph.add_node(0, Attributes::from([("foo", "bar")])).unwrap();
    /// graph.add_node(1, HashMap::from([("bar", "foo")])).unwrap();
    ///
    /// // Trying to add another node with the same index will fail
    /// assert!(graph.add_node(0, Attributes::new()).is_err());
    ///
    /// assert_eq!(graph.node_count(), 2);
    /// ```
    pub fn add_node<I: Into<NodeIndex>, A: Into<Attributes>>(
        &mut self,
        node_index: I,
        attributes: A,
    ) -> GraphsterResult<()> {
        let node_index = node_index.into();

        if self.nodes.contains_key(&node_index) {
            return Err(GraphsterError::NodeAlreadyExists { node_index });
        }

        self.nodes.insert(node_index, attributes.into().into());

        Ok(())
    }

    /// Adds multiple nodes to the graph from an iterator.
    ///
    /// If a node with the same index already exists in the graph, this function returns
    /// an error of type `GraphsterError::NodeAlreadyExists`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![
    ///     (0, Attributes::from([("foo", "bar")])),
    ///     (1, Attributes::from([("bar", "foo")])),
    /// ];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// // Trying to add the same nodes again will fail
    /// assert!(graph.add_nodes(nodes).is_err());
    /// ```
    pub fn add_nodes<N, T>(&mut self, nodes: N) -> GraphsterResult<()>
    where
        N: IntoParallelIterator<Item = T>,
        T: IntoNodeTuple,
    {
        let nodes = nodes
            .into_par_iter()
            .map(|node| {
                let (node_index, attributes) = node.into_node_tuple();

                if self.nodes.contains_key(&node_index) {
                    return Err(GraphsterError::NodeAlreadyExists { node_index });
                }

                Ok((node_index, attributes.into()))
            })
            .collect::<GraphsterResult<Vec<(NodeIndex, Node)>>>()?;

        self.nodes.extend(nodes);

        Ok(())
    }

    /// Adds a new edge to the graph between the specified source and target nodes.
    ///
    /// If either the source or target node doesn't exist in the graph, this function returns
    /// an error of type `GraphsterError::NodeNotFound`.
    ///
    /// This function returns a `Result` containing the newly created edge's index on success
    /// or a `GraphsterError` on failure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// graph.add_node(0, Attributes::new()).unwrap();
    /// graph.add_node(1, Attributes::new()).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::from([("foo", "bar")])).unwrap();
    /// let second_edge_index = graph.add_edge(0, 1, HashMap::from([("foo", "bar")])).unwrap();
    /// assert_eq!(graph.edge_count(), 2);
    /// ```
    pub fn add_edge<NS: Into<NodeIndex>, NT: Into<NodeIndex>, A: Into<Attributes>>(
        &mut self,
        source_index: NS,
        target_index: NT,
        attributes: A,
    ) -> Result<EdgeIndex, GraphsterError> {
        let edge_index = self
            .edge_index_counter
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            .into();

        let source_index = source_index.into();
        let target_index = target_index.into();

        let source_node =
            self.nodes
                .get_mut(&source_index)
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: source_index.clone(),
                })?;
        source_node.outgoing_edges.insert(edge_index);

        let target_node =
            self.nodes
                .get_mut(&target_index)
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: target_index.clone(),
                })?;
        target_node.incoming_edges.insert(edge_index);

        let edge = (source_index, target_index, attributes).into();

        self.edges.insert(edge_index, edge);

        Ok(edge_index)
    }

    /// Adds multiple edges to the graph from an iterator.
    ///
    /// If a source or target node referenced in an edge doesn't exist in the graph,
    /// this function returns a `GraphsterResult` containing a `GraphsterError::NodeNotFound` error.
    ///
    /// This function returns a `GraphsterResult` containing a vector of indices for the added edges
    /// on success or a `GraphsterError` on failure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![
    ///     (0, Attributes::new()),
    ///     (1, Attributes::new()),
    ///     (2, Attributes::new()),
    /// ];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edges = vec![
    ///     (0, 1, Attributes::from([("foo", "bar")])),
    ///     (1, 2, Attributes::from([("bar", "foo")])),
    /// ];
    /// let edge_indices = graph.add_edges(edges).unwrap();
    ///
    /// assert_eq!(graph.edge_count(), 2);
    /// ```
    pub fn add_edges<E, T>(&mut self, edges: E) -> GraphsterResult<Vec<EdgeIndex>>
    where
        E: IntoParallelIterator<Item = T>,
        T: Into<Edge>,
    {
        let (edge_indices, edges) = edges
            .into_par_iter()
            .map(|edge| {
                let edge: Edge = edge.into();

                if !self.nodes.contains_key(&edge.source_index) {
                    return Err(GraphsterError::NodeNotFound {
                        node_index: edge.source_index,
                    });
                }

                if !self.nodes.contains_key(&edge.target_index) {
                    return Err(GraphsterError::NodeNotFound {
                        node_index: edge.target_index,
                    });
                }

                let edge_index = self
                    .edge_index_counter
                    .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                    .into();

                Ok((edge_index, (edge_index, edge)))
            })
            .collect::<GraphsterResult<(Vec<EdgeIndex>, Vec<(EdgeIndex, Edge)>)>>()?;

        for (edge_index, edge) in edges {
            let source_node = self
                .nodes
                .get_mut(&edge.source_index)
                .expect("Node must exist");
            source_node.outgoing_edges.insert(edge_index);

            let target_node = self
                .nodes
                .get_mut(&edge.target_index)
                .expect("Node must exist");
            target_node.incoming_edges.insert(edge_index);

            self.edges.insert(edge_index, edge);
        }

        Ok(edge_indices)
    }

    /// Removes the node with the specified index from the graph.
    ///
    /// Also removes any edges connected to the node. Returns the attributes of the removed node.
    ///
    /// If the node does not exist, this function returns an error
    /// of type `GraphsterError::NodeNotFound`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// graph.add_node(0, Attributes::from([("foo", "bar")])).unwrap();
    /// assert_eq!(graph.node_count(), 1);
    ///
    /// let attributes = graph.remove_node(0).unwrap();
    /// assert_eq!(graph.node_count(), 0);
    /// assert_eq!(attributes, Attributes::from([("foo", "bar")]));
    /// ```
    pub fn remove_node<'a, N: Into<NodeIndexRef<'a>>>(
        &mut self,
        node_index: N,
    ) -> GraphsterResult<Attributes> {
        let node_index_ref = node_index.into();

        let node =
            self.nodes
                .remove(node_index_ref.as_ref())
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: node_index_ref.clone(),
                })?;

        for edge_index in node.incoming_edges {
            self.edges.remove(&edge_index).expect("Edge must exist");
        }

        for edge_index in node.outgoing_edges {
            self.edges.remove(&edge_index).expect("Edge must exist");
        }

        Ok(node.attributes)
    }

    /// Removes the edge with the specified index from the graph.
    ///
    /// Also removes the edge from the source and target nodes' respective edge lists.
    /// Returns the attributes of the removed edge.
    ///
    /// If the edge does not exist, this function returns an error of type `GraphsterError::EdgeNotFound`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::from([("foo", "bar")])).unwrap();
    /// graph.add_edge(0, 1, Attributes::from([("foo", "bar")])).unwrap();
    /// assert_eq!(graph.edge_count(), 2);
    ///
    /// let attributes = graph.remove_edge(&edge_index).unwrap();
    /// assert_eq!(graph.edge_count(), 1);
    /// assert_eq!(attributes, Attributes::from([("foo", "bar")]));
    ///
    /// graph.remove_edge(1).unwrap();
    /// assert_eq!(graph.edge_count(), 0);
    /// ```
    pub fn remove_edge<'a, E: Into<EdgeIndexRef<'a>>>(
        &mut self,
        edge_index: E,
    ) -> GraphsterResult<Attributes> {
        let edge_index_ref: EdgeIndexRef = edge_index.into();

        let edge =
            self.edges
                .remove(edge_index_ref.as_ref())
                .ok_or(GraphsterError::EdgeNotFound {
                    edge_index: *edge_index_ref,
                })?;

        let source_node = self
            .nodes
            .get_mut(&edge.source_index)
            .expect("Node must exist");
        source_node.outgoing_edges.remove(edge_index_ref.as_ref());

        let target_node = self
            .nodes
            .get_mut(&edge.target_index)
            .expect("Node must exist");
        target_node.incoming_edges.remove(edge_index_ref.as_ref());

        Ok(edge.attributes)
    }

    /// Returns the number of nodes in the graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// graph.add_node(1, Attributes::new()).unwrap();
    /// graph.add_node(2, Attributes::new()).unwrap();
    ///
    /// assert_eq!(graph.node_count(), 2);
    /// ```
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the number of valid edges in the graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new()), (2, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// graph.add_edge(0, 1, Attributes::new()).unwrap();
    /// graph.add_edge(1, 2, Attributes::new()).unwrap();

    /// assert_eq!(graph.edge_count(), 2);
    /// ```
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// Returns an iterator over the indices of all nodes in the graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    /// graph.add_node(0, Attributes::new()).unwrap();
    /// graph.add_node(1, Attributes::new()).unwrap();
    ///
    /// for node_index in graph.node_indices() {
    ///   println!("Node index: {}", node_index);
    /// }
    /// ```
    pub fn node_indices(&self) -> impl Iterator<Item = &NodeIndex> {
        self.nodes.keys()
    }

    /// Returns an iterator over the indices of all edges in the graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new()), (2, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// graph.add_edge(0, 1, Attributes::new()).unwrap();
    /// graph.add_edge(1, 2, Attributes::new()).unwrap();

    /// for edge_index in graph.edge_indices() {
    ///   println!("Edge index: {}", edge_index);
    /// }
    /// ```
    pub fn edge_indices(&self) -> impl Iterator<Item = &EdgeIndex> {
        self.edges.keys()
    }

    /// Checks if a node with the given index exists in the graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    /// graph.add_node(0, Attributes::new()).unwrap();
    ///
    /// assert!(graph.contains_node(0));
    /// assert!(!graph.contains_node(1));
    /// ```
    pub fn contains_node<'a, N: Into<NodeIndexRef<'a>>>(&self, node_index: N) -> bool {
        self.nodes.contains_key(node_index.into().as_ref())
    }

    /// Checks if an edge with the given index exists in the graph.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
    ///
    /// assert!(graph.contains_edge(&edge_index));
    /// assert!(!graph.contains_edge(100));
    /// ```
    pub fn contains_edge<'a, E: Into<EdgeIndexRef<'a>>>(&self, edge_index: E) -> bool {
        self.edges.contains_key(edge_index.into().as_ref())
    }

    /// Returns a reference to the attributes of the node with the given index.
    ///
    /// Returns an error of type `GraphsterError::NodeNotFound` if the node does not exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// let mut graph = DataGraph::new();
    /// graph.add_node(0, HashMap::from([("name", "Alice")])).unwrap();
    ///
    /// let node_attributes = graph.node_attributes(0).unwrap();
    /// assert_eq!(node_attributes.get("name"), Some(&"Alice".into()));
    /// ```
    pub fn node_attributes<'a, N: Into<NodeIndexRef<'a>>>(
        &self,
        node_index: N,
    ) -> GraphsterResult<&Attributes> {
        let node_index_ref = node_index.into();

        Ok(&self
            .nodes
            .get(node_index_ref.as_ref())
            .ok_or(GraphsterError::NodeNotFound {
                node_index: node_index_ref.clone(),
            })?
            .attributes)
    }

    /// Returns a mutable reference to the attributes of the node with the given index.
    ///
    /// Returns an error of type `GraphsterError::NodeNotFound` if the node does not exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    /// graph.add_node(0, Attributes::new()).unwrap();
    ///
    /// let mut node_attributes = graph.node_attributes_mut(0).unwrap();
    /// node_attributes.insert("name", "Alice");
    /// ```
    pub fn node_attributes_mut<'a, N: Into<NodeIndexRef<'a>>>(
        &mut self,
        node_index: N,
    ) -> GraphsterResult<&mut Attributes> {
        let node_index_ref = node_index.into();

        Ok(&mut self
            .nodes
            .get_mut(node_index_ref.as_ref())
            .ok_or(GraphsterError::NodeNotFound {
                node_index: node_index_ref.clone(),
            })?
            .attributes)
    }

    /// Returns a reference to the attributes of the edge with the given index.
    ///
    /// Returns an error of type `GraphsterError::EdgeNotFound` if the edge does not exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, HashMap::from([("weight", 10)])).unwrap();
    ///
    /// let edge_attributes = graph.edge_attributes(&edge_index).unwrap();
    /// assert_eq!(edge_attributes.get("weight"), Some(&10.into()));
    ///
    /// let edge_attributes = graph.edge_attributes(0).unwrap();
    /// assert_eq!(edge_attributes.get("weight"), Some(&10.into()));
    /// ```
    pub fn edge_attributes<'a, E: Into<EdgeIndexRef<'a>>>(
        &self,
        edge_index: E,
    ) -> GraphsterResult<&Attributes> {
        let edge_index_ref = edge_index.into();

        Ok(&self
            .edges
            .get(edge_index_ref.as_ref())
            .ok_or(GraphsterError::EdgeNotFound {
                edge_index: *edge_index_ref,
            })?
            .attributes)
    }

    /// Returns a mutable reference to the attributes of the edge with the given index.
    ///
    /// Returns an error of type `GraphsterError::EdgeNotFound` if the edge does not exist.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
    ///
    /// let mut edge_attributes = graph.edge_attributes_mut(&edge_index).unwrap();
    /// edge_attributes.insert("weight", 20);
    ///
    /// let mut edge_attributes = graph.edge_attributes_mut(0).unwrap();
    /// edge_attributes.insert("weight2", 20);
    /// ```
    pub fn edge_attributes_mut<'a, E: Into<EdgeIndexRef<'a>>>(
        &mut self,
        edge_index: E,
    ) -> GraphsterResult<&mut Attributes> {
        let edge_index_ref = edge_index.into();

        Ok(&mut self
            .edges
            .get_mut(edge_index_ref.as_ref())
            .ok_or(GraphsterError::EdgeNotFound {
                edge_index: *edge_index_ref,
            })?
            .attributes)
    }

    pub fn node_edge_indices<'a, N: Into<NodeIndexRef<'a>>>(
        &'a self,
        node_index: N,
        edge_direction: EdgeDirection,
    ) -> GraphsterResult<EdgeIndices<'a>> {
        let node_index_ref: NodeIndexRef = node_index.into();

        let node = self
            .nodes
            .get(node_index_ref.as_ref())
            .ok_or(GraphsterError::NodeNotFound {
                node_index: node_index_ref.clone(),
            })?;

        Ok(match edge_direction {
            EdgeDirection::Incoming => node.incoming_edges.iter().into(),
            EdgeDirection::Outgoing => node.outgoing_edges.iter().into(),
            EdgeDirection::Any => node
                .incoming_edges
                .iter()
                .chain(node.outgoing_edges.iter())
                .into(),
        })
    }

    /// Returns an iterator over the indices of all incoming edges for the specified node.
    ///
    /// If the node does not exist, this function returns an error
    /// of type `GraphsterError::NodeNotFound`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
    ///
    /// let incoming_edge_indices = graph.incoming_edge_indices(1).unwrap().collect::<Vec<_>>();
    /// assert_eq!(incoming_edge_indices, vec![&edge_index]);
    /// ```
    pub fn incoming_edge_indices<'a, N: Into<NodeIndexRef<'a>>>(
        &self,
        node_index: N,
    ) -> GraphsterResult<impl Iterator<Item = &EdgeIndex>> {
        let node_index_ref = node_index.into();

        Ok(self
            .nodes
            .get(node_index_ref.as_ref())
            .ok_or(GraphsterError::NodeNotFound {
                node_index: node_index_ref.clone(),
            })?
            .incoming_edges
            .iter())
    }

    /// Returns an iterator over the indices of all outgoing edges for the specified node.
    ///
    /// If the node does not exist, this function returns an error
    /// of type `GraphsterError::NodeNotFound`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
    ///
    /// let outgoing_edge_indices = graph.outgoing_edge_indices(0).unwrap().collect::<Vec<_>>();
    /// assert_eq!(outgoing_edge_indices, vec![&edge_index]);
    /// ```
    pub fn outgoing_edge_indices<'a, N: Into<NodeIndexRef<'a>>>(
        &self,
        node_index: N,
    ) -> GraphsterResult<impl Iterator<Item = &EdgeIndex>> {
        let node_index_ref = node_index.into();

        Ok(self
            .nodes
            .get(node_index_ref.as_ref())
            .ok_or(GraphsterError::NodeNotFound {
                node_index: node_index_ref.clone(),
            })?
            .outgoing_edges
            .iter())
    }

    /// Returns an iterator over the indices of all edges connecting the specified
    /// source and target nodes.
    ///
    /// If either the source or target node does not exist, this function returns an error
    /// of type `GraphsterError::NodeNotFound`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
    ///
    /// let mut edge_indices = graph.edges_connecting(0, 1).unwrap().collect::<Vec<_>>();
    /// edge_indices.sort();
    ///
    /// assert_eq!(edge_indices, vec![&edge_index]);
    /// ```
    pub fn edges_connecting<'a, 'b, N1: Into<NodeIndexRef<'a>>, N2: Into<NodeIndexRef<'b>>>(
        &self,
        source_index: N1,
        target_index: N2,
    ) -> GraphsterResult<impl Iterator<Item = &EdgeIndex>> {
        let source_index_ref = source_index.into();
        let target_index_ref = target_index.into();

        let source_node =
            self.nodes
                .get(source_index_ref.as_ref())
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: source_index_ref.clone(),
                })?;

        let target_node =
            self.nodes
                .get(target_index_ref.as_ref())
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: target_index_ref.clone(),
                })?;

        Ok(source_node
            .outgoing_edges
            .intersection(&target_node.incoming_edges))
    }

    /// Returns an iterator over the indices of all undirected edges connecting the specified nodes.
    ///
    /// This includes edges where either node can be the source or target.
    /// If either node does not exist, this function returns an error
    /// of type `GraphsterError::NodeNotFound`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let first_edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
    /// let second_edge_index = graph.add_edge(1, 0, Attributes::new()).unwrap();
    ///
    /// let mut edge_indices = graph
    ///     .edges_connecting_undirected(0, 1)
    ///     .unwrap()
    ///     .collect::<Vec<_>>();
    /// edge_indices.sort();
    ///
    /// assert_eq!(edge_indices, vec![&first_edge_index, &second_edge_index]);
    /// ```
    pub fn edges_connecting_undirected<
        'a,
        'b,
        N1: Into<NodeIndexRef<'a>>,
        N2: Into<NodeIndexRef<'b>>,
    >(
        &self,
        first_node_index: N1,
        second_node_index: N2,
    ) -> GraphsterResult<impl Iterator<Item = &EdgeIndex>> {
        let first_node_index_ref = first_node_index.into();
        let second_node_index_ref = second_node_index.into();

        let first_node =
            self.nodes
                .get(first_node_index_ref.as_ref())
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: first_node_index_ref.clone(),
                })?;

        let second_node =
            self.nodes
                .get(second_node_index_ref.as_ref())
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: second_node_index_ref.clone(),
                })?;

        Ok(first_node
            .outgoing_edges
            .intersection(&second_node.incoming_edges)
            .chain(
                first_node
                    .incoming_edges
                    .intersection(&second_node.outgoing_edges),
            ))
    }

    pub fn neighbors<'a, N: Into<NodeIndexRef<'a>>>(
        &'a self,
        node_index: N,
        edge_direction: EdgeDirection,
    ) -> GraphsterResult<NodeIndices<'a>> {
        let node_index_ref = node_index.into();

        let node = self
            .nodes
            .get(node_index_ref.as_ref())
            .ok_or(GraphsterError::NodeNotFound {
                node_index: node_index_ref.clone(),
            })?;

        Ok(match edge_direction {
            EdgeDirection::Incoming => node
                .incoming_edges
                .iter()
                .map(|edge_index| {
                    &self
                        .edges
                        .get(edge_index)
                        .expect("Edge must exist")
                        .source_index
                })
                .unique()
                .into_node_indices(),
            EdgeDirection::Outgoing => node
                .outgoing_edges
                .iter()
                .map(|edge_index| {
                    &self
                        .edges
                        .get(edge_index)
                        .expect("Edge must exist")
                        .target_index
                })
                .unique()
                .into_node_indices(),
            EdgeDirection::Any => node
                .outgoing_edges
                .iter()
                .map(|edge_index| {
                    &self
                        .edges
                        .get(edge_index)
                        .expect("Edge must exist")
                        .target_index
                })
                .chain(node.incoming_edges.iter().map(|edge_index| {
                    &self
                        .edges
                        .get(edge_index)
                        .expect("Edge must exist")
                        .source_index
                }))
                .unique()
                .into_node_indices(),
        })
    }

    /// Removes all nodes and edges from the graph, effectively resetting it to an empty state.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![
    ///     (0, Attributes::new()),
    ///     (1, Attributes::new()),
    ///     (2, Attributes::new()),
    /// ];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edges = vec![
    ///     (0, 1, Attributes::new()),
    ///     (1, 2, Attributes::new()),
    /// ];
    /// graph.add_edges(edges).unwrap();
    ///
    /// assert_eq!(graph.node_count(), 3);
    /// assert_eq!(graph.edge_count(), 2);
    ///
    /// graph.clear();
    /// assert_eq!(graph.node_count(), 0);
    /// assert_eq!(graph.edge_count(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.edges.clear();
        self.edge_index_counter = AtomicUsize::new(0);
    }

    /// Removes all edges from the graph.
    ///
    /// This function leaves the nodes intact but clears all edges and resets the
    /// edge index counter.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let mut graph = DataGraph::new();
    ///
    /// let nodes = vec![
    ///     (0, Attributes::new()),
    ///     (1, Attributes::new()),
    ///     (2, Attributes::new()),
    /// ];
    /// graph.add_nodes(nodes).unwrap();
    ///
    /// let edges = vec![
    ///     (0, 1, Attributes::new()),
    ///     (1, 2, Attributes::new()),
    /// ];
    /// graph.add_edges(edges).unwrap();
    /// assert_eq!(graph.edge_count(), 2);
    ///
    /// graph.clear_edges();
    /// assert_eq!(graph.edge_count(), 0);
    /// ```
    pub fn clear_edges(&mut self) {
        self.edges.clear();
        self.edge_index_counter = AtomicUsize::new(0);

        for node in self.nodes.values_mut() {
            node.incoming_edges.clear();
            node.outgoing_edges.clear();
        }
    }
}

impl Default for DataGraph {
    /// Creates a new empty graph using the `DataGraph::new` function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    ///
    /// let graph = DataGraph::default();
    /// assert_eq!(graph.node_count(), 0);
    /// assert_eq!(graph.edge_count(), 0);
    /// ```
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        datatypes::Attributes,
        errors::GraphsterError,
        graph::{edge::EdgeDirection, DataGraph},
    };

    #[test]
    fn test_new() {
        let graph = DataGraph::new();

        assert_eq!(graph.node_count(), 0);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn test_from_nodes() {
        let nodes = vec![
            (0, Attributes::from([("foo", "bar")])),
            (1, Attributes::from([("bar", "foo")])),
        ];
        let graph = DataGraph::from_nodes(nodes);

        assert_eq!(graph.node_count(), 2);
        assert_eq!(graph.edge_count(), 0);
    }

    #[test]
    fn test_from_nodes_and_edges() {
        let nodes = vec![
            (0, Attributes::from([("foo", "bar")])),
            (1, Attributes::from([("bar", "foo")])),
        ];
        let edges = vec![(0, 1, Attributes::from([("foo", "bar")]))];
        let graph = DataGraph::from_nodes_and_edges(nodes.clone(), edges).unwrap();

        assert_eq!(graph.node_count(), 2);
        assert_eq!(graph.edge_count(), 1);

        let edges = vec![(0, 100, Attributes::from([("foo", "bar")]))];
        assert!(DataGraph::from_nodes_and_edges(nodes.clone(), edges)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));

        let edges = vec![(100, 0, Attributes::from([("foo", "bar")]))];
        assert!(DataGraph::from_nodes_and_edges(nodes, edges)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_add_node() {
        let mut graph = DataGraph::new();

        graph
            .add_node(0, Attributes::from([("foo", "bar")]))
            .unwrap();
        assert_eq!(graph.node_count(), 1);

        assert!(graph
            .add_node(0, Attributes::new())
            .is_err_and(|e| matches!(e, GraphsterError::NodeAlreadyExists { .. })));
    }

    #[test]
    fn test_add_nodes() {
        let mut graph = DataGraph::new();

        let nodes = vec![
            (0, Attributes::from([("foo", "bar")])),
            (1, Attributes::from([("bar", "foo")])),
        ];
        graph.add_nodes(nodes).unwrap();
        assert_eq!(graph.node_count(), 2);

        let nodes = vec![(0, Attributes::from([("foo", "bar")]))];
        assert!(graph
            .add_nodes(nodes)
            .is_err_and(|e| matches!(e, GraphsterError::NodeAlreadyExists { .. })));
    }

    #[test]
    fn test_add_edge() {
        let mut graph = DataGraph::new();

        graph
            .add_node(0, Attributes::from([("foo", "bar")]))
            .unwrap();
        graph
            .add_node(1, Attributes::from([("bar", "foo")]))
            .unwrap();

        let edge_index = graph
            .add_edge(0, 1, Attributes::from([("foo", "bar")]))
            .unwrap();

        assert_eq!(graph.edge_count(), 1);
        assert_eq!(edge_index, 0.into());

        assert!(graph
            .add_edge(0, 100, Attributes::new())
            .is_err_and(|e| { matches!(e, GraphsterError::NodeNotFound { .. }) }));
        assert!(graph
            .add_edge(100, 0, Attributes::new())
            .is_err_and(|e| { matches!(e, GraphsterError::NodeNotFound { .. }) }));
    }

    #[test]
    fn test_add_edges() {
        let mut graph = DataGraph::new();

        let nodes = vec![
            (0, Attributes::from([("foo", "bar")])),
            (1, Attributes::from([("bar", "foo")])),
            (2, Attributes::from([("baz", "qux")])),
        ];
        graph.add_nodes(nodes).unwrap();

        let edges = vec![
            (0, 1, Attributes::from([("foo", "bar")])),
            (1, 2, Attributes::from([("bar", "foo")])),
        ];
        let mut edge_indices = graph.add_edges(edges).unwrap();
        edge_indices.sort();

        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 2);
        assert_eq!(edge_indices, vec![0.into(), 1.into()]);

        let edges = vec![(0, 100, Attributes::new())];
        assert!(graph
            .add_edges(edges)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));

        let edges = vec![(100, 0, Attributes::new())];
        assert!(graph
            .add_edges(edges)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_remove_node() {
        let mut graph = DataGraph::new();

        graph
            .add_node(0, Attributes::from([("foo", "bar")]))
            .unwrap();

        assert_eq!(graph.node_count(), 1);

        let attributes = graph.remove_node(0).unwrap();

        assert_eq!(graph.node_count(), 0);
        assert_eq!(attributes, Attributes::from([("foo", "bar")]));

        assert!(graph
            .remove_node(0)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_remove_edge() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph
            .add_edge(0, 1, Attributes::from([("foo", "bar")]))
            .unwrap();

        assert_eq!(graph.edge_count(), 1);

        let attributes = graph.remove_edge(&edge_index).unwrap();

        assert_eq!(graph.edge_count(), 0);
        assert_eq!(attributes, Attributes::from([("foo", "bar")]));

        assert!(graph
            .remove_edge(&edge_index)
            .is_err_and(|e| matches!(e, GraphsterError::EdgeNotFound { .. })));
    }

    #[test]
    fn test_node_count() {
        let mut graph = DataGraph::new();

        assert_eq!(graph.node_count(), 0);

        graph.add_node(0, Attributes::new()).unwrap();
        graph.add_node(1, Attributes::new()).unwrap();

        assert_eq!(graph.node_count(), 2);
    }

    #[test]
    fn test_edge_count() {
        let mut graph = DataGraph::new();

        assert_eq!(graph.edge_count(), 0);

        let nodes = vec![
            (0, Attributes::new()),
            (1, Attributes::new()),
            (2, Attributes::new()),
        ];
        graph.add_nodes(nodes).unwrap();

        graph.add_edge(0, 1, Attributes::new()).unwrap();
        graph.add_edge(1, 2, Attributes::new()).unwrap();

        assert_eq!(graph.edge_count(), 2);
    }

    #[test]
    fn test_node_indices() {
        let mut graph = DataGraph::new();

        let nodes = vec![
            (0, Attributes::new()),
            (1, Attributes::new()),
            (2, Attributes::new()),
        ];
        graph.add_nodes(nodes).unwrap();

        let mut node_indices = graph.node_indices().collect::<Vec<_>>();
        node_indices.sort();

        assert_eq!(node_indices, vec![&0.into(), &1.into(), &2.into()]);
    }

    #[test]
    fn test_edge_indices() {
        let mut graph = DataGraph::new();

        let nodes = vec![
            (0, Attributes::new()),
            (1, Attributes::new()),
            (2, Attributes::new()),
        ];
        graph.add_nodes(nodes).unwrap();

        graph.add_edge(0, 1, Attributes::new()).unwrap();
        graph.add_edge(1, 2, Attributes::new()).unwrap();

        let mut edge_indices = graph.edge_indices().collect::<Vec<_>>();
        edge_indices.sort();

        assert_eq!(edge_indices, vec![&0.into(), &1.into()]);
    }

    #[test]
    fn test_contains_node() {
        let mut graph = DataGraph::new();

        graph.add_node(0, Attributes::new()).unwrap();

        assert!(graph.contains_node(0));
        assert!(!graph.contains_node(1));
    }

    #[test]
    fn test_contains_edge() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();

        assert!(graph.contains_edge(&edge_index));
        assert!(!graph.contains_edge(100_usize));
    }

    #[test]
    fn test_node_attributes() {
        let mut graph = DataGraph::new();

        graph
            .add_node(0, Attributes::from([("name", "Alice")]))
            .unwrap();

        let node_attributes = graph.node_attributes(0).unwrap();

        assert_eq!(node_attributes.get("name"), Some(&"Alice".into()));

        assert!(graph
            .node_attributes(100)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_node_attributes_mut() {
        let mut graph = DataGraph::new();

        graph.add_node(0, Attributes::new()).unwrap();

        let node_attributes = graph.node_attributes_mut(0).unwrap();
        node_attributes.insert("name", "Alice");

        assert_eq!(node_attributes.get("name"), Some(&"Alice".into()));

        assert!(graph
            .node_attributes_mut(100)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_edge_attributes() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph
            .add_edge(0, 1, Attributes::from([("weight", 10)]))
            .unwrap();

        let edge_attributes = graph.edge_attributes(&edge_index).unwrap();

        assert_eq!(edge_attributes.get("weight"), Some(&10.into()));

        assert!(graph
            .edge_attributes(100)
            .is_err_and(|e| matches!(e, GraphsterError::EdgeNotFound { .. })));
    }

    #[test]
    fn test_edge_attributes_mut() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();

        let edge_attributes = graph.edge_attributes_mut(&edge_index).unwrap();
        edge_attributes.insert("weight", 20);

        assert_eq!(edge_attributes.get("weight"), Some(&20.into()));

        assert!(graph
            .edge_attributes_mut(100)
            .is_err_and(|e| matches!(e, GraphsterError::EdgeNotFound { .. })));
    }

    #[test]
    fn test_incoming_edge_indices() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();

        let incoming_edge_indices = graph.incoming_edge_indices(1).unwrap().collect::<Vec<_>>();

        assert_eq!(incoming_edge_indices, vec![&edge_index]);

        assert!(graph
            .incoming_edge_indices(100)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_outgoing_edge_indices() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();

        let outgoing_edge_indices = graph.outgoing_edge_indices(0).unwrap().collect::<Vec<_>>();

        assert_eq!(outgoing_edge_indices, vec![&edge_index]);

        assert!(graph
            .outgoing_edge_indices(100)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_edges_connecting() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();

        let mut edge_indices = graph.edges_connecting(0, 1).unwrap().collect::<Vec<_>>();
        edge_indices.sort();

        assert_eq!(edge_indices, vec![&edge_index]);

        assert!(graph
            .edges_connecting(0, 100)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));

        assert!(graph
            .edges_connecting(100, 0)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_edges_connecting_undirected() {
        let mut graph = DataGraph::new();

        let nodes = vec![(0, Attributes::new()), (1, Attributes::new())];
        graph.add_nodes(nodes).unwrap();

        let first_edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
        let second_edge_index = graph.add_edge(1, 0, Attributes::new()).unwrap();

        let mut edge_indices = graph
            .edges_connecting_undirected(0, 1)
            .unwrap()
            .collect::<Vec<_>>();
        edge_indices.sort();

        assert_eq!(edge_indices, vec![&first_edge_index, &second_edge_index]);

        assert!(graph
            .edges_connecting(0, 100)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));

        assert!(graph
            .edges_connecting(100, 0)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }

    #[test]
    fn test_neighbors() {
        let mut graph = DataGraph::new();

        let nodes = vec![
            (0, Attributes::new()),
            (1, Attributes::new()),
            (2, Attributes::new()),
        ];
        graph.add_nodes(nodes).unwrap();

        graph.add_edge(0, 1, Attributes::new()).unwrap();
        graph.add_edge(2, 0, Attributes::new()).unwrap();

        let mut neighbor_indices = graph
            .neighbors(0, EdgeDirection::Outgoing)
            .unwrap()
            .collect::<Vec<_>>();
        neighbor_indices.sort();

        assert_eq!(neighbor_indices, vec![&1.into()]);

        assert!(graph
            .neighbors(100, EdgeDirection::Outgoing)
            .is_err_and(|e| matches!(e, GraphsterError::NodeNotFound { .. })));
    }
}
