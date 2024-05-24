#![cfg_attr(docsrs, feature(doc_cfg))]

//! # Graphster
//!
//! Graphster is a versatile graph data structure library designed for rapid data manipulation,
//! analysis, and processing. It provides a rich set of features to create, manage,
//! and manipulate graphs with various types of nodes and edges, each capable of
//! holding multiple attributes.
//!
//! ## Features
//!
//! - **Nodes and Edges**: Add, remove, and manipulate nodes and edges with ease.
//! - **Attributes**: Each node and edge can have associated attributes with flexible types,
//! including integers, floats, strings, and more.
//! - **Error Handling**: Comprehensive error handling for common graph operations.
//! - **Polars Integration**: Optional support for Polars data frames to import graph data.
//!
//! ## Examples
//!
//! ### Creating a Graph
//!
//! ```rust
//! use graphster::prelude::*;
//! use std::collections::HashMap;
//!
//! let mut graph = DataGraph::new();
//!
//! // Add nodes with attributes
//! graph.add_node(0, Attributes::from([("foo", "bar")])).unwrap();
//! graph.add_node(1, HashMap::from([("bar", "foo")])).unwrap();
//!
//! // Add an edge between nodes
//! graph.add_edge(0, 1, Attributes::from([("weight", 10)])).unwrap();
//!
//! // Get node and edge counts
//! assert_eq!(graph.node_count(), 2);
//! assert_eq!(graph.edge_count(), 1);
//! ```
//!
//! ### Using Attributes
//!
//! ```rust
//! use graphster::prelude::*;
//!
//! let mut attrs = Attributes::new();
//! attrs.insert("key1", "value1");
//! attrs.insert("key2", 42);
//!
//! assert_eq!(attrs.get("key1"), Some(&AttributeValue::String("value1".to_string())));
//! assert_eq!(attrs.get("key2"), Some(&AttributeValue::Int32(42)));
//! ```
//!
//! ### Handling Errors
//!
//! ```rust
//! use graphster::prelude::*;
//!
//! let mut graph = DataGraph::new();
//! match graph.add_edge(0, 1, Attributes::new()) {
//!     Ok(_) => println!("Edge added successfully"),
//!     Err(e) => println!("Error adding edge: {}", e),
//! }
//! ```
//!
//! ### Using Polars DataFrames
//!
//! ```rust
//! use graphster::prelude::*;
//! use polars::prelude::*;
//!
//! let s0 = Series::new("index", &[0, 1, 2]);
//! let s1 = Series::new("values", &[Some(1), None, Some(3)]);
//! let df = DataFrame::new(vec![s0, s1]).unwrap();
//!
//! let nodes_df = NodesDataFrame::new(&df, "index");
//! let graph = DataGraph::from_nodes_dataframes(nodes_df).unwrap();
//! ```
//!
//! ### Examples of Advanced Operations
//!
//! #### Neighbors
//!
//! Retrieve all neighboring nodes that can be reached by outgoing edges from a specified node.
//!
//! ```rust
//! use graphster::prelude::*;
//!
//! let mut graph = DataGraph::new();
//! graph.add_node(0, Attributes::new()).unwrap();
//! graph.add_node(1, Attributes::new()).unwrap();
//! graph.add_edge(0, 1, Attributes::new()).unwrap();
//!
//! let neighbors: Vec<_> = graph.neighbors(0, EdgeDirection::Outgoing).unwrap().collect();
//! assert_eq!(neighbors, vec![&1.into()]);
//! ```
//!
//! #### Undirected Neighbors
//!
//! Retrieve all neighboring nodes regardless of the direction of the edges.
//!
//! ```rust
//! use graphster::prelude::*;
//!
//! let mut graph = DataGraph::new();
//! graph.add_node(0, Attributes::new()).unwrap();
//! graph.add_node(1, Attributes::new()).unwrap();
//! graph.add_edge(0, 1, Attributes::new()).unwrap();
//! graph.add_edge(1, 0, Attributes::new()).unwrap();
//!
//! let neighbors: Vec<_> = graph.neighbors(0, EdgeDirection::Any).unwrap().collect();
//! assert_eq!(neighbors, vec![&1.into()]);
//! ```
//!
//! #### Edges Connecting Nodes
//!
//! Retrieve all edges connecting a specified source node to a target node.
//!
//! ```rust
//! use graphster::prelude::*;
//!
//! let mut graph = DataGraph::new();
//! graph.add_node(0, Attributes::new()).unwrap();
//! graph.add_node(1, Attributes::new()).unwrap();
//! let edge_index = graph.add_edge(0, 1, Attributes::new()).unwrap();
//!
//! let edges: Vec<_> = graph.edges_connecting(0, 1).unwrap().collect();
//! assert_eq!(edges, vec![&edge_index]);
//! ```
//!
//! #### Undirected Edges Connecting Nodes
//!
//! Retrieve all edges connecting two nodes, regardless of the direction of the edges.
//!
//! ```rust
//! use graphster::prelude::*;
//!
//! let mut graph = DataGraph::new();
//! graph.add_node(0, Attributes::new()).unwrap();
//! graph.add_node(1, Attributes::new()).unwrap();
//! let edge_index_1 = graph.add_edge(0, 1, Attributes::new()).unwrap();
//! let edge_index_2 = graph.add_edge(1, 0, Attributes::new()).unwrap();
//!
//! let edges: Vec<_> = graph.edges_connecting_undirected(0, 1).unwrap().collect();
//! assert_eq!(edges, vec![&edge_index_1, &edge_index_2]);
//! ```
//!
//! ## Optional Features
//!
//! - **Polars**: Enable support for Polars data frames by specifying the `polars` feature.

pub mod datatypes;
pub mod errors;
pub mod from_marker;
pub mod graph;
mod macros;
pub mod prelude;
mod ref_wrapper;
