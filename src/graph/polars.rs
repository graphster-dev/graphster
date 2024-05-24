use super::{
    edge::{Edge, EdgeIndex},
    node::{Node, NodeIndex},
    DataGraph,
};
use crate::{
    errors::{GraphsterError, GraphsterResult},
    prelude::{AttributeKey, AttributeValue, Attributes},
};
use polars::{datatypes::AnyValue, frame::DataFrame};
use rayon::prelude::*;
use std::{collections::HashMap, sync::atomic::AtomicUsize};

impl TryFrom<AnyValue<'_>> for AttributeKey {
    type Error = GraphsterError;

    fn try_from(value: AnyValue) -> GraphsterResult<Self> {
        match value {
            AnyValue::Boolean(value) => Ok(Self::Boolean(value)),
            AnyValue::Int16(value) => Ok(Self::Int16(value)),
            AnyValue::Int32(value) => Ok(Self::Int32(value)),
            AnyValue::Int64(value) => Ok(Self::Int64(value)),
            AnyValue::Int8(value) => Ok(Self::Int8(value)),
            AnyValue::String(value) => Ok(Self::String(value.to_string())),
            AnyValue::UInt16(value) => Ok(Self::UInt16(value)),
            AnyValue::UInt32(value) => Ok(Self::UInt32(value)),
            AnyValue::UInt64(value) => Ok(Self::UInt64(value)),
            AnyValue::UInt8(value) => Ok(Self::UInt8(value)),
            _ => Err(GraphsterError::ConversionError(format!(
                "Could not convert {} into AttributeKey",
                value
            ))),
        }
    }
}

impl TryFrom<AnyValue<'_>> for AttributeValue {
    type Error = GraphsterError;

    fn try_from(value: AnyValue) -> GraphsterResult<Self> {
        match value {
            AnyValue::Boolean(value) => Ok(Self::Boolean(value)),
            AnyValue::Float32(value) => Ok(Self::Float32(value)),
            AnyValue::Float64(value) => Ok(Self::Float64(value)),
            AnyValue::Int16(value) => Ok(Self::Int16(value)),
            AnyValue::Int32(value) => Ok(Self::Int32(value)),
            AnyValue::Int64(value) => Ok(Self::Int64(value)),
            AnyValue::Int8(value) => Ok(Self::Int8(value)),
            AnyValue::Null => Ok(Self::Null),
            AnyValue::String(value) => Ok(Self::String(value.to_string())),
            AnyValue::UInt16(value) => Ok(Self::UInt16(value)),
            AnyValue::UInt32(value) => Ok(Self::UInt32(value)),
            AnyValue::UInt64(value) => Ok(Self::UInt64(value)),
            AnyValue::UInt8(value) => Ok(Self::UInt8(value)),
            _ => Err(GraphsterError::ConversionError(format!(
                "Could not convert {} into AttributeValue",
                value
            ))),
        }
    }
}

/// A wrapper around a Polars DataFrame that represents nodes in a graph.
///
/// The `NodesDataFrame` struct provides a view into a Polars `DataFrame` with an
/// associated index column.
/// This is used to facilitate operations on node data within a DataFrame.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::NodesDataFrame;
/// use polars::prelude::*;
///
/// let s0 = Series::new("index", &[0, 1, 2]);
/// let s1 = Series::new("values", &[Some(1), None, Some(3)]);
/// let df = DataFrame::new(vec![s0, s1]).unwrap();
///
/// let nodes_df = NodesDataFrame::new(&df, "index");
/// ```
#[derive(Debug, Clone)]
pub struct NodesDataFrame<'a> {
    pub(crate) dataframe: &'a DataFrame,
    pub(crate) index_column: &'a str,
}

impl NodesDataFrame<'_> {
    /// Creates a new `NodesDataFrame` with the specified DataFrame and index column.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::NodesDataFrame;
    /// use polars::prelude::*;
    ///
    /// let s0 = Series::new("index", &[0, 1, 2]);
    /// let s1 = Series::new("values", &[Some(1), None, Some(3)]);
    /// let df = DataFrame::new(vec![s0, s1]).unwrap();
    ///
    /// let nodes_df = NodesDataFrame::new(&df, "index");
    /// ```
    pub fn new<'a>(dataframe: &'a DataFrame, index_column: &'a str) -> NodesDataFrame<'a> {
        NodesDataFrame {
            dataframe,
            index_column,
        }
    }
}

impl<'a> From<(&'a DataFrame, &'a str)> for NodesDataFrame<'a> {
    fn from(value: (&'a DataFrame, &'a str)) -> Self {
        NodesDataFrame::new(value.0, value.1)
    }
}

/// An enum representing input for node data in a graph, which can be either a single `NodesDataFrame` or multiple `NodesDataFrame`s.
///
/// The `NodeDataFrameInput` enum provides a flexible way to handle different types of node data inputs,
/// allowing for single or multiple data frames to be used.
pub enum NodeDataFrameInput<'a> {
    Single(NodesDataFrame<'a>),
    Multiple(Vec<NodesDataFrame<'a>>),
}

impl<'a> From<NodesDataFrame<'a>> for NodeDataFrameInput<'a> {
    fn from(value: NodesDataFrame<'a>) -> Self {
        NodeDataFrameInput::Single(value)
    }
}

impl<'a> From<Vec<NodesDataFrame<'a>>> for NodeDataFrameInput<'a> {
    fn from(value: Vec<NodesDataFrame<'a>>) -> Self {
        NodeDataFrameInput::Multiple(value)
    }
}

impl<'a, const N: usize> From<[NodesDataFrame<'a>; N]> for NodeDataFrameInput<'a> {
    fn from(value: [NodesDataFrame<'a>; N]) -> Self {
        NodeDataFrameInput::Multiple(value.to_vec())
    }
}

/// A wrapper around a Polars DataFrame that represents edges in a graph.
///
/// The `EdgesDataFrame` struct provides a view into a Polars `DataFrame` with associated
/// source and target index columns.
/// This is used to facilitate operations on edge data within a DataFrame.
///
/// # Examples
///
/// ```rust
/// use graphster::prelude::EdgesDataFrame;
/// use polars::prelude::*;
///
/// let s0 = Series::new("source", &[0, 1, 2]);
/// let s1 = Series::new("target", &[1, 2, 0]);
/// let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
/// let df = DataFrame::new(vec![s0, s1, s2]).unwrap();
///
/// let edges_df = EdgesDataFrame::new(&df, "source", "target");
/// ```
#[derive(Debug, Clone)]
pub struct EdgesDataFrame<'a> {
    pub(crate) dataframe: &'a DataFrame,
    pub(crate) source_index_column: &'a str,
    pub(crate) target_index_column: &'a str,
}

impl EdgesDataFrame<'_> {
    /// Creates a new `EdgesDataFrame` with the specified DataFrame, source index column,
    /// and target index column.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::EdgesDataFrame;
    /// use polars::prelude::*;
    ///
    /// let s0 = Series::new("source", &[0, 1, 2]);
    /// let s1 = Series::new("target", &[1, 2, 0]);
    /// let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
    /// let df = DataFrame::new(vec![s0, s1, s2]).unwrap();
    ///
    /// let edges_df = EdgesDataFrame::new(&df, "source", "target");
    /// ```
    pub fn new<'a>(
        dataframe: &'a DataFrame,
        source_index_column: &'a str,
        target_index_column: &'a str,
    ) -> EdgesDataFrame<'a> {
        EdgesDataFrame {
            dataframe,
            source_index_column,
            target_index_column,
        }
    }
}

impl<'a> From<(&'a DataFrame, &'a str, &'a str)> for EdgesDataFrame<'a> {
    fn from(value: (&'a DataFrame, &'a str, &'a str)) -> Self {
        EdgesDataFrame::new(value.0, value.1, value.2)
    }
}

/// An enum representing input for edge data in a graph, which can be either a single `EdgesDataFrame` or multiple `EdgesDataFrame`s.
///
/// The `EdgeDataFrameInput` enum provides a flexible way to handle different types of edge data inputs,
/// allowing for single or multiple data frames to be used.
pub enum EdgeDataFrameInput<'a> {
    Single(EdgesDataFrame<'a>),
    Multiple(Vec<EdgesDataFrame<'a>>),
}

impl<'a> From<EdgesDataFrame<'a>> for EdgeDataFrameInput<'a> {
    fn from(value: EdgesDataFrame<'a>) -> Self {
        EdgeDataFrameInput::Single(value)
    }
}

impl<'a> From<Vec<EdgesDataFrame<'a>>> for EdgeDataFrameInput<'a> {
    fn from(value: Vec<EdgesDataFrame<'a>>) -> Self {
        EdgeDataFrameInput::Multiple(value)
    }
}

impl<'a, const N: usize> From<[EdgesDataFrame<'a>; N]> for EdgeDataFrameInput<'a> {
    fn from(value: [EdgesDataFrame<'a>; N]) -> Self {
        EdgeDataFrameInput::Multiple(value.to_vec())
    }
}

fn dataframe_to_nodes(
    nodes_dataframe: NodesDataFrame<'_>,
) -> GraphsterResult<impl Iterator<Item = GraphsterResult<(NodeIndex, Node)>> + '_> {
    let dataframe = nodes_dataframe.dataframe;
    let index_column = nodes_dataframe.index_column;

    let attribute_column_names = dataframe
        .get_column_names()
        .into_iter()
        .filter(|name| *name != index_column)
        .collect::<Vec<_>>();

    let index_column = dataframe
        .column(index_column)
        .map_err(|_| {
            GraphsterError::ConversionError(format!(
                "Could not find column with name {} in dataframe",
                index_column
            ))
        })?
        .iter();

    let mut attribute_columns = dataframe
        .columns(&attribute_column_names)
        .expect("Columns must exist")
        .iter()
        .map(|s| s.iter())
        .zip(attribute_column_names)
        .collect::<Vec<_>>();

    Ok(index_column.map(move |index_value| {
        Ok((
            AttributeKey::try_from(index_value)?.into(),
            attribute_columns
                .iter_mut()
                .map(|(column, column_name)| {
                    Ok((
                        *column_name,
                        AttributeValue::try_from(
                            column
                                .next()
                                .expect("Has as many iterations as index_column"),
                        )?,
                    ))
                })
                .collect::<GraphsterResult<Attributes>>()?
                .into(),
        ))
    }))
}

fn dataframe_to_edges<'a>(
    edges_dataframe: EdgesDataFrame<'a>,
    edge_index_counter: &'a mut AtomicUsize,
) -> GraphsterResult<impl Iterator<Item = GraphsterResult<(EdgeIndex, Edge)>> + 'a> {
    let dataframe = edges_dataframe.dataframe;
    let source_index_column = edges_dataframe.source_index_column;
    let target_index_column = edges_dataframe.target_index_column;

    let attribute_column_names = dataframe
        .get_column_names()
        .into_iter()
        .filter(|name| *name != source_index_column && *name != target_index_column)
        .collect::<Vec<_>>();

    let source_index_column = dataframe
        .column(source_index_column)
        .map_err(|_| {
            GraphsterError::ConversionError(format!(
                "Could find column with name {} in dataframe",
                source_index_column
            ))
        })?
        .iter();

    let target_index_column = dataframe
        .column(target_index_column)
        .map_err(|_| {
            GraphsterError::ConversionError(format!(
                "Could find column with name {} in dataframe",
                target_index_column
            ))
        })?
        .iter();

    let mut attribute_columns = dataframe
        .columns(&attribute_column_names)
        .expect("Columns must exist")
        .iter()
        .map(|s| s.iter())
        .zip(attribute_column_names)
        .collect::<Vec<_>>();

    Ok(source_index_column.zip(target_index_column).map(
        move |(source_index_value, target_index_value)| {
            let index = edge_index_counter
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                .into();

            Ok((
                index,
                (
                    NodeIndex::from(AttributeKey::try_from(source_index_value)?),
                    NodeIndex::from(AttributeKey::try_from(target_index_value)?),
                    attribute_columns
                        .iter_mut()
                        .map(|(column, column_name)| {
                            Ok((
                                *column_name,
                                AttributeValue::try_from(
                                    column
                                        .next()
                                        .expect("Has as many iterations as index_columns"),
                                )?,
                            ))
                        })
                        .collect::<GraphsterResult<Attributes>>()?,
                )
                    .into(),
            ))
        },
    ))
}

fn create_nodes_from_single_dataframe(
    nodes_dataframe: NodesDataFrame,
) -> GraphsterResult<Vec<(NodeIndex, Node)>> {
    dataframe_to_nodes(nodes_dataframe)?.par_bridge().collect()
}

fn create_nodes_from_multiple_dataframes(
    nodes_dataframes: Vec<NodesDataFrame>,
) -> GraphsterResult<Vec<(NodeIndex, Node)>> {
    let nodes = nodes_dataframes
        .into_par_iter()
        .map(|nodes_dataframe| {
            dataframe_to_nodes(nodes_dataframe)?.collect::<GraphsterResult<Vec<_>>>()
        })
        .collect::<GraphsterResult<Vec<_>>>()?
        .into_par_iter()
        .flatten()
        .collect();

    Ok(nodes)
}

fn create_edges_from_single_dataframe<'a>(
    edges_dataframe: EdgesDataFrame<'a>,
    nodes: &'a mut HashMap<NodeIndex, Node>,
    edge_index_counter: &'a mut AtomicUsize,
) -> GraphsterResult<impl Iterator<Item = GraphsterResult<(EdgeIndex, Edge)>> + 'a> {
    let edges = dataframe_to_edges(edges_dataframe, edge_index_counter)?;

    Ok(edges.map(|result| {
        let (edge_index, edge) = result?;

        let source_node =
            nodes
                .get_mut(&edge.source_index)
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: edge.source_index.clone(),
                })?;
        source_node.outgoing_edges.insert(edge_index);

        let target_node =
            nodes
                .get_mut(&edge.target_index)
                .ok_or(GraphsterError::NodeNotFound {
                    node_index: edge.target_index.clone(),
                })?;
        target_node.incoming_edges.insert(edge_index);

        Ok((edge_index, edge))
    }))
}

fn create_edges_from_multiple_dataframes<'a>(
    edges_dataframes: Vec<EdgesDataFrame>,
    nodes: &'a mut HashMap<NodeIndex, Node>,
    edge_index_counter: &'a mut AtomicUsize,
) -> GraphsterResult<impl Iterator<Item = (EdgeIndex, Edge)> + 'a> {
    let edges = edges_dataframes
        .into_par_iter()
        .map(|edges_dataframe| {
            let mut counter = AtomicUsize::new(edge_index_counter.fetch_add(
                edges_dataframe.dataframe.height(),
                std::sync::atomic::Ordering::Relaxed,
            ));

            let raw_edges = dataframe_to_edges(edges_dataframe, &mut counter)?;

            raw_edges.collect::<GraphsterResult<Vec<_>>>()
        })
        .collect::<GraphsterResult<Vec<_>>>()?
        .into_par_iter()
        .flatten();

    Ok(edges
        .map(|result| {
            let (edge_index, edge) = result;

            if !nodes.contains_key(&edge.source_index) {
                return Err(GraphsterError::NodeNotFound {
                    node_index: edge.source_index,
                });
            }

            if !nodes.contains_key(&edge.target_index) {
                return Err(GraphsterError::NodeNotFound {
                    node_index: edge.target_index,
                });
            }

            Ok((edge_index, edge))
        })
        .collect::<GraphsterResult<Vec<_>>>()?
        .into_iter()
        .map(|(edge_index, edge)| {
            let source_node = nodes
                .get_mut(&edge.source_index)
                .expect("Source node must exist");
            source_node.outgoing_edges.insert(edge_index);

            let target_node = nodes
                .get_mut(&edge.target_index)
                .expect("Target node must exist");
            target_node.incoming_edges.insert(edge_index);

            (edge_index, edge)
        }))
}

impl DataGraph {
    /// Creates a new graph from node data frames.
    ///
    /// This method accepts a single or multiple node data frames and constructs
    /// a `DataGraph` instance from them.
    ///
    /// # Parameters
    /// - `nodes`: A single `NodesDataFrame`, a vector of `NodesDataFrame`
    ///  or an array of `NodesDataFrame`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use polars::prelude::*;
    ///
    /// let s0 = Series::new("index", &[0, 1, 2]);
    /// let s1 = Series::new("values", &[Some(1), None, Some(3)]);
    /// let df = DataFrame::new(vec![s0, s1]).unwrap();
    ///
    /// let nodes_df = NodesDataFrame::new(&df, "index");
    /// let graph = DataGraph::from_nodes_dataframes(nodes_df).unwrap();
    /// ```
    pub fn from_nodes_dataframes<'a, N: Into<NodeDataFrameInput<'a>>>(
        nodes: N,
    ) -> GraphsterResult<Self> {
        match nodes.into() {
            NodeDataFrameInput::Single(dataframe_tuple) => {
                Self::_from_single_nodes_dataframe(dataframe_tuple)
            }
            NodeDataFrameInput::Multiple(dataframe_tuples) => {
                Self::_from_multiple_nodes_dataframes(dataframe_tuples)
            }
        }
    }

    /// Creates a new graph from node and edge data frames.
    ///
    /// This method accepts a combination of single or multiple node and edge data frames
    /// and constructs a `DataGraph` instance from them.
    ///
    /// # Parameters
    /// - `nodes`: A single `NodesDataFrame`, a vector of `NodesDataFrame`,
    /// or an array of `NodesDataFrame`.
    /// - `edges`: A single `EdgesDataFrame`, a vector of `EdgesDataFrame`,
    /// or an array of `EdgesDataFrame`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use polars::prelude::*;
    ///
    /// let s0 = Series::new("index", &[0, 1, 2]);
    /// let s1 = Series::new("values", &[Some(1), None, Some(3)]);
    /// let s2 = Series::new("source", &[0, 1, 2]);
    /// let s3 = Series::new("target", &[1, 2, 0]);
    /// let s4 = Series::new("values", &[Some(1), None, Some(3)]);
    /// let df_nodes = DataFrame::new(vec![s0, s1]).unwrap();
    /// let df_edges = DataFrame::new(vec![s2, s3, s4]).unwrap();
    ///
    /// let nodes_df = NodesDataFrame::new(&df_nodes, "index");
    /// let edges_df = EdgesDataFrame::new(&df_edges, "source", "target");
    /// let graph = DataGraph::from_nodes_and_edges_dataframes(nodes_df, edges_df).unwrap();
    /// ```
    pub fn from_nodes_and_edges_dataframes<
        'a,
        N: Into<NodeDataFrameInput<'a>>,
        E: Into<EdgeDataFrameInput<'a>>,
    >(
        nodes: N,
        edges: E,
    ) -> GraphsterResult<Self> {
        match (nodes.into(), edges.into()) {
            (
                NodeDataFrameInput::Single(nodes_dataframe_tuple),
                EdgeDataFrameInput::Single(edges_dataframe_tuple),
            ) => Self::_from_single_nodes_single_edges_dataframe(
                nodes_dataframe_tuple,
                edges_dataframe_tuple,
            ),
            (
                NodeDataFrameInput::Single(nodes_dataframe_tuple),
                EdgeDataFrameInput::Multiple(edges_dataframe_tuples),
            ) => Self::_from_single_nodes_multiple_edges_dataframe(
                nodes_dataframe_tuple,
                edges_dataframe_tuples,
            ),
            (
                NodeDataFrameInput::Multiple(nodes_dataframe_tuples),
                EdgeDataFrameInput::Single(edges_dataframe_tuple),
            ) => Self::_from_multiple_nodes_single_edges_dataframe(
                nodes_dataframe_tuples,
                edges_dataframe_tuple,
            ),
            (
                NodeDataFrameInput::Multiple(nodes_dataframe_tuples),
                EdgeDataFrameInput::Multiple(edges_dataframe_tuples),
            ) => Self::_from_multiple_nodes_multiple_edges_dataframe(
                nodes_dataframe_tuples,
                edges_dataframe_tuples,
            ),
        }
    }

    /// Adds nodes to the graph from node data frames.
    ///
    /// This method accepts a single or multiple node data frames and adds the nodes
    /// to the existing `DataGraph` instance.
    ///
    /// # Parameters
    /// - `nodes`: A single `NodesDataFrame`, a vector of `NodesDataFrame`,
    /// or an array of `NodesDataFrame`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use polars::prelude::*;
    ///
    /// let s0 = Series::new("index", &[0, 1, 2]);
    /// let s1 = Series::new("values", &[Some(1), None, Some(3)]);
    /// let df = DataFrame::new(vec![s0, s1]).unwrap();
    ///
    /// let nodes_df = NodesDataFrame::new(&df, "index");
    /// let mut graph = DataGraph::new();
    /// graph.add_nodes_dataframes(nodes_df).unwrap();
    /// ```
    pub fn add_nodes_dataframes<'a, N: Into<NodeDataFrameInput<'a>>>(
        &mut self,
        nodes: N,
    ) -> GraphsterResult<()> {
        match nodes.into() {
            NodeDataFrameInput::Single(nodes_dataframe_tuple) => {
                self._add_single_nodes_dataframe(nodes_dataframe_tuple)
            }
            NodeDataFrameInput::Multiple(nodes_dataframe_tuples) => {
                self._add_multiple_nodes_dataframes(nodes_dataframe_tuples)
            }
        }
    }

    /// Adds edges to the graph from edge data frames.
    ///
    /// This method accepts a single or multiple edge data frames and adds the edges
    /// to the existing `DataGraph` instance.
    ///
    /// # Parameters
    /// - `edges`: A single `EdgesDataFrame`, a vector of `EdgesDataFrame`,
    /// or an array of `EdgesDataFrame`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use graphster::prelude::*;
    /// use polars::prelude::*;
    ///
    /// let s0 = Series::new("source", &[0, 1, 2]);
    /// let s1 = Series::new("target", &[1, 2, 0]);
    /// let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
    /// let df = DataFrame::new(vec![s0, s1, s2]).unwrap();
    ///
    /// let edges_df = EdgesDataFrame::new(&df, "source", "target");
    ///
    /// let nodes = vec![
    ///    (0, Attributes::new()),
    ///    (1, Attributes::new()),
    ///    (2, Attributes::new()),
    /// ];
    /// let mut graph = DataGraph::from_nodes(nodes);
    /// graph.add_edges_dataframes(edges_df).unwrap();
    /// ```
    pub fn add_edges_dataframes<'a, E: Into<EdgeDataFrameInput<'a>>>(
        &mut self,
        edges: E,
    ) -> GraphsterResult<()> {
        match edges.into() {
            EdgeDataFrameInput::Single(edges_dataframe_tuple) => {
                self._add_single_edges_dataframe(edges_dataframe_tuple)
            }
            EdgeDataFrameInput::Multiple(edges_dataframe_tuples) => {
                self._add_multiple_edges_dataframes(edges_dataframe_tuples)
            }
        }
    }

    fn _from_single_nodes_dataframe(nodes_dataframe: NodesDataFrame) -> GraphsterResult<Self> {
        let nodes = create_nodes_from_single_dataframe(nodes_dataframe)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        Ok(Self {
            nodes: nodes_map,
            edges: HashMap::new(),
            edge_index_counter: AtomicUsize::new(0),
        })
    }

    fn _from_multiple_nodes_dataframes(
        nodes_dataframes: Vec<NodesDataFrame>,
    ) -> GraphsterResult<Self> {
        let nodes = create_nodes_from_multiple_dataframes(nodes_dataframes)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        Ok(Self {
            nodes: nodes_map,
            edges: HashMap::new(),
            edge_index_counter: AtomicUsize::new(0),
        })
    }

    fn _from_single_nodes_single_edges_dataframe(
        nodes_dataframe: NodesDataFrame,
        edges_dataframe: EdgesDataFrame,
    ) -> GraphsterResult<Self> {
        let nodes = create_nodes_from_single_dataframe(nodes_dataframe)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        let mut edge_index_counter = AtomicUsize::new(0);

        let edges = create_edges_from_single_dataframe(
            edges_dataframe,
            &mut nodes_map,
            &mut edge_index_counter,
        )?
        .collect::<GraphsterResult<_>>()?;

        Ok(DataGraph {
            nodes: nodes_map,
            edges,
            edge_index_counter,
        })
    }

    fn _from_single_nodes_multiple_edges_dataframe(
        nodes_dataframe: NodesDataFrame,
        edges_dataframes: Vec<EdgesDataFrame>,
    ) -> GraphsterResult<Self> {
        let mut nodes = dataframe_to_nodes(nodes_dataframe)?
            .par_bridge()
            .collect::<GraphsterResult<_>>()?;

        let mut edge_index_counter = AtomicUsize::new(0);

        let edges = create_edges_from_multiple_dataframes(
            edges_dataframes,
            &mut nodes,
            &mut edge_index_counter,
        )?
        .collect();

        Ok(DataGraph {
            nodes,
            edges,
            edge_index_counter,
        })
    }

    fn _from_multiple_nodes_single_edges_dataframe(
        nodes_dataframes: Vec<NodesDataFrame>,
        edges_dataframe: EdgesDataFrame,
    ) -> GraphsterResult<Self> {
        let nodes = create_nodes_from_multiple_dataframes(nodes_dataframes)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        let mut edge_index_counter = AtomicUsize::new(0);

        let edges = create_edges_from_single_dataframe(
            edges_dataframe,
            &mut nodes_map,
            &mut edge_index_counter,
        )?
        .collect::<GraphsterResult<_>>()?;

        Ok(DataGraph {
            nodes: nodes_map,
            edges,
            edge_index_counter,
        })
    }

    fn _from_multiple_nodes_multiple_edges_dataframe(
        nodes_dataframes: Vec<NodesDataFrame>,
        edges_dataframes: Vec<EdgesDataFrame>,
    ) -> GraphsterResult<Self> {
        let nodes = create_nodes_from_multiple_dataframes(nodes_dataframes)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        let mut edge_index_counter = AtomicUsize::new(0);

        let edges = create_edges_from_multiple_dataframes(
            edges_dataframes,
            &mut nodes_map,
            &mut edge_index_counter,
        )?
        .collect();

        Ok(DataGraph {
            nodes: nodes_map,
            edges,
            edge_index_counter,
        })
    }

    fn _add_single_nodes_dataframe(
        &mut self,
        nodes_dataframe: NodesDataFrame,
    ) -> GraphsterResult<()> {
        let nodes = create_nodes_from_single_dataframe(nodes_dataframe)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            if self.nodes.contains_key(&node_index) {
                return Err(GraphsterError::NodeAlreadyExists { node_index });
            }

            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        self.nodes.extend(nodes_map);

        Ok(())
    }

    fn _add_multiple_nodes_dataframes(
        &mut self,
        nodes_dataframes: Vec<NodesDataFrame>,
    ) -> GraphsterResult<()> {
        let nodes = create_nodes_from_multiple_dataframes(nodes_dataframes)?;

        let mut nodes_map = HashMap::<NodeIndex, Node>::new();

        for (node_index, node) in nodes {
            if self.nodes.contains_key(&node_index) {
                return Err(GraphsterError::NodeAlreadyExists { node_index });
            }

            match nodes_map.entry(node_index) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    return Err(GraphsterError::NodeAlreadyExists {
                        node_index: entry.key().clone(),
                    });
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(node);
                }
            }
        }

        self.nodes.extend(nodes_map);

        Ok(())
    }

    fn _add_single_edges_dataframe(
        &mut self,
        edges_dataframe: EdgesDataFrame,
    ) -> GraphsterResult<()> {
        let edges = create_edges_from_single_dataframe(
            edges_dataframe,
            &mut self.nodes,
            &mut self.edge_index_counter,
        )?
        .collect::<GraphsterResult<Vec<_>>>()?;

        self.edges.extend(edges);

        Ok(())
    }

    fn _add_multiple_edges_dataframes(
        &mut self,
        edges_dataframes: Vec<EdgesDataFrame>,
    ) -> GraphsterResult<()> {
        let edges = create_edges_from_multiple_dataframes(
            edges_dataframes,
            &mut self.nodes,
            &mut self.edge_index_counter,
        )?;

        self.edges.extend(edges);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use polars::prelude::*;

    #[test]
    fn test_attribute_key_try_from() {
        assert_eq!(
            AttributeKey::try_from(AnyValue::Boolean(false)).unwrap(),
            AttributeKey::Boolean(false)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::Int16(0)).unwrap(),
            AttributeKey::Int16(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::Int32(0)).unwrap(),
            AttributeKey::Int32(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::Int64(0)).unwrap(),
            AttributeKey::Int64(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::Int8(0)).unwrap(),
            AttributeKey::Int8(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::String("foo")).unwrap(),
            AttributeKey::String("foo".to_string())
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::UInt16(0)).unwrap(),
            AttributeKey::UInt16(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::UInt32(0)).unwrap(),
            AttributeKey::UInt32(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::UInt64(0)).unwrap(),
            AttributeKey::UInt64(0)
        );
        assert_eq!(
            AttributeKey::try_from(AnyValue::UInt8(0)).unwrap(),
            AttributeKey::UInt8(0)
        );

        // Only testing one other variant to ensure the error is thrown should be enough
        assert!(AttributeKey::try_from(AnyValue::Null)
            .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) }));
    }

    #[test]
    fn test_attribute_value_try_from() {
        assert_eq!(
            AttributeValue::try_from(AnyValue::Boolean(false)).unwrap(),
            AttributeValue::Boolean(false)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Float32(0.0)).unwrap(),
            AttributeValue::Float32(0.0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Float64(0.0)).unwrap(),
            AttributeValue::Float64(0.0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Int16(0)).unwrap(),
            AttributeValue::Int16(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Int32(0)).unwrap(),
            AttributeValue::Int32(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Int64(0)).unwrap(),
            AttributeValue::Int64(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Int8(0)).unwrap(),
            AttributeValue::Int8(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::Null).unwrap(),
            AttributeValue::Null
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::String("foo")).unwrap(),
            AttributeValue::String("foo".to_string())
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::UInt16(0)).unwrap(),
            AttributeValue::UInt16(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::UInt32(0)).unwrap(),
            AttributeValue::UInt32(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::UInt64(0)).unwrap(),
            AttributeValue::UInt64(0)
        );
        assert_eq!(
            AttributeValue::try_from(AnyValue::UInt8(0)).unwrap(),
            AttributeValue::UInt8(0)
        );

        // Only testing one other variant to ensure the error is thrown should be enough
        assert!(AttributeValue::try_from(AnyValue::Binary(&[0, 1, 2]))
            .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) }));
    }

    #[test]
    fn test_nodes_dataframe_new() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let df = DataFrame::new(vec![s0, s1]).unwrap();

        let nodes_df = NodesDataFrame::new(&df, "index");

        assert_eq!(nodes_df.dataframe, &df);
        assert_eq!(nodes_df.index_column, "index");
    }

    #[test]
    fn test_nodes_dataframe_from() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let df = DataFrame::new(vec![s0, s1]).unwrap();

        let nodes_df = NodesDataFrame::from((&df, "index"));

        assert_eq!(nodes_df.dataframe, &df);
        assert_eq!(nodes_df.index_column, "index");
    }

    #[test]
    fn test_node_dataframe_input_from() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let df = DataFrame::new(vec![s0, s1]).unwrap();

        let nodes_df = NodesDataFrame::new(&df, "index");

        let input = NodeDataFrameInput::from(nodes_df.clone());

        match input {
            NodeDataFrameInput::Single(dataframe) => {
                assert_eq!(dataframe.dataframe, &df);
                assert_eq!(dataframe.index_column, "index");
            }
            _ => panic!("Expected NodeDataFrameInput::Single"),
        }

        let input = NodeDataFrameInput::from(vec![nodes_df.clone()]);

        match input {
            NodeDataFrameInput::Multiple(dataframes) => {
                assert_eq!(dataframes.len(), 1);
                assert_eq!(dataframes[0].dataframe, &df);
                assert_eq!(dataframes[0].index_column, "index");
            }
            _ => panic!("Expected NodeDataFrameInput::Multiple"),
        }

        let input = NodeDataFrameInput::from([nodes_df]);

        match input {
            NodeDataFrameInput::Multiple(dataframes) => {
                assert_eq!(dataframes.len(), 1);
                assert_eq!(dataframes[0].dataframe, &df);
                assert_eq!(dataframes[0].index_column, "index");
            }
            _ => panic!("Expected NodeDataFrameInput::Multiple"),
        }
    }

    #[test]
    fn test_edges_dataframe_new() {
        let s0 = Series::new("source", &[0, 1, 2]);
        let s1 = Series::new("target", &[1, 2, 0]);
        let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
        let df = DataFrame::new(vec![s0, s1, s2]).unwrap();

        let edges_df = EdgesDataFrame::new(&df, "source", "target");

        assert_eq!(edges_df.dataframe, &df);
        assert_eq!(edges_df.source_index_column, "source");
        assert_eq!(edges_df.target_index_column, "target");
    }

    #[test]
    fn test_edges_dataframe_from() {
        let s0 = Series::new("source", &[0, 1, 2]);
        let s1 = Series::new("target", &[1, 2, 0]);
        let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
        let df = DataFrame::new(vec![s0, s1, s2]).unwrap();

        let edges_df = EdgesDataFrame::from((&df, "source", "target"));

        assert_eq!(edges_df.dataframe, &df);
        assert_eq!(edges_df.source_index_column, "source");
        assert_eq!(edges_df.target_index_column, "target");
    }

    #[test]
    fn test_edge_dataframe_input_from() {
        let s0 = Series::new("source", &[0, 1, 2]);
        let s1 = Series::new("target", &[1, 2, 0]);
        let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
        let df = DataFrame::new(vec![s0, s1, s2]).unwrap();

        let edges_df = EdgesDataFrame::new(&df, "source", "target");

        let input = EdgeDataFrameInput::from(edges_df.clone());

        match input {
            EdgeDataFrameInput::Single(dataframe) => {
                assert_eq!(dataframe.dataframe, &df);
                assert_eq!(dataframe.source_index_column, "source");
                assert_eq!(dataframe.target_index_column, "target");
            }
            _ => panic!("Expected EdgeDataFrameInput::Single"),
        }

        let input = EdgeDataFrameInput::from(vec![edges_df.clone()]);

        match input {
            EdgeDataFrameInput::Multiple(dataframes) => {
                assert_eq!(dataframes.len(), 1);
                assert_eq!(dataframes[0].dataframe, &df);
                assert_eq!(dataframes[0].source_index_column, "source");
                assert_eq!(dataframes[0].target_index_column, "target");
            }
            _ => panic!("Expected EdgeDataFrameInput::Multiple"),
        }

        let input = EdgeDataFrameInput::from([edges_df]);

        match input {
            EdgeDataFrameInput::Multiple(dataframes) => {
                assert_eq!(dataframes.len(), 1);
                assert_eq!(dataframes[0].dataframe, &df);
                assert_eq!(dataframes[0].source_index_column, "source");
                assert_eq!(dataframes[0].target_index_column, "target");
            }
            _ => panic!("Expected EdgeDataFrameInput::Multiple"),
        }
    }

    #[test]
    fn test_datagraph_from_nodes_dataframes() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let df = DataFrame::new(vec![s0.clone(), s1.clone()]).unwrap();

        let nodes_df = NodesDataFrame::new(&df, "index");

        let graph = DataGraph::from_nodes_dataframes(nodes_df.clone()).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 0);

        let graph = DataGraph::from_nodes_dataframes(vec![nodes_df]).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 0);

        let nodes_df = NodesDataFrame::new(&df, "not_exists");
        assert!(DataGraph::from_nodes_dataframes(nodes_df)
            .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) }));

        let invalid_s0 = Series::new("index", &[0, 1, 0]);
        let invalid_df_nodes = DataFrame::new(vec![invalid_s0, s1]).unwrap();

        let invalid_nodes_df = NodesDataFrame::new(&invalid_df_nodes, "index");
        assert!(DataGraph::from_nodes_dataframes(invalid_nodes_df)
            .is_err_and(|e| { matches!(e, GraphsterError::NodeAlreadyExists { .. }) }));

        let invalid_s1 = Series::new(
            "values",
            &[
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
            ],
        );
        let invalid_df_nodes = DataFrame::new(vec![s0, invalid_s1]).unwrap();

        let invalid_nodes_df = NodesDataFrame::new(&invalid_df_nodes, "index");
        assert!(DataGraph::from_nodes_dataframes(invalid_nodes_df)
            .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) }));
    }

    #[test]
    fn test_datagraph_from_nodes_and_edges_dataframes() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let s2 = Series::new("source", &[0, 1, 2]);
        let s3 = Series::new("target", &[1, 2, 0]);
        let s4 = Series::new("values", &[Some(1), None, Some(3)]);
        let df_nodes = DataFrame::new(vec![s0, s1]).unwrap();
        let df_edges = DataFrame::new(vec![s2, s3, s4]).unwrap();

        let nodes_df = NodesDataFrame::new(&df_nodes, "index");
        let edges_df = EdgesDataFrame::new(&df_edges, "source", "target");

        let graph =
            DataGraph::from_nodes_and_edges_dataframes(nodes_df.clone(), edges_df.clone()).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);

        let graph =
            DataGraph::from_nodes_and_edges_dataframes(nodes_df.clone(), vec![edges_df.clone()])
                .unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);

        let graph =
            DataGraph::from_nodes_and_edges_dataframes(vec![nodes_df.clone()], edges_df.clone())
                .unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);

        let graph =
            DataGraph::from_nodes_and_edges_dataframes(vec![nodes_df], vec![edges_df]).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);
    }

    #[test]
    fn test_invalid_from_nodes_and_edges_dataframes() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let s2 = Series::new("source", &[0, 1, 2]);
        let s3 = Series::new("target", &[1, 2, 0]);
        let s4 = Series::new("values", &[Some(1), None, Some(3)]);
        let df_nodes = DataFrame::new(vec![s0.clone(), s1.clone()]).unwrap();
        let df_edges = DataFrame::new(vec![s2.clone(), s3.clone(), s4.clone()]).unwrap();

        let nodes_df = NodesDataFrame::new(&df_nodes, "not_exists");
        let edges_df = EdgesDataFrame::new(&df_edges, "source", "target");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(nodes_df, edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) })
        );

        let nodes_df = NodesDataFrame::new(&df_nodes, "index");
        let edges_df = EdgesDataFrame::new(&df_edges, "not_exists", "target");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(nodes_df.clone(), edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) })
        );

        let edges_df = EdgesDataFrame::new(&df_edges, "source", "not_exists");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(nodes_df.clone(), edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) })
        );

        let invalid_s0 = Series::new("index", &[0, 1, 0]);
        let invalid_df_nodes = DataFrame::new(vec![invalid_s0, s1]).unwrap();

        let invalid_nodes_df = NodesDataFrame::new(&invalid_df_nodes, "index");
        let edges_df = EdgesDataFrame::new(&df_edges, "source", "target");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(invalid_nodes_df, edges_df.clone())
                .is_err_and(|e| { matches!(e, GraphsterError::NodeAlreadyExists { .. }) })
        );

        let invalid_s2 = Series::new("source", &[0, 1, 50]);
        let invalid_df_edges = DataFrame::new(vec![invalid_s2, s3.clone(), s4.clone()]).unwrap();

        let invalid_edges_df = EdgesDataFrame::new(&invalid_df_edges, "source", "target");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(nodes_df.clone(), invalid_edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::NodeNotFound { .. }) })
        );

        let invalid_s3 = Series::new("target", &[1, 2, 50]);
        let invalid_df_edges = DataFrame::new(vec![s2.clone(), invalid_s3, s4]).unwrap();

        let invalid_edges_df = EdgesDataFrame::new(&invalid_df_edges, "source", "target");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(nodes_df.clone(), invalid_edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::NodeNotFound { .. }) })
        );

        let invalid_s1 = Series::new(
            "values",
            &[
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
            ],
        );
        let invalid_df_nodes = DataFrame::new(vec![s0, invalid_s1]).unwrap();

        let invalid_nodes_df = NodesDataFrame::new(&invalid_df_nodes, "index");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(invalid_nodes_df, edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) })
        );

        let invalid_s4 = Series::new(
            "values",
            &[
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
            ],
        );
        let invalid_df_edges = DataFrame::new(vec![s2, s3, invalid_s4]).unwrap();

        let invalid_edges_df = EdgesDataFrame::new(&invalid_df_edges, "source", "target");
        assert!(
            DataGraph::from_nodes_and_edges_dataframes(nodes_df, invalid_edges_df)
                .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) })
        );
    }

    #[test]
    fn test_datagraph_add_nodes_dataframes() {
        let s0 = Series::new("index", &[0, 1, 2]);
        let s1 = Series::new("values", &[Some(1), None, Some(3)]);
        let df = DataFrame::new(vec![s0.clone(), s1.clone()]).unwrap();

        let mut graph = DataGraph::new();
        let nodes_df = NodesDataFrame::new(&df, "index");

        graph.add_nodes_dataframes(nodes_df.clone()).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 0);

        let mut graph = DataGraph::new();
        graph.add_nodes_dataframes(vec![nodes_df.clone()]).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 0);

        assert!(graph
            .add_nodes_dataframes(nodes_df.clone())
            .is_err_and(|e| { matches!(e, GraphsterError::NodeAlreadyExists { .. }) }));

        let mut graph = DataGraph::new();
        let invalid_s0 = Series::new("index", &[0, 1, 0]);
        let invalid_df_nodes = DataFrame::new(vec![invalid_s0, s1]).unwrap();

        let invalid_nodes_df = NodesDataFrame::new(&invalid_df_nodes, "index");
        assert!(graph
            .add_nodes_dataframes(invalid_nodes_df)
            .is_err_and(|e| { matches!(e, GraphsterError::NodeAlreadyExists { .. }) }));

        let invalid_s1 = Series::new(
            "values",
            &[
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
            ],
        );
        let invalid_df_nodes = DataFrame::new(vec![s0, invalid_s1]).unwrap();

        let invalid_nodes_df = NodesDataFrame::new(&invalid_df_nodes, "index");
        assert!(graph
            .add_nodes_dataframes(invalid_nodes_df)
            .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) }));
    }

    #[test]
    fn test_datagraph_add_edges_dataframes() {
        let s0 = Series::new("source", &[0, 1, 2]);
        let s1 = Series::new("target", &[1, 2, 0]);
        let s2 = Series::new("weight", &[1.0, 2.0, 3.0]);
        let df = DataFrame::new(vec![s0.clone(), s1.clone(), s2.clone()]).unwrap();

        let nodes = vec![
            (0, Attributes::new()),
            (1, Attributes::new()),
            (2, Attributes::new()),
        ];
        let mut graph = DataGraph::from_nodes(nodes.clone());
        let edges_df = EdgesDataFrame::new(&df, "source", "target");

        graph.add_edges_dataframes(edges_df.clone()).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);

        let mut graph = DataGraph::from_nodes(nodes.clone());
        graph.add_edges_dataframes(vec![edges_df.clone()]).unwrap();
        assert_eq!(graph.node_count(), 3);
        assert_eq!(graph.edge_count(), 3);

        let mut graph = DataGraph::from_nodes(nodes.clone());
        let invalid_s0 = Series::new("source", &[0, 1, 50]);
        let invalid_df_edges = DataFrame::new(vec![invalid_s0, s1.clone(), s2.clone()]).unwrap();

        let invalid_edges_df = EdgesDataFrame::new(&invalid_df_edges, "source", "target");
        assert!(graph
            .add_edges_dataframes(invalid_edges_df)
            .is_err_and(|e| { matches!(e, GraphsterError::NodeNotFound { .. }) }));

        let mut graph = DataGraph::new();
        let invalid_s1 = Series::new("target", &[1, 2, 50]);
        let invalid_df_edges = DataFrame::new(vec![s0.clone(), invalid_s1, s2.clone()]).unwrap();

        let invalid_edges_df = EdgesDataFrame::new(&invalid_df_edges, "source", "target");
        assert!(graph
            .add_edges_dataframes(invalid_edges_df)
            .is_err_and(|e| { matches!(e, GraphsterError::NodeNotFound { .. }) }));

        let mut graph = DataGraph::new();
        let invalid_s2 = Series::new(
            "weight",
            &[
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
                AnyValue::Binary(&[0, 1, 2]),
            ],
        );
        let invalid_df_edges = DataFrame::new(vec![s0, s1, invalid_s2]).unwrap();

        let invalid_edges_df = EdgesDataFrame::new(&invalid_df_edges, "source", "target");
        assert!(graph
            .add_edges_dataframes(invalid_edges_df)
            .is_err_and(|e| { matches!(e, GraphsterError::ConversionError(_)) }));
    }
}
