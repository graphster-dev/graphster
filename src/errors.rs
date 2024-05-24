use super::graph::NodeIndex;
use crate::graph::EdgeIndex;
use std::fmt::Display;

/// An enumeration of possible errors that can occur in the graph operations.
///
/// `GraphsterError` defines various error types that can be encountered while working with a graph,
/// including node and edge operations, as well as data conversion errors.
#[derive(Debug)]
pub enum GraphsterError {
    NodeNotFound { node_index: NodeIndex },
    NodeAlreadyExists { node_index: NodeIndex },
    EdgeNotFound { edge_index: EdgeIndex },
    ConversionError(String),
}

impl Display for GraphsterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GraphsterError::NodeNotFound { node_index } => {
                write!(f, "NodeNotFound: Node with index {} not found", node_index)
            }
            GraphsterError::NodeAlreadyExists { node_index } => {
                write!(f, "Node with index {} already exists", node_index)
            }
            GraphsterError::EdgeNotFound { edge_index } => {
                write!(f, "EdgeNotFound: Edge with index {} not found", edge_index)
            }
            GraphsterError::ConversionError(message) => write!(f, "ConversionError: {}", message),
        }
    }
}

pub type GraphsterResult<T> = Result<T, GraphsterError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_graphster_error_display() {
        let node_not_found = GraphsterError::NodeNotFound {
            node_index: NodeIndex::from(42),
        };
        assert_eq!(
            format!("{}", node_not_found),
            "NodeNotFound: Node with index NodeIndex(42) not found"
        );

        let node_already_exists = GraphsterError::NodeAlreadyExists {
            node_index: NodeIndex::from(42),
        };
        assert_eq!(
            format!("{}", node_already_exists),
            "Node with index NodeIndex(42) already exists"
        );

        let edge_not_found = GraphsterError::EdgeNotFound {
            edge_index: EdgeIndex::from(42),
        };
        assert_eq!(
            format!("{}", edge_not_found),
            "EdgeNotFound: Edge with index EdgeIndex(42) not found"
        );

        let conversion_error = GraphsterError::ConversionError("Test error".to_string());
        assert_eq!(
            format!("{}", conversion_error),
            "ConversionError: Test error"
        );
    }
}
