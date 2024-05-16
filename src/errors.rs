#[derive(Debug)]
pub enum GraphsterError {
    NodeNotFound(String),
    EdgeNotFound(String),
}
