// use wy_graph::EdgeVisitor;

// use super::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VisitError {
    Binding,
}

impl std::fmt::Display for VisitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VisitError::Binding => write!(f, "Error visiting binding"),
        }
    }
}

impl std::error::Error for VisitError {}

/// Applying the visitor pattern to relevant AST Nodes. The methods involved
/// have all been predefined, but any overwritten definitions *must* ensure
/// that they still recurse throughout the tree.
pub trait Visit {}
pub trait VisitMut {}

#[cfg(test)]
mod tests {}
