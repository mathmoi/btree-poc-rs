use super::slot_directory::{SlotDirectory, SlotDirectoryError};
use std::fmt::Debug;
use thiserror::Error;

pub use super::slot_directory::Cell;

/// Unique identifier for nodes in the B+Tree.
///
/// Node IDs are used to reference nodes stored in the tree's internal storage, allowing for efficient lookup and
/// traversal operations.
pub type NodeId = u32;

// =====================================================================================================================
// CellError
// =====================================================================================================================

/// Errors that can occur during node operations.
#[derive(Error, Debug)]
pub enum NodeError {
    /// Attempted to insert a key that already exists in the node.
    #[error("Key already exists")]
    KeyAlreadyExists,

    /// Attempted an operation that requires an internal node on a non-internal node.
    #[error("The node is not an internal node")]
    NotInternalNode,

    /// An unexpected error occurred during a node operation.
    #[error("Unexpected error: {0}")]
    Unexpected(#[from] Box<dyn std::error::Error + Send + Sync>),
}

/// Converts a `SlotDirectoryError` into a `NodeError`.
///
/// This conversion maps slot directory errors to their corresponding node errors, wrapping unexpected errors in the
/// `Unexpected` variant.
impl From<SlotDirectoryError> for NodeError {
    fn from(err: SlotDirectoryError) -> Self {
        match err {
            SlotDirectoryError::KeyAlreadyExists => NodeError::KeyAlreadyExists,
            SlotDirectoryError::IndexOutOfBounds { .. } => NodeError::Unexpected(Box::new(err)),
        }
    }
}

// =====================================================================================================================
// LeafNode
// =====================================================================================================================

/// Represents a leaf node in a B+Tree.
///
/// Leaf nodes contain key-value pairs where the value is the actual data being stored in the B+Tree. Unlike internal
/// nodes, leaf nodes do not have child nodes. Leaf nodes are linked together via the `next_leaf` pointer to allow for
/// efficient range queries and sequential scans.
///
/// # Type Parameters
/// * `K` - The key type
/// * `V` - The value type
pub struct LeafNode<K, V> {
    slot_directory: SlotDirectory<K, V>,
    next_leaf: Option<u32>,
}

impl<K: Ord + Clone, V: Clone> LeafNode<K, V> {
    /// Inserts a cell into the leaf node.
    ///
    /// The cell is inserted in sorted order by key. If the key already exists, the insertion fails.
    ///
    /// # Arguments
    /// * `cell` - The key-value pair to insert
    ///
    /// # Returns
    /// * `Ok(())` - If the insertion was successful
    ///
    /// # Errors
    /// * `NodeError::KeyAlreadyExists` - If the key is already present in the node
    pub fn insert(&mut self, cell: Cell<K, V>) -> Result<(), NodeError> {
        self.slot_directory.insert(cell)?;
        Ok(())
    }
}

/// Creates a new, empty `LeafNode` with no next leaf pointer.
impl<K, V> Default for LeafNode<K, V> {
    fn default() -> Self {
        LeafNode { slot_directory: SlotDirectory::default(), next_leaf: None }
    }
}

impl<K: Debug, V> Debug for LeafNode<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[LEAF] {:?}", self.slot_directory)?;
        Ok(())
    }
}

impl<K: Ord + PartialEq + Clone, V: PartialEq + Clone> PartialEq for LeafNode<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.slot_directory == other.slot_directory
    }
}

// =====================================================================================================================
// InternalNode
// =====================================================================================================================

/// Represents an internal node in a B+Tree.
///
/// Internal nodes contain keys and references to child nodes. Each key in an internal node acts as a separator, with
/// the child to the left containing keys less than the separator and the child to the right containing keys greater
/// than or equal to it. Internal nodes also maintain a rightmost child pointer for keys greater than all separators in
/// the node.
///
/// # Type Parameters
/// * `K` - The key type
pub struct InternalNode<K> {
    slot_directory: SlotDirectory<K, NodeId>,
    right_most_child: Option<NodeId>,
}

impl<K: Clone + Ord> InternalNode<K> {
    /// Returns an iterator over all keys in this internal node.
    ///
    /// # Returns
    /// An iterator that yields references to the keys (`&K`) stored in this internal node.
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.slot_directory.iter().map(|cell| &cell.key)
    }

    /// Returns an iterator over all child node IDs in this internal node.
    ///
    /// The iterator yields child node IDs in left-to-right order, including:
    /// - All child nodes referenced in the slot directory (one child per key)
    /// - The rightmost child node (if present)
    ///
    /// # Returns
    /// An iterator that yields `NodeId` values representing the child nodes.
    pub fn children(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.slot_directory.iter().map(|cell| cell.value).chain(self.right_most_child)
    }

    /// Returns the number of children this internal node has.
    ///
    /// This count includes all children in the slot directory plus the rightmost child if it exists.
    ///
    /// # Returns
    /// The total number of child nodes
    pub fn len(&self) -> usize {
        self.slot_directory.len() + if self.right_most_child.is_some() { 1 } else { 0 }
    }

    /// Returns the rightmost child of this internal node, if it exists.
    ///
    /// The rightmost child contains all keys greater than every separator key in the node.
    ///
    /// # Returns
    /// * `Some(NodeId)` - The ID of the rightmost child node
    /// * `None` - If no rightmost child has been set
    pub fn right_most_child(&self) -> Option<NodeId> {
        self.right_most_child
    }

    /// Sets the rightmost child of this internal node.
    ///
    /// # Arguments
    /// * `child` - The node ID to set as the rightmost child
    pub fn set_right_most_child(&mut self, child: NodeId) {
        self.right_most_child = Some(child);
    }

    /// Inserts a cell into the internal node.
    ///
    /// The cell contains a separator key and a reference to a child node. The cell is inserted in sorted order by key.
    ///
    /// # Arguments
    /// * `cell` - The key and child node ID pair to insert
    ///
    /// # Returns
    /// * `Ok(())` - If the insertion was successful
    ///
    /// # Errors
    /// * `NodeError::KeyAlreadyExists` - If the key is already present in the node
    pub fn insert(&mut self, cell: Cell<K, NodeId>) -> Result<(), NodeError> {
        self.slot_directory.insert(cell)?;
        Ok(())
    }
}

impl<K> Default for InternalNode<K> {
    /// Creates a new, empty `InternalNode` with no children.
    fn default() -> Self {
        InternalNode { slot_directory: SlotDirectory::default(), right_most_child: None }
    }
}

impl<K: Debug> Debug for InternalNode<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[INTERNAL] {:?}", self.slot_directory)?;
        Ok(())
    }
}

// =====================================================================================================================
// Node
// =====================================================================================================================

/// Enum representing either a leaf node or an internal node in a B+Tree.
///
/// This enum provides a unified interface for working with different node types, allowing operations to be performed
/// without knowing the specific node type in advance.
///
/// # Variants
/// * `Leaf` - A leaf node containing key-value pairs with actual data
/// * `Internal` - An internal node containing keys and child node references
///
/// # Type Parameters
/// * `K` - The key type
/// * `V` - The value type for leaf nodes
pub enum Node<K, V> {
    Leaf(LeafNode<K, V>),
    Internal(InternalNode<K>),
}

impl<K, V> Node<K, V> {
    /// Returns a reference to the internal node if this node is an internal node, or `None` otherwise.
    ///
    /// # Returns
    /// * `Some(&InternalNode<K>)` - If this node is an internal node
    /// * `None` - If this node is a leaf node
    pub fn as_internal(&self) -> Option<&InternalNode<K>> {
        match self {
            Node::Internal(internal) => Some(internal),
            _ => None,
        }
    }

    /// Returns a mutable reference to the internal node if this node is an internal node, or `None` otherwise.
    ///
    /// # Returns
    /// * `Some(&mut InternalNode<K>)` - If this node is an internal node
    /// * `None` - If this node is a leaf node
    pub fn as_internal_mut(&mut self) -> Option<&mut InternalNode<K>> {
        match self {
            Node::Internal(internal) => Some(internal),
            _ => None,
        }
    }

    /// Returns a reference to the leaf node if this node is a leaf node, or `None` otherwise.
    ///
    /// # Returns
    /// * `Some(&LeafNode<K, V>)` - If this node is a
    /// * `None` - If this node is an internal node
    pub fn as_leaf(&self) -> Option<&LeafNode<K, V>> {
        match self {
            Node::Leaf(leaf) => Some(leaf),
            _ => None,
        }
    }

    /// Returns a mutable reference to the leaf node if this node is a leaf node, or `None` otherwise.
    ///
    /// # Returns
    /// * `Some(&mut LeafNode<K, V>)` - If this node is a leaf node
    /// * `None` - If this node is an internal node
    pub fn as_leaf_mut(&mut self) -> Option<&mut LeafNode<K, V>> {
        match self {
            Node::Leaf(leaf) => Some(leaf),
            _ => None,
        }
    }
}

impl<K: Debug, V> Debug for Node<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Leaf(leaf) => write!(f, "{:?}", leaf),
            Node::Internal(internal) => write!(f, "{:?}", internal),
        }
    }
}
