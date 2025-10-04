use super::slot_directory::{SlotDirectory, SlotDirectoryError};
use std::fmt::Debug;
use thiserror::Error;

pub use super::slot_directory::Cell;

pub type NodeId = u32;

// =====================================================================================================================
// CellError
// =====================================================================================================================

#[derive(Error, Debug)]
pub enum NodeError {
    #[error("Key already exists")]
    KeyAlreadyExists,

    #[error("The node is not an internal node")]
    NotInternalNode,

    #[error("Unexpected error: {0}")]
    Unexpected(#[from] Box<dyn std::error::Error + Send + Sync>),
}

impl From<SlotDirectoryError> for NodeError {
    /// Converts a `SlotDirectoryError` into a `NodeError`.
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

/// Represents a leaf node in a B+Tree. Leaf nodes contains key-value pairs where the value is the data being stored in
/// the B+Tree. Leaf nodes are linked together to allow for efficient range queries.
pub struct LeafNode<K: Ord + Clone, V: Clone> {
    slot_directory: SlotDirectory<K, V>,
    next_leaf: Option<u32>,
}

impl<K: Ord + Clone, V: Clone> LeafNode<K, V> {
    /// Inserts a cell into the leaf node.
    pub fn insert(&mut self, cell: Cell<K, V>) -> Result<(), NodeError> {
        self.slot_directory.insert(cell)?;
        Ok(())
    }
}

impl<K: Ord + Clone, V: Clone> Default for LeafNode<K, V> {
    /// Creates a new, empty `LeafNode`.
    fn default() -> Self {
        LeafNode { slot_directory: SlotDirectory::default(), next_leaf: None }
    }
}

impl<K: Ord + Clone + Debug, V: Clone> Debug for LeafNode<K, V> {
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

/// Represents an internal node in a B+Tree. Internals nodes contains keys and refernces to child nodes.
pub struct InternalNode<K>
where
    K: Ord + Clone,
{
    slot_directory: SlotDirectory<K, NodeId>,
    right_most_child: Option<NodeId>,
}

impl<K> InternalNode<K>
where
    K: Ord + Clone,
{
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
    pub fn len(&self) -> usize {
        self.slot_directory.len() + if self.right_most_child.is_some() { 1 } else { 0 }
    }

    /// Returns the right most child of this internal node, if it exists.
    pub fn right_most_child(&self) -> Option<NodeId> {
        self.right_most_child
    }

    /// Sets the right most child of this internal node.
    pub fn set_right_most_child(&mut self, child: NodeId) {
        self.right_most_child = Some(child);
    }

    /// Inserts a cell into the internal node.
    pub fn insert(&mut self, cell: Cell<K, NodeId>) -> Result<(), NodeError> {
        self.slot_directory.insert(cell)?;
        Ok(())
    }
}

impl<K> Default for InternalNode<K>
where
    K: Ord + Clone,
{
    /// Creates a new, empty `InternalNode`.
    fn default() -> Self {
        InternalNode { slot_directory: SlotDirectory::default(), right_most_child: None }
    }
}

impl<K> Debug for InternalNode<K>
where
    K: Ord + Debug + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[INTERNAL] {:?}", self.slot_directory)?;
        Ok(())
    }
}

// =====================================================================================================================
// Node
// =====================================================================================================================

/// Enum that can store either a leaf node or an internal node.
pub enum Node<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    Leaf(LeafNode<K, V>),
    Internal(InternalNode<K>),
}

impl<K, V> Debug for Node<K, V>
where
    K: Ord + Debug + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Node::Leaf(leaf) => write!(f, "{:?}", leaf),
            Node::Internal(internal) => write!(f, "{:?}", internal),
        }
    }
}
