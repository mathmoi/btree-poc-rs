use super::slot_directory::{Drain as SlotDirectoryDrain, SlotDirectory, SlotDirectoryError};
use std::{fmt::Debug, ops::RangeBounds};
use thiserror::Error;

pub use super::slot_directory::Cell;

/// Unique identifier for nodes in the B+Tree.
///
/// Node IDs are used to reference nodes stored in the tree's internal storage, allowing for efficient lookup and
/// traversal operations.
pub type NodeId = u32;

// =====================================================================================================================
// NodeError
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

impl<K, V> LeafNode<K, V> {
    /// Clears all cells from the leaf node.
    pub fn clear(&mut self) {
        self.slot_directory.clear();
    }

    /// Drains a range of cells from the leaf node.
    ///
    /// # Arguments
    /// * `range` - The range of indices to drain
    ///
    /// # Returns
    /// An `SlotDirectoryDrain` iterator that yields the drained cells.
    ///
    /// # Panics
    /// * Panics if the range is invalid (start > end or end > len)
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> SlotDirectoryDrain<K, V> {
        let range = crate::utils::normalize_range(range, self.slot_directory.len());
        assert!(range.start <= range.end && range.end <= self.slot_directory.len()); // TODO : Should we return a Result instead?

        self.slot_directory.drain(range)
    }
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

    /// Returns an iterator over all key-value pairs in this leaf node.
    ///
    /// # Returns
    /// An iterator that yields references to the cells (`&Cell<K, V>`) stored in this leaf node.
    pub fn iter(&self) -> impl Iterator<Item = &Cell<K, V>> {
        self.slot_directory.iter()
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
#[derive(PartialEq, Eq)]
pub struct InternalNode<K> {
    slot_directory: SlotDirectory<K, NodeId>,
    right_most_child: Option<NodeId>,
}

impl<K> InternalNode<K> {
    /// Returns the number of children this internal node has.
    ///
    /// This count includes all children in the slot directory plus the rightmost child if it exists.
    ///
    /// # Returns
    /// The total number of child nodes
    pub fn len(&self) -> usize {
        self.slot_directory.len() + if self.right_most_child.is_some() { 1 } else { 0 }
    }
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

    /// Finds the child node ID that should be followed for the given key.
    ///
    /// # Arguments
    /// * `key` - The key to search for
    ///
    /// # Returns
    /// * `NodeId` - The ID of the child node to follow for the given key
    pub fn find_child_id(&self, key: &K) -> NodeId {
        let index = match self.slot_directory.find_index(key) {
            Ok(index) => index + 1,
            Err(index) => index,
        };

        if index < self.slot_directory.len() {
            self.slot_directory.cell_at(index).expect("There should be an Cell at this index").value
        } else {
            self.right_most_child.expect("Right most child should exist")
        }
    }
}

impl<K: Clone> InternalNode<K> {
    /// Returns the child node ID at the specified index.
    ///     
    /// # Arguments
    /// * `index` - The index of the child node to retrieve
    ///
    /// # Returns
    /// * `NodeId` - The ID of the child node at the specified index
    ///
    /// # Panics
    /// * Panics if the index is out of bounds
    pub fn child_at(&self, index: usize) -> NodeId {
        if index < self.slot_directory.len() {
            self.slot_directory.cell_at(index).unwrap().value
        } else if index == self.slot_directory.len() {
            self.right_most_child.expect("Right most child should exist")
        } else {
            panic!("Index out of bounds");
        }
    }

    /// Drains a range of cells from the internal node.
    ///
    /// The specified range is removed from the slot directory, and if the range includes the rightmost child,
    /// that child is also removed. If the rightmost child is removed and there are still
    /// cells left in the slot directory, the rightmost child is updated to be the last cell's value.
    ///
    /// If the left most child is drained it will be returned as part of a Cell with a None key.
    ///
    /// # Arguments
    /// * `range` - The range of indices to drain
    ///
    /// # Returns
    /// An `InternalNodeDrain` iterator that yields the drained cells.
    ///
    /// # Panics
    /// * Panics if the range is invalid (start > end or end > len)
    ///
    /// # Notes
    /// The node is in an invalid state after calling this method until all drained items have been consumed.
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> InternalNodeDrain<K> {
        let range = crate::utils::normalize_range(range, self.len());
        assert!(range.start <= range.end && range.end <= self.len()); // TODO : Should we return a Result instead?

        // Determine if we need to take the right most child
        let right_most_child = if range.end > self.slot_directory.len() { self.right_most_child.take() } else { None };

        // If we drain the right most child and there is at least one cell left in the slot directory after the drain,
        // we need to update the right most child to be the last cell's value
        let mut range = range;
        if self.right_most_child.is_none() && 0 < range.start {
            let removed = self.slot_directory.remove_at(range.start - 1);
            self.right_most_child = Some(removed.value);
            range = range.start - 1..range.end - 1;
        }

        // Drain the slot directory for the specified range
        let slot_directory_drain = if range.start < self.slot_directory.len() {
            let end = std::cmp::min(range.end, self.slot_directory.len());
            Some(self.slot_directory.drain(range.start..end))
        } else {
            None
        };

        InternalNodeDrain { slot_directory_drain, right_most_child }
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
// InternalNodeDrain
// =====================================================================================================================

pub struct InternalNodeDrain<'a, K> {
    slot_directory_drain: Option<SlotDirectoryDrain<'a, K, NodeId>>,
    right_most_child: Option<NodeId>,
}

impl<'a, K> Iterator for InternalNodeDrain<'a, K> {
    type Item = Cell<Option<K>, NodeId>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut inner_drain) = self.slot_directory_drain {
            if let Some(cell) = inner_drain.next() {
                return Some(Cell { key: Some(cell.key), value: cell.value });
            } else {
                self.slot_directory_drain = None;
            }
        }

        if let Some(right_most_child) = self.right_most_child.take() {
            return Some(Cell { key: None, value: right_most_child });
        }

        None
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

    /// Returns a reference to the internal node if this node is an internal node.
    ///
    /// # Returns
    /// * `&InternalNode<K>` - If this node is an internal node
    ///
    /// # Panics
    /// * Panics if this node is a leaf node
    pub fn as_internal_unchecked(&self) -> &InternalNode<K> {
        match self {
            Node::Internal(internal) => internal,
            _ => panic!("Called as_internal_unchecked on a leaf node"),
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

    /// Returns a mutable reference to the internal node if this node is an internal node.
    ///
    /// # Returns
    /// * `&mut InternalNode<K>` - If this node is an internal node
    ///
    /// # Panics
    /// * Panics if this node is a leaf node
    pub fn as_internal_mut_unchecked(&mut self) -> &mut InternalNode<K> {
        match self {
            Node::Internal(internal) => internal,
            _ => panic!("Called as_internal_mut_unchecked on a leaf node"),
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

    /// Checks if the node is overflowing based on the given order.
    ///
    /// A node is considered overflowing if it contains more keys than allowed by the B+Tree order. For a B+Tree of
    /// order `m`, a node can contain at most `m - 1` keys.
    ///
    /// # Arguments
    /// * `order` - The order of the B+Tree
    ///
    /// # Returns
    /// * `true` if the node is overflowing, `false` otherwise
    pub fn is_overflowing(&self, order: usize) -> bool {
        match self {
            Node::Leaf(leaf) => leaf.slot_directory.is_overflowing(order),
            Node::Internal(internal) => internal.slot_directory.is_overflowing(order),
        }
    }

    /// Checks if the node is underflowing based on the given order.
    ///
    /// A node is considered underflowing if it contains fewer keys than the minimum required by the B+Tree order. For a
    /// B+Tree of order `m`, a node must contain at least `ceil(m / 2) - 1` keys, except for the root node which can
    ///      have fewer keys. This method does not check if the node is the root; it simply checks the key count against
    ///      the minimum.
    ///
    /// # Arguments
    /// * `order` - The order of the B+Tree
    ///
    /// # Returns
    /// * `true` if the node is underflowing, `false` otherwise
    pub fn is_underflowing(&self, order: usize) -> bool {
        match self {
            Node::Leaf(leaf) => leaf.slot_directory.is_underflowing(order),
            Node::Internal(internal) => internal.slot_directory.is_underflowing(order),
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

// =====================================================================================================================
// Tests
// =====================================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    mod leaf_node {
        use super::*;

        #[test]
        fn after_calling_clear_len_is_0() {
            let mut leaf: LeafNode<u32, u32> = LeafNode::default();
            leaf.insert(Cell { key: 1, value: 10 }).unwrap();
            leaf.insert(Cell { key: 2, value: 20 }).unwrap();
            assert_eq!(leaf.slot_directory.len(), 2);
            leaf.clear();
            assert_eq!(leaf.slot_directory.len(), 0);
        }
    }

    mod internal_node {
        use super::*;

        #[test]
        fn draining_from_middle() {
            let mut internal: InternalNode<u32> = InternalNode::default();
            internal.insert(Cell { key: 1, value: 10 }).unwrap();
            internal.insert(Cell { key: 2, value: 20 }).unwrap();
            internal.insert(Cell { key: 3, value: 30 }).unwrap();
            internal.set_right_most_child(40);

            let drained: Vec<Cell<Option<u32>, NodeId>> = internal.drain(1..3).collect();

            let expected_drained = vec![Cell { key: Some(2), value: 20 }, Cell { key: Some(3), value: 30 }];
            assert_eq!(drained, expected_drained);

            let mut expected_remaining: InternalNode<u32> = InternalNode::default();
            expected_remaining.insert(Cell { key: 1, value: 10 }).unwrap();
            expected_remaining.set_right_most_child(40);
            assert_eq!(internal, expected_remaining);
        }

        #[test]
        fn draining_including_right_most_child() {
            let mut internal: InternalNode<u32> = InternalNode::default();
            internal.insert(Cell { key: 1, value: 10 }).unwrap();
            internal.insert(Cell { key: 2, value: 20 }).unwrap();
            internal.set_right_most_child(30);

            let drained: Vec<Cell<Option<u32>, NodeId>> = internal.drain(1..3).collect();

            let expected_drained = vec![Cell { key: Some(2), value: 20 }, Cell { key: None, value: 30 }];
            assert_eq!(drained, expected_drained);

            let mut expected_remaining: InternalNode<u32> = InternalNode::default();
            expected_remaining.set_right_most_child(10);
            assert_eq!(internal, expected_remaining);
        }

        #[test]
        fn draining_all() {
            let mut internal: InternalNode<u32> = InternalNode::default();
            internal.insert(Cell { key: 1, value: 10 }).unwrap();
            internal.insert(Cell { key: 2, value: 20 }).unwrap();
            internal.set_right_most_child(30);

            let drained: Vec<Cell<Option<u32>, NodeId>> = internal.drain(0..3).collect();

            let expected_drained =
                vec![Cell { key: Some(1), value: 10 }, Cell { key: Some(2), value: 20 }, Cell { key: None, value: 30 }];
            assert_eq!(drained, expected_drained);

            let expected_remaining: InternalNode<u32> = InternalNode::default();
            assert_eq!(internal, expected_remaining);
        }
    }
}
