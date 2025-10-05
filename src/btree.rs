mod node;
mod slot_directory;

use node::{Cell, LeafNode, Node, NodeError, NodeId};
use std::{collections::HashMap, fmt::Debug};
use thiserror::Error;

// =====================================================================================================================
// Errors
// =====================================================================================================================

/// Errors that can occur during B+Tree operations.
#[derive(Error, Debug)]
pub enum BTreeError {
    /// Attempted to insert a key that already exists in the tree.
    #[error("Attempted to insert a key that already exists in the tree")]
    KeyAlreadyExists,

    /// The specified order is below the minimum required for a valid B+Tree.
    ///
    /// B+Trees require a minimum order of 3 to maintain their structural properties.
    #[error("The minimum order for a B-Tree is 3")]
    MinimumOrderNotMet,

    /// An unexpected error occurred during a B+Tree operation.
    #[error("Unexpected error: {0}")]
    Unexpected(#[from] Box<dyn std::error::Error + Send + Sync>),
}

impl From<NodeError> for BTreeError {
    fn from(err: NodeError) -> Self {
        match err {
            NodeError::KeyAlreadyExists => BTreeError::KeyAlreadyExists,
            NodeError::Unexpected(e) => BTreeError::Unexpected(e),
            NodeError::NotInternalNode => BTreeError::Unexpected(Box::new(err)),
        }
    }
}

/// Errors that can occur during B+Tree construction using the builder pattern.
///
/// This error type is only available in test builds and is used by `BTreeBuilder`
/// to provide detailed error information during tree construction for testing purposes.
#[cfg(test)]
#[derive(Error, Debug)]
pub enum BTreeBuilderError {
    /// Attempted to set a rightmost child when one already exists.
    #[error("Attempted to set a rightmost child when one already exists")]
    MostRightChildAlreadyExists,

    /// Attempted to add a child to a node that is not an internal node.
    #[error("The parent node is not an internal node")]
    ParentNodeIsNotInternalNode,

    /// Called `end_node()` without a corresponding node to complete.
    #[error("No node to end")]
    NoNodeToEnd,

    /// Attempted an operation that requires a current node when none exists.
    #[error("No current node to build upon")]
    NoCurrentNode,

    /// Attempted to add a key-value pair to a node that is not a leaf node.
    #[error("The current node is not a leaf node")]
    CurrentNodeIsNotLeaf,

    /// A node operation failed during tree construction.
    #[error(transparent)]
    NodeError(#[from] NodeError),

    /// An unexpected error occurred during tree construction.
    #[error("Unexpected error: {0}")]
    Unexpected(#[from] Box<dyn std::error::Error + Send + Sync>),
}

// =====================================================================================================================
// BTree
// =====================================================================================================================

/// Represents a B+Tree data structure.
///
/// This implementation stores nodes in a hashmap where the key is a unique node identifier and the value is the node
/// itself. While storing nodes in memory via a hashmap is not typical for production B+Trees, this design serves as a
/// proof of concept before implementing a B+Tree that stores nodes in disk pages. In the final implementation, nodes
/// will be stored in pages on disk and a pager will manage reading and writing pages to and from disk.
///
/// # Type Parameters
/// * `K` - The key type, which must be orderable, debuggable, and cloneable
/// * `V` - The value type, which must be debuggable and cloneable
pub struct BTree<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    nodes: HashMap<NodeId, Node<K, V>>,
    order: usize,
    root_node_id: NodeId,
}

impl<K, V> BTree<K, V>
where
    K: Ord + Debug + Clone,
    V: Debug + Clone,
{
    /// Creates a new, empty `BTree` with the specified order.
    ///
    /// The order determines the branching factor of the tree, which affects performance characteristics. Higher orders
    /// result in wider, shallower trees with better cache locality but potentially more wasted space. The order
    /// represents the maximum number of children an internal node can have.
    ///
    /// # Arguments
    /// * `order` - The maximum number of children each internal node can have. Must be at least 3 for a valid B+Tree
    ///   structure.
    ///
    /// # Returns
    /// * `Ok(BTree)` - A new empty B+Tree ready for insertions
    ///
    /// # Errors
    /// * `BTreeError::MinimumOrderNotMet` - If the order is less than 3
    pub fn new(order: usize) -> Result<Self, BTreeError> {
        if order < 3 {
            return Err(BTreeError::MinimumOrderNotMet);
        }

        let root_node = Node::<K, V>::Leaf(LeafNode::<K, V>::default());
        let mut nodes = HashMap::new();
        nodes.insert(0, root_node);
        Ok(BTree::<K, V> { nodes, order, root_node_id: 0 })
    }

    // TODO : Implement search

    /// Inserts a key-value pair into the B+Tree.
    ///
    /// The insertion maintains the B+Tree properties by recursively traversing to the appropriate leaf node and
    /// inserting the cell. If the key already exists anywhere in the tree, the insertion fails.
    ///
    /// # Arguments
    /// * `cell` - The key-value pair to insert
    ///
    /// # Returns
    /// * `Ok(())` - If the insertion was successful
    ///
    /// # Errors
    /// * `BTreeError::KeyAlreadyExists` - If the key is already present in the tree
    pub fn insert(&mut self, cell: Cell<K, V>) -> Result<(), BTreeError> {
        self.insert_recursive(self.root_node_id, cell)
    }

    /// Recursively inserts a cell into the tree starting from the specified node.
    ///
    /// This is an internal helper method that performs the actual recursive insertion logic. Currently only supports
    /// insertion into leaf nodes.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to start insertion from
    /// * `cell` - The key-value pair to insert
    ///
    /// # Returns
    /// * `Ok(())` - If the insertion was successful
    ///
    /// # Errors
    /// * `BTreeError::KeyAlreadyExists` - If the key is already present in the node
    ///
    /// # Panics
    /// Panics if the specified node ID does not exist in the tree's node storage. This indicates a bug in the tree
    /// implementation, as all node IDs passed to this method should be valid by invariant.
    fn insert_recursive(&mut self, node_id: NodeId, cell: Cell<K, V>) -> Result<(), BTreeError> {
        let node = self.nodes.get_mut(&node_id).expect("Node ID should exist in the tree");

        match node {
            Node::Leaf(leaf) => {
                leaf.insert(cell)?;
                Ok(())
            }
            Node::Internal(_internal) => {
                unimplemented!("Internal node insertion not yet implemented");
            }
        }
    }

    /// Formats a node and its descendants in a tree-like structure.
    ///
    /// This is an internal helper method used by the `Debug` implementation to recursively format the tree structure
    /// with proper indentation and tree connectors.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to format
    /// * `prefix` - The string prefix for indentation (accumulated through recursion)
    /// * `is_last` - Whether this node is the last child of its parent
    /// * `f` - The formatter to write to
    ///
    /// # Returns
    /// * `Ok(())` - If formatting was successful
    /// * `Err` - If a formatting error occurred
    fn fmt_node(
        &self,
        node_id: NodeId,
        prefix: &str,
        is_last: bool,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let connector = if is_last { "└── " } else { "├── " };
        let node = self.nodes.get(&node_id).unwrap();

        writeln!(f, "{}{}{:?}", prefix, connector, node)?;

        // If it's an internal node, recursively print its children
        if let Node::Internal(internal_node) = node {
            let child_prefix = format!("{}{}", prefix, if is_last { "    " } else { "│   " });
            for (i, child_id) in internal_node.children().enumerate() {
                let is_last_child = i == internal_node.len() - 1;
                self.fmt_node(child_id, &child_prefix, is_last_child, f)?;
            }
        }
        Ok(())
    }

    // TODO : Implement deletion
}

impl<K, V> BTree<K, V>
where
    K: Ord + PartialEq + Clone,
    V: PartialEq + Clone,
{
    /// Recursively checks if two nodes and their subtrees are equal.
    ///
    /// This helper method performs a deep comparison of node structures, comparing not only the keys but also
    /// recursively comparing all child nodes in the subtrees.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node in this tree to compare
    /// * `other` - The other B+Tree to compare against
    /// * `other_node_id` - The ID of the node in the other tree to compare with
    ///
    /// # Returns
    /// `true` if the nodes and their entire subtrees are equal, `false` otherwise
    fn check_node_eq_recursive(&self, node_id: NodeId, other: &BTree<K, V>, other_node_id: NodeId) -> bool {
        let self_node = self.nodes.get(&node_id);
        let other_node = other.nodes.get(&other_node_id);

        match (self_node, other_node) {
            (Some(Node::Leaf(self_leaf)), Some(Node::Leaf(other_leaf))) => self_leaf == other_leaf,
            (Some(Node::Internal(self_internal)), Some(Node::Internal(other_internal))) => {
                if self_internal.len() != other_internal.len() {
                    return false;
                }

                if self_internal.keys().ne(other_internal.keys()) {
                    return false;
                }

                // Recursively check all children
                for (self_child_id, other_child_id) in self_internal.children().zip(other_internal.children()) {
                    if !self.check_node_eq_recursive(self_child_id, other, other_child_id) {
                        return false;
                    }
                }
                true
            }
            _ => false, // One is leaf and the other is internal or one of them doesn't exist
        }
    }
}

impl<K, V> PartialEq for BTree<K, V>
where
    K: Ord + PartialEq + Clone,
    V: PartialEq + Clone,
{
    fn eq(&self, other: &Self) -> bool {
        self.order == other.order && self.check_node_eq_recursive(self.root_node_id, other, other.root_node_id)
    }
}

impl<K, V> Debug for BTree<K, V>
where
    K: Ord + Debug + Clone,
    V: Debug + Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "B+Tree (order={}):", self.order)?;
        self.fmt_node(self.root_node_id, "", true, f)?;
        Ok(())
    }
}

// =====================================================================================================================
// BTreeBuilder (for tests)
// =====================================================================================================================

/// Builder for creating B+Tree instances with custom configurations for testing purposes.
///
/// This builder provides a fluent interface for constructing B+Trees with specific structures, allowing tests to create
/// complex tree configurations easily. The builder maintains a stack of nodes being constructed, enabling hierarchical
/// node creation.
///
/// # Type Parameters
/// * `K` - The key type, which must be orderable and cloneable
/// * `V` - The value type, which must be cloneable
///
/// # Note
/// This type is only available in test builds.
#[cfg(test)]
struct BTreeBuilder<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    order: usize,
    nodes: HashMap<NodeId, Node<K, V>>,
    next_node_id: NodeId,
    node_id_stack: Vec<NodeId>,
}

/// Creates a new `BTreeBuilder` with default configurations.
///
/// The default builder starts with:
/// - Order of 3 (minimum valid B+Tree order)
/// - Empty node collection
/// - Node ID counter starting at 0
/// - Empty node stack
#[cfg(test)]
impl<K, V> Default for BTreeBuilder<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    /// Creates a new `BTreeBuilder` with default configurations.
    fn default() -> Self {
        BTreeBuilder::<K, V> { order: 3, nodes: HashMap::new(), next_node_id: 0, node_id_stack: Vec::new() }
    }
}

#[cfg(test)]
impl<K, V> BTreeBuilder<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    /// Sets the order of the B+Tree to be built.
    ///
    /// # Arguments
    /// * `order` - The maximum number of children each internal node can have
    ///
    /// # Returns
    /// The builder instance for method chaining
    fn with_order(mut self, order: usize) -> Self {
        self.order = order;
        self
    }

    /// Builds and returns a new B+Tree instance with the configured nodes and order.
    ///
    /// This consumes the builder and produces the final B+Tree. The root node is assumed to be the node with ID 0.
    ///
    /// # Returns
    /// A fully constructed `BTree` instance
    fn build(self) -> BTree<K, V> {
        BTree { nodes: self.nodes, order: self.order, root_node_id: 0 }
    }

    /// Adds a new leaf node to the B+Tree being built.
    ///
    /// If a key is provided and there is a parent node on the stack, the new leaf is attached to the parent as a child
    /// with the given key as the separator. If no key is provided, the leaf is set as the parent's rightmost child.
    ///
    /// # Arguments
    /// * `key_opt` - Optional key to use as separator in the parent node. If `None` and a parent exists, this node
    ///   becomes the rightmost child.
    ///
    /// # Returns
    /// * `Ok(Self)` - The builder instance for method chaining
    ///
    /// # Errors
    /// * `BTreeBuilderError::ParentNodeIsNotInternalNode` - If the parent is not an internal node
    /// * `BTreeBuilderError::MostRightChildAlreadyExists` - If trying to set a rightmost child when one already exists
    /// * `BTreeBuilderError::NodeError` - If inserting the key-child pair into the parent fails
    fn add_leaf_node(mut self, key_opt: Option<K>) -> Result<Self, BTreeBuilderError> {
        self.add_node(key_opt, Node::Leaf(LeafNode::default()))?;
        Ok(self)
    }

    /// Adds a new internal node to the B+Tree being built.
    ///
    /// If a key is provided and there is a parent node on the stack, the new internal node is attached to the parent as
    /// a child with the given key as the separator. If no key is provided, the internal node is set as the parent's
    /// rightmost child.
    ///
    /// # Arguments
    /// * `key_opt` - Optional key to use as separator in the parent node. If `None` and a parent exists, this node
    ///   becomes the rightmost child.
    ///
    /// # Returns
    /// * `Ok(Self)` - The builder instance for method chaining
    ///
    /// # Errors
    /// * `BTreeBuilderError::ParentNodeIsNotInternalNode` - If the parent is not an internal node
    /// * `BTreeBuilderError::MostRightChildAlreadyExists` - If trying to set a rightmost child when one already exists
    /// * `BTreeBuilderError::NodeError` - If inserting the key-child pair into the parent fails
    fn add_internal_node(mut self, key_opt: Option<K>) -> Result<Self, BTreeBuilderError> {
        use crate::btree::node::InternalNode;

        self.add_node(key_opt, Node::Internal(InternalNode::default()))?;
        Ok(self)
    }

    /// Internal helper method that adds a node to the tree being built.
    ///
    /// This method handles the common logic for adding both leaf and internal nodes, including assigning node IDs,
    /// attaching to parent nodes, and managing the node stack.
    ///
    /// # Arguments
    /// * `key_opt` - Optional key for attaching to the parent. If `None` and a parent exists, this node becomes the
    ///   rightmost child.
    /// * `new_node` - The node to add to the tree
    ///
    /// # Returns
    /// * `Ok(())` - If the node was successfully added
    ///
    /// # Errors
    /// * `BTreeBuilderError::ParentNodeIsNotInternalNode` - If the parent is not an internal node
    /// * `BTreeBuilderError::MostRightChildAlreadyExists` - If trying to set a rightmost child when one already exists
    /// * `BTreeBuilderError::NodeError` - If inserting the key-child pair into the parent fails
    fn add_node(&mut self, key_opt: Option<K>, new_node: Node<K, V>) -> Result<(), BTreeBuilderError> {
        let new_node_id = self.next_node_id;
        self.next_node_id += 1;

        // If there is a parent node, we need to attach the new node to it.
        if let Some(parent_node_id) = self.node_id_stack.last() {
            let parent_node =
                match self.nodes.get_mut(parent_node_id).expect("Parent node should be present in the nodes map") {
                    Node::Internal(internal) => internal,
                    _ => return Err(BTreeBuilderError::ParentNodeIsNotInternalNode),
                };

            if let Some(key) = key_opt {
                parent_node.insert(Cell::new(key, new_node_id))?;
            } else {
                // No key provided, we are adding the right most child.
                if parent_node.right_most_child().is_some() {
                    return Err(BTreeBuilderError::MostRightChildAlreadyExists);
                }
                parent_node.set_right_most_child(new_node_id);
            }
        }

        self.nodes.insert(new_node_id, new_node);
        self.node_id_stack.push(new_node_id);

        Ok(())
    }

    /// Adds a key-value pair to the current leaf node.
    ///
    /// The current node is the most recently added node that has not been closed with `end_node()`. This method can
    /// only be called when the current node is a leaf node.
    ///
    /// # Arguments
    /// * `key` - The key of the pair to insert
    /// * `value` - The value of the pair to insert
    ///
    /// # Returns
    /// * `Ok(Self)` - The builder instance for method chaining
    ///
    /// # Errors
    /// * `BTreeBuilderError::NoCurrentNode` - If there is no current node on the stack
    /// * `BTreeBuilderError::CurrentNodeIsNotLeaf` - If the current node is not a leaf node
    /// * `BTreeBuilderError::NodeError` - If the key already exists in the leaf node
    fn add_key_value_pair(mut self, key: K, value: V) -> Result<Self, BTreeBuilderError> {
        let node_id = self.node_id_stack.last().ok_or(BTreeBuilderError::NoCurrentNode)?;
        let leaf_node = match self.nodes.get_mut(node_id) {
            Some(Node::Leaf(leaf)) => leaf,
            _ => return Err(BTreeBuilderError::CurrentNodeIsNotLeaf),
        };

        leaf_node.insert(Cell::new(key, value))?;
        Ok(self)
    }

    /// Completes the current node and returns to the parent node context in the builder chain.
    ///
    /// This method signals that you have finished adding children or key-value pairs to the current node and want to
    /// return to working with its parent node (or exit the current node's scope if it is the root). It pops the current
    /// node from the internal node stack, allowing subsequent builder operations to apply to the parent level.
    ///
    /// # Returns
    /// * `Ok(Self)` - The builder instance for method chaining
    ///
    /// # Errors
    /// * `BTreeBuilderError::NoNodeToEnd` - If the node stack is empty (no node to complete)
    fn end_node(mut self) -> Result<Self, BTreeBuilderError> {
        self.node_id_stack.pop().ok_or(BTreeBuilderError::NoNodeToEnd)?;
        Ok(self)
    }
}

// =====================================================================================================================
// Tests
// =====================================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    mod btree_tests {
        use super::*;
        use std::error::Error;

        #[test]
        fn when_inserting_key_value_pair_into_empty_btree_succeeds() -> Result<(), Box<dyn Error>> {
            let mut btree = BTree::<u32, u32>::new(3)?;
            let result = btree.insert(Cell::new(1, 42));
            assert!(result.is_ok());
            Ok(())
        }

        #[test]
        fn when_inserting_a_key_already_present_insertions_fails() -> Result<(), Box<dyn Error>> {
            #[rustfmt::skip]
            let mut btree = BTreeBuilder::<u32, u32>::default()
                .add_leaf_node(None)?
                    .add_key_value_pair(1, 42)?
                .end_node()?
                .build();
            let result = btree.insert(Cell::new(1, 43));
            assert!(matches!(result, Err(BTreeError::KeyAlreadyExists)));
            Ok(())
        }

        #[test]
        fn when_inserting_two_different_keys_both_insertions_succeed() -> Result<(), Box<dyn Error>> {
            #[rustfmt::skip]
            let mut btree = BTreeBuilder::<u32, u32>::default()
                .add_leaf_node(None)?
                    .add_key_value_pair(1, 42)?
                .end_node()?
                .build();
            let result = btree.insert(Cell::new(2, 43));
            assert!(matches!(result, Ok(())));
            Ok(())
        }

        // /// When the btree is only a root node and the root node is full, inserting a new key-value pair should create a
        // /// new root node and split the existing root node into two child nodes.
        // ///
        // /// ```text
        // ///              Insert 3
        // ///                 |
        // ///                 v
        // ///           +-----+-----+
        // ///           |  1  |  2  |
        // ///           +-----+-----+
        // ///
        // ///
        // ///              Result
        // ///                 |
        // ///                 v
        // ///           +-----+-----+
        // ///       +-- |  3  |     |--+
        // ///       |   +-----+-----+  |
        // ///       v                  v
        // /// +-----+-----+      +-----+-----+
        // /// |  1  |  2  |      |  3  |     |
        // /// +-----+-----+      +-----+-----+
        // /// ```
        // #[test]
        // fn when_root_node_full_insertion_creates_new_root() {
        //     #[rustfmt::skip]
        //     let mut btree = BTreeBuilder::<u32, u32>::default()
        //         .with_order(3)
        //         .add_leaf_node()
        //             .add_key_value_pair(1, 42)
        //             .add_key_value_pair(2, 43)
        //         .end_node()
        //         .build();

        //     #[rustfmt::skip]
        //     let expected = BTreeBuilder::<u32, u32>::default()
        //         .with_order(3)
        //         .add_internal_node()
        //             .add_leaf_node() // Left child of new root
        //                 .add_key_value_pair(1, 42)
        //                 .add_key_value_pair(2, 43)
        //             .end_node()
        //             .add_leaf_node() // Right child of new root
        //                 .add_key_value_pair(3, 44)
        //             .end_node()
        //         .end_node()
        //         .build();

        //     let result = btree.insert(3, 44);

        //     assert!(matches!(result, Ok(())));
        //     assert_eq!(expected, btree);
        // }
    }
}
