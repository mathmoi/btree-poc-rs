mod node;
mod slot_directory;

use node::{Cell, LeafNode, Node, NodeError, NodeId};
use std::{collections::HashMap, fmt::Debug};
use thiserror::Error;

// =====================================================================================================================
// Errors
// =====================================================================================================================

#[derive(Error, Debug)]
pub enum BTreeError {
    #[error("Key already exists")]
    KeyAlreadyExists,

    #[error("The minum order for a B-Tree is 3")]
    MinimumOrderNotMet,

    #[error("Unexpected error: {0}")]
    Unexpected(#[from] Box<dyn std::error::Error + Send + Sync>),
}

impl From<NodeError> for BTreeError {
    /// Converts a `NodeError` into a `BTreeError`.
    fn from(err: NodeError) -> Self {
        match err {
            NodeError::KeyAlreadyExists => BTreeError::KeyAlreadyExists,
            NodeError::Unexpected(e) => BTreeError::Unexpected(e),
            NodeError::NotInternalNode => BTreeError::Unexpected(Box::new(err)),
        }
    }
}

#[cfg(test)]
#[derive(Error, Debug)]
pub enum BTreeBuilderError {
    #[error("The right most child of the internal node already exists")]
    MostRightChildAlreadyExists,

    #[error("The parent node is not an internal node")]
    ParentNodeIsNotInternalNode,

    #[error("No node to end")]
    NoNodeToEnd,

    #[error("No current node to build upon")]
    NoCurrentNode,

    #[error("The current node is not a leaf node")]
    CurrentNodeIsNotLeaf,

    #[error(transparent)]
    NodeError(#[from] NodeError),

    #[error("Unexpected error: {0}")]
    Unexpected(#[from] Box<dyn std::error::Error + Send + Sync>),
}

// =====================================================================================================================
// BTree
// =====================================================================================================================

/// Represents a B+Tree data structure.
///
/// The structure stores nodes in a hashmap where the key is a unique node identifier and the value is the node itself.
/// It does not makes a lot of sense to have a BTree that stores it's nodes in a haBox<dyn Error>shmap in memory, but this is just a
/// proof of concept before implementing a B+Tree that stores it's nodes in a file. In the final product, nodes will be
/// stored in pages on disk and pager will manage reading and writing pages to and from disk.
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
    /// result in wider, shallower trees with better cache locality but potentially more wasted space.
    ///
    /// # Arguments
    /// * `order` - The maximum number of children each internal node can have. Must be at least 2 for a valid B-tree
    ///   structure.
    ///
    /// # Returns
    /// A new empty `BTree` ready for insertions and operations.
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

    /// Inserts a key-value pair into the BTree. If the key already exists, an error is returned.
    pub fn insert(&mut self, cell: Cell<K, V>) -> Result<(), BTreeError> {
        self.insert_recursive(self.root_node_id, cell)
    }

    fn insert_recursive(&mut self, node_id: NodeId, cell: Cell<K, V>) -> Result<(), BTreeError> {
        let Some(node) = self.nodes.get_mut(&node_id) else {
            panic!("Node id {} not found", node_id);
        };

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

impl<K, V> BTree<K, V>
where
    K: Ord + PartialEq + Clone,
    V: PartialEq + Clone,
{
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

// =====================================================================================================================
// BTreeBuilder (for tests)
// =====================================================================================================================

/// Builder for creating BTree instances with custom configurations for testing purposes.
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
    /// Sets the order of the BTree to be built.
    fn with_order(mut self, order: usize) -> Self {
        self.order = order;
        self
    }

    /// Builds and returns a new BTree instance with the specified configurations.
    fn build(self) -> BTree<K, V> {
        BTree { nodes: self.nodes, order: self.order, root_node_id: 0 }
    }

    /// Adds a new leaf node to the BTree being built.
    fn add_leaf_node(mut self, key_opt: Option<K>) -> Result<Self, BTreeBuilderError> {
        self.add_node(key_opt, Node::Leaf(LeafNode::default()))?;
        Ok(self)
    }

    fn add_internal_node(mut self, key_opt: Option<K>) -> Result<Self, BTreeBuilderError> {
        use crate::btree::node::InternalNode;

        self.add_node(key_opt, Node::Internal(InternalNode::default()))?;
        Ok(self)
    }

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

    /// Adds key-value pair to the current leaf node.
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
    /// This method is used to signal that you've finished adding children or key-value pairs to the current node and
    /// want to return to working with its parent node (or exit the current node's scope if it's the root). It pops the
    /// current node from the internal node stack, allowing subsequent builder operations to apply to the parent level.
    ///
    /// # Returns
    /// * `Ok(Self)` - Returns the builder for method chaining if a node was successfully popped
    /// * `Err(BTreeError::NoNodeToEnd)` - Returns an error if the node stack is empty
    ///
    /// # Errors
    /// Returns `BTreeError::NoNodeToEnd` when called without a corresponding node to complete, typically when
    /// `end_node()` is called more times than nodes were added.
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
