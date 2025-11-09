mod node;
mod slot_directory;

use node::{Cell, LeafNode, Node, NodeError, NodeId};
use std::{
    cell::{Ref, RefCell, RefMut},
    collections::HashMap,
    fmt::Debug,
    iter,
};
use thiserror::Error;

use crate::btree::node::InternalNode;

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
/// * `K` - The key type
/// * `V` - The value type
pub struct BTree<K, V> {
    nodes: HashMap<NodeId, Node<K, V>>,
    order: usize,
    root_node_id: NodeId,
    next_node_id: NodeId,
}

impl<K, V> BTree<K, V> {
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
        Ok(BTree::<K, V> { nodes: HashMap::from([(0, root_node)]), order, root_node_id: 0, next_node_id: 1 })
    }

    /// Adds a new node to the tree and returns its assigned ID.
    ///
    /// This is an internal helper method used to allocate new nodes during tree operations.
    ///
    /// # Arguments
    /// * `node` - The node to add to the tree
    ///
    /// # Returns
    /// * `NodeId` - The unique ID assigned to the newly added node
    fn register_new_node(&mut self, node: Node<K, V>) -> NodeId {
        let new_node_id = self.next_node_id;
        self.next_node_id += 1;
        self.nodes.insert(new_node_id, node);
        new_node_id
    }

    /// Retrieves a reference to a node by its ID.
    ///
    /// The node ID must exist in the tree's node storage; otherwise, this method will panic. This is an internal helper
    /// method used to access nodes during tree operations.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to retrieve
    ///
    /// # Returns
    /// * `&Node<K, V>` - A reference to the node with the specified ID
    ///
    /// # Panics
    /// Panics if the specified node ID does not exist in the tree's node storage. This indicates a bug in the tree
    fn get_node(&self, node_id: NodeId) -> &Node<K, V> {
        self.nodes.get(&node_id).expect("Node ID should exist in the tree")
    }

    /// Retrieves a mutable reference to a node by its ID.
    ///
    /// The node ID must exist in the tree's node storage; otherwise, this method will panic. This is an internal helper
    /// method used to access nodes during tree operations.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to retrieve
    ///
    /// # Returns
    /// * `&mut Node<K, V>` - A mutable reference to the node with the specified ID
    ///
    /// # Panics
    /// Panics if the specified node ID does not exist in the tree's node storage. This indicates a bug in the tree
    fn get_node_mut(&mut self, node_id: NodeId) -> &mut Node<K, V> {
        self.nodes.get_mut(&node_id).expect("Node ID should exist in the tree")
    }

    // TODO : Implement search
    // TODO : Implement deletion
}

impl<K: Debug + Clone + Ord, V: Debug + Clone> BTree<K, V> {
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
        self.insert_recursive(0, cell, Vec::new())
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
    fn insert_recursive(&mut self, node_id: NodeId, cell: Cell<K, V>, parents: Vec<NodeId>) -> Result<(), BTreeError> {
        let mut node = self.get_node_mut(node_id);

        match &mut *node {
            Node::Leaf(leaf) => {
                leaf.insert(cell)?;
                drop(node);
                self.balance_leaf(node_id, parents);
                Ok(())
            }
            Node::Internal(_internal) => {
                unimplemented!("Internal node insertion not yet implemented");
            }
        }
    }

    /// Calculates a balanced distribution of cells across the specified number of nodes.
    ///
    /// This is an internal helper method used during balancing operations to determine how many cells should be
    /// assigned to each node to achieve a balanced state. When the cells cannot be evenly distributed, the method
    /// ensures that the first few nodes receive one extra cell until all cells are allocated.
    ///
    /// # Arguments
    /// * `cells_count` - The total number of cells to distribute
    /// * `nodes_count` - The number of nodes to distribute the cells across
    ///
    /// # Returns
    /// * `Vec<usize>` - A vector where each element represents the number of cells assigned to the corresponding node
    fn calculate_balanced_cells_distribution(cells_count: usize, nodes_count: usize) -> Vec<usize> {
        let base_cells_per_node = cells_count / nodes_count;
        let remainder = cells_count % nodes_count;

        std::iter::repeat_n(base_cells_per_node + 1, remainder)
            .chain(std::iter::repeat_n(base_cells_per_node, nodes_count - remainder))
            .collect()
    }

    /// Balance the tree starting from the nodes in the provided stack.
    ///
    /// This is an internal helper method that performs the actual balancing logic after insertions or deletions.
    ///
    /// # Algorithm
    ///
    /// First we check if the node to balance is the root node (single node in the node_id_stack). If it is the case,
    /// we check if the root node is overflowing. If it is, we need to create a new node, move all the cells from
    /// the root node to the new node and set the new node as a chilf of the root node and continue balancing from the
    /// new node. In this way, the overflowing node will be split and the root node remains the same. This is important
    /// because the root node id must remains the same.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to start balancing from
    /// * `parents` - A stack of parent node IDs leading to the node to balance from the root of the tree
    ///
    /// # References
    /// * [Antonio Sarosi's implementation of a BTree](https://github.com/antoniosarosi/mkdb/blob/master/src/storage/btree.rs)
    fn balance_leaf(&mut self, mut node_id: NodeId, mut parents: Vec<NodeId>) {
        let is_root = parents.is_empty();

        // Special case for the root node
        if is_root {
            let is_overflowing = self.get_node(node_id).is_overflowing(self.order);
            if is_overflowing {
                let new_id = self.grow_new_root(node_id); // TODO : Could we need to balance a root we just grew?

                parents.push(node_id);
                node_id = new_id;
            } else {
                return;
            }
        }

        // Find the index of the current node in it's parent
        let parent_id = parents.last().cloned().expect("There should be a parent");
        let parent = self.get_node_mut(parent_id).as_internal_mut_unchecked();
        let index_in_parent =
            parent.children().position(|id| id == node_id).expect("Node should be a child of its parent");

        // Find the index of the sibling nodes that will participate in the balancing
        let (start_sibling_index, end_sibling_index) =
            BTree::<K, V>::get_index_siblings_balance(index_in_parent, parent.len());

        // Removes the nodes participating in the balancing from the parent
        let mut siblings = parent.drain(start_sibling_index..=end_sibling_index).collect::<Vec<_>>();

        // Removes the cells from the nodes to balance
        let mut cells: Vec<Cell<K, V>> = Vec::new(); // TODO : Should this be a VecDeque?
        for sibling in &siblings {
            let node = self.get_node_mut(sibling.value).as_leaf_mut().expect("Node should be a leaf"); // TODO : Generalize for internal nodes
            cells.extend(node.drain(..));
        }

        let last_separator_key = siblings.pop().expect("There should be at least one sibling to balance").key;

        let mut sibling_ids: Vec<NodeId> = siblings.iter().map(|cell| cell.value).collect();

        // Calculate the number of nodes needed after balancing
        let cells_per_node = self.order - 1; // TODO : would be self.order for internal nodes
        let num_nodes_needed = cells.len().div_ceil(cells_per_node);

        // TODO : From here maybe siblings should not be a Vec<Cell<K, V>> but a Vec<NodeId>?
        // TODO : Remove excess nodes if we have more than needed
        // Add new nodes if we needs more
        sibling_ids.resize_with(num_nodes_needed, || {
            self.register_new_node(Node::Leaf(LeafNode::<K, V>::default())) // TODO : Generalize for internal nodes
        });

        // Calculate the balanced distribution of cells across the nodes
        let balanced_distribution = BTree::<K, V>::calculate_balanced_cells_distribution(cells.len(), num_nodes_needed);

        // Distribute the cells to the nodes according to the balanced distribution and insert them back to the parent
        // TODO : Would it be more efficient to do this backwards to avoid shifting on drain?
        for (index, (&sibling_id, &distribution_count)) in
            sibling_ids.iter().zip(balanced_distribution.iter()).enumerate()
        {
            let node = self.get_node_mut(sibling_id).as_leaf_mut().expect("Node should be a leaf"); // TODO : Generalize for internal nodes
            for cell in cells.drain(0..distribution_count) {
                node.insert(cell).expect("Insertion should succeed, key uniqueness is guaranteed");
            }

            let parent = self.get_node_mut(parent_id).as_internal_mut_unchecked();
            if index < sibling_ids.len() - 1 {
                parent
                    .insert(Cell {
                        key: cells.first().expect("There should be cells remaining").key.clone(),
                        value: sibling_id,
                    })
                    .expect("Insertion into parent should succeed");
            } else {
                match last_separator_key.clone() {
                    Some(key) => {
                        parent.insert(Cell { key, value: sibling_id }).expect("Insertion into parent should succeed")
                    }
                    None => parent.set_right_most_child(sibling_id),
                }
            }
        }

        // let mut cells: Vec<Cell<K, V>> = Vec::new();
        // for sibling_index in start_sibling_index..=end_sibling_index {
        //     let sibling = self.get_node(parent.child_at(sibling_index));

        // NEXT : Continue here

        // let sibling_index = if sibling_index < parent.len() - 1 {

        // let sibling_node_id = parent.children().nth(sibling_index).expect("Sibling node should exist");
        // let sibling_node = self.get_node_mut(sibling_node_id).as_leaf_mut().expect("Node should be a leaf");

        // cells.extend(sibling_node.iter().cloned());
        // sibling_node.clear();
        //}

        // Removes the cells from the nodes to balance
        // let node = self.get_node_mut(node_id).as_leaf_mut().expect("Node should be a leaf");
        // let mut cells: Vec<Cell<K, V>> = node.iter().cloned().collect();
        // node.clear();

        // TODO : Create a new node, add cells in both nodes, connect the new nodes to the parent...
    }

    /// Creates a new root node and makes the existing root its child.
    ///
    /// This is an internal helper method used during balancing when the root node overflows. It creates a new internal
    /// node, moves the existing root node to be a child of the new root, and updates the tree structure accordingly.
    ///
    /// The id of the root node remains the same. The old root that becomes a child of the new root gets a new id.
    ///
    /// # Arguments
    /// * `node_id` - The ID of the current root node that is overflowing
    ///
    /// # Returns
    /// * `NodeId` - The ID of the newly created child node (the old root)
    fn grow_new_root(&mut self, node_id: NodeId) -> NodeId {
        // We replace the root with a new node with the same id. The original root becomes a child of the new root.
        let original_root = self.nodes.remove(&node_id).expect("Node should exist");
        let new_id = self.register_new_node(original_root);

        let mut new_root = InternalNode::<K>::default();
        new_root.set_right_most_child(new_id);
        self.nodes.insert(node_id, Node::Internal(new_root));
        new_id
    }

    /// Determines the indices of sibling nodes for balancing based on the index of the current node in its parent.
    ///
    /// This is an internal helper function used during balancing operations to identify which sibling nodes should
    /// be involved in the balancing process. It considers edge cases where the current node is the first or last child.
    ///
    /// # Arguments
    /// * `index_in_parent` - The index of the current node in its parent
    /// * `parent_size` - The total number of children in the parent node
    ///
    /// # Returns
    /// * `(usize, usize)` - A tuple containing the start and end indices of the sibling nodes to consider for balancing
    fn get_index_siblings_balance(index_in_parent: usize, parent_size: usize) -> (usize, usize) {
        if parent_size <= 2 {
            // All children are used
            (0, parent_size - 1)
        } else if index_in_parent == 0 {
            // First child, use the two right siblings
            (0, 2)
        } else if index_in_parent == parent_size - 1 {
            // Last child, use the two left siblings
            (parent_size - 3, parent_size - 1)
        } else {
            // Normal case, use left and right sibling
            (index_in_parent - 1, index_in_parent + 1)
        }
    }
}

impl<K: Clone + Ord + Debug, V> BTree<K, V> {
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
        let node = self.get_node(node_id);

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
}

impl<K: Clone + Ord + PartialEq, V: Clone + PartialEq> BTree<K, V> {
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
        let self_node = self.get_node(node_id);
        let other_node = other.get_node(other_node_id);

        match (self_node, other_node) {
            (Node::Leaf(self_leaf), Node::Leaf(other_leaf)) => self_leaf == other_leaf,
            (Node::Internal(self_internal), Node::Internal(other_internal)) => {
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

impl<K: Clone + Ord + PartialEq, V: Clone + PartialEq> PartialEq for BTree<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.order == other.order && self.check_node_eq_recursive(self.root_node_id, other, other.root_node_id)
    }
}

impl<K: Clone + Ord + PartialEq + Debug, V: Clone> Debug for BTree<K, V> {
    /// Implements the `Debug` trait for `BTree` to provide a custom, tree-like visualization of the structure.
    ///
    /// This implementation uses the `fmt_node` helper function to recursively format the tree's nodes and their
    /// descendants. The root node is printed first, followed by its children, with proper indentation and tree
    /// connectors to visually represent the hierarchy.
    ///
    /// # Arguments
    /// * `f` - The formatter to write the debug output to
    ///
    /// # Returns
    /// * `Ok(())` - If formatting was successful
    /// * `Err` - If a formatting error occurred
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Write the header line with the tree's order
        writeln!(f, "B+Tree (order={}):", self.order)?;

        // Use the helper function to recursively format the tree starting from the root node
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
/// * `K` - The key type
/// * `V` - The value type
///
/// # Note
/// This type is only available in test builds.
#[cfg(test)]
struct BTreeBuilder<K, V> {
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
impl<K, V> Default for BTreeBuilder<K, V> {
    /// Creates a new `BTreeBuilder` with default configurations.
    fn default() -> Self {
        BTreeBuilder::<K, V> { order: 3, nodes: HashMap::new(), next_node_id: 0, node_id_stack: Vec::new() }
    }
}

#[cfg(test)]
impl<K: Clone + Ord, V: Clone> BTreeBuilder<K, V> {
    /// Retrieves a reference to a node by its ID.
    ///
    /// The node ID must exist in the builder's node storage; otherwise, this method will panic. This is an internal
    /// helper
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to retrieve
    ///
    /// # Returns
    /// * `&Node<K, V>` - A reference to the node with the specified ID
    ///
    /// # Panics
    /// Panics if the specified node ID does not exist in the builder's node storage. This indicates a bug in the
    /// builder
    fn get_node(&self, node_id: NodeId) -> &Node<K, V> {
        self.nodes.get(&node_id).expect("Node ID should exist in the builder")
    }

    /// Retrieves a mutable reference to a node by its ID.
    ///
    /// The node ID must exist in the builder's node storage; otherwise, this method will panic. This is an internal
    /// helper
    ///
    /// # Arguments
    /// * `node_id` - The ID of the node to retrieve
    ///
    /// # Returns
    /// * `&mut Node<K, V>` - A mutable reference to the node with the specified ID
    ///
    /// # Panics
    /// Panics if the specified node ID does not exist in the builder's node storage. This indicates a bug in the
    /// builder
    fn get_node_mut(&mut self, node_id: NodeId) -> &mut Node<K, V> {
        self.nodes.get_mut(&node_id).expect("Node ID should exist in the builder")
    }

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
        BTree { nodes: self.nodes, order: self.order, root_node_id: 0, next_node_id: self.next_node_id }
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
            let parent_node = self
                .get_node_mut(*parent_node_id)
                .as_internal_mut()
                .ok_or(BTreeBuilderError::ParentNodeIsNotInternalNode)?;

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
        let node_id = *self.node_id_stack.last().ok_or(BTreeBuilderError::NoCurrentNode)?;
        let leaf_node = self.get_node_mut(node_id).as_leaf_mut().ok_or(BTreeBuilderError::CurrentNodeIsNotLeaf)?;

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
    use std::error::Error;

    mod private_tests {
        use super::super::*;

        #[test]
        fn test_calculate_balanced_cells_distribution() {
            let distribution = BTree::<u32, u32>::calculate_balanced_cells_distribution(36, 3);
            assert_eq!(distribution, vec![12, 12, 12]);

            let distribution = BTree::<u32, u32>::calculate_balanced_cells_distribution(10, 3);
            assert_eq!(distribution, vec![4, 3, 3]);

            let distribution = BTree::<u32, u32>::calculate_balanced_cells_distribution(7, 2);
            assert_eq!(distribution, vec![4, 3]);

            let distribution = BTree::<u32, u32>::calculate_balanced_cells_distribution(5, 5);
            assert_eq!(distribution, vec![1, 1, 1, 1, 1]);

            let distribution = BTree::<u32, u32>::calculate_balanced_cells_distribution(0, 3);
            assert_eq!(distribution, vec![0, 0, 0]);
        }
    }

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

    /// When the btree is only a root node and the root node is full, inserting a new key-value pair should create a new
    /// root node and split the existing root node into two child nodes.
    ///
    /// ```text
    ///              Insert 3
    ///                 |
    ///                 v
    ///           +-----+-----+
    ///           |  1  |  2  |
    ///           +-----+-----+
    ///
    ///
    ///              Result
    ///                 |
    ///                 v
    ///           +-----+-----+
    ///       +-- |  3  |     |--+
    ///       |   +-----+-----+  |
    ///       v                  v
    /// +-----+-----+      +-----+-----+
    /// |  1  |  2  |      |  3  |     |
    /// +-----+-----+      +-----+-----+
    /// ```
    #[test]
    fn when_root_node_full_insertion_creates_new_root() -> Result<(), Box<dyn Error>> {
        #[rustfmt::skip]
            let mut btree = BTreeBuilder::<u32, u32>::default()
                .with_order(3)
                .add_leaf_node(None)?
                    .add_key_value_pair(1, 42)?
                    .add_key_value_pair(2, 43)?
                .end_node()?
                .build();

        #[rustfmt::skip]
            let expected = BTreeBuilder::<u32, u32>::default()
                .with_order(3)
                .add_internal_node(None)?
                    .add_leaf_node(Some(3))? // Left child of new root
                        .add_key_value_pair(1, 42)?
                        .add_key_value_pair(2, 43)?
                    .end_node()?
                    .add_leaf_node(None)? // Right child of new root
                        .add_key_value_pair(3, 44)?
                    .end_node()?
                .end_node()?
                .build();

        let result = btree.insert(Cell::new(3, 44));

        assert!(matches!(result, Ok(())));
        assert_eq!(expected, btree);
        Ok(())
    }
}
