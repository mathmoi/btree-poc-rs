# btree-poc-rs TODOs

## Unit tests
- [X] when_root_node_full_insertion_creates_new_root
- [X] when_leaf_node_overflows_can_send_cell_to_sibling
- [X] when_overflowing_node_is_the_first_child_first_three_nodes_are_used_for_balancing
- [X] leaf_node_overflowing_needs_to_split
- [X] leaf_node_split_causes_parent_to_overflow_and_split

### From btree-poc
- [ ] Insert When the overflowing node is the last node of four childre, the last tree nodes are balanced
- [ ] Insert Leaf node should split when keys can't be moved around siblings
- [ ] Insert a B*+Tree of order 4 should have four full leaf nodes and one internal node if we add the keys 12 keys sequentially
- [ ] Insert When we insert a key/value pair, we can read it back.

### From Antonio Sarosi's mkdb
- [ ] When `order = 4` the root should be able to sustain 3 keys without splitting.
- [ ] Differents scenarios of deleting keys from the tree