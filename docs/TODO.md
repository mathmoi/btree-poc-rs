# btree-poc-rs TODOs

## Unit Tests

### Read (Search)

- [x] Reading from an empty tree should return None
- [x] Reading an existing key in a single node tree should return the correct value
- [x] Reading a non-existing key in a non-empty single node tree should return None
- [x] Reading a key that exists in a multi-level tree traverse the nodes and return the correct value
- [x] Reading the smallest key in the tree returns the correct value
- [x] Reading the largest key in the tree returns the correct value

### Insert — Basic / No Rebalancing

- [ ] Inserting into an empty tree creates a root leaf with one entry
- [ ] Inserting multiple keys into a single leaf node stores them in sorted order
- [ ] Inserting a duplicate key updates (or rejects) the existing value according to your chosen semantics
- [ ] Filling a leaf node exactly to capacity without triggering a split

### Insert — Leaf Split (no redistribution possible)

- [ ] Inserting into a full leaf with no siblings (root is leaf) splits into two leaves and creates a new internal root
- [ ] Inserting into a full leaf whose left sibling is also full triggers a leaf split
- [ ] Inserting into a full leaf whose right sibling is also full triggers a leaf split
- [ ] Inserting into a full leaf at the left extremity (no left sibling) with two full right sibling triggers a split
- [ ] Inserting into a full leaf at the right extremity (no right sibling) with two full left sibling triggers a split
- [ ] After a leaf split, the parent internal node receives the correct separator key
- [ ] After a leaf split, keys are distributed correctly between the two resulting leaves

### Insert — Leaf Redistribution (borrow instead of split)

- [ ] Inserting into a full leaf redistributes to the right sibling when it has space
- [ ] Inserting into a full leaf redistributes to the left sibling when it has space
- [ ] After leaf redistribution to the right, the parent separator key is updated correctly
- [ ] After leaf redistribution to the left, the parent separator key is updated correctly
- [ ] Inserting into a full leaf at the left extremity redistributes to the right sibling when it has space
- [ ] Inserting into a full leaf at the right extremity redistributes to the left sibling when it has space
- [ ] Redistribution prefers a specific sibling when both have space (tests your tie-breaking policy)

### Insert — Internal Node Split (no redistribution possible)

- [ ] A leaf split that overflows a full internal node whose siblings are also full triggers an internal node split
- [ ] After an internal node split, the promoted key is pushed to the parent correctly
- [ ] After an internal node split, child pointers are distributed correctly between the two internal nodes
- [ ] Cascading splits propagate up to the root, increasing tree height by one

### Insert — Internal Node Redistribution

- [ ] A leaf split that overflows an internal node redistributes to the right internal sibling when it has space
- [ ] A leaf split that overflows an internal node redistributes to the left internal sibling when it has space
- [ ] After internal node redistribution, the parent separator key and child pointers are updated correctly (rotation through parent)
- [ ] Internal redistribution at the left extremity borrows from the right internal sibling
- [ ] Internal redistribution at the right extremity borrows from the left internal sibling

### Delete — Basic / No Rebalancing

- [ ] Deleting from a single-entry root leaf produces an empty tree
- [ ] Deleting a key that doesn't exist returns not-found and leaves the tree unchanged
- [ ] Deleting a key from a leaf that stays at or above minimum occupancy requires no rebalancing
- [ ] Deleting a key that appears as a separator in an ancestor updates (or doesn't need to update) the separator correctly

### Delete — Leaf Redistribution (borrow instead of merge)

- [ ] Deleting from a leaf below minimum borrows a key from the right sibling when it has enough keys
- [ ] Deleting from a leaf below minimum borrows a key from the left sibling when it has enough keys
- [ ] After borrowing from the right leaf sibling, the parent separator key is updated correctly
- [ ] After borrowing from the left leaf sibling, the parent separator key is updated correctly
- [ ] Deleting from a leaf at the left extremity borrows from the right sibling
- [ ] Deleting from a leaf at the right extremity borrows from the left sibling

### Delete — Leaf Merge (redistribution not possible)

- [ ] Deleting from an underflowing leaf merges with the right sibling when it is also at minimum
- [ ] Deleting from an underflowing leaf merges with the left sibling when it is also at minimum
- [ ] After a leaf merge, the separator key is removed from the parent internal node
- [ ] After a leaf merge, the merged leaf contains all keys in sorted order
- [ ] Merging at the left extremity merges with the right sibling
- [ ] Merging at the right extremity merges with the left siblings

### Delete — Internal Node Redistribution

- [ ] A leaf merge that causes an internal node to underflow borrows from the right internal sibling when it has enough keys
- [ ] A leaf merge that causes an internal node to underflow borrows from the left internal sibling when it has enough keys
- [ ] After internal node redistribution on delete, the rotation through the parent updates separator and child pointers correctly
- [ ] Internal redistribution at the left extremity borrows from the right internal sibling
- [ ] Internal redistribution at the right extremity borrows from the left internal sibling

### Delete — Internal Node Merge

- [ ] A leaf merge that causes an internal node to underflow with minimum-occupancy siblings triggers an internal merge
- [ ] After an internal merge, the pulled-down parent separator and children are combined correctly
- [ ] Cascading merges propagate up to the root, decreasing tree height when the root has one remaining child

### Structural Invariants (applicable after every mutating operation)

- [ ] All leaves are at the same depth after any insert or delete
- [ ] Every internal node has between ⌈order/2⌉ and order children (except the root)
- [ ] Every leaf node has between ⌈(order-1)/2⌉ and order-1 keys (except the root)
- [ ] Keys within every node are in strictly sorted order
- [ ] Separator keys in internal nodes correctly partition the ranges of their children
- [ ] The root has at least 2 children if it is an internal node

### Integration / Stress

- [ ] Inserting a large ascending sequence produces a valid tree
- [ ] Inserting a large descending sequence produces a valid tree
- [ ] Inserting a large random sequence produces a valid tree
- [ ] Deleting all keys in insertion order results in an empty tree with valid structure at every step
- [ ] Deleting all keys in reverse order results in an empty tree with valid structure at every step
- [ ] Deleting all keys in random order results in an empty tree with valid structure at every step
- [ ] Interleaving inserts and deletes randomly maintains all structural invariants throughout
