# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
cargo build              # Debug build
cargo build --release    # Release build
cargo test               # Run all tests
cargo test <test_name>   # Run a single test by name (substring match)
cargo fmt                # Format code (max_width=120, per rustfmt.toml)
cargo clippy             # Lint
```

## Architecture

This is a B+Tree proof of concept in Rust, inspired by SQLite's implementation. The goal is a balanced B+Tree with sibling cell borrowing/redistribution — not just node splitting.

**Current storage:** Nodes live in a `HashMap<NodeId, Node<K, V>>`. This is intentionally in-memory for the POC; a future version will use disk pages via a pager.

### Module structure

- **`btree/btree.rs`** — `BTree<K, V>` struct and all tree-level logic: `insert()`, `balance()`, `balance_leaf()`, `balance_internal()`, and helpers. Also contains `BTreeBuilder` (test-only fluent API for constructing trees).
- **`btree/node.rs`** — `LeafNode<K, V>`, `InternalNode<K>`, and the `Node<K, V>` enum. `LeafNode` has a `next_leaf` pointer for range queries. `InternalNode` has a `right_most_child` that sits outside the `SlotDirectory`.
- **`btree/slot_directory.rs`** — `SlotDirectory<K, V>` is the sorted, duplicate-free cell store used by both node types. Keys are kept in ascending order; all insertions use binary search.

### Insertion and balancing flow

1. `insert()` traverses the tree recursively to find the correct leaf, tracking the parent chain.
2. The cell is inserted into the leaf (sorted order, no duplicates).
3. If the node overflows (`len > order - 1`), `balance_leaf()` or `balance_internal()` is called.
4. Balancing gathers up to 3 siblings, extracts all their cells, redistributes them evenly, creates new nodes if needed, updates separator keys in the parent, then recursively balances the parent if it also overflows.
5. Root overflow is a special case: a new internal root is created and the old root becomes its child.

**Key invariants:**
- Max keys per node: `order - 1`
- Min keys per non-root node: `ceil(order / 2) - 1`
- Default test order: 3 (max 2 keys per node)

### Error types

Each layer has its own error type (`BTreeError`, `NodeError`, `SlotDirectoryError`) defined with `thiserror`. `BTreeBuilderError` is test-only.

## Notes

- `#![allow(dead_code)]` is intentionally in `lib.rs` while the API is still being built out — remove it when the public interface stabilizes.
- `TODO.md` tracks pending test cases for last-child balancing, complex splits, sequential insertion, and deletion.
- Architecture decisions are documented in `docs/adr/`.
