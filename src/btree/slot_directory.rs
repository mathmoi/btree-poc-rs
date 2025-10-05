use std::fmt::Debug;

use thiserror::Error;

// =====================================================================================================================
// Errors
// =====================================================================================================================

/// Errors that can occur during `SlotDirectory` operations.
#[derive(Error, Debug)]
pub enum SlotDirectoryError {
    /// The key being inserted already exists in the slot directory.
    #[error("The key being inserted already exists in the slot directory")]
    KeyAlreadyExists,

    /// The requested index is outside the valid range of the slot directory.
    ///
    /// This error is returned when attempting to access a cell at an index that is greater than or equal to the number
    /// of cells in the directory.
    #[error("Index {index} out of bounds, SlotDirectory has {size} cells")]
    IndexOutOfBounds { index: usize, size: usize },
}

// =====================================================================================================================
// Cell
// =====================================================================================================================

/// Represents a key-value pair stored in the slot directory.
///
/// While this could be a simple tuple, a struct is used to allow control over the memory layout when cells are
/// eventually stored in buffer pages on disk.
#[derive(Clone)]
pub struct Cell<K, V> {
    /// The key component of this key-value pair.
    pub key: K,

    /// The value associated with the key.
    pub value: V,
}

impl<K, V> Cell<K, V> {
    /// Creates a new `Cell` containing the specified key-value pair.
    ///
    /// # Arguments
    /// * `key` - The key to store in the cell
    /// * `value` - The value associated with the key
    ///
    /// # Returns
    /// A new `Cell` instance containing the provided key and value.
    pub fn new(key: K, value: V) -> Self {
        Cell { key, value }
    }
}

impl<K, V> PartialEq for Cell<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.value == other.value
    }
}

// =====================================================================================================================
// SlotDirectory
// =====================================================================================================================

/// Represents a slot directory for a B+Tree node.
///
/// A slot directory maintains a sorted collection of key-value pairs ([`Cell`]s) within a B+Tree node. Keys are kept in
/// sorted order to enable efficient binary search operations. In the current implementation, cells are stored in a
/// dynamically-sized vector for simplicity. The final implementation will use a fixed-size memory region (page buffer)
/// to store cells on disk.
///
/// # Type Parameters
/// * `K` - The key type, which must implement `Ord` and `Clone`
/// * `V` - The value type, which must implement `Clone`
///
/// # Invariants
/// * Keys are always maintained in sorted ascending order
/// * No duplicate keys are allowed
pub struct SlotDirectory<K, V> {
    cells: Vec<Cell<K, V>>,
}

impl<K, V> Default for SlotDirectory<K, V> {
    fn default() -> Self {
        SlotDirectory { cells: Vec::new() }
    }
}

impl<K: Ord + Clone, V: Clone> SlotDirectory<K, V> {
    /// Inserts a cell into the `SlotDirectory`.
    ///
    /// The cell is inserted while maintaining the sorted order of keys.
    ///
    /// # Arguments
    /// * `cell` - The cell to insert into the directory
    ///
    /// # Returns
    /// Returns `Ok(())` if the insertion was successful.
    ///
    /// # Errors
    /// Returns `Err(SlotDirectoryError::KeyAlreadyExists)` if the key is already present in the directory.
    pub fn insert(&mut self, cell: Cell<K, V>) -> Result<(), SlotDirectoryError> {
        match self.cells.binary_search_by(|c| c.key.cmp(&cell.key)) {
            Ok(_) => Err(SlotDirectoryError::KeyAlreadyExists),
            Err(pos) => {
                self.cells.insert(pos, cell);
                Ok(())
            }
        }
    }

    /// Returns the number of key-value pairs in the `SlotDirectory`.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Returns `true` if the `SlotDirectory` is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Returns a copy of the cell at the specified index.
    ///
    /// # Arguments
    /// * `index` - The zero-based index of the cell to retrieve
    ///
    /// # Returns
    /// Returns a copy of the cell at the given index.
    ///
    /// # Errors
    /// Returns `SlotDirectoryError::IndexOutOfBounds` if the index is greater than or equal to the number of cells in
    /// the directory.
    pub fn get_cell(&self, index: usize) -> Result<Cell<K, V>, SlotDirectoryError> {
        if index >= self.len() {
            return Err(SlotDirectoryError::IndexOutOfBounds { index, size: self.len() });
        }

        Ok(self.cells[index].clone())
    }

    /// Returns an iterator over the cells in the `SlotDirectory`.
    ///
    /// The iterator yields cells in sorted order by key.
    ///
    /// # Returns
    /// An iterator that yields references to cells (`&Cell<K, V>`) in ascending key order.
    pub fn iter(&self) -> SlotDirectoryIterator<K, V> {
        SlotDirectoryIterator { slot_directory: self, current_index: 0 }
    }
}

impl<K: Debug, V> Debug for SlotDirectory<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Keys: [")?;
        for (i, cell) in self.cells.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", cell.key)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

impl<K, V> PartialEq for SlotDirectory<K, V>
where
    K: Ord + Clone + PartialEq,
    V: Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.cells == other.cells
    }
}

// =====================================================================================================================
// SlotDirectoryIterator
// =====================================================================================================================

/// An iterator over the cells in a [`SlotDirectory`].
///
/// This iterator yields immutable references to [`Cell`]s in sorted order by key. It is created by calling the
/// [`SlotDirectory::iter`] method.
///
/// # Type Parameters
/// * `'a` - The lifetime of the borrow from the [`SlotDirectory`]
/// * `K` - The key type, which must implement `Ord` and `Clone`
/// * `V` - The value type, which must implement `Clone`
pub struct SlotDirectoryIterator<'a, K, V> {
    slot_directory: &'a SlotDirectory<K, V>,
    current_index: usize,
}

impl<'a, K: Ord + Clone, V: Clone> Iterator for SlotDirectoryIterator<'a, K, V> {
    type Item = &'a Cell<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.slot_directory.len() {
            return None;
        }

        let cell = &self.slot_directory.cells[self.current_index];
        self.current_index += 1;
        Some(cell)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.slot_directory.len() - self.current_index;
        (remaining, Some(remaining))
    }
}

impl<'a, K: Ord + Clone, V: Clone> ExactSizeIterator for SlotDirectoryIterator<'a, K, V> {
    fn len(&self) -> usize {
        self.slot_directory.len() - self.current_index
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_slot_directory_is_empty() {
        let slot = SlotDirectory::<u32, u32>::default();
        assert!(slot.is_empty());
    }

    #[test]
    fn after_insert_new_slot_len_is_1() {
        const KEY: u32 = 1;
        const VALUE: u32 = 42;

        let mut slot = SlotDirectory::<u32, u32>::default();
        slot.insert(Cell::new(KEY, VALUE)).unwrap();
        assert_eq!(slot.len(), 1);
    }

    #[test]
    fn after_insert_can_read_back_key_values_by_index() {
        const KEY: u32 = 1;
        const VALUE: u32 = 42;

        let mut slot = SlotDirectory::<u32, u32>::default();
        slot.insert(Cell::new(KEY, VALUE)).unwrap();
        let cell = slot.get_cell(0).unwrap();
        assert_eq!(cell.key, KEY);
        assert_eq!(cell.value, VALUE);
    }

    #[test]
    fn inserting_two_keys_lowest_key_is_at_index_0() {
        const KEY1: u32 = 1;
        const VALUE1: u32 = 42;
        const KEY2: u32 = 2;
        const VALUE2: u32 = 43;
        const KEY: u32 = 1;
        const VALUE: u32 = 42;

        let mut slot = SlotDirectory::<u32, u32>::default();
        slot.insert(Cell::new(KEY, VALUE)).unwrap();
        assert_eq!(slot.len(), 1);
        let mut slot = SlotDirectory::<u32, u32>::default();
        slot.insert(Cell::new(KEY2, VALUE2)).unwrap();
        slot.insert(Cell::new(KEY1, VALUE1)).unwrap();
        let cell_at_index_0 = slot.get_cell(0).unwrap();
        assert_eq!(cell_at_index_0.key, KEY1);
        assert_eq!(cell_at_index_0.value, VALUE1);
    }

    #[test]
    fn inserting_existing_key_returns_key_already_exists() {
        let mut slot = SlotDirectory::<u32, u32>::default();
        slot.insert(Cell::new(1, 42)).unwrap();
        let result = slot.insert(Cell::new(1, 43));
        assert!(matches!(result, Err(SlotDirectoryError::KeyAlreadyExists)));
    }
}
