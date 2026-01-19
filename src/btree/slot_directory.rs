use std::{fmt::Debug, ops::Index, ptr};

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
#[derive(Clone, PartialEq, Eq)]
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

impl<K, V> From<(K, V)> for Cell<K, V> {
    fn from(value: (K, V)) -> Self {
        Cell { key: value.0, value: value.1 }
    }
}

impl<K: Debug, V: Debug> Debug for Cell<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cell {{ key: {:?}, value: {:?} }}", self.key, self.value)
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
#[derive(PartialEq, Eq)]
pub struct SlotDirectory<K, V> {
    cells: Vec<Cell<K, V>>,
}

impl<K, V> Default for SlotDirectory<K, V> {
    fn default() -> Self {
        SlotDirectory { cells: Vec::new() }
    }
}

impl<K, V> SlotDirectory<K, V> {
    /// Returns the number of key-value pairs in the `SlotDirectory`.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Returns whether the `SlotDirectory` is overflowing given the specified order.
    ///
    /// A `SlotDirectory` is considered overflowing if it contains more than `order - 1` keys.
    ///
    /// # Arguments
    /// * `order` - The order of the B+Tree containing this slot directory
    ///
    /// # Returns
    /// Returns `true` if the number of keys exceeds `order - 1`, otherwise returns `false`.
    pub fn is_overflowing(&self, order: usize) -> bool {
        self.len() > order - 1
    }

    /// Returns whether the `SlotDirectory` is underflowing given the specified order.
    ///
    /// A `SlotDirectory` is considered underflowing if it contains fewer than `(order - 1) / 2`
    /// keys.
    ///
    /// # Arguments
    /// * `order` - The order of the B+Tree containing this slot directory
    ///
    /// # Returns
    /// Returns `true` if the number of keys is less than `(order - 1) / 2`, otherwise returns
    /// `false`.
    pub fn is_underflowing(&self, order: usize) -> bool {
        self.len() < (order - 1) / 2
    }

    /// Returns `true` if the `SlotDirectory` is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Returns an iterator over the cells in the `SlotDirectory`.
    ///
    /// The iterator yields cells in sorted order by key.
    ///
    /// # Returns
    /// An iterator that yields references to cells (`&Cell<K, V>`) in ascending key order.
    pub fn iter(&self) -> SlotDirectoryIterator<'_, K, V> {
        SlotDirectoryIterator { slot_directory: self, current_index: 0 }
    }

    /// Clears all cells from the `SlotDirectory`.
    pub fn clear(&mut self) {
        self.cells.clear();
    }

    /// Removes the cell at the specified index from the `SlotDirectory`.
    ///
    /// # Arguments
    /// * `index` - The zero-based index of the cell to remove
    ///
    /// # Returns
    /// The removed cell.
    ///
    /// # Panics
    /// Panics if the index is out of bounds.
    pub fn remove_at(&mut self, index: usize) -> Cell<K, V> {
        self.cells.remove(index)
    }

    /// Drains a range of cells from the `SlotDirectory`.
    ///
    /// The specified range of cells is removed from the directory and returned as an iterator. The remaining cells are
    /// shifted to close the gap left by the drained cells. The SlotDirectory is in an undefined state until the Drain
    /// iterator is fully consumed or dropped.
    ///
    /// # Arguments
    /// * `range` - The range of indices to drain from the directory
    ///
    /// # Returns
    /// An iterator that yields the drained cells.
    ///
    /// # Panics
    /// Panics if the range is invalid (start > end or end > length of the directory).
    pub fn drain(&mut self, range: std::ops::Range<usize>) -> Drain<'_, K, V> {
        assert!(range.start <= range.end && range.end <= self.len());

        let start = range.start;
        Drain { slot_directory: self, range, current_index: start }
    }
}

impl<K: Ord, V> SlotDirectory<K, V> {
    /// Finds the index of the specified key in the `SlotDirectory` wheteher it exists or not.
    ///
    /// # Arguments
    /// * `key` - The key to search for
    ///
    /// # Returns
    /// * `Ok(index)` if the key is found, where `index` is the position of the key in the directory
    /// * `Err(index)` if the key is not found, where `index` is the position where the key can be inserted to maintain
    ///   sorted order
    pub fn find_index(&self, key: &K) -> Result<usize, usize> {
        self.cells.binary_search_by(|c| c.key.cmp(key))
    }

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
}

impl<K: Clone, V: Clone> SlotDirectory<K, V> {
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
    pub fn cell_at(&self, index: usize) -> Result<Cell<K, V>, SlotDirectoryError> {
        if index >= self.len() {
            return Err(SlotDirectoryError::IndexOutOfBounds { index, size: self.len() });
        }

        Ok(self.cells[index].clone())
    }
}

impl<K, V, const N: usize> From<[(K, V); N]> for SlotDirectory<K, V> {
    fn from(value: [(K, V); N]) -> Self {
        SlotDirectory { cells: value.into_iter().map(|x| x.into()).collect() }
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

impl<K, V> Index<usize> for SlotDirectory<K, V> {
    type Output = Cell<K, V>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.cells[index]
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

// =====================================================================================================================
// SlotDirectory Drain
// =====================================================================================================================

pub struct Drain<'a, K, V> {
    slot_directory: &'a mut SlotDirectory<K, V>,
    range: std::ops::Range<usize>,
    current_index: usize,
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = Cell<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.range.end {
            return None;
        }

        let cell = unsafe { ptr::read(&self.slot_directory.cells[self.current_index]) };
        self.current_index += 1;
        Some(cell)
    }
}

impl<'a, K, V> Drop for Drain<'a, K, V> {
    fn drop(&mut self) {
        // consume remaining items
        for _ in self.by_ref() {}

        // shift remaining items to close the gap
        let tail_len = self.slot_directory.len() - self.range.end;
        if tail_len > 0 {
            unsafe {
                let src = self.slot_directory.cells.as_ptr().add(self.range.end);
                let dst = self.slot_directory.cells.as_mut_ptr().add(self.range.start);
                ptr::copy(src, dst, tail_len);
            }
        }

        // adjust length
        let new_len = self.slot_directory.len() - self.range.len();
        unsafe {
            self.slot_directory.cells.set_len(new_len);
        }
    }
}

// =====================================================================================================================
// Tests
// =====================================================================================================================

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
        let mut slot = SlotDirectory::<u32, u32>::default();
        slot.insert(Cell::new(1, 42)).unwrap();
        assert_eq!(slot.len(), 1);
    }

    #[test]
    fn after_insert_can_read_back_key_values_by_index() {
        const KEY: u32 = 1;
        const VALUE: u32 = 42;
        let mut slot = SlotDirectory::<u32, u32>::default();

        slot.insert(Cell::new(KEY, VALUE)).unwrap();
        let cell = slot.cell_at(0).unwrap();

        assert_eq!(cell.key, KEY);
        assert_eq!(cell.value, VALUE);
    }

    #[test]
    fn inserting_two_keys_lowest_key_is_at_index_0() {
        let mut slot = SlotDirectory::<u32, u32>::default();

        slot.insert(Cell::new(2, 2)).unwrap();
        slot.insert(Cell::new(1, 1)).unwrap();

        assert_eq!(slot, SlotDirectory::from([(1, 1), (2, 2)]));
    }

    #[test]
    fn inserting_existing_key_returns_key_already_exists() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42)]);

        let result = slot.insert(Cell::new(1, 43));

        assert!(matches!(result, Err(SlotDirectoryError::KeyAlreadyExists)));
    }

    #[test]
    fn after_calling_clear_len_is_0() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42)]);

        slot.clear();

        assert_eq!(slot.len(), 0);
    }

    #[test]
    fn draining_zero_items() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42), (2, 43), (3, 44), (4, 45)]);
        let expected_remaining = SlotDirectory::<u32, u32>::from([(1, 42), (2, 43), (3, 44), (4, 45)]);

        let drained: Vec<Cell<u32, u32>> = slot.drain(2..2).collect();

        assert!(drained.is_empty());
        assert_eq!(slot, expected_remaining);
    }

    #[test]
    fn draining_one_item_from_middle() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42), (2, 43), (3, 44), (4, 45)]);
        let expected = vec![Cell::new(2, 43)];
        let expected_remaining = SlotDirectory::<u32, u32>::from([(1, 42), (3, 44), (4, 45)]);

        let drained: Vec<Cell<u32, u32>> = slot.drain(1..2).collect();

        assert_eq!(drained, expected);
        assert_eq!(slot, expected_remaining);
    }

    #[test]
    fn draining_two_items_from_the_start() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42), (2, 43), (3, 44)]);
        let expected = vec![Cell::new(1, 42), Cell::new(2, 43)];
        let expected_remaining = SlotDirectory::<u32, u32>::from([(3, 44)]);

        let drained: Vec<Cell<u32, u32>> = slot.drain(0..2).collect();

        assert_eq!(drained, expected);
        assert_eq!(slot, expected_remaining);
    }

    #[test]
    fn draining_two_items_from_middle() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42), (2, 43), (3, 44), (4, 45)]);
        let expected = vec![Cell::new(2, 43), Cell::new(3, 44)];
        let expected_remaining = SlotDirectory::<u32, u32>::from([(1, 42), (4, 45)]);

        let drained: Vec<Cell<u32, u32>> = slot.drain(1..3).collect();

        assert_eq!(drained, expected);
        assert_eq!(slot, expected_remaining);
    }

    #[test]
    fn draining_two_items_from_the_end() {
        let mut slot = SlotDirectory::<u32, u32>::from([(1, 42), (2, 43), (3, 44)]);
        let expected = vec![Cell::new(2, 43), Cell::new(3, 44)];
        let expected_remaining = SlotDirectory::<u32, u32>::from([(1, 42)]);

        let drained: Vec<Cell<u32, u32>> = slot.drain(1..3).collect();

        assert_eq!(drained, expected);
        assert_eq!(slot, expected_remaining);
    }
}
