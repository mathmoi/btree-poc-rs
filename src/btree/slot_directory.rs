use std::fmt::Debug;

use thiserror::Error;

#[derive(Error, Debug)]
pub enum SlotDirectoryError {
    #[error("Key already exists")]
    KeyAlreadyExists,

    #[error("Index {index} out of bounds, SlotDirectory has {size} cells")]
    IndexOutOfBounds { index: usize, size: usize },
}

/// Represents a key-value pair stored in the slot directory. This could be a simele tuple, but since we will eventually
/// needs an object to control the memory layout of the cell in a buffer page we use a struct here.
#[derive(Clone)]
pub struct Cell<K: Clone, V: Clone> {
    // TODO : In the final implementation K and V should not need to be Clone
    pub key: K,
    pub value: V,
}

impl<K: Clone, V: Clone> Cell<K, V> {
    /// Creates a new cell with the given key and value.
    pub fn new(key: K, value: V) -> Self {
        Cell { key, value }
    }
}

/// Represents a slot directory for a B+Tree node. A slot directory is a structure that holds a sorted list of keys and
/// values in a way that allows for efficient access and modification of keys and values stored in a fixed-sixe memory
/// region.
pub struct SlotDirectory<K: Ord + Clone, V: Clone> {
    cells: Vec<Cell<K, V>>,
}

pub struct SlotDirectoryIterator<'a, K: Ord + Clone, V: Clone> {
    slot_directory: &'a SlotDirectory<K, V>,
    current_index: usize,
}

impl<K, V> PartialEq for Cell<K, V>
where
    K: Clone + PartialEq,
    V: Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.value == other.value
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
    /// * `Ok(())` if the insertion was successful
    /// * `Err(SlotDirectoryError::KeyAlreadyExists)` if the key is already present in the directory
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
    /// # Errors
    /// Returns `SlotDirectoryError::IndexOutOfBounds` if the index is greater than or equal to the collection length.
    pub fn get_cell(&self, index: usize) -> Result<Cell<K, V>, SlotDirectoryError> {
        if index >= self.len() {
            return Err(SlotDirectoryError::IndexOutOfBounds { index, size: self.len() });
        }

        Ok(self.cells[index].clone())
    }

    /// Returns an iterator over the cells in the `SlotDirectory`.
    pub fn iter(&self) -> SlotDirectoryIterator<K, V> {
        SlotDirectoryIterator { slot_directory: self, current_index: 0 }
    }
}

impl<K: Ord + Clone, V: Clone> Default for SlotDirectory<K, V> {
    /// Creates a new, empty `SlotDirectory`.
    fn default() -> Self {
        SlotDirectory { cells: Vec::new() }
    }
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

impl<K: Ord + Clone + Debug, V: Clone> Debug for SlotDirectory<K, V> {
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
