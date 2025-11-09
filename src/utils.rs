use std::ops::{Range, RangeBounds};

/// Normalizes a range with potentially unbounded start or end to a concrete range within the bounds of `0..len`.
///
/// # Arguments
/// * `range` - The range to normalize, which can have unbounded start or end.
/// * `len` - The length of the collection to which the range will be applied.
///
/// # Returns
/// A `Range<usize>` representing the normalized range.
pub fn normalize_range<R: RangeBounds<usize>>(range: R, len: usize) -> Range<usize> {
    let start = match range.start_bound() {
        std::ops::Bound::Included(&s) => s,
        std::ops::Bound::Excluded(&s) => s + 1,
        std::ops::Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        std::ops::Bound::Included(&e) => e + 1,
        std::ops::Bound::Excluded(&e) => e,
        std::ops::Bound::Unbounded => len,
    };

    start..end
}
