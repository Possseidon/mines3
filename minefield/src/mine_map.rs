use std::num::NonZeroUsize;

use bitvec::{bitbox, boxed::BitBox};

/// Stores which fields of a minefield contain a mine.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct MineMap {
    mines: BitBox,
}

impl AsRef<Self> for MineMap {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl MineMap {
    /// Creates a new [`MineMap`] without any mines.
    pub fn new(field_count: NonZeroUsize) -> Self {
        Self {
            mines: bitbox![0; field_count.get()],
        }
    }

    /// The total number of fields.
    pub fn field_count(&self) -> NonZeroUsize {
        self.mines
            .len()
            .try_into()
            .expect("should have at least one field")
    }

    /// Returns whether the given field conains a mine.
    pub fn is_mine(&self, field_index: usize) -> bool {
        self.mines[field_index]
    }

    /// Returns the total number of mines.
    pub fn mine_count(&self) -> usize {
        self.mines.count_ones()
    }

    /// Places or removes a mine at the given field.
    ///
    /// Does nothing if the state of the field already matches.
    pub fn set_mine(&mut self, field_index: usize, is_mine: bool) {
        self.mines.set(field_index, is_mine);
    }

    /// Shorthand for [`Self::set_mine()`] with `true`.
    pub fn place_mine(&mut self, field_index: usize) {
        self.set_mine(field_index, true);
    }

    /// Shorthand for [`Self::set_mine()`] with `false`.
    pub fn remove_mine(&mut self, field_index: usize) {
        self.set_mine(field_index, false);
    }

    /// Removes all mines, leaving the field size unchanged.
    pub fn reset(&mut self) {
        self.mines.fill(false);
    }
}
