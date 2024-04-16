// pub mod cache;

use crate::playfield::Playfield;

/// Contains required interactions that a player can perform with a minefield.
///
/// This trait can be used for both:
///
/// - Minefields that are fully handled by the application, where all mine locations are already
/// known - [`IS_ORACLE = true`](Player::IS_ORACLE)
/// - Minefields that are e.g. read via a screen-reader from an external Minesweeper/Hexcells/etc...
/// game - [`IS_ORACLE = false`](Player::IS_ORACLE)
pub trait Player {
    /// Whether all mines are known beforehand.
    ///
    /// - `true` when the mine layout is handled by the program itself and thus known.
    /// - `false` when solving an external puzzle for which mine locations are not known beforehand.
    const IS_ORACLE: bool;

    type Playfield: Playfield;

    /// The playfield containing information about the connections between fields.
    fn playfield(&self) -> &Self::Playfield;

    /// The total number of mines hidden on the playfield, if known.
    ///
    /// Must be less than or equal to [`Playfield::field_count`].
    fn mine_count(&self) -> Option<usize>;

    /// Reveals or flags the given field, returning which one it was including its count.
    ///
    /// Flagging might return [`Field::Mine`] even if that isn't correct unless
    /// [`Player::IS_ORACLE`] is `true`.
    ///
    /// # Panics
    ///
    /// May panic when called twice on the same field; use [`Player::get`] instead.
    ///
    /// Panics when `flag` does not match the actual field if [`Player::IS_ORACLE`] is `true`.
    ///
    /// May panic when more mines than [`Player::mine_count`] are flagged.
    fn click(&mut self, field_index: usize, flag: bool) -> Field;

    /// Returns the state of the given field that has already been clicked.
    ///
    /// Should return a cached value that was generated by the required call to [`Player::click`].
    ///
    /// # Panics
    ///
    /// May panic if a field has not been [`Player::click`]ed yet.
    fn get(&self, field_index: usize) -> PartialField;
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Field {
    Free { count: usize },
    Flag { count: Option<usize> },
}

impl Field {
    pub fn is_free(self) -> bool {
        matches!(self, Self::Free { .. })
    }

    pub fn is_flag(self) -> bool {
        matches!(self, Self::Flag { .. })
    }

    pub fn count(self) -> Option<usize> {
        match self {
            Self::Free { count } => Some(count),
            Self::Flag { count } => count,
        }
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum PartialField {
    Free,
    Flag { has_count: bool },
}

impl PartialField {
    pub fn with_count(self, count: impl FnOnce() -> usize) -> Field {
        match self {
            PartialField::Free => Field::Free { count: count() },
            PartialField::Flag { has_count } => Field::Flag {
                count: has_count.then(count),
            },
        }
    }

    pub fn is_free(self) -> bool {
        matches!(self, Self::Free)
    }

    pub fn is_flag(self) -> bool {
        matches!(self, Self::Flag { .. })
    }

    pub fn has_count(self) -> bool {
        match self {
            Self::Free => true,
            Self::Flag { has_count } => has_count,
        }
    }
}