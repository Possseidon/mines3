pub mod grid;
// TODO: pub mod mesh;

use std::num::NonZeroUsize;

/// A generic graph of fields for a game of Minesweeper.
///
/// Does not have information about where mines are located.
///
/// Unlike the usual Minesweeper, this is not limited to a grid, but instead can be a free-form
/// graph. Connectivity between fields does not even have to be reflexive. For more info, refer to
/// [`Playfield::counted_fields`].
pub trait Playfield {
    /// The total number of fields, if already known.
    ///
    /// [`None`] means that the maximum `field_index` is not known yet. E.g. if the map is generated
    /// dynamically as it is being played.
    ///
    /// Fields are never empty. `field_index` of `0` must always exist as a starting point, but is
    /// not required to be used as a starting point, if the size is already known.
    fn field_count(&self) -> Option<NonZeroUsize> {
        None
    }

    /// All fields that (if containing a mine) will contribute to the displayed count on the field.
    ///
    /// Returned fields must be unique and returned in ascending order. The given `field_index`
    /// should also *never* be part of the returned set of fields.
    ///
    /// There is no requirement on reflexivity, i.e. if field `0` counts `1`, that does not
    /// imply, that `1` also counts `0`.
    ///
    /// # Panics
    ///
    /// Panics if `field_index` is out of bounds.
    fn counted_fields(&self, field_index: usize) -> impl Iterator<Item = usize>;

    /// All fields to which the given field contributes to the displayed count.
    ///
    /// Has similar requirements on its returned value as [`Playfield::counted_fields`] and is often
    /// times implemented the same for classic reflexive connections between fields.
    ///
    /// # Panics
    ///
    /// Panics if `field_index` is out of bounds.
    fn counted_by_fields(&self, field_index: usize) -> impl Iterator<Item = usize>;
}

impl<T: Playfield> Playfield for &T {
    fn field_count(&self) -> Option<NonZeroUsize> {
        (*self).field_count()
    }

    fn counted_fields(&self, field_index: usize) -> impl Iterator<Item = usize> {
        (*self).counted_fields(field_index)
    }

    fn counted_by_fields(&self, field_index: usize) -> impl Iterator<Item = usize> {
        (*self).counted_fields(field_index)
    }
}
