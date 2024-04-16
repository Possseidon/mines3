use std::num::NonZeroUsize;

use super::Playfield;

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GridPos {
    pub x: usize,
    pub y: usize,
}

impl GridPos {
    fn from_field_index(field_index: usize, size: GridSize) -> Option<Self> {
        let y = field_index / size.width;
        (y < size.height.get()).then(|| Self {
            x: field_index % size.width,
            y,
        })
    }

    fn to_field_index(self, size: GridSize) -> Option<usize> {
        (self.x < size.width.get() && self.y < size.height.get())
            .then(|| self.x + self.y * size.width.get())
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct GridSize {
    pub width: NonZeroUsize,
    pub height: NonZeroUsize,
}

impl GridSize {
    /// Returns the x position to the left of the given position, if any.
    ///
    /// Wraps around if `wrap` is `true`; otherwise returns [`None`] in that case.
    fn left(self, x: usize, wrap: bool) -> Option<usize> {
        assert!(x < self.width.get());
        x.checked_sub(1)
            .or_else(|| wrap.then(|| self.width.get() - 1))
    }

    /// Returns the x position to the right of the given position, if any.
    ///
    /// Wraps around if `wrap` is `true`; otherwise returns [`None`] in that case.
    fn right(self, x: usize, wrap: bool) -> Option<usize> {
        assert!(x < self.width.get());
        (x < self.width.get() - 1)
            .then(|| x + 1)
            .or_else(|| wrap.then_some(0))
    }

    /// Returns the y position above the given position, if any.
    ///
    /// Wraps around if `wrap` is `true`; otherwise returns [`None`] in that case.
    fn above(self, y: usize, wrap: bool) -> Option<usize> {
        assert!(y < self.height.get());
        y.checked_sub(1)
            .or_else(|| wrap.then(|| self.height.get() - 1))
    }

    /// Returns the y position below the given position, if any.
    ///
    /// Wraps around if `wrap` is `true`; otherwise returns [`None`] in that case.
    fn below(self, y: usize, wrap: bool) -> Option<usize> {
        assert!(y < self.height.get());
        (y < self.height.get() - 1)
            .then(|| y + 1)
            .or_else(|| wrap.then_some(0))
    }
}

impl Default for GridSize {
    fn default() -> Self {
        Self {
            width: NonZeroUsize::MIN,
            height: NonZeroUsize::MIN,
        }
    }
}

/// A playfield in the shape of the classical grid-based Minesweeper.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Grid {
    /// The width and height of the playfield.
    pub size: GridSize,
    /// Which fields a field should count towards its displayed number when revealed.
    pub count: Count,
    /// Whether the entire board wraps horizontally, vertically or both.
    pub wrap: Wrap,
}

/// Which directions to count for a given field.
///
/// Defaults to all directions, including diagonals, like in classical Minesweeper.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Count {
    /// Whether a given field counts the fields to the left of it.
    pub left: bool,
    /// Whether a given field counts the fields to the right of it.
    pub right: bool,
    /// Whether a given field counts the fields above it.
    pub above: bool,
    /// Whether a given field counts the fields below it.
    pub below: bool,
    /// Whether diagonals are counted like in classical Minesweeper.
    pub diagonals: bool,
}

impl Default for Count {
    fn default() -> Self {
        Self {
            left: true,
            right: true,
            above: true,
            below: true,
            diagonals: true,
        }
    }
}

/// Whether the field wraps to the opposite site at edges instead of cutting of.
///
/// Defaults to `false` for both horizontal and vertical wrapping.
#[derive(Clone, Copy, Default, Debug, Hash, PartialEq, Eq)]
pub struct Wrap {
    /// Whether fields wrap around horizontally.
    pub x: bool,
    /// Whether fields wrap around vertically.
    pub y: bool,
}

impl Grid {
    /// Returns the fields that this fields counts.
    ///
    /// If `inverse` is set to `true`, returns the fields that count this field instead.
    fn counted_fields(
        &self,
        field_index: usize,
        inverse: bool,
    ) -> impl DoubleEndedIterator<Item = usize> {
        let GridPos { x, y } =
            GridPos::from_field_index(field_index, self.size).expect("field_index should be valid");

        let count = if inverse {
            Count {
                left: self.count.right,
                right: self.count.left,
                above: self.count.below,
                below: self.count.above,
                ..self.count
            }
        } else {
            self.count
        };

        let size = self.size;

        let wrap_x = self.wrap.x;
        let left = count.left.then(|| size.left(x, wrap_x)).flatten();
        let right = count.right.then(|| size.right(x, wrap_x)).flatten();

        let wrap_y = self.wrap.y;
        let above = count.above.then(|| size.above(y, wrap_y)).flatten();
        let below = count.below.then(|| size.below(y, wrap_y)).flatten();

        let if_diagonal = |pos| if count.diagonals { pos } else { None };

        // TODO: This is not sorted when it wraps
        [
            if_diagonal(left.zip(above)),
            above.map(|y| (x, y)),
            if_diagonal(right.zip(above)),
            left.map(|x| (x, y)),
            right.map(|x| (x, y)),
            if_diagonal(left.zip(below)),
            below.map(|y| (x, y)),
            if_diagonal(right.zip(below)),
        ]
        .into_iter()
        .flatten()
        .map(|(x, y)| GridPos { x, y })
        .map(move |grid_pos| {
            grid_pos
                .to_field_index(size)
                .expect("adjacent grid pos should be within bounds")
        })
    }
}

impl Playfield for Grid {
    fn field_count(&self) -> Option<NonZeroUsize> {
        self.size.width.checked_mul(self.size.height)
    }

    fn counted_fields(&self, field_index: usize) -> impl Iterator<Item = usize> {
        self.counted_fields(field_index, false)
    }

    fn counted_by_fields(&self, field_index: usize) -> impl Iterator<Item = usize> {
        self.counted_fields(field_index, true)
    }
}
