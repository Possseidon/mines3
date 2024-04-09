use std::collections::BTreeSet;

use bitvec::vec::BitVec;
use itertools::iproduct;

use crate::minefield::{AdjacentFields, MinefieldReader, MinefieldWriter};

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct UVec2 {
    pub x: usize,
    pub y: usize,
}

impl UVec2 {
    pub fn new(x: usize, y: usize) -> Self {
        Self { x, y }
    }
}

#[derive(Clone, Debug)]
pub struct Minefield2D {
    mines: BitVec,
    width: usize,
}

impl Minefield2D {
    pub fn new(size: UVec2) -> Self {
        Self {
            mines: BitVec::repeat(false, size.x * size.y),
            width: size.x,
        }
    }

    pub fn size(&self) -> UVec2 {
        UVec2 {
            x: self.width,
            y: self.mines.len() / self.width,
        }
    }

    pub fn is_mine(&self, coord: UVec2) -> Option<bool> {
        self.coord_to_field_index(coord)
            .map(|field_index| self.mines[field_index])
    }

    pub fn set_mine(&mut self, coord: UVec2, mine: bool) {
        let field_index = self
            .coord_to_field_index(coord)
            .expect("coord out of range");
        self.mines.set(field_index, mine);
    }

    pub fn place_mine(&mut self, coord: UVec2) {
        self.set_mine(coord, true);
    }

    pub fn coord_to_field_index(&self, coord: UVec2) -> Option<usize> {
        let field_index = (coord.x < self.width).then_some(coord.x + coord.y * self.width)?;
        (field_index < self.field_count()).then_some(field_index)
    }

    pub fn field_index_to_coord(&self, field_index: usize) -> Option<UVec2> {
        (field_index < self.field_count()).then_some(UVec2 {
            x: field_index % self.width,
            y: field_index / self.width,
        })
    }
}

impl AdjacentFields for Minefield2D {
    fn field_count(&self) -> usize {
        self.mines.len()
    }

    fn adjacent_fields(&self, field_index: usize) -> BTreeSet<usize> {
        let coord = self
            .field_index_to_coord(field_index)
            .expect("invalid field index");

        iproduct!(
            coord.x.saturating_sub(1)..=coord.x.saturating_add(1),
            coord.y.saturating_sub(1)..=coord.y.saturating_add(1)
        )
        .filter_map(move |(x, y)| {
            if UVec2::new(x, y) != coord {
                self.coord_to_field_index(UVec2 { x, y })
            } else {
                None
            }
        })
        .collect()
    }
}

impl MinefieldWriter for Minefield2D {
    fn set_mine(&mut self, field_index: usize, is_mine: bool) {
        self.set_mine(self.field_index_to_coord(field_index).unwrap(), is_mine);
    }
}

impl MinefieldReader for Minefield2D {
    fn is_mine(&self, field_index: usize) -> bool {
        self.field_index_to_coord(field_index)
            .and_then(|coord| self.is_mine(coord))
            .unwrap_or_default()
    }
}
