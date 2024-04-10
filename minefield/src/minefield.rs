use std::collections::BTreeSet;

pub trait AdjacentFields {
    fn field_count(&self) -> usize;
    fn adjacent_fields(&self, field_index: usize) -> BTreeSet<usize>;
}

pub trait MinefieldWriter: AdjacentFields {
    fn set_mine(&mut self, field_index: usize, is_mine: bool);

    fn place_mine(&mut self, field_index: usize) {
        self.set_mine(field_index, true);
    }

    fn remove_mine(&mut self, field_index: usize) {
        self.set_mine(field_index, false);
    }
}

pub trait MinefieldReader: AdjacentFields {
    fn is_mine(&self, field_index: usize) -> bool;

    fn mine_count(&self) -> usize {
        (0..self.field_count())
            .filter(|&field_index| self.is_mine(field_index))
            .count()
    }
}

pub trait Minefield: MinefieldWriter + MinefieldReader {}

impl<T: MinefieldWriter + MinefieldReader> Minefield for T {}
