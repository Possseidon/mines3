use crate::{
    mine_map::MineMap,
    player::{Field, PartialField, Player},
    playfield::Playfield,
};

/// Combines a generic [`Playfield`] with a [`MineMap`] and adds some [`MinefieldRules`] on top.
///
/// Implements the [`Player`] trait.
pub struct Minefield<T: Playfield> {
    pub playfield: T,
    pub mines: MineMap,
    pub rules: MinefieldRules,
}

impl<T: Playfield> Minefield<T> {
    fn count_mines(&self, field_index: usize) -> usize {
        self.playfield
            .counted_fields(field_index)
            .filter(|&field_index| self.mines.is_mine(field_index))
            .count()
    }

    fn simulate_click(&self, field_index: usize, flag: bool) -> Field {
        assert_eq!(self.mines.is_mine(field_index), flag);
        self.get(field_index)
            .with_count(|| self.count_mines(field_index))
    }
}

impl<T: Playfield> Player for Minefield<T> {
    const IS_ORACLE: bool = true;

    type Playfield = T;

    fn playfield(&self) -> &Self::Playfield {
        &self.playfield
    }

    fn mine_count(&self) -> Option<usize> {
        self.rules
            .mine_count_available
            .then(|| self.mines.mine_count())
    }

    fn click(&mut self, field_index: usize, flag: bool) -> Field {
        self.simulate_click(field_index, flag)
    }

    fn get(&self, field_index: usize) -> PartialField {
        if self.mines.is_mine(field_index) {
            PartialField::Flag {
                has_count: self.rules.reveal_mines,
            }
        } else {
            PartialField::Free
        }
    }
}

impl<T: Playfield> Player for &Minefield<T> {
    const IS_ORACLE: bool = true;

    type Playfield = T;

    fn playfield(&self) -> &Self::Playfield {
        (*self).playfield()
    }

    fn mine_count(&self) -> Option<usize> {
        (*self).mine_count()
    }

    fn click(&mut self, field_index: usize, flag: bool) -> Field {
        self.simulate_click(field_index, flag)
    }

    fn get(&self, field_index: usize) -> PartialField {
        (*self).get(field_index)
    }
}

/// Configures how the [`Player`] trait is implemented by [`Minefield`].
pub struct MinefieldRules {
    /// Whether mines also show their count upon being flagged.
    ///
    /// This also implies that flagging no longer optional like in classical Minesweeper. A field
    /// without a mine getting flagged is now considered a mistake.
    pub reveal_mines: bool,
    /// Whether the total number of mines is known.
    ///
    /// This allows flagging all remaining fields once there are only `mine_count` fields left. At
    /// the same time it also allows revealing all remaining fields once `mine_count` fields have
    /// been flagged (assuming the flags are correct, which they always are; invalid flags are fully
    /// handled by the frontend).
    pub mine_count_available: bool,
}
