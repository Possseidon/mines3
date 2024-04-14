use bitvec::{bitvec, vec::BitVec};

use crate::{
    player::{Field, Player},
    playfield::Playfield,
};

/// Adds more functionality on top of an existing [`Player`].
///
/// - Remembers which fields have already been clicked.
/// - Caches the number of flagged and revealed fields for faster access.
/// - Keeps track of which fields are relevant to find the next field to click.
pub struct GameState<T: Player> {
    player: T,
    clicked: BitVec,
    flag_count: usize,
    reveal_count: usize,
    relevant: BitVec,
}

impl<T: Player> GameState<T> {
    pub const IS_ORACLE: bool = T::IS_ORACLE;

    /// Wraps the given [`Player`] in a [`GameState`].
    ///
    /// [`Player::click`] must not have been called yet and will likely eventually lead to a panic.
    pub fn new(player: T) -> Self {
        let field_count_hint = player
            .playfield()
            .field_count()
            .map(|count| count.get())
            .unwrap_or(0);
        Self {
            player,
            clicked: bitvec![0; field_count_hint],
            flag_count: 0,
            reveal_count: 0,
            relevant: bitvec![0; field_count_hint],
        }
    }

    /// Delegates to [`Player::playfield`].
    pub fn playfield(&self) -> &T::Playfield {
        self.player.playfield()
    }

    /// Delegates to [`Player::mine_count`].
    pub fn mine_count(&self) -> Option<usize> {
        self.player.mine_count()
    }

    /// The total number of fields that do not contain a mine, if known.
    pub fn free_count(&self) -> Option<usize> {
        self.playfield()
            .field_count()
            .zip(self.mine_count())
            .map(|(field_count, mine_count)| field_count.get() - mine_count)
    }

    /// The total number of placed flags.
    ///
    /// This value is guaranteed to have fast access due to being cached.
    pub fn flag_count(&self) -> usize {
        self.flag_count
    }

    /// The total number of fields that have been revealed.
    ///
    /// This value is guaranteed to have fast access due to being cached.
    pub fn reveal_count(&self) -> usize {
        self.reveal_count
    }

    /// The number of remaining flags that can be placed (if the total number of mines is known).
    pub fn remaining_flags(&self) -> Option<usize> {
        self.mine_count().map(|count| count - self.flag_count())
    }

    /// The number of fields that are yet to be revealed (if the total number of fields is known).
    pub fn remaining_reveals(&self) -> Option<usize> {
        self.playfield()
            .field_count()
            .map(|count| count.get() - self.reveal_count())
    }

    /// Reveals or flags the given field, returning which one it was including its count.
    ///
    /// Flagging might return [`Field::Mine`] even if that isn't correct unless
    /// [`GameState::IS_ORACLE`] is `true`.
    ///
    /// # Panics
    ///
    /// May panic if `field_index` is out of bounds.
    ///
    /// Panics when called twice on the same field; use [`GameState::get`] instead.
    ///
    /// Panics when `flag` does not match the actual field if [`GameState::IS_ORACLE`] is `true`.
    ///
    /// Panics when more mines than [`Self::mine_count`] are flagged.
    pub fn click(&mut self, field_index: usize, flag: bool) -> Field {
        // udpate clicked
        if field_index >= self.clicked.len() {
            self.clicked.resize(field_index + 1, false);
        }
        let already_clicked = self.clicked.replace(field_index, true);
        assert!(!already_clicked);

        // increment flag/reveal count
        if flag {
            self.flag_count += 1;
            if let Some(mine_count) = self.mine_count() {
                assert!(self.flag_count <= mine_count);
            }
        } else {
            self.reveal_count += 1;
        }

        // forward call to player
        let result = self.player.click(field_index, flag);

        // make field_index relevant if necessary
        if result.count().is_some() && self.check_relevant(field_index) {
            if field_index >= self.relevant.len() {
                self.relevant.resize(field_index + 1, false);
            }
            self.relevant.set(field_index, true);
        }

        // make fields that count field_index irrelevant if necessary
        for field_index in self.player.playfield().counted_by_fields(field_index) {
            if self.is_relevant(field_index) && !self.check_relevant(field_index) {
                self.relevant.set(field_index, false);
            }
        }

        result
    }

    /// Whether the field has been clicked yet.
    pub fn is_clicked(&self, field_index: usize) -> bool {
        self.clicked
            .get(field_index)
            .as_deref()
            .copied()
            .unwrap_or(false)
    }

    /// Returns the state of the given field.
    ///
    /// Returns [`None`] if the field has not been [`GameState::click`]ed yet.
    pub fn get(&self, field_index: usize) -> Option<Field> {
        self.is_clicked(field_index)
            .then(|| self.player.get(field_index))
    }

    /// All revealed fields that contribute to the deduction of at least one unclicked field.
    ///
    /// Trying to flag or reveal a field that isn't in this set can only be a random guess. Although
    /// there is one exception: If the number of remaining mines matches the number of remaining
    /// fields, all fields can be flagged despite not being part of this set. (Same for the number
    /// of revealed fields.)
    ///
    /// While this is mainly used by the solver, it can also be used to gray out or even completely
    /// hide fields that are no longer relevant to solving the puzzle.
    pub fn relevant(&self) -> impl ExactSizeIterator<Item = usize> + '_ {
        self.relevant.iter_ones()
    }

    /// Whether this field is relevant for deducing the next field.
    ///
    /// See [`Self::relevant`] for more info.
    pub fn is_relevant(&self, field_index: usize) -> bool {
        self.relevant
            .get(field_index)
            .as_deref()
            .copied()
            .unwrap_or(false)
    }

    /// Whether this field should be part of [`Self::relevant`].
    ///
    /// Relevant fields have at least one counted, unclicked field.
    ///
    /// # Panics
    ///
    /// Panics if `field_index` is out of bounds.
    fn check_relevant(&self, field_index: usize) -> bool {
        self.playfield()
            .counted_fields(field_index)
            .any(|field_index| !self.is_clicked(field_index))
    }
}
