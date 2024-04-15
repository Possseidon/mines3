use std::{mem::size_of, num::NonZeroU8};

use bitvec::{array::BitArray, bitbox, bitvec, boxed::BitBox, slice::BitSlice, vec::BitVec};
use itertools::{zip_eq, Itertools, MinMaxResult};
use thiserror::Error;

use crate::{
    player::{Field, Player},
    playfield::Playfield,
};

/// Adds more functionality on top of an existing [`Player`].
///
/// - Remembers which fields have already been clicked.
/// - Caches revealed mine counts.
/// - Caches the number of flagged and revealed fields for faster access.
/// - Keeps track of which fields are relevant to find the next field to click.
pub struct GameState<T: Player> {
    player: T,
    clicked: BitVec,
    mine_counts: Vec<usize>,
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
            mine_counts: vec![0; field_count_hint],
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
    pub fn click(&mut self, field_index: usize, flag: bool) {
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

        // cache mine_count
        if let Some(mine_count) = result.count() {
            // self.mine_counts defaults to 0, so we can just ignore 0
            if mine_count > 0 {
                if field_index >= self.mine_counts.len() {
                    self.mine_counts.resize(field_index + 1, 0);
                }
                self.mine_counts[field_index] = mine_count;
            }
        }

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
    }

    /// Whether the field has been clicked yet.
    pub fn is_clicked(&self, field_index: usize) -> bool {
        self.clicked
            .get(field_index)
            .as_deref()
            .copied()
            .unwrap_or(false)
    }

    /// Returns an iterator over all unclicked field indices.
    pub fn unclicked_fields(&self) -> impl Iterator<Item = usize> + '_ {
        let field_count = self
            .playfield()
            .field_count()
            .map(|count| count.get())
            .unwrap_or(usize::MAX);
        self.clicked
            .iter_zeros()
            .chain(self.clicked.len()..field_count)
    }

    /// Returns the state of the given field.
    ///
    /// Returns [`None`] if the field has not been [`GameState::click`]ed yet.
    pub fn get(&self, field_index: usize) -> Option<Field> {
        self.is_clicked(field_index).then(|| {
            self.player
                .get(field_index)
                .with_count(|| self.mine_counts.get(field_index).copied().unwrap_or(0))
        })
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
    pub fn relevant(&self) -> &BitSlice {
        &self.relevant
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

/// Implements solving logic.
impl<T: Player> GameState<T> {
    pub fn solve(&mut self, max_difficulty: Difficulty) -> Result<Difficulty, SolveError> {
        let mut difficulty = Difficulty::Trivial;
        while !self.solved() {
            difficulty = difficulty.max(self.apply_next_solve_actions(max_difficulty)?);
        }
        Ok(difficulty)
    }

    pub fn solved(&self) -> bool {
        todo!()
    }

    pub fn apply_solve_actions(&mut self, solve_actions: &SolveActions) {
        for &field_index in solve_actions.reveal.iter() {
            self.click(field_index, false);
        }
        for &field_index in solve_actions.flag.iter() {
            self.click(field_index, true);
        }
    }

    pub fn apply_next_solve_actions(
        &mut self,
        max_difficulty: Difficulty,
    ) -> Result<Difficulty, SolveError> {
        let (difficulty, solve_actions) = self.next_solve_actions(max_difficulty)?;
        self.apply_solve_actions(&solve_actions);
        Ok(difficulty)
    }

    pub fn next_solve_actions(
        &self,
        max_difficulty: Difficulty,
    ) -> Result<(Difficulty, SolveActions), SolveError> {
        if self.remaining_flags() == Some(0) {
            return Ok((
                Difficulty::Trivial,
                SolveActions {
                    reveal: self.unclicked_fields().collect(),
                    ..Default::default()
                },
            ));
        }

        if self.remaining_reveals() == Some(0) {
            return Ok((
                Difficulty::Trivial,
                SolveActions {
                    flag: self.unclicked_fields().collect(),
                    ..Default::default()
                },
            ));
        }

        let relevant_fields = self.relevant().iter_ones().map(|field_index| {
            let flag_count = self
                .playfield()
                .counted_fields(field_index)
                .filter_map(|field_index| self.get(field_index))
                .filter(|field| field.is_flag())
                .count();
            let counted_fields = self
                .playfield()
                .counted_fields(field_index)
                .filter(|&field_index| !self.is_clicked(field_index));
            let shown_count = self
                .get(field_index)
                .expect("relevant fields should be revealed")
                .count()
                .expect("relevant fields should have a count");

            RelevantField {
                field_index,
                remaining_mine_count: shown_count - flag_count,
                counted_fields: counted_fields.collect(),
            }
        });

        let mut additional_mines_scratch = Vec::new();
        let mut counted_fields = Vec::new();

        // k == 1
        let solve_actions = relevant_fields
            .clone()
            .map(|relevant_field| Self::click_all_solve_actions(&relevant_field))
            .collect::<SolveActions>();
        if !solve_actions.is_empty() {
            return Ok((Difficulty::Trivial, solve_actions));
        }

        // k == 2
        let relevant_fields = relevant_fields.collect_vec();
        let MinMaxResult::MinMax(min_field_index, max_field_index) = relevant_fields
            .iter()
            .flat_map(|relevant_field| relevant_field.counted_fields.clone())
            .minmax()
        else {
            // TODO: panic or unsolvable?
            // return Err(SolveError::Unsolvable);
            panic!();
        };
        let relevant_field_range = max_field_index - min_field_index;
        let mut intersection_matrix = IntersectionMatrix::new(relevant_field_range);

        let mut too_complex_lower_bound = Complexity::MAX;
        let mut complexity_upper_bound = Complexity::MIN;

        let solve_actions = relevant_fields
            .iter()
            .tuple_combinations()
            .filter_map(|(a, b)| {
                counted_fields.clone_from(&a.counted_fields);
                counted_fields.extend(&b.counted_fields);
                counted_fields.sort_unstable();
                let old_len = counted_fields.len();
                counted_fields.dedup();
                if counted_fields.len() == old_len {
                    return None;
                }
                let complexity = Complexity::new_clamped(counted_fields.len());
                if Difficulty::Complex(complexity) > max_difficulty {
                    too_complex_lower_bound = too_complex_lower_bound.min(complexity);
                    return None;
                }
                complexity_upper_bound = complexity_upper_bound.max(complexity);
                intersection_matrix.set(a.field_index, b.field_index);
                Some(self.solve_actions(&[a, b], &counted_fields, &mut additional_mines_scratch))
            })
            .collect::<SolveActions>();
        if !solve_actions.is_empty() {
            return Ok((Difficulty::Complex(complexity_upper_bound), solve_actions));
        }

        // k >= 3
        for k in 3..=relevant_fields.len() {
            let solve_actions = relevant_fields
                .iter()
                .combinations(k)
                .filter_map(|relevant_fields| {
                    if !relevant_fields
                        .iter()
                        .tuple_combinations()
                        .any(|(a, b)| intersection_matrix.get(a.field_index, b.field_index))
                    {
                        return None;
                    }

                    counted_fields.clear();
                    counted_fields.extend(
                        relevant_fields
                            .iter()
                            .flat_map(|relevant_field| &relevant_field.counted_fields),
                    );
                    counted_fields.sort_unstable();
                    counted_fields.dedup();
                    Some(self.solve_actions(
                        &relevant_fields,
                        &counted_fields,
                        &mut additional_mines_scratch,
                    ))
                })
                .collect::<SolveActions>();
            if !solve_actions.is_empty() {
                return Ok((Difficulty::Complex(complexity_upper_bound), solve_actions));
            }
        }

        Err(SolveError::Unsolvable)
    }

    /// Returns simple solve actions when all surrounding fields can either be revealed or flagged.
    fn click_all_solve_actions(relevant_field: &RelevantField) -> SolveActions {
        if relevant_field.remaining_mine_count == 0 {
            SolveActions {
                flag: relevant_field.counted_fields.clone(),
                ..Default::default()
            }
        } else if relevant_field.remaining_mine_count == relevant_field.counted_fields.len() {
            SolveActions {
                reveal: relevant_field.counted_fields.clone(),
                ..Default::default()
            }
        } else {
            SolveActions::default()
        }
    }

    /// Returns which fields can safely be revealed or flagged.
    ///
    /// Done by checking for all valid mine placements:
    ///
    /// - If a field in `counted_fields` is free in all valid placements it can be revealed.
    /// - If a field in `counted_fields` contains a mine in all valid placements it can be flagged.
    fn solve_actions(
        &self,
        relevant_fields: &[&RelevantField],
        counted_fields: &[usize],
        additional_mines_scratch: &mut Vec<usize>,
    ) -> SolveActions {
        assert!(
            counted_fields.len() < size_of::<MineFlags>() * 8,
            "should be limited by Difficulty::MAX"
        );

        additional_mines_scratch.resize(relevant_fields.len(), 0);

        let (reveal, flag) = (0..1 << counted_fields.len()).fold(
            (!MineFlags::ZERO, !MineFlags::ZERO),
            |(mut reveal, mut flag), mines| {
                let mines = BitArray::new(mines);

                additional_mines_scratch
                    .iter_mut()
                    .for_each(|count| *count = 0);

                for mine in mines.iter_ones() {
                    let relevant_field_indices = self
                        .playfield()
                        .counted_by_fields(counted_fields[mine])
                        .filter_map(|field_index| {
                            relevant_fields.iter().position(|relevant_field| {
                                relevant_field.field_index == field_index
                            })
                        });
                    for relevant_field_index in relevant_field_indices {
                        additional_mines_scratch[relevant_field_index] += 1;
                    }
                }

                let valid = zip_eq(relevant_fields, additional_mines_scratch.iter()).all(
                    |(relevant_field, additional_mines)| {
                        relevant_field.remaining_mine_count == *additional_mines
                    },
                );

                if valid {
                    reveal &= !mines;
                    flag &= mines;
                }

                (reveal, flag)
            },
        );

        SolveActions {
            reveal: reveal.iter_ones().map(|i| counted_fields[i]).collect(),
            flag: flag.iter_ones().map(|i| counted_fields[i]).collect(),
        }
    }
}

struct RelevantField {
    field_index: usize,
    remaining_mine_count: usize,
    counted_fields: Vec<usize>, // TODO: benchmark with different SmallVec buffer sizes
}

// TODO: Maybe consider u64, but u32 is probably sufficient.
type MineFlags = BitArray<u32>;

/// How hard it is to solve a minefield.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Difficulty {
    Trivial,
    Complex(Complexity),
}

/// How many unrevealed fields have to be looked at in parallel.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Complexity(NonZeroU8);

impl Complexity {
    const MIN: Self = Self(match NonZeroU8::new(2) {
        Some(min) => min,
        None => unreachable!(),
    });

    const MAX: Self = Self(match NonZeroU8::new(8 * size_of::<MineFlags>() as u8) {
        Some(max) => max,
        None => unreachable!(),
    });

    fn new_clamped(len: usize) -> Self {
        Self(
            NonZeroU8::new(
                len.clamp(Self::MIN.0.get().into(), Self::MAX.0.get().into())
                    .try_into()
                    .expect("should be clamped"),
            )
            .expect("should be clamped"),
        )
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct SolveActions {
    pub reveal: Vec<usize>, // TODO: consider SmallVec
    pub flag: Vec<usize>,   // TODO: consider SmallVec
}

impl SolveActions {
    fn is_empty(&self) -> bool {
        self.reveal.is_empty() && self.flag.is_empty()
    }
}

impl FromIterator<SolveActions> for SolveActions {
    fn from_iter<T: IntoIterator<Item = SolveActions>>(iter: T) -> Self {
        let mut result = Self::default();
        for solve_actions in iter {
            result.reveal.extend(solve_actions.reveal);
            result.flag.extend(solve_actions.flag);
        }
        result
    }
}

#[derive(Debug, Error)]
pub enum SolveError {
    #[error("not solvable")]
    Unsolvable,
    #[error("too difficult to solve; requires {complexity:?} or possibly higher")]
    TooDifficult { complexity: Complexity },
}

/// Stores intersections between fields using a bitfield.
struct IntersectionMatrix(BitBox);

impl IntersectionMatrix {
    fn new(count: usize) -> Self {
        let len = count * (count + 1) / 2;
        Self(bitbox![0; len])
    }

    fn set(&mut self, low: usize, high: usize) {
        let index = self.index(low, high);
        self.0.set(index, true)
    }

    fn get(&self, low: usize, high: usize) -> bool {
        self.0[self.index(low, high)]
    }

    fn index(&self, low: usize, high: usize) -> usize {
        assert!(high < self.0.len());
        // TODO: pretty sure this is always the case
        assert!(low < high);
        low * (2 * self.0.len() - low - 1) / 2 + high - low - 1
    }
}
