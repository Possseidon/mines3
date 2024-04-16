use std::{cmp::Ordering, mem::size_of, num::NonZeroU8};

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
            .map(|count| count.get() - self.reveal_count() - self.flag_count())
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
            // println!("{self}");
            difficulty = difficulty.max(self.apply_next_solve_actions(max_difficulty)?);
        }
        Ok(difficulty)
    }

    pub fn solved(&self) -> bool {
        // TODO: If mines are also required to be flagged, remaining_flags must also be 0
        self.remaining_reveals() == Some(0)
    }

    pub fn apply_solve_actions(&mut self, mut solve_actions: SolveActions) {
        solve_actions.reveal.sort_unstable();
        for &field_index in solve_actions.reveal.iter().dedup() {
            self.click(field_index, false);
        }
        solve_actions.flag.sort_unstable();
        for &field_index in solve_actions.flag.iter().dedup() {
            self.click(field_index, true);
        }
    }

    pub fn apply_next_solve_actions(
        &mut self,
        max_difficulty: Difficulty,
    ) -> Result<Difficulty, SolveError> {
        let (difficulty, solve_actions) = self.next_solve_actions(max_difficulty)?;
        // println!(
        //     "flags: {} reveals: {}",
        //     solve_actions.flag.len(),
        //     solve_actions.reveal.len()
        // );
        self.apply_solve_actions(solve_actions);
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

        let relevant_fields = self.relevant_fields();

        if let Some(result) = Self::solve_actions_trivial(relevant_fields.clone(), max_difficulty) {
            return result;
        }

        // TODO: Optionally pass these vecs in somehow to reuse allocations across calls.
        let relevant_fields = relevant_fields.collect_vec();
        let mut any_too_complex = false;
        let intersection_matrix = self.intersection_matrix(&relevant_fields);
        let mut counted_fields_scratch = Vec::new();
        let mut additional_mines_scratch = Vec::new();

        for k in 3..=relevant_fields.len() {
            if let Some(result) = self.solve_actions_complex(
                k,
                max_difficulty,
                &relevant_fields,
                &mut any_too_complex,
                &intersection_matrix,
                &mut counted_fields_scratch,
                &mut additional_mines_scratch,
            ) {
                return result;
            }
        }

        Err(if any_too_complex {
            SolveError::TooComplex
        } else {
            SolveError::Unsolvable
        })
    }

    fn relevant_fields(&self) -> impl ExactSizeIterator<Item = RelevantField> + Clone + '_ {
        self.relevant().iter_ones().map(|field_index| {
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
        })
    }

    fn solve_actions_trivial(
        relevant_fields: impl Iterator<Item = RelevantField>,
        max_difficulty: Difficulty,
    ) -> Option<Result<(Difficulty, SolveActions), SolveError>> {
        let solve_actions = relevant_fields
            .map(|relevant_field| Self::click_all_solve_actions(&relevant_field))
            .collect::<SolveActions>();

        if !solve_actions.is_empty() {
            return Some(Ok((Difficulty::Trivial, solve_actions)));
        }

        if max_difficulty < Difficulty::Complex(Complexity::MIN) {
            return Some(Err(SolveError::TooDifficult {
                complexity: Complexity::MIN,
            }));
        }

        None
    }

    fn intersection_matrix(&self, relevant_fields: &[RelevantField]) -> IntersectionMatrix {
        let Some((min_field_index, max_field_index)) = relevant_fields
            .iter()
            .map(|relevant_field| relevant_field.field_index)
            .minmax()
            .into_option()
        else {
            panic!("should not be empty");
        };

        let mut intersection_matrix = IntersectionMatrix::new(min_field_index, max_field_index);
        for (low, high) in relevant_fields.iter().tuple_combinations() {
            let mut low_iter = low.counted_fields.iter();
            let mut high_iter = high.counted_fields.iter();
            let mut current_low_index = low_iter.next();
            let mut current_high_index = high_iter.next();
            // assuming both listst are sorted, find duplicates, which signifies overlap
            while let Some((low_index, high_index)) = current_low_index.zip(current_high_index) {
                match low_index.cmp(high_index) {
                    Ordering::Equal => {
                        intersection_matrix.set(low.field_index, high.field_index);
                        break;
                    }
                    Ordering::Less => current_low_index = low_iter.next(),
                    Ordering::Greater => current_high_index = high_iter.next(),
                }
            }
        }
        intersection_matrix
    }

    fn solve_actions_complex(
        &self,
        k: usize,
        max_difficulty: Difficulty,
        relevant_fields: &[RelevantField],
        any_too_complex: &mut bool,
        intersection_matrix: &IntersectionMatrix,
        counted_fields_scratch: &mut Vec<usize>,
        additional_mines_scratch: &mut Vec<usize>,
    ) -> Option<Result<(Difficulty, SolveActions), SolveError>> {
        let mut min_complexity = None;
        let solve_actions = relevant_fields
            .iter()
            .combinations(k)
            .filter_map(|relevant_fields| {
                if !relevant_fields
                    .iter()
                    .tuple_combinations()
                    .any(|(low, high)| intersection_matrix.get(low.field_index, high.field_index))
                {
                    return None;
                }

                counted_fields_scratch.clear();
                counted_fields_scratch.extend(
                    relevant_fields
                        .iter()
                        .flat_map(|relevant_field| &relevant_field.counted_fields),
                );
                counted_fields_scratch.sort_unstable();
                counted_fields_scratch.dedup();
                let Some(complexity) =
                    Complexity::from_counted_fields_len(counted_fields_scratch.len())
                else {
                    *any_too_complex = true;
                    return None;
                };
                if min_complexity.is_some_and(|min_complexity| complexity > min_complexity) {
                    return None;
                }
                min_complexity = Some(complexity);
                if Difficulty::Complex(complexity) > max_difficulty {
                    return None;
                }
                Some((
                    complexity,
                    self.solve_actions(
                        &relevant_fields,
                        counted_fields_scratch,
                        additional_mines_scratch,
                    ),
                ))
            })
            .collect_vec();

        // must collect so that min_complexity is set

        let Some(min_complexity) = min_complexity else {
            return None;
        };
        if Difficulty::Complex(min_complexity) <= max_difficulty {
            let solve_actions = solve_actions
                .into_iter()
                .filter(|(complexity, _)| *complexity == min_complexity)
                .map(|(_, solve_actions)| solve_actions)
                .collect::<SolveActions>();
            (!solve_actions.is_empty())
                .then_some(Ok((Difficulty::Complex(min_complexity), solve_actions)))
        } else {
            Some(Err(SolveError::TooDifficult {
                complexity: min_complexity,
            }))
        }
    }

    /// Returns simple solve actions when all surrounding fields can either be revealed or flagged.
    fn click_all_solve_actions(relevant_field: &RelevantField) -> SolveActions {
        if relevant_field.remaining_mine_count == 0 {
            SolveActions {
                reveal: relevant_field.counted_fields.clone(),
                ..Default::default()
            }
        } else if relevant_field.remaining_mine_count == relevant_field.counted_fields.len() {
            SolveActions {
                flag: relevant_field.counted_fields.clone(),
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
    ///
    /// The complexity of the returned solve actions is just the length of `counted_fields`.
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

        let reveal = &reveal[0..counted_fields.len()];
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
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Difficulty {
    #[default]
    Trivial,
    Complex(Complexity),
}

// TODO: Currently complexity only includes how many mines are looked at
//       However there are other things that can drastically slow down the solver, like a lot of relevant fields

/// How many unrevealed fields have to be looked at in parallel.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Complexity(NonZeroU8);

impl Complexity {
    /// The minimum possible complexity, which is 3.
    ///
    /// When looking at just 1 mine, from the view of the relevant fields, it either exists or
    /// doesn't. This is trivial.
    ///
    /// When looking at 2 mines at once, that has four possible mine configurations:
    ///
    /// - `[0, 0]` -> trivial
    /// - `[0, 1]` -> impossible to know, unless trivial
    /// - `[1, 0]` -> impossible to know, unless trivial
    /// - `[1, 1]` -> trivial
    ///
    /// If the middle two cases _would_ lead to an answer, this same answer can also be found by
    /// just looking at that field alone. So 2 is still considered trivial.
    ///
    /// Only at 3 mines is where it starts to get interesting. E.g. three consecutive `1` can be
    /// deduced to contain a mine in the middle:
    ///
    /// ```txt
    /// 1|1|1
    /// -+-+-
    ///  |M|
    /// ```
    ///
    /// And in a similar fashion, a `1 2 1` configuration can also be deduced:
    ///
    /// ```txt
    /// 1|2|1
    /// -+-+-
    /// M| |M
    /// ```
    const MIN: Self = Self(match NonZeroU8::new(3) {
        Some(min) => min,
        None => unreachable!(),
    });

    /// The maximum valid complexity
    const MAX: Self = Self(match NonZeroU8::new(8 * size_of::<MineFlags>() as u8) {
        Some(max) => max,
        None => unreachable!(),
    });

    pub fn new(complexity: u8) -> Option<Self> {
        (Self::MIN.0.get()..=Self::MAX.0.get())
            .contains(&complexity)
            .then(|| Complexity(complexity.try_into().expect("should be in range")))
    }

    /// Returns [`None`] if there are more than [`Self::MAX`] counted fields.
    ///
    /// # Panics
    ///
    /// Panics if there are less than [`Self::MIN`] counted fields.
    fn from_counted_fields_len(counted_fields_len: usize) -> Option<Self> {
        assert!(counted_fields_len >= Self::MIN.0.get().into());
        (counted_fields_len <= Self::MAX.0.get().into()).then(|| {
            Self(
                NonZeroU8::new(counted_fields_len.try_into().expect("should be in range"))
                    .expect("should be in range"),
            )
        })
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct SolveActions {
    reveal: Vec<usize>, // TODO: consider SmallVec
    flag: Vec<usize>,   // TODO: consider SmallVec
}

impl SolveActions {
    fn is_empty(&self) -> bool {
        self.reveal.is_empty() && self.flag.is_empty()
    }
}

impl FromIterator<SolveActions> for SolveActions {
    fn from_iter<T: IntoIterator<Item = SolveActions>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        let mut result = iter.next().unwrap_or_default();
        for solve_actions in iter {
            result.reveal.extend(solve_actions.reveal);
            result.flag.extend(solve_actions.flag);
        }
        result
    }
}

#[derive(Debug, Error)]
pub enum SolveError {
    #[error("too difficult to solve; requires {complexity:?} or possibly higher")]
    TooDifficult { complexity: Complexity },
    #[error("too complex for the solver")]
    TooComplex,
    #[error("not solvable")]
    Unsolvable,
}

/// Stores intersections between fields using a bitfield.
///
/// TODO: This probably goes out of hand faster than I thought...
///       I probably want to use BTreeSet<(usize, usize)> after all or fall back to it after certain sizes.
struct IntersectionMatrix {
    offset: usize,
    count: usize,
    bits: BitBox,
}

impl IntersectionMatrix {
    fn new(min: usize, max: usize) -> Self {
        let range = max - min;
        let len = range * (range + 1) / 2;
        Self {
            bits: bitbox![0; len],
            count: range + 1,
            offset: min,
        }
    }

    fn set(&mut self, low: usize, high: usize) {
        let index = self.index(low, high);
        self.bits.set(index, true)
    }

    fn get(&self, low: usize, high: usize) -> bool {
        self.bits[self.index(low, high)]
    }

    fn index(&self, mut low: usize, mut high: usize) -> usize {
        low -= self.offset;
        high -= self.offset;
        assert!(high < self.count);
        // TODO: pretty sure this is always the case
        assert!(low < high);
        low * (2 * self.count - low - 1) / 2 + high - low - 1
    }
}

// TODO: Remove everything below.

fn color_code(mines: usize) -> &'static str {
    match mines {
        1 => "\x1B[34m",
        2 => "\x1B[32m",
        3 => "\x1B[31m",
        4 => "\x1B[34m",
        _ => "",
    }
}

impl<T: Player> std::fmt::Display for GameState<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for field_index in 0..16 * 30 {
            match self.get(field_index) {
                Some(Field::Flag { count: None }) => write!(f, "🚩")?,
                Some(Field::Free { count }) => write!(f, "{}{count}\x1B[0m ", color_code(count))?,
                _ => write!(f, "  ")?,
            }

            if (field_index + 1) % 30 == 0 {
                writeln!(f)?;
            }
        }

        writeln!(
            f,
            "mines left: {:?} unrevealed: {:?}",
            self.remaining_flags(),
            self.remaining_reveals()
        )?;
        Ok(())
    }
}

/// Merges the given sorted lists into a single sorted list in `result`.
///
/// The lists must not contain any duplicates and must themselves be already sorted.
///
/// `result` is not cleared.
fn merge(lists: &mut Vec<&[usize]>, result: &mut Vec<usize>) {
    while let Some(&current) = lists.iter().flat_map(|list| list.first()).min() {
        result.push(current);
        lists.retain_mut(|list| {
            if let Some(&first) = list.first() {
                if first == current {
                    *list = &list[1..];
                }
                true
            } else {
                false
            }
        });
    }
}
