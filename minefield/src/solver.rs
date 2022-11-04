use std::collections::BTreeSet;

use itertools::Itertools;
use maybe_owned::MaybeOwned;
use thiserror::Error;

use crate::minefield::MinefieldReader;

#[derive(Error, Debug)]
pub enum RevealError {
    #[error("field already revealed")]
    AlreadyRevealed,
    #[error("mine revealed")]
    Boom,
}

#[derive(Error, Debug)]
pub enum FlagError {
    #[error("field already flagged")]
    AlreadyFlagged,
    #[error("all mines flagged")]
    AllMinesFlagged,
}

#[derive(Error, Debug)]
pub enum SolveError {
    #[error("not solvable")]
    Unsolvable,
    #[error("too complex")]
    TooComplex,
}

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Field {
    #[default]
    Unrevealed,
    Revealed {
        adjacent_mines: usize,
    },
    Flagged,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SolveActions {
    reveal: BTreeSet<usize>,
    flag: BTreeSet<usize>,
}

impl SolveActions {
    fn is_empty(&self) -> bool {
        self.reveal.is_empty() && self.flag.is_empty()
    }
}

impl std::ops::BitOr for SolveActions {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self::Output {
        self |= rhs;
        self
    }
}

impl std::ops::BitOrAssign for SolveActions {
    fn bitor_assign(&mut self, rhs: Self) {
        self.reveal.extend(rhs.reveal);
        self.flag.extend(rhs.flag);
    }
}

#[derive(Debug)]
pub struct MinefieldSolver<'a, T: MinefieldReader> {
    minefield: MaybeOwned<'a, T>,
    max_complexity: Option<usize>,
    fields: Vec<Field>,
    adjacent_unrevealed: BTreeSet<usize>,
    unflagged_mines_left: usize,
    reveals_left: usize,
}

pub(crate) const DEFAULT_MAX_COMPLEXITY: usize = 10;

impl<'a, T: MinefieldReader> MinefieldSolver<'a, T> {
    pub fn new(minefield: impl Into<MaybeOwned<'a, T>>) -> Self {
        Self::with_max_complexity(minefield, Some(DEFAULT_MAX_COMPLEXITY))
    }

    pub fn with_max_complexity(
        minefield: impl Into<MaybeOwned<'a, T>>,
        max_complexity: Option<usize>,
    ) -> Self {
        let minefield = minefield.into();
        let field_count = minefield.field_count();
        let mines = minefield.mine_count();
        Self {
            minefield,
            max_complexity,
            fields: vec![Default::default(); field_count],
            adjacent_unrevealed: Default::default(),
            unflagged_mines_left: mines,
            reveals_left: field_count - mines,
        }
    }

    pub fn fully_flagged_and_revealed(&self) -> bool {
        self.unflagged_mines_left == 0 && self.reveals_left == 0
    }

    pub fn reveal(&mut self, field_index: usize) -> Result<(), RevealError> {
        self.reveal_multiple([field_index].into())
    }

    pub fn reveal_multiple(&mut self, mut field_indices: BTreeSet<usize>) -> Result<(), RevealError> {
        while let Some(&field_index) = field_indices.iter().next() {
            if self.minefield.is_mine(field_index) {
                return Err(RevealError::Boom);
            } else if self.fields[field_index] != Field::Unrevealed {
                return Err(RevealError::AlreadyRevealed);
            } else {
                field_indices.remove(&field_index);
                self.reveals_left -= 1;

                let adjacent_fields = self.minefield.adjacent_fields(field_index);

                let adjacent_mines = adjacent_fields
                    .iter()
                    .filter(|&&field_index| self.minefield.is_mine(field_index))
                    .count();
                self.fields[field_index] = Field::Revealed { adjacent_mines };

                self.adjacent_unrevealed.remove(&field_index);
                self.adjacent_unrevealed.extend(
                    adjacent_fields
                        .iter()
                        .filter(|&&field_index| self.fields[field_index] == Field::Unrevealed),
                );

                if adjacent_mines == 0 {
                    field_indices.extend(
                        adjacent_fields
                            .into_iter()
                            .filter(|&field_index| self.fields[field_index] == Field::Unrevealed),
                    );
                }
            }
        }
        Ok(())
    }

    pub fn flag(&mut self, field_index: usize) -> Result<(), FlagError> {
        if self.unflagged_mines_left == 0 {
            Err(FlagError::AllMinesFlagged)
        } else if self.fields[field_index] == Field::Flagged {
            Err(FlagError::AlreadyFlagged)
        } else {
            assert!(
                self.minefield.is_mine(field_index),
                "solver tried to flag a non-mine"
            );
            self.unflagged_mines_left -= 1;
            self.fields[field_index] = Field::Flagged;
            self.adjacent_unrevealed.remove(&field_index);
            Ok(())
        }
    }

    pub fn solve(&mut self) -> Result<(), SolveError> {
        while !self.fully_flagged_and_revealed() {
            self.solve_step()?;
        }
        Ok(())
    }

    pub fn solvable(mut self) -> bool {
        self.solve().is_ok()
    }

    pub fn solve_step(&mut self) -> Result<(), SolveError> {
        let solve_actions = self.next_solve_actions()?;

        self.reveal_multiple(solve_actions.reveal)
            .expect("solve tried to reveal an invalid field");

        for field_index in solve_actions.flag {
            self.flag(field_index)
                .expect("solve tried to flag an invalid field");
        }

        Ok(())
    }

    pub fn next_solve_actions(&self) -> Result<SolveActions, SolveError> {
        if let Some(actions) = self.flag_rest_if_no_reveals_left() {
            return Ok(actions);
        }

        if let Some(actions) = self.reveal_rest_if_no_mines_left() {
            return Ok(actions);
        }

        let adjacent_revealed_per_unrevealed = self
            .adjacent_unrevealed
            .iter()
            .map(|&field_index| {
                self.minefield
                    .adjacent_fields(field_index)
                    .into_iter()
                    .filter(|&field_index| {
                        matches!(self.fields[field_index], Field::Revealed { .. })
                    })
                    .collect::<BTreeSet<_>>()
            })
            .collect::<Vec<_>>();

        let adjacent_revealed = adjacent_revealed_per_unrevealed
            .iter()
            .flatten()
            .copied()
            .collect();

        let mut actions = self.trivial_solve_actions(&adjacent_revealed);

        // TODO: Look at possible mine placements only for a single revealed cell's neighbors.
        //       Aka, still use a powerset, but only around a single field.
        //       Instead of globally like the current complex_solve_actions function.

        let revealed_groups = group_overlapping(adjacent_revealed_per_unrevealed);

        let groups = revealed_groups.into_iter().map(|revealed_group| {
            let unrevealed_group = revealed_group
                .iter()
                .flat_map(|&field_index| {
                    self.minefield
                        .adjacent_fields(field_index)
                        .into_iter()
                        .filter(|&field_index| self.fields[field_index] == Field::Unrevealed)
                })
                .collect::<BTreeSet<_>>();
            (revealed_group, unrevealed_group)
        });

        for (revealed_group, unrevealed_group) in groups {
            if let Some(max_complexity) = self.max_complexity {
                let complexity = unrevealed_group.len();
                if complexity > max_complexity {
                    return if actions.is_empty() {
                        Err(SolveError::TooComplex)
                    } else {
                        Ok(actions)
                    };
                }
            }

            actions |= self.complex_solve_actions(&revealed_group, &unrevealed_group);
        }

        if actions.is_empty() {
            Err(SolveError::Unsolvable)
        } else {
            Ok(actions)
        }
    }

    fn flag_rest_if_no_reveals_left(&self) -> Option<SolveActions> {
        (self.reveals_left == 0).then(|| SolveActions {
            flag: self
                .fields
                .iter()
                .enumerate()
                .filter_map(|(field_index, &field)| {
                    (field == Field::Unrevealed).then_some(field_index)
                })
                .collect(),
            ..Default::default()
        })
    }

    fn reveal_rest_if_no_mines_left(&self) -> Option<SolveActions> {
        (self.unflagged_mines_left == 0).then(|| SolveActions {
            reveal: self
                .fields
                .iter()
                .enumerate()
                .filter_map(|(field_index, &field)| {
                    (field == Field::Unrevealed).then_some(field_index)
                })
                .collect(),
            ..Default::default()
        })
    }

    fn trivial_solve_actions(&self, adjacent_revealed: &BTreeSet<usize>) -> SolveActions {
        adjacent_revealed
            .iter()
            .fold(SolveActions::default(), |acc, &field_index| {
                acc | match self.fields[field_index] {
                    Field::Revealed { adjacent_mines } => {
                        let (flags, unrevealed) = self
                            .minefield
                            .adjacent_fields(field_index)
                            .into_iter()
                            .fold((0, 0), |(flags, unrevealed), field_index| {
                                match self.fields[field_index] {
                                    Field::Flagged => (flags + 1, unrevealed),
                                    Field::Unrevealed { .. } => (flags, unrevealed + 1),
                                    Field::Revealed { .. } => (flags, unrevealed),
                                }
                            });
                        if flags == adjacent_mines {
                            SolveActions {
                                reveal: self
                                    .minefield
                                    .adjacent_fields(field_index)
                                    .into_iter()
                                    .filter(|&field_index| {
                                        self.fields[field_index] == Field::Unrevealed
                                    })
                                    .collect(),
                                ..Default::default()
                            }
                        } else if flags + unrevealed == adjacent_mines {
                            SolveActions {
                                flag: self
                                    .minefield
                                    .adjacent_fields(field_index)
                                    .into_iter()
                                    .filter(|&field_index| {
                                        self.fields[field_index] == Field::Unrevealed
                                    })
                                    .collect(),
                                ..Default::default()
                            }
                        } else {
                            Default::default()
                        }
                    }
                    Field::Unrevealed | Field::Flagged => panic!("field should be revealed"),
                }
            })
    }

    fn complex_solve_actions(
        &self,
        adjacent_revealed: &BTreeSet<usize>,
        adjacent_unrevealed: &BTreeSet<usize>,
    ) -> SolveActions {
        let valid_mine_placements = adjacent_unrevealed
            .iter()
            .copied()
            .powerset()
            .filter(|mine_placement| {
                self.is_mine_placement_valid(
                    &mine_placement.iter().copied().collect(),
                    adjacent_revealed,
                )
            })
            .map(|mine_placement| mine_placement.into_iter().collect::<BTreeSet<_>>())
            .collect::<BTreeSet<_>>();

        adjacent_unrevealed
            .iter()
            .fold(SolveActions::default(), move |mut acc, &field_index| {
                let count = valid_mine_placements
                    .iter()
                    .filter(|mine_placement| mine_placement.contains(&field_index))
                    .count();
                if count == 0 {
                    acc.reveal.insert(field_index);
                } else if count == valid_mine_placements.len() {
                    acc.flag.insert(field_index);
                }
                acc
            })
    }

    fn is_mine_placement_valid(
        &self,
        mines: &BTreeSet<usize>,
        adjacent_revealed: &BTreeSet<usize>,
    ) -> bool {
        if mines.len() > self.unflagged_mines_left {
            return false;
        }

        adjacent_revealed.iter().all(|&field_index| {
            let expected_mines = match self.fields[field_index] {
                Field::Revealed { adjacent_mines } => adjacent_mines,
                Field::Unrevealed | Field::Flagged => {
                    panic!("field should be revealed");
                }
            };

            let (actual_mines, unrevealed) = self
                .minefield
                .adjacent_fields(field_index)
                .into_iter()
                .fold((0, 0), |(actual_mines, unrevealed), field_index| {
                    if mines.contains(&field_index) {
                        (actual_mines + 1, unrevealed)
                    } else if self.adjacent_unrevealed.contains(&field_index) {
                        (actual_mines, unrevealed)
                    } else {
                        match self.fields[field_index] {
                            Field::Unrevealed => (actual_mines, unrevealed + 1),
                            Field::Revealed { .. } => (actual_mines, unrevealed),
                            Field::Flagged => (actual_mines + 1, unrevealed),
                        }
                    }
                });

            (actual_mines..=(actual_mines + unrevealed)).contains(&expected_mines)
        })
    }
}

fn group_overlapping(mut small_revealed_groups: Vec<BTreeSet<usize>>) -> Vec<BTreeSet<usize>> {
    let mut revealed_groups = Vec::new();
    while let Some(mut revealed_group) = small_revealed_groups.pop() {
        revealed_groups.push(loop {
            // TODO: Try using drain_filter once stabilized
            let mut overlap = false;
            for i in (0..small_revealed_groups.len()).rev() {
                if !small_revealed_groups[i].is_disjoint(&revealed_group) {
                    revealed_group.extend(small_revealed_groups.swap_remove(i));
                    overlap = true;
                }
            }
            if !overlap {
                break revealed_group;
            }
        });
    }
    revealed_groups
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

impl<T: MinefieldReader> std::fmt::Display for MinefieldSolver<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (field_index, &field) in self.fields.iter().enumerate() {
            match field {
                Field::Unrevealed => {
                    if self.adjacent_unrevealed.contains(&field_index) {
                        write!(f, "\x1B[33m?\x1B[0m ")
                    } else {
                        write!(f, "  ")
                    }
                }
                Field::Revealed { adjacent_mines } => {
                    if adjacent_mines == 0 {
                        write!(f, "  ")
                    } else {
                        write!(f, "{}{adjacent_mines}\x1B[0m ", color_code(adjacent_mines),)
                    }
                }
                Field::Flagged => write!(f, "🚩"),
            }?;

            if (field_index + 1) % 9 == 0 {
                writeln!(f)?;
            }
        }

        writeln!(
            f,
            "mines left: {} unrevealed: {}",
            self.unflagged_mines_left, self.reveals_left
        )?;
        Ok(())
    }
}
