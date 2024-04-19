/// Solves generic minesweeper games.
#[derive(Debug)]
pub struct MinefieldSolver<T: Playfield, P: PlayerOnce> {
    state: GameState<T, P>,
}

impl<T: Playfield, P: PlayerOnce> MinefieldSolver<T, P> {
    pub fn new(state: GameState<T, P>) -> Self {
        Self {
            state,
            edge: todo!("find all revealed fields that count at least one non-revealed field"),
        }
    }

    /// Reveals a single field.
    ///
    /// The main use-case for this is to reveal the initial field that was clicked by the user
    /// before starting the solver.
    pub fn reveal(&mut self, field_index: usize) -> Result<(), RevealError> {
        self.reveal_many([field_index].into())
    }

    /// Reveals all of the given fields, including adjacent fields that are know to not be mines.
    pub fn reveal_many(&mut self, mut field_indices: BTreeSet<usize>) -> Result<(), RevealError> {
        while let Some(field_index) = field_indices.pop_first() {
            if self.deduced[field_index] {
                return Err(RevealError::Duplicate);
            }

            let counted_fields = self.playfield.counted_fields(field_index);

            let adjacent_mines = counted_fields
                .iter()
                .filter(|&&field_index| self.minefield.is_mine(field_index))
                .count();

            self.deduced.set(field_index, true);
            self.reveals_left -= 1;

            self.deduce_from.remove(&field_index);
            self.deduce_from.extend(
                counted_fields
                    .iter()
                    .filter(|&&field_index| !self.deduced[field_index]),
            );

            if adjacent_mines == 0 {
                field_indices.extend(
                    counted_fields
                        .into_iter()
                        .filter(|&field_index| !self.deduced[field_index]),
                );
            }
        }
        Ok(())
    }

    /// Attempts to solve the board, returning the required complexity to solve.
    pub fn solve(&mut self, max_difficulty: Difficulty) -> Result<Difficulty, SolveError> {
        let mut difficulty = Difficulty::Trivial;
        while !self.fully_flagged_and_revealed() {
            difficulty = difficulty.max(self.solve_step(max_difficulty)?.difficulty());
        }
        Ok(difficulty)
    }

    /// Returns `true` if all fields got either flagged or revealed.
    pub fn fully_flagged_and_revealed(&self) -> bool {
        self.unflagged_mines_left == 0 && self.reveals_left == 0
    }

    /// Applies reveals/flags returned by [`Self::next_solve_actions`].
    ///
    /// # Panics
    ///
    /// Panics if invalid fields are revealed. This should not happen as long as [`MinefieldReader`]
    /// is implemented properly.
    pub fn solve_step(&mut self, max_difficulty: Difficulty) -> Result<SolveStepInfo, SolveError> {
        let (solve_actions, info) = self.next_solve_actions(max_difficulty)?;

        self.reveal_many(solve_actions.reveal).unwrap();

        for field_index in solve_actions.flag {
            self.flag(field_index).unwrap();
        }

        Ok(info)
    }

    /// Uses a bunch of heuristics to find the next [`SolveActions`], i.e. reveals/flags to perform.
    ///
    /// The current implementation uses the following series of heuristics:
    ///
    /// 1. [`Self::flag_rest_if_no_reveals_left`]
    /// 2. [`Self::reveal_rest_if_no_mines_left`]
    /// 3. [`Self::trivial_solve_actions`]
    /// 4. [`Self::complex_solve_actions`]
    ///
    /// Since the last step can quickly get out of hand in terms of complexity, it will only try to
    /// solve groups of up to [`Self::max_complexity`] fields.
    pub fn next_solve_actions(
        &self,
        max_difficulty: Difficulty,
    ) -> Result<(SolveActions, Difficulty), SolveError> {
    }

    /// Marks the given field as flagged.
    pub fn flag(&mut self, field_index: usize) -> Result<(), FlagError> {
        if self.deduced[field_index] {
            Err(FlagError::Duplicate)
        } else if !self.minefield.is_mine(field_index) {
            Err(FlagError::NotMine)
        } else {
            assert!(self.unflagged_mines_left > 0);
            self.unflagged_mines_left -= 1;
            self.deduced.set(field_index, true);
            self.deduce_from.remove(&field_index);
            Ok(())
        }
    }

    /// Returns [`SolveActions`] to flag all remaining fields if there are only mines left.
    fn flag_rest_if_no_reveals_left(&self) -> Option<SolveActions> {
        (self.reveals_left == 0).then(|| SolveActions {
            flag: self.deduced.iter_zeros().collect(),
            ..Default::default()
        })
    }

    // TODO: Does this make sense?
    /// Returns [`SolveActions`] to reveal all remaining fields if there are no more mines left.
    fn reveal_rest_if_no_mines_left(&self) -> Option<SolveActions> {
        (self.unflagged_mines_left == 0).then(|| SolveActions {
            reveal: self.deduced.iter_zeros().collect(),
            ..Default::default()
        })
    }

    /// Returns [`SolveActions`] for trivial fields.
    ///
    /// A field is considered "trivial" if its unrevealed adjacent fields are either all mines or
    /// contains no more mines.
    fn trivial_solve_actions(&self, adjacent_revealed: &BTreeSet<usize>) -> SolveActions {
        let mut solve_actions = SolveActions::default();
        for &field_index in adjacent_revealed {
            let (flags, unrevealed) = self
                .minefield
                .adjacent_fields(field_index)
                .into_iter()
                .fold((0, 0), |(flags, unrevealed), field_index| {
                    if !self.deduced[field_index] {
                        (flags, unrevealed + 1)
                    } else if self.minefield.is_mine(field_index) {
                        (flags + 1, unrevealed)
                    } else {
                        (flags, unrevealed)
                    }
                });

            let adjacent_mines = self.mine_counts[field_index];
            if flags == adjacent_mines {
                solve_actions.merge(SolveActions {
                    reveal: self
                        .minefield
                        .adjacent_fields(field_index)
                        .into_iter()
                        .filter(|&field_index| !self.deduced[field_index])
                        .collect(),
                    ..Default::default()
                });
            } else if flags + unrevealed == adjacent_mines {
                solve_actions.merge(SolveActions {
                    flag: self
                        .minefield
                        .adjacent_fields(field_index)
                        .into_iter()
                        .filter(|&field_index| !self.deduced[field_index])
                        .collect(),
                    ..Default::default()
                });
            }
        }
        solve_actions
    }

    /// Returns _all_ [`SolveActions`].
    ///
    /// This is implemented by trying all valid mine placements.
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

    /// Checks if the given set of mines would be valid when tested against `adjacent_revealed`.
    ///
    /// "Valid" means, the number of adjacent mines does not conflict with the placed mines.
    fn is_mine_placement_valid(
        &self,
        mines: &BTreeSet<usize>,
        adjacent_revealed: &BTreeSet<usize>,
    ) -> bool {
        if mines.len() > self.unflagged_mines_left {
            return false;
        }

        adjacent_revealed.iter().all(|&field_index| {
            let expected_mines = self.mine_counts[field_index];

            let (actual_mines, unrevealed) = self
                .minefield
                .adjacent_fields(field_index)
                .into_iter()
                .fold((0, 0), |(actual_mines, unrevealed), field_index| {
                    if mines.contains(&field_index) {
                        (actual_mines + 1, unrevealed)
                    } else if self.deduce_from.contains(&field_index) {
                        (actual_mines, unrevealed)
                    } else if !self.deduced[field_index] {
                        (actual_mines, unrevealed + 1)
                    } else if self.minefield.is_mine(field_index) {
                        (actual_mines + 1, unrevealed)
                    } else {
                        (actual_mines, unrevealed)
                    }
                });

            (actual_mines..=actual_mines + unrevealed).contains(&expected_mines)
        })
    }
}

/// A set of fields to reveal or flag.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct SolveActions {
    reveal: BTreeSet<usize>,
    flag: BTreeSet<usize>,
}

impl SolveActions {
    /// Whether this set contains neither reveals nor flags.
    fn is_empty(&self) -> bool {
        self.reveal.is_empty() && self.flag.is_empty()
    }

    /// Extends this set by another one.
    fn merge(&mut self, other: Self) {
        self.reveal.extend(other.reveal);
        self.flag.extend(other.flag);
    }
}

#[derive(Debug, Error)]
pub enum RevealError {
    #[error("field already revealed or flagged")]
    Duplicate,
    #[error("mine revealed")]
    Mine,
}

#[derive(Debug, Error)]
pub enum FlagError {
    #[error("field already revealed or flagged")]
    Duplicate,
    #[error("the flagged field is not a mine")]
    NotMine,
}

/// Finds overlapping sets of fields and merges them into a single set.
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

impl<T: Playfield> std::fmt::Display for MinefieldSolver<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (field_index, processed) in self.processed.iter().enumerate() {
            if !*processed {
                if self.adjacent_unrevealed.contains(&field_index) {
                    write!(f, "\x1B[33m?\x1B[0m ")?;
                } else {
                    write!(f, "  ")?;
                }
            } else if self.minefield.is_mine(field_index) {
                write!(f, "🚩")?;
            } else {
                let adjacent_mines = self.adjacent_mines[field_index];
                if adjacent_mines == 0 {
                    write!(f, "  ")?;
                } else {
                    write!(f, "{}{adjacent_mines}\x1B[0m ", color_code(adjacent_mines))?;
                }
            }

            if (field_index + 1) % 30 == 0 {
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
