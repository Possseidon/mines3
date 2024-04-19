mod bin_eq;

use std::iter::Filter;

use itertools::Itertools;
use thiserror::Error;

use crate::{game_state::GameState, player::Player, playfield::Playfield};

/// Can be used solve a minefield step by step.
///
/// Does not actually carry any state that is related to solving, however it can make sense to keep
/// this around to avoid having to reallocate buffers.
///
/// Does not implement any of the usual traits for that reason as well. There is no point in cloning
/// or comparing.
#[derive(Default)]
struct Solver {}

impl Solver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn solve(&mut self, game_state: &mut GameState<impl Player>) -> Result<(), Unsolvable> {
        todo!("apply solve steps until done")
    }

    pub fn solve_step(&mut self, game_state: &GameState<impl Player>) -> Result<(), Unsolvable> {
        let relevant_fields = RelevantField::gather(game_state);

        let counted_fields =
            RelevantField::merge_counted_fields(relevant_fields, self.counted_fields);

        Ok(())
    }
}

#[derive(Debug, Error)]
#[error("minefield is unsolvable")]
pub struct Unsolvable;

struct RelevantField {
    field_index: usize,
    remaining_mine_count: usize,
    counted_fields: Filter,
}

fn gather(game_state: &GameState<impl Player>, relevant_fields: &mut Vec<RelevantField>) {
    relevant_fields.clear();
    relevant_fields.extend(game_state.relevant().iter_ones().map(|field_index| {
        let flag_count = game_state
            .playfield()
            .counted_fields(field_index)
            .filter_map(|field_index| game_state.get(field_index))
            .filter(|field| field.is_flag())
            .count();
        let counted_fields = game_state
            .playfield()
            .counted_fields(field_index)
            .filter(|&field_index| !game_state.is_clicked(field_index));
        let shown_count = game_state
            .get(field_index)
            .expect("relevant fields should be revealed")
            .count()
            .expect("relevant fields should have a count");

        RelevantField {
            field_index,
            remaining_mine_count: shown_count - flag_count,
            counted_fields,
        }
    }));
}

// fn merge_counted_fields(relevant_fields: &mut Vec<Self>, counted_fields: &mut Vec<usize>) {
//     counted_fields.clear();
// }
