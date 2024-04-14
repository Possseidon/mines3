use std::num::NonZeroU128;

use rand::{seq::IteratorRandom, thread_rng, Rng, SeedableRng};
use rand_pcg::Pcg64Mcg;
use thiserror::Error;

use crate::{
    playfield::Playfield,
    solver::{Complexity, Difficulty, MinefieldSolver, RevealError, SolveError},
};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct DifficultyRange {
    min: Difficulty,
    max: Difficulty,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Seed(NonZeroU128);

pub trait MinefieldGenerator {
    type Error;

    fn generate<T: Playfield>(
        &self,
        playfield: &T,
        initial_field: usize,
        difficulty: DifficultyRange,
        seed: Seed,
    ) -> Result<(Difficulty, MineMap), Self::Error>;
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct RandomMinefield {
    mine_count: usize,
}

impl MinefieldGenerator for RandomMinefield {
    type Error = RandomMinefieldGenerationError;

    fn generate<T: Playfield>(
        &self,
        minefield: &mut T,
        initial_field: usize,
        difficulty: DifficultyRange,
        seed: Seed,
    ) -> Result<Difficulty, Self::Error> {
        let rng = Pcg64Mcg::from_seed(seed.0.get().to_le_bytes());
        Pcg64Mcg::from_entropy();

        let values = (0..minefield.len().get())
            .choose_multiple(&mut thread_rng(), self.mine_count)
            .into_iter();

        for field_index in values {
            minefield.place_mine(field_index)
        }

        let mut solver = MinefieldSolver::new(minefield);

        solver.reveal(initial_field).map_err(|error| match error {
            RevealError::Duplicate => unreachable!(),
            RevealError::Mine => RandomMinefieldGenerationError::Unsolvable,
        })?;

        let difficulty = solver
            .solve(self.max_difficulty)
            .map_err(|error| match error {
                SolveError::Unsolvable => RandomMinefieldGenerationError::Unsolvable,
                SolveError::TooComplex {
                    complexity: required_complexity,
                } => RandomMinefieldGenerationError::TooHard(required_complexity),
            })?;

        if difficulty >= self.min_difficulty {
            Ok(difficulty)
        } else {
            Err(RandomMinefieldGenerationError::TooEasy(difficulty))
        }
    }
}

#[derive(Debug, Error)]
pub enum RandomMinefieldGenerationError {
    #[error("randomly generated minefield is {0:?} which is too easy")]
    TooEasy(Difficulty),
    #[error("randomly generated minefield requires {0:?} or more which is too hard")]
    TooHard(Complexity),
    #[error("randomly generated minefield is unsolvable")]
    Unsolvable,
}

pub struct IncrementalMinefield {
    mine_count: usize,
    initial_field: usize,
    min_difficulty: Difficulty,
    max_difficulty: Difficulty,
    seed: u64,
}

// impl MinefieldGenerator for GenerateIncrementally {
//     fn generate<T: Minefield>(&self, minefield: T) -> Result<T, T> {
//         let mut open_fields = (0..self.field_count()).collect::<Vec<_>>();

//         open_fields.swap_remove(initial_field);

//         for _ in 0..mine_count {
//             for retries in 0.. {
//                 let unused_fields = open_fields.len() - retries;
//                 if unused_fields == 0 {
//                     return None;
//                 }

//                 let mine_field = open_fields.remove(thread_rng().gen_range(0..unused_fields));
//                 self.place_mine(mine_field);

//                 let mut solver = MinefieldSolver::new(&self);
//                 solver
//                     .reveal(initial_field)
//                     .expect("initial field should be revealable");

//                 let result = &solver.solve(None);
//                 println!("{result:?}");
//                 if result.is_ok() {
//                     break;
//                 }

//                 self.remove_mine(mine_field);
//                 open_fields.push(mine_field);
//             }
//         }

//         Some(self)
//     }
// }

// TODO: Try combined approach
//  -> Generate multiple mines (or everything) at once with full history
//      Skip a lot of solving that likely passes anyway
//  -> Backtrack (possibly multiple) if necessary
//      Skip a lot of solving that likely fails anyway
