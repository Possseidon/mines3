use std::num::{NonZeroU128, NonZeroU64};

use rand::{
    distributions::{Distribution, Standard},
    seq::IteratorRandom,
    Rng, SeedableRng,
};
use rand_pcg::Pcg64Mcg;
use thiserror::Error;

use crate::{
    game_state::{Complexity, Difficulty, GameState, SolveError},
    mine_map::MineMap,
    minefield::{Minefield, MinefieldRules},
    playfield::Playfield,
};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct DifficultyRange {
    pub min: Difficulty,
    pub max: Difficulty,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Seed(pub NonZeroU64);

impl Distribution<Seed> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Seed {
        Seed(self.sample(rng))
    }
}

pub trait MinefieldGenerator {
    type Error;

    fn generate(
        &self,
        playfield: &impl Playfield,
        initial_field: usize,
        difficulty: DifficultyRange,
        seed: Seed,
    ) -> Result<(Difficulty, MineMap), Self::Error>;
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct RandomMinefield {
    pub mine_count: usize,
}

impl MinefieldGenerator for RandomMinefield {
    type Error = RandomMinefieldGenerationError;

    fn generate(
        &self,
        playfield: &impl Playfield,
        initial_field: usize,
        difficulty_range: DifficultyRange,
        seed: Seed,
    ) -> Result<(Difficulty, MineMap), Self::Error> {
        let mut rng = Pcg64Mcg::seed_from_u64(seed.0.get());

        let field_count = playfield.field_count().unwrap();
        let mut mines = MineMap::new(field_count);

        let mine_indices = (0..field_count.get())
            .choose_multiple(&mut rng, self.mine_count)
            .into_iter();

        for field_index in mine_indices {
            mines.place_mine(field_index);
        }

        if mines.is_mine(initial_field) {
            return Err(RandomMinefieldGenerationError::Unsolvable);
        }

        let player = Minefield {
            playfield,
            mines: &mines,
            rules: MinefieldRules {
                reveal_mines: false,
                mine_count_available: true,
            },
        };
        let mut game_state = GameState::new(player);

        game_state.click(initial_field, false);
        let difficulty = game_state
            .solve(difficulty_range.max)
            .map_err(|error| match error {
                SolveError::TooDifficult { complexity } => {
                    RandomMinefieldGenerationError::TooHard { complexity }
                }
                SolveError::TooComplex => RandomMinefieldGenerationError::TooComplex,
                SolveError::Unsolvable => RandomMinefieldGenerationError::Unsolvable,
            })?;

        if difficulty >= difficulty_range.min {
            Ok((difficulty, mines))
        } else {
            Err(RandomMinefieldGenerationError::TooEasy { difficulty })
        }
    }
}

#[derive(Debug, Error)]
pub enum RandomMinefieldGenerationError {
    #[error("randomly generated minefield is {difficulty:?} which is too easy")]
    TooEasy { difficulty: Difficulty },
    #[error("randomly generated minefield requires {complexity:?} or more which is too hard")]
    TooHard { complexity: Complexity },
    #[error("randomly generated minefield is too complex for the solver")]
    TooComplex,
    #[error("randomly generated minefield is unsolvable")]
    Unsolvable,
}

// pub struct IncrementalMinefield {
//     mine_count: usize,
//     initial_field: usize,
//     min_difficulty: Difficulty,
//     max_difficulty: Difficulty,
//     seed: u64,
// }

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
