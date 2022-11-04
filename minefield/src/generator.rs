use rand::{seq::IteratorRandom, thread_rng, Rng};

use crate::{minefield::Minefield, solver::MinefieldSolver};

// TODO: Generation Settings as struct including Seed

pub trait GenerateRandomly: Minefield + Sized {
    fn generate(&self, mine_count: usize, initial_field: usize) -> Self
    where
        Self: Clone,
    {
        loop {
            if let Some(minefield) = self.clone().try_generate(mine_count, initial_field) {
                break minefield;
            }
        }
    }

    fn try_generate(mut self, mine_count: usize, initial_field: usize) -> Option<Self> {
        let values = (0..self.field_count())
            .choose_multiple(&mut thread_rng(), mine_count)
            .into_iter();

        for field_index in values {
            self.place_mine(field_index)
        }

        let mut solver = MinefieldSolver::<Self>::new(&self);
        solver.reveal(initial_field).ok()?;

        solver.solvable().then_some(self)
    }
}

impl<T: Minefield + Sized> GenerateRandomly for T {}

pub trait GenerateIncrementally: Minefield + Sized {
    fn generate(&self, mine_count: usize, initial_field: usize) -> Self
    where
        Self: Clone,
    {
        loop {
            if let Some(minefield) = self.clone().try_generate(mine_count, initial_field) {
                break minefield;
            }
        }
    }

    fn try_generate(mut self, mine_count: usize, initial_field: usize) -> Option<Self> {
        let mut open_fields = (0..self.field_count()).collect::<Vec<_>>();

        open_fields.swap_remove(initial_field);

        for _ in 0..mine_count {
            for retries in 0.. {
                let unused_fields = open_fields.len() - retries;
                if unused_fields == 0 {
                    return None;
                }

                let mine_field = open_fields.remove(thread_rng().gen_range(0..unused_fields));
                self.place_mine(mine_field);

                let mut solver = MinefieldSolver::<Self>::new(&self);
                solver
                    .reveal(initial_field)
                    .expect("initial field should be revealable");
                if solver.solvable() {
                    break;
                }

                self.remove_mine(mine_field);
                open_fields.push(mine_field);
            }
        }

        Some(self)
    }
}

impl<T: Minefield + Sized> GenerateIncrementally for T {}

/*

pub(crate) trait GenerationMinePlacer {}

pub(crate) struct GenerationPlacer {
    mine_count: usize,
    seed: u64,
}

impl GenerationPlacer {
    fn with_seed(mine_count: usize, seed: u64) -> Self {
        Self { mine_count, seed }
    }

    fn random_seed(mine_count: usize) -> Self {
        Self::with_seed(mine_count, random())
    }

    fn start(&self) -> GenerationPlaceContext {
        GenerationPlaceContext {
            placer: self,
            mines: Default::default(),
        }
    }
}

struct GenerationPlaceContext<'a> {
    placer: &'a GenerationPlacer,
    mines: Vec<usize>,
}

impl GenerationPlaceContext<'_> {
    fn try_place<T: MinefieldWriter>(&self, minefield: &mut T) -> Option<Placement> {
        Some(Placement {
            done: todo!(),
            mines: todo!(),
        })
    }
}

struct Placement {
    done: bool,
    mines: Vec<usize>,
}

impl Placement {
    fn revert<T: MinefieldWriter>(&self, minefield: &mut T) {
        todo!()
    }
}

#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct GenerationValidator {
    initial_field: usize,
    max_complexity: Option<usize>,
}

impl GenerationValidator {
    fn new(initial_field: usize) -> Self {
        Self {
            initial_field,
            max_complexity: Some(DEFAULT_MAX_COMPLEXITY),
        }
    }

    fn initial_field(&mut self, initial_field: usize) -> &mut Self {
        self.initial_field = initial_field;
        self
    }

    fn max_complexity(&mut self, max_complexity: Option<usize>) -> &mut Self {
        self.max_complexity = max_complexity;
        self
    }

    fn validate<T: MinefieldReader>(&self, minefield: &T) -> bool {
        let mut solver = MinefieldSolver::<T>::with_max_complexity(minefield, self.max_complexity);
        solver.reveal(self.initial_field).is_ok() && solver.solvable()
    }
}

pub(crate) struct GenerationSettings {
    pub(crate) mine_placer: GenerationPlacer,
    pub(crate) validator: GenerationValidator,
}

impl GenerationSettings {
    pub(crate) fn generate<T: Minefield + Clone>(&self, minefield: T) -> T {
        loop {
            if let Some(minefield) = self.try_generate(minefield.clone()) {
                break minefield;
            }
        }
    }

    pub(crate) fn try_generate<T: Minefield>(&self, mut minefield: T) -> Option<T> {
        loop {
            let context = self.mine_placer.start();
            loop {
                if let Some(placement) = context.try_place(&mut minefield) {
                    if self.validator.validate(&minefield) {
                        if placement.done {
                            return Some(minefield);
                        } else {
                            break;
                        }
                    } else {
                        placement.revert(&mut minefield);
                    }
                } else {
                    return None;
                }
            }
        }
    }
}

pub(crate) trait GenerateMinefield: Minefield + Sized {}

impl<T: Minefield + Sized> GenerateMinefield for T {}

*/

// TODO: Try combined approach
//  -> Generate multiple mines (or everything) at once with full history
//      Skip a lot of solving that likely passes anyway
//  -> Backtrack (possibly multiple) if necessary
//      Skip a lot of solving that likely fails anyway
