// TODO: Remove this, it's no longer relevant, GameState does the caching.

use std::num::NonZeroUsize;

use bitvec::boxed::BitBox;

use super::{CheckFlagResult, CheckResult, PlayerContinue, PlayerFlag, PlayerMineCount};

/// A `StaticPlayerCache` type cannot exist, since the cache cannot be generated upfront due to
/// [`Player::reveal`] being allowed to panic when called again after a mine was revealed.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StaticPlayerContinueCache {
    mine_count: Option<usize>,
    mines: BitBox,
    mine_counts: Vec<usize>,
}

impl StaticPlayerContinueCache {
    pub fn new(cached: &impl PlayerContinue, field_count: NonZeroUsize) -> Self {
        let (mines, mine_counts) = (0..field_count.get())
            .map(|field_index| {
                let result = cached.check(field_index);
                (result.is_mine(), result.count().unwrap_or(0))
            })
            .unzip();
        Self {
            mine_count: cached.mine_count(),
            mines,
            mine_counts,
        }
    }
}

impl PlayerMineCount for StaticPlayerContinueCache {
    fn mine_count(&self) -> Option<usize> {
        self.mine_count
    }
}

impl PlayerContinue for StaticPlayerContinueCache {
    fn check(&self, field_index: usize) -> CheckResult {
        if self.mines[field_index] {
            CheckResult::Mine
        } else {
            CheckResult::Free {
                count: self.mine_counts[field_index],
            }
        }
    }
}

struct StaticPlayerFlagCache {
    mine_count: Option<usize>,
    mines: BitBox,
    mine_counts: Vec<usize>,
}

impl StaticPlayerFlagCache {
    pub fn new(cached: &impl PlayerFlag, field_count: NonZeroUsize) -> Self {
        let (mines, mine_counts) = (0..field_count.get())
            .map(|field_index| {
                let result = cached.check_flag(field_index);
                (result.is_mine(), result.count())
            })
            .unzip();
        Self {
            mine_count: cached.mine_count(),
            mines,
            mine_counts,
        }
    }
}

impl PlayerMineCount for StaticPlayerFlagCache {
    fn mine_count(&self) -> Option<usize> {
        self.mine_count
    }
}

impl PlayerFlag for StaticPlayerFlagCache {
    fn check_flag(&self, field_index: usize) -> CheckFlagResult {
        let count = self.mine_counts[field_index];
        if self.mines[field_index] {
            CheckFlagResult::Mine { count }
        } else {
            CheckFlagResult::Free { count }
        }
    }
}

// TODO: IncrementalPlayerCache: Same as above but it caches everything up to that field; usable for dynamic minefields
// TODO: DynamicPlayerCache: Same as above but it caches only fields that get queried; usable for external minefields

// /// Caches the number of adjacent mines for each field.
// ///
// /// Caching is performed dynamically, which makes it possible to use this for dynamic playfields.
// ///
// /// Note, that it caches not only the fields that are explicitly queried, but everything before that
// /// as well. This simplifies the implementation, since it does not _also_ have to keep track of
// /// which fields were already cached and instead can just use the length of the list for that.
// ///
// /// Unlike [`FixedPlayerCache`], this does *not* cache the total number of mines.
// #[derive(Clone, Debug, Hash, PartialEq, Eq)]
// pub struct DynamicPlayerCache<T: Player> {
//     pub(crate) cached: T,
//     pub(crate) revealable: BitVec,
//     pub(crate) mine_counts: Vec<usize>,
// }

// impl<T: Player> DynamicPlayerCache<T> {
//     pub(crate) fn new(cached: T) -> Self {
//         Self {
//             cached,
//             revealable: Default::default(),
//             mine_counts: Default::default(),
//         }
//     }
// }

// impl<T: Player> Player for DynamicPlayerCache<T> {
//     fn mine_count(&self) -> Option<usize> {
//         self.cached.mine_count()
//     }

//     fn count_mines(&self, field_index: usize) -> Option<usize> {
//         for _ in self.revealable.len()..=field_index {
//             let count = self.cached.count_mines(field_index);
//             self.revealable.push(count.is_some());
//             self.mine_counts.push(count.unwrap_or(0));
//             return count;
//         }
//         self.revealable[field_index].then(|| self.mine_counts[field_index])
//     }
// }

// /// Caches the number of adjacent mines for each field.
// ///
// /// If possible, uses [`FixedPlayerCache`], otherwise [`DynamicPlayerCache`]. The decision basically
// /// boils down to whether the total number of fields is known up front.
// ///
// /// Note, that this has slight overhead over using the wrapped types directly, since it has to
// /// dispatch to the right one on every call.
// ///
// /// TODO: Compare performance against just using a helper function returning `&dyn MinefieldPlayer`
// #[derive(Clone, Debug, Hash, PartialEq, Eq)]
// pub enum PlayerCache<T: Player> {
//     Fixed(FixedPlayerCache),
//     Dynamic(DynamicPlayerCache<T>),
// }

// impl<T: Player> PlayerCache<T> {
//     pub(crate) fn new(cached: T, field_count: Option<NonZeroUsize>) -> Self {
//         if let Some(field_count) = field_count {
//             Self::Fixed(FixedPlayerCache::new(&cached, field_count))
//         } else {
//             Self::Dynamic(DynamicPlayerCache::new(cached))
//         }
//     }
// }

// impl<T: Player> Player for PlayerCache<T> {
//     fn mine_count(&self) -> Option<usize> {
//         match self {
//             Self::Fixed(cache) => cache.mine_count(),
//             Self::Dynamic(cache) => cache.mine_count(),
//         }
//     }

//     fn count_mines(&self, field_index: usize) -> Option<usize> {
//         match self {
//             Self::Fixed(cache) => cache.count_mines(field_index),
//             Self::Dynamic(cache) => cache.count_mines(field_index),
//         }
//     }
// }
