use std::mem::size_of;

use bitvec::{order::Lsb0, vec::BitVec, view::BitView};
use itertools::zip_eq;

/// An equation where the lhs is fully binary and the rhs holds positive integers.
///
/// E.g. the following can be used to solve for `a`, `b` and `c`.
///
/// ```txt
/// a * 1 + b * 1 + c * 0 = 1
/// a * 1 + b * 1 + c * 1 = 2
/// a * 0 + b * 1 + c * 1 = 1
/// ```
///
/// This example would result in: `a = 1`, `b = 0` and `c = 1`
///
/// In the context of a minefield, `rhs` contains the count on a relevant field, `a` to `c` would
/// represent all relevant counted fields and the constants being `1` indicates that the relevant
/// field of that row is connected to that counted field.
///
/// The example above as a small classic Minesweeper grid could look like so:
///
/// ```txt
/// +-----+
/// |1 2 1|
/// |a b c|
/// +-----+
/// ```
///
/// Note how the right `1` is _not_ connected to `a` and therefore `0` in `lhs`.
pub(crate) struct BinEq {
    /// The number of columns in `lhs`.
    ///
    /// I.e. the number of bits per row in [`Self::equations`].
    cols: usize,
    /// Contains a set of equations.
    ///
    /// Equations are stored as follows:
    ///
    /// 1. One [`usize`] for the rhs of the equation.
    /// 2. Enough [`usize`]s to store [`Self::cols`] bits for the lhs of the equation.
    ///
    /// Repeated for each row.
    equations: Vec<usize>,
}

impl BinEq {
    pub(crate) fn solve(&mut self, result: &mut BinEqResult) {
        result.zeros.resize(self.cols, false);
        result.zeros.fill(false);
        result.ones.resize(self.cols, false);
        result.ones.fill(false);

        loop {
            let mut any_new_ones = false;
            let mut any_new_zeros = false;

            let width = 1 + self.cols.div_ceil(size_of::<usize>());
            for index in (0..self.equations.len() / width).rev() {
                let rhs_index = index * width;
                let lhs_start = rhs_index + 1;
                let lhs_end = rhs_index + width;
                let view_bits = self.equations[lhs_start..lhs_end].view_bits::<Lsb0>();
                if self.equations[index * width] == 0 {
                    result.zeros |= view_bits;
                    self.equations.drain(rhs_index..lhs_end);
                    any_new_zeros = true;
                } else if self.equations[index * width] == view_bits.count_ones() {
                    result.ones |= view_bits;
                    self.equations.drain(rhs_index..lhs_end);
                    any_new_ones = true;
                }
            }

            if any_new_zeros {
                for equation in self.equations.chunks_mut(width) {
                    for (lhs, &zeros) in zip_eq(&mut equation[1..], result.zeros.as_raw_slice()) {
                        *lhs &= !zeros;
                    }
                }
            }

            if any_new_ones {
                for equation in self.equations.chunks_mut(width) {
                    let (rhs, lhs) = equation.split_first_mut().unwrap();
                    for (lhs, &ones) in zip_eq(lhs, result.ones.as_raw_slice()) {
                        *rhs -= usize::try_from((*lhs & ones).count_ones()).unwrap();
                        *lhs &= !ones;
                    }
                }
            }

            let mut any_subset = false;
            let mut rest = &mut self.equations[..];
            while let ([rhs, lhs @ ..], tail) = rest.split_at_mut(width) {
                rest = tail;
                for other in rest.chunks_mut(width) {
                    let (other_rhs, other_lhs) = other.split_first_mut().unwrap();
                    any_subset |= Self::check_subset(lhs, *rhs, other_lhs, other_rhs)
                        | Self::check_subset(other_lhs, *other_rhs, lhs, rhs);
                }
            }

            if !any_subset {
                break;
            }
        }
    }

    fn check_subset(
        subset_lhs: &[usize],
        subset_rhs: usize,
        superset_lhs: &mut [usize],
        superset_rhs: &mut usize,
    ) -> bool {
        let is_subset = zip_eq(subset_lhs, superset_lhs.iter())
            .all(|(&subset, &superset)| superset == subset | superset);
        if is_subset {
            for (superset, &subset) in zip_eq(superset_lhs, subset_lhs) {
                *superset ^= subset;
            }
            *superset_rhs = superset_rhs
                .checked_sub(subset_rhs)
                .expect("invalid equation");
        }
        is_subset
    }
}

/// Contains the result of a [`BinEq`].
///
/// The result actually has three and not just two states for each field, since it is usually not
/// possible to solve the entire equation. So some variables remain in an uncertain state.
#[derive(Default)]
pub(crate) struct BinEqResult {
    /// All variables that the equation could be resolved to contain a `0`.
    pub(crate) zeros: BitVec,
    /// All variables that the equation could be resolved to contain a `1`.
    pub(crate) ones: BitVec,
}

impl BinEqResult {
    pub(crate) fn new() -> Self {
        Default::default()
    }
}
