use bitvec::{bitbox, boxed::BitBox, order::Lsb0, slice::BitSlice};

#[derive(Clone, Debug, PartialEq, Eq)]
struct BinaryEquationResult {
    /// Columns that were solved to be `0`.
    zeros: BitBox,
    /// Columns that were solved to be `1`.
    ones: BitBox,
}

impl BinaryEquationResult {
    fn new(cols: usize) -> Self {
        Self {
            zeros: bitbox![0; cols],
            ones: bitbox![0; cols],
        }
    }
}

fn solve(mut equations: Vec<Equation>, scratch: &mut BitSlice) -> BinaryEquationResult {
    let cols = equations[0].lhs.len();
    let mut result = BinaryEquationResult::new(cols);

    loop {
        let mut any_new_ones = false;
        let mut any_new_zeros = false;
        equations.retain(|equation| {
            if equation.rhs == 0 {
                result.zeros |= &equation.lhs;
                any_new_zeros = true;
                false
            } else if equation.rhs == equation.lhs.count_ones() {
                result.ones |= &equation.lhs;
                any_new_ones = true;
                false
            } else {
                true
            }
        });

        if any_new_ones {
            for equation in &mut equations {
                scratch.copy_from_bitslice(&equation.lhs);
                *scratch &= &result.ones;
                equation.rhs = equation
                    .rhs
                    .checked_sub(scratch.count_ones())
                    .expect("invalid equation");
                equation.lhs ^= &*scratch;
            }
        }

        if any_new_zeros {
            for equation in &mut equations {
                scratch.copy_from_bitslice(&equation.lhs);
                *scratch &= &result.zeros;
                equation.lhs ^= &*scratch;
            }
        }

        equations.sort_by_key(|equation| equation.lhs.count_ones());

        let mut any_subsets = false;
        let mut rest = &mut equations[..];
        while let [current, tail @ ..] = rest {
            rest = tail;
            for other in rest.iter_mut() {
                any_subsets |= check_subset(current, other, scratch);
            }
        }

        if !any_subsets {
            break;
        }
    }

    result
}

struct Equation {
    // TODO: Store all equations in one big Vec<usize>, I can still BitSlice into it
    //       One usize for count, however many usize are required to store lhs bits for that row
    //       Column length has to be stored separately
    lhs: BitBox,
    rhs: usize,
}

impl Equation {
    fn new(lhs: BitBox, rhs: usize) -> Self {
        Self { lhs, rhs }
    }
}

fn check_subset(subset: &Equation, superset: &mut Equation, scratch: &mut BitSlice) -> bool {
    scratch.copy_from_bitslice(&superset.lhs);
    *scratch |= &subset.lhs;
    let is_subset = scratch == superset.lhs;
    if is_subset {
        superset.lhs ^= &subset.lhs;
        superset.rhs = superset.rhs.checked_sub(subset.rhs).expect("invalid input");
    }
    is_subset
}

fn main() {
    let mines = solve(
        vec![
            Equation::new(bitbox![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], 1),
            Equation::new(bitbox![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 1),
        ],
        &mut bitbox![0; 12],
    );
    println!("reveal: {}", mines.zeros);
    println!("flag:   {}", mines.ones);
}
