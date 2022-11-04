use minefield::{
    generator::GenerateIncrementally,
    minefields::minefield2d::{Minefield2D, Vec2},
    solver::MinefieldSolver,
};

fn main() {
    let minefield = Minefield2D::new(Vec2::new(9, 9)).generate(10, 40);

    let mut solver = MinefieldSolver::new(minefield);

    solver.reveal(40).unwrap();
    println!("{solver}");

    while !solver.fully_flagged_and_revealed() {
        solver.solve_step().unwrap();
        println!("{solver}");
    }
}
