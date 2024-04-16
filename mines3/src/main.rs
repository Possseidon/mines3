use std::{io::stdin, num::NonZeroUsize};

use minefield::{
    game_state::{Complexity, Difficulty, GameState},
    generator::{DifficultyRange, MinefieldGenerator, RandomMinefield, Seed},
    minefield::{Minefield, MinefieldRules},
    playfield::grid::{Grid, GridSize},
};

fn main() {
    let playfield = Grid {
        size: GridSize {
            // width: NonZeroUsize::new(30).unwrap(),
            // height: NonZeroUsize::new(16).unwrap(),
            width: NonZeroUsize::new(9).unwrap(),
            height: NonZeroUsize::new(9).unwrap(),
        },
        count: Default::default(),
        wrap: Default::default(),
    };
    let initial_field = 42;
    let mut seed = 0;
    let mut okay = 0;
    let (difficulty, mines) = loop {
        seed += 1;

        let result = RandomMinefield { mine_count: 10 }.generate(
            &playfield,
            initial_field,
            DifficultyRange {
                min: Difficulty::Trivial,
                max: Difficulty::Complex(Complexity::new(2).unwrap()),
            },
            Seed(seed.try_into().unwrap()),
        );
        if let Ok(result) = result {
            okay += 1;
            let percentage = okay as f32 / seed as f32 * 100.0;
            println!("{seed}: {:?} {percentage}", result.0);
            continue;
            break result;
        }
        // println!("{seed}: {result:?}");
    };

    println!("Seed: {seed}");
    println!("Difficulty: {difficulty:?}");

    let minefield = Minefield {
        playfield,
        mines,
        rules: MinefieldRules {
            reveal_mines: false,
            mine_count_available: true,
        },
    };
    let mut game_state = GameState::new(minefield);
    game_state.click(initial_field, false);
    while !game_state.solved() {
        println!("{game_state}");
        game_state
            .apply_next_solve_actions(Difficulty::Trivial)
            .unwrap();
        stdin().read_line(&mut String::new()).unwrap();
    }
    println!("{game_state}");
}

// use bevy::prelude::*;
// use minefield::{
//     generator::MinefieldGenerator,
//     mine_map::MinefieldReader,
//     playfield::minefield2d::{Minefield2D, UVec2},
// };

// fn main() {
//     App::new()
//         .add_plugins(DefaultPlugins)
//         .insert_resource(ClearColor(Color::BLACK))
//         .add_systems(Startup, (setup_camera, setup_minefield))
//         .run();
// }

// #[derive(Component)]
// struct Minefield(Minefield2D);

// #[derive(Component)]
// struct Field {
//     index: usize,
//     revealed: bool,
// }

// fn setup_camera(mut commands: Commands) {
//     commands.spawn(Camera3dBundle::default());
// }

// fn setup_minefield(
//     mut commands: Commands,
//     mut meshes: ResMut<Assets<Mesh>>,
//     mut materials: ResMut<Assets<StandardMaterial>>,
// ) {
//     let minefield = Minefield2D::new(UVec2::new(90, 90));
//     // .generate(1000, 40);

//     let UVec2 {
//         x: width,
//         y: height,
//     } = minefield.size();

//     commands
//         .spawn(SpatialBundle::default())
//         .with_children(|parent| {
//             for field_index in 0..minefield.field_count() {
//                 let UVec2 { x, y } = minefield.field_index_to_coord(field_index).unwrap();
//                 let x = (x as f32 + 0.5 - width as f32 / 2.0);
//                 let y = (y as f32 + 0.5 - height as f32 / 2.0);
//                 let mut field = parent.spawn((
//                     Field {
//                         index: field_index,
//                         revealed: false,
//                     },
//                     MaterialMeshBundle {
//                         mesh: meshes.add(Rectangle::default()),
//                         transform: Transform::from_xyz(x, y, -150.0),
//                         material: materials.add(StandardMaterial::from(
//                             if MinefieldReader::is_mine(&minefield, field_index) {
//                                 Color::rgb(0.75, 0.25, 0.25)
//                             } else {
//                                 Color::rgb(0.25, 0.25, 0.75)
//                             },
//                         )),
//                         ..default()
//                     },
//                 ));

//                 if !MinefieldReader::is_mine(&minefield, field_index) {
//                     field.with_children(|parent| {
//                         let mine_count = minefield
//                             .adjacent_fields(field_index)
//                             .into_iter()
//                             .filter(|&field_index| {
//                                 MinefieldReader::is_mine(&minefield, field_index)
//                             })
//                             .count();
//                     });
//                 }
//             }
//         });
// }
