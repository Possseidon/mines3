use bevy::{prelude::*, render::camera::ScalingMode, sprite::MaterialMesh2dBundle};
use minefield::{
    generator::GenerateRandomly,
    minefield::{AdjacentFields, MinefieldReader},
    minefields::minefield2d::{Minefield2D, UVec2},
};

fn main() {
    App::new()
        .add_plugins(DefaultPlugins)
        .insert_resource(ClearColor(Color::BLACK))
        .add_startup_system(setup_camera)
        .add_startup_system(setup_minefield)
        .run();
}

#[derive(Component)]
struct Minefield(Minefield2D);

#[derive(Component)]
struct Field {
    index: usize,
    revealed: bool,
}

fn setup_camera(
    mut commands: Commands,
    mut meshes: ResMut<Assets<Mesh>>,
    mut materials: ResMut<Assets<ColorMaterial>>,
    asset_server: Res<AssetServer>,
) {
    commands.spawn(Camera2dBundle {
        projection: OrthographicProjection {
            scaling_mode: ScalingMode::AutoMin {
                min_width: 1.0,
                min_height: 1.0,
            },
            ..default()
        },
        ..default()
    });
}

fn setup_minefield() {
    let minefield = Minefield2D::new(UVec2::new(9, 9)).generate(10, 40);

    let UVec2 {
        x: width,
        y: height,
    } = minefield.size();

    commands
        .spawn(SpatialBundle::default())
        .with_children(|parent| {
            for field_index in 0..minefield.field_count() {
                let UVec2 { x, y } = minefield.field_index_to_coord(field_index).unwrap();
                let x = (x as f32 + 0.5 - width as f32 / 2.0) / 10.0;
                let y = (y as f32 + 0.5 - height as f32 / 2.0) / 10.0;
                let mut field = parent.spawn((
                    Field {
                        index: field_index,
                        revealed: false,
                    },
                    MaterialMesh2dBundle {
                        mesh: meshes.add(Mesh::from(shape::Quad::default())).into(),
                        transform: Transform::from_xyz(x, y, 0.0).with_scale(Vec3::splat(0.09)),
                        material: materials.add(ColorMaterial::from(
                            if MinefieldReader::is_mine(&minefield, field_index) {
                                Color::rgb(0.75, 0.25, 0.25)
                            } else {
                                Color::rgb(0.25, 0.25, 0.75)
                            },
                        )),
                        ..default()
                    },
                ));

                if !MinefieldReader::is_mine(&minefield, field_index) {
                    field.with_children(|parent| {
                        let mine_count = minefield
                            .adjacent_fields(field_index)
                            .into_iter()
                            .filter(|&field_index| {
                                MinefieldReader::is_mine(&minefield, field_index)
                            })
                            .count();

                        parent.spawn(Text2dBundle {
                            text: Text {
                                sections: vec![TextSection::new(
                                    format!("{mine_count}"),
                                    TextStyle {
                                        // font: asset_server.load("fonts/FiraSans-Bold.ttf"),
                                        font_size: 200.0,
                                        color: Color::WHITE,
                                    },
                                )],
                                alignment: TextAlignment::Center,
                                ..default()
                            },
                            transform: Transform::default().with_scale(Vec3::splat(1.0 / 200.0)),
                            ..default()
                        });
                    });
                }
            }
        })
        .insert(Minefield(minefield));
}
