use std::collections::{BTreeMap, BTreeSet};

use bitvec::vec::BitVec;
use itertools::iproduct;

struct Vertex {
    x: f32,
    y: f32,
    z: f32,
}

struct Face {
    vertices: Vec<usize>,
}

struct Minefield3DMesh {
    vertices: Vec<Vertex>,
    faces: Vec<Face>,
}

impl Minefield3DMesh {
    fn generate_adjacency_lookup(&self, adjacency_rule: AdjacencyRule) -> Vec<BTreeSet<usize>> {
        match adjacency_rule {
            AdjacencyRule::Vertex => self
                .faces
                .iter()
                .map(|face| {
                    self.faces
                        .iter()
                        .enumerate()
                        .filter_map(|(field_index, maybe_adjacent)| {
                            face.vertices
                                .iter()
                                .any(|vertex| maybe_adjacent.vertices.contains(vertex))
                                .then_some(field_index)
                        })
                        .collect()
                })
                .collect(),
            AdjacencyRule::Edge => todo!(),
        }
    }

    fn cuboid(width: usize, height: usize, depth: usize) -> Self {
        let mut vertices = BTreeMap::new();
        let mut faces = Vec::new();

        let mut vertex_at = |x, y, z| {
            let i = vertices.len();
            *vertices.entry((x, y, z)).or_insert(i)
        };

        for (x1, y1) in iproduct!(0..(width - 1), 0..(height - 1)) {
            let x2 = x1 + 1;
            let y2 = y1 + 1;
            faces.push(Face {
                vertices: vec![
                    vertex_at(x1, y1, 0),
                    vertex_at(x2, y1, 0),
                    vertex_at(x2, y2, 0),
                    vertex_at(x1, y2, 0),
                ],
            });
        }

        let mut vertices = vertices.into_iter().collect::<Vec<_>>();
        vertices.sort_unstable_by_key(|(_, i)| *i);

        Self {
            vertices: vertices
                .into_iter()
                .map(|((x, y, z), _)| Vertex {
                    x: x as f32,
                    y: y as f32,
                    z: z as f32,
                })
                .collect(),
            faces,
        }
    }
}

/// How two faces must be connected in order to be treated as "adjacent".
enum AdjacencyRule {
    /// Only a single common vertex is enough got fields to be adjacent.
    ///
    /// This results in classic minesweeper behavior, where diagonals are also considered.
    Vertex,
    /// Two faces must have an entire edge in common in order to be treated as adjacent.
    ///
    /// For classic minesweeper, this would mean that diagonals must no longer be considered.
    Edge,
}

struct Minefield3D {
    mesh: Minefield3DMesh,
    mines: BitVec,
    adjacency_lookup: Vec<BTreeSet<usize>>,
}

impl Minefield3D {
    pub fn new(mesh: Minefield3DMesh) -> Self {
        let adjacency_lookup = mesh.generate_adjacency_lookup(AdjacencyRule::Vertex);
        Self {
            mesh,
            mines: Default::default(),
            adjacency_lookup,
        }
    }
}

impl PlayfieldGraph for Minefield3D {
    fn field_count(&self) -> usize {
        self.mines.len()
    }

    fn counted_fields(&self, field_index: usize) -> BTreeSet<usize> {
        self.adjacency_lookup[field_index].clone()
    }
}

impl MinefieldReader for Minefield3D {
    fn is_mine(&self, field_index: usize) -> bool {
        self.mines[field_index]
    }
}

impl MinefieldWriter for Minefield3D {
    fn set_mine(&mut self, field_index: usize, is_mine: bool) {
        self.mines.set(field_index, is_mine);
    }
}
