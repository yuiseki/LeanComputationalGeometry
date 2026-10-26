# LeanComputationalGeometry

Machine-checked computational geometry of the plane, in Lean 4 with Mathlib.

LeanComputationalGeometry formalises the predicates and constructions that
planar computational geometry is built from (orientation, segment
intersection, triangles, polygons, signed area) and proves them correct
against Mathlib's definitions of the plane, segments, convex hulls,
collinearity and affine independence. The library has no `sorry`, no `admit`
and no `axiom` of its own (see [Axioms and proofs](#axioms-and-proofs)).

It is the third of three sibling libraries that share one plane:

| Library | Responsibility |
| --- | --- |
| [LeanGeodesy](https://github.com/yuiseki/LeanGeodesy) | Earth, ellipsoid, geodesics, projections, CRS, tiles: bringing the Earth to the plane |
| LeanComputationalGeometry | orientation, segments, polygons, winding, triangulation, clipping: computing geometry in the plane |
| [LeanGeospatial](https://github.com/yuiseki/LeanGeospatial) | topology, RCC8, DE-9IM, SFA, GeoSPARQL: what follows logically from spatial relations |

LeanGeospatial does not compute geometry, and that stays so: segment
intersection, point-in-polygon, triangulation and the like belong here.
Planar computational geometry does not belong in LeanGeodesy either.

## Mathematical model

The plane is Mathlib's `EuclideanSpace ℝ (Fin 2)`.

```lean
abbrev Point2D := EuclideanSpace ℝ (Fin 2)
```

is a reducible abbreviation, not a new type, so `ComputationalGeometry.Point2D`,
`Geospatial.Point2D` and `Geodesy.E2` are the same type by `rfl`, and a point
from either sibling library is a point here without conversion.
`Point2D.x`, `Point2D.y` read coordinates and `Point2D.mk x y` builds a point.

| Notion | Definition |
| --- | --- |
| `cross u v` | `u.x * v.y - u.y * v.x` |
| `orient a b c` | `cross (b - a) (c - a)`, twice the signed area of the triangle `a b c` |
| `Segment` | two endpoints `p q`, possibly equal |
| `Segment.toSet` | Mathlib's `segment ℝ p q` |
| `Segment.relInterior` | Mathlib's `openSegment ℝ p q` |
| `Triangle` | three vertices `a b c` in order |
| `Triangle.toSet` | Mathlib's `convexHull ℝ {a, b, c}` |
| `RawPolygon` | `n` vertices `Fin n → Point2D`, joined cyclically by `finRotate` |
| `RawPolygon.IsSimple` | at least three vertices, no zero-length edge, consecutive edges meeting only at their vertex, other edges disjoint |
| `RawPolygon.signedArea2` | the shoelace sum `∑ cross (vertex i) (vertex (next i))` |
| `RawPolygon.IsCCW`, `IsCW` | `0 < signedArea2`, `signedArea2 < 0` |
| `RawPolygon.reverse` | the ring traversed the other way, its edges reversed (`reverse_edge`) |
| `edgeContribution p a b` | the edge `a → b` on the horizontal ray from `p` to the right: `+1` upward (`a.y ≤ p.y < b.y`, `orient a b p > 0`), `-1` downward (`b.y ≤ p.y < a.y`, `orient a b p < 0`), else `0` |
| `RawPolygon.windingNumber P p` | the sum of the edges' contributions |
| `RawPolygon.OnBoundary P p` | `p` is on some edge segment |
| `RawPolygon.region P` | `OnBoundary P p ∨ windingNumber P p ≠ 0`: the closed region, nonzero rule |
| `RawPolygon.openRegion P` | `¬ OnBoundary P p ∧ windingNumber P p ≠ 0`: the open region |
| `SimplePolygon.toRegion`, `toOpenRegion`, `boundary` | the above for a simple polygon |

Polygons are kept at three levels:

1. raw ring data (`RawPolygon`, built from a list by `RawPolygon.ofList`),
   about which nothing is assumed;
2. simple polygons (`RawPolygon.IsSimple`, the subtype `SimplePolygon`);
3. region semantics: the closed and open regions under the nonzero winding
   rule. They are defined for any ring, but this library takes them to mean
   the region a polygon bounds only for simple polygons
   (`SimplePolygon.toRegion`); for self-intersecting rings no claim is made.

The half-open intervals in `edgeContribution` count a crossing through a
vertex once. The winding number is not trusted on the boundary (an edge
whose line passes through `p` counts `0`), so the boundary is added to the
closed region and removed from the open one explicitly.

Decisions that a program would make are stated as propositions over the
reals (`CrossTest`, `IntersectTest`, `Triangle.ContainsTest`), separate from
the geometric notions they decide (`ProperlyIntersect`, `Intersects`,
membership in `Triangle.toSet`), and theorems connect the two. Constructions
are definitions with their properties as separate theorems: `crossingPoint`
is a formula, and `crossingPoint_mem_relInterior` says where it lies.

## What is proved

### Orientation

| Result | Theorem |
| --- | --- |
| `orient` is a 2×2 `Matrix.det` | `orient_eq_det` |
| it vanishes exactly on Mathlib's `Collinear ℝ {a, b, c}` | `orient_eq_zero_iff_collinear` |
| it is nonzero exactly on `AffineIndependent ℝ ![a, b, c]` | `orient_ne_zero_iff_affineIndependent` |
| swapping two arguments negates it | `orient_swap₁₂`, `orient_swap₂₃`, `orient_swap₁₃` |
| a cyclic permutation keeps it | `orient_rotate` |
| translation keeps it | `orient_add_vec` |
| it interpolates linearly along a line | `orient_lineMap`, `orient_lineMap₁` |
| it is the triangle's shoelace sum | `orient_eq_cross_sum` |

### Segments

Each theorem states the cases it covers.

| Result | Assumptions | Theorem |
| --- | --- | --- |
| The strict orientation test decides proper intersection (lines not parallel, open segments meet) | none | `properlyIntersect_iff_crossTest` |
| The crossing point lies inside both segments | `Straddles` | `crossingPoint_mem_relInterior`, `crossingPoint_comm` |
| The strict test decides intersection; touching cannot happen | `GeneralPosition` (no endpoint on the other segment's line) | `intersects_iff_crossTest_of_generalPosition` |
| The classical test (strict test, or an endpoint on the other segment) decides intersection | none: endpoint touching and collinear overlap included | `intersects_iff_intersectTest` |
| A point is on a segment exactly when it is collinear with the endpoints and each coordinate lies between theirs | none: degenerate segments included | `mem_toSet_iff` |

### Triangles

| Result | Theorem |
| --- | --- |
| The signed double area is the shoelace sum of the vertices | `Triangle.signedArea2_eq_cross_sum` |
| Nondegenerate means affinely independent, and not collinear | `Triangle.nondegenerate_iff_affineIndependent`, `Triangle.nondegenerate_iff_not_collinear` |
| Barycentric coordinates: the orientations against the edges sum to the area and weight the vertices to the point | `Triangle.orient_sum`, `Triangle.orient_smul_sum` |
| For a counterclockwise triangle, a point is in the closed triangle exactly when it is on the left of, or on, each edge | `Triangle.mem_toSet_iff_containsTest` |
| Two edges of a nondegenerate triangle meet only at their shared vertex | `Triangle.segment_inter_segment_eq` |
| For a counterclockwise triangle, a point is strictly inside, Mathlib's `interior` of the convex hull, exactly when every edge orientation is positive | `Triangle.mem_interior_toSet_iff` |
| ...on the boundary, Mathlib's `frontier`, exactly when it is in the triangle with some edge orientation zero | `Triangle.mem_frontier_toSet_iff` |
| ...which is being on one of the three edges | `Triangle.mem_frontier_toSet_iff_edges`, `Triangle.mem_segment_iff_of_isCCW` |

### Polygons

| Result | Theorem |
| --- | --- |
| A nondegenerate triangle is a simple polygon | `Triangle.isSimple_toPolygon` |
| The shoelace sum does not depend on translation or on the starting vertex | `RawPolygon.signedArea2_translate`, `RawPolygon.signedArea2_rotate` |
| For a triangle it is the orientation of the vertices | `Triangle.signedArea2_toPolygon` |
| Reversing the ring reverses its edges and negates the shoelace sum, so it swaps counterclockwise and clockwise | `RawPolygon.reverse_edge`, `RawPolygon.signedArea2_reverse`, `RawPolygon.isCCW_reverse_iff`, `RawPolygon.isCW_reverse_iff` |

### Winding numbers and regions

| Result | Theorem |
| --- | --- |
| Horizontal edges, and edges whose line passes through `p`, do not count | `edgeContribution_of_horizontal`, `edgeContribution_of_orient_eq_zero` |
| Edges at, above, below, or left of `p` do not count | `edgeContribution_of_below`, `edgeContribution_of_above`, `edgeContribution_of_right` |
| Upward and downward crossings count with opposite signs, and reversing an edge negates its count | `edgeContribution_of_up`, `edgeContribution_of_down`, `edgeContribution_swap` |
| The winding number does not depend on the starting vertex or on translation | `RawPolygon.windingNumber_rotate`, `RawPolygon.windingNumber_translate` |
| Reversing the ring negates it | `RawPolygon.windingNumber_reverse` |
| It vanishes below, above, or to the right of every vertex | `RawPolygon.windingNumber_eq_zero_of_below`, `_of_above`, `_of_right` |
| The regions do not depend on the starting vertex or the direction | `RawPolygon.region_rotate`, `RawPolygon.region_reverse`, `RawPolygon.openRegion_rotate`, `RawPolygon.openRegion_reverse` |
| Vertices and edge interiors are on the boundary; a point on one edge of a simple polygon is on no nonadjacent edge | `RawPolygon.onBoundary_vertex`, `RawPolygon.onBoundary_of_mem_relInterior`, `SimplePolygon.not_mem_edge_of_nonadjacent` |

The first end-to-end check of the region semantics: for a nondegenerate
triangle as a simple polygon, the winding region is the closed triangle and
the open winding region is its interior.

| Result | Theorem |
| --- | --- |
| `p ∈ (T.toSimplePolygon h).toRegion ↔ p ∈ T.toSet` | `Triangle.mem_toRegion_iff`, `Triangle.toRegion_eq` |
| `p ∈ (T.toSimplePolygon h).toOpenRegion ↔ p ∈ interior T.toSet` | `Triangle.mem_toOpenRegion_iff`, `Triangle.toOpenRegion_eq` |
| Off the boundary of a counterclockwise triangle, the winding number is nonzero exactly at the points strictly inside | `Triangle.winding3_ne_zero_iff` |

The proof splits on which vertices lie at or below the ray's height. If all
or none do, no edge counts. Otherwise a rotation of the triangle puts a vertex
alone on its side at `a`, the two edges at `a` are the only ones that can
count, and the y-coordinate of the barycentric formula,
`o_bc (a.y - p.y) + o_ca (b.y - p.y) + o_ab (c.y - p.y) = 0`, decides each
case. A clockwise triangle is handled through its reverse.

For general simple polygons, that `toRegion` is the closure of `toOpenRegion`
and `toOpenRegion` the interior of `toRegion` is the Jordan curve theorem for
polygons, not proved here.

### Examples

`LeanComputationalGeometry/Examples/Basic.lean` runs concrete coordinates
through the segment and triangle theorems: crossing diagonals, a corner where
two edges only touch, overlapping collinear segments, disjoint parallel
segments, a point in and a point out of a triangle, and the unit square's
shoelace sum. `LeanComputationalGeometry/Examples/Polygons.lean` checks a
point inside, outside and on the boundary of a triangle, the unit square and
a concave L-shaped hexagon (including a point in the notch, with winding
number `0`), and shows the reversed square winding `-1` around its centre
with the same region.

### On LeanGeospatial's shoelace

LeanGeospatial already has a small shoelace of its own (`cross`,
`signedArea2`, `polygonArea`, and the shoelace area of a rectangle). This
library implements signed area independently, because computing geometry is
its job and not LeanGeospatial's, and it does not depend on LeanGeospatial.
LeanGeospatial may later use this library as the canonical implementation;
that refactor is not part of this release, and the sibling libraries'
dependencies stay as they are until this API is stable.

## Trust boundary

Lean checks that every theorem follows from the definitions above and from
Mathlib. It does not check:

- that the definitions match what a particular GIS or graphics library
  computes. They follow the textbook definitions, stated over the reals;
- floating-point behaviour. The tests are propositions about real numbers,
  not executable code; robustness of a floating-point implementation of
  `orient` is outside the scope;
- external data: a ring that a file claims is simple is a `RawPolygon` until
  `IsSimple` is proved for it.

## Roadmap

Roughly in order:

1. orientation (done)
2. segment intersection (done, every case)
3. triangle predicates (done: closed, strict interior, boundary)
4. signed area and the shoelace formula (done: translation, rotation,
   reversal)
5. simple polygons (the predicate exists; more structure next)
6. winding number and point-in-polygon, and with them region semantics
   (done: winding numbers, boundary, closed and open regions, and the
   triangle case end to end; the general Jordan curve theorem for polygons
   is not attempted)
7. ears
8. ear clipping triangulation
9. triangulation correctness
10. polygons with holes
11. clipping
12. convex hull

For ear clipping the goal is, for a simple polygon as input and triangles as
output, theorems that

- the output triangles are built from input vertices;
- their interiors do not overlap;
- together they cover the polygon's interior exactly;
- there are `n - 2` of them;
- the algorithm terminates.

The target is the classical algorithm's correctness. Mapbox Earcut's
specifics (z-order hashing, hole elimination, fallbacks for invalid input)
are out of scope at this stage.

The ear predicate can already be stated with the present API. For a
counterclockwise simple polygon, with `T i` the triangle
`⟨P.vertex (P.prev i), P.vertex i, P.vertex (P.next i)⟩`:

```lean
def IsEar (P : SimplePolygon) (i : Fin P.1.n) : Prop :=
  (T i).IsCCW ∧
  (∀ j, j ≠ P.1.prev i → j ≠ i → j ≠ P.1.next i → ¬ (T i).StrictContainsTest (P.1.vertex j)) ∧
  (T i).toSet ⊆ P.toRegion
```

It is not defined yet: whether the third clause follows from the first two
for a simple polygon is the first theorem of the ear step, and it needs more
of the region semantics than the triangle case.

The winding number is the common ground of two ways of drawing a polygon:

```
SimplePolygon
    │
    ├── winding number / nonzero rule
    │      → stencil fill (Gint-style rendering)
    │
    └── ear clipping
           → triangle mesh (Earcut-style rendering)
```

A stencil-buffer fill colours a pixel by its winding number; a triangle mesh
colours it by the triangle containing it. Both are correct when they agree
with `SimplePolygon.toRegion`, which is what this library is building toward.
This is motivation only: no rendering code is a dependency or is ported.

A certificate verifier is a parallel goal: an external triangulator (Earcut
or any other) produces candidate triangle indices, and a Lean-verified checker
decides whether they form a valid triangulation of the input. A fast
implementation then need not be reimplemented in Lean for its output to be
trusted, which is where this meets practical GIS and graphics.

## Build

```
lake exe cache get
lake build
```

Lean `v4.34.0`, Mathlib `v4.34.0`, the same as LeanGeodesy and LeanGeospatial.
`lake build` must finish with no errors and no warnings.

`scripts/joint_check.sh` checks that the three libraries import together on
one plane. With the three repositories side by side:

```
scripts/joint_check.sh ../LeanGeodesy ../LeanGeospatial . /tmp/joint
```

## Axioms and proofs

`LeanComputationalGeometry/Axioms.lean` pins the main theorems to Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`, which come in
through Mathlib's real numbers) with `#guard_msgs`, so adding an axiom or
leaving a proof unfinished makes `lake build` fail. CI also rejects any
`sorry`, `admit` or `axiom` in the sources, checks that the library does not
import its examples, and runs the joint check against the sibling libraries.

## Repository layout

| File | Contents |
| --- | --- |
| `LeanComputationalGeometry/Point.lean` | `Point2D`, coordinates |
| `LeanComputationalGeometry/Orientation.lean` | `cross`, `orient`, determinant, collinearity, affine independence |
| `LeanComputationalGeometry/Segment.lean` | segments, intersection notions and tests, their correctness |
| `LeanComputationalGeometry/Triangle.lean` | triangles, signed area, barycentric coordinates, membership |
| `LeanComputationalGeometry/Polygon/Basic.lean` | raw rings, reversal, simple polygons |
| `LeanComputationalGeometry/Polygon/SignedArea.lean` | the shoelace sum, ring orientation and reversal |
| `LeanComputationalGeometry/Polygon/Winding.lean` | edge crossing contributions and winding numbers |
| `LeanComputationalGeometry/Polygon/Region.lean` | boundary, closed and open regions, `SimplePolygon.toRegion` |
| `LeanComputationalGeometry/Polygon/TriangleRegion.lean` | a triangle's winding region is the closed triangle |
| `LeanComputationalGeometry/Examples/Basic.lean` | worked examples: segments, triangles, signed area |
| `LeanComputationalGeometry/Examples/Polygons.lean` | worked examples: inside, outside and boundary points of three polygons |
| `LeanComputationalGeometry/Axioms.lean` | the axiom audit |
| `scripts/joint_check.sh` | the joint check with the sibling libraries |
