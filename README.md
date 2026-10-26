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

Polygons are kept at three levels, and only the first two exist yet:

1. raw ring data (`RawPolygon`, built from a list by `RawPolygon.ofList`),
   about which nothing is assumed;
2. simple polygons (`RawPolygon.IsSimple`, the subtype `SimplePolygon`);
3. region semantics, the interior a simple polygon bounds. It is not
   defined yet; winding numbers come next on the roadmap, and nothing so far
   presumes them.

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

### Polygons

| Result | Theorem |
| --- | --- |
| A nondegenerate triangle is a simple polygon | `Triangle.isSimple_toPolygon` |
| The shoelace sum does not depend on translation or on the starting vertex | `RawPolygon.signedArea2_translate`, `RawPolygon.signedArea2_rotate` |
| For a triangle it is the orientation of the vertices | `Triangle.signedArea2_toPolygon` |

`LeanComputationalGeometry/Examples/Basic.lean` runs concrete coordinates
through these: crossing diagonals, a corner where two edges only touch,
overlapping collinear segments, disjoint parallel segments, a point in and a
point out of a triangle, and the unit square's shoelace sum.

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
3. triangle predicates (membership done; strict interior and boundary next)
4. signed area and the shoelace formula (translation and rotation done;
   reversal next)
5. simple polygons (the predicate exists; more structure next)
6. winding number and point-in-polygon, and with them region semantics
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
| `LeanComputationalGeometry/Polygon/Basic.lean` | raw rings, simple polygons |
| `LeanComputationalGeometry/Polygon/SignedArea.lean` | the shoelace sum |
| `LeanComputationalGeometry/Examples/Basic.lean` | worked examples |
| `LeanComputationalGeometry/Axioms.lean` | the axiom audit |
| `scripts/joint_check.sh` | the joint check with the sibling libraries |
