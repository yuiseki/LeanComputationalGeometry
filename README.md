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
| `RawPolygon.earTriangle P i` | `⟨prevVertex i, vertex i, nextVertex i⟩`, the vertex and its two neighbours |
| `RawPolygon.earDiagonal P i` | the segment from `prevVertex i` to `nextVertex i` |
| `ConvexVertex`, `ReflexVertex`, `LocallyDegenerate` | `orient (prevVertex i) (vertex i) (nextVertex i)` is `> 0`, `< 0`, `= 0` |
| `RawPolygon.IsEar P i` | vertex `i` is convex and no other vertex lies in the closed ear triangle |
| `RawPolygon.removeEar P i` | the ring without vertex `i`, its neighbours joined by the ear diagonal |
| `RawPolygon.WindsZeroOrOne P` | off the boundary, `windingNumber P p` is `0` or `1`; true for every counterclockwise simple polygon (`IsSimple.windsZeroOrOne_of_isCCW`) |

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
| Two segments from a common endpoint meet only there, unless one holds the other's far endpoint | `Triangle.segment_inter_segment_eq_of_not_mem` |
| Leaving a counterclockwise triangle, a segment reaches its boundary | `Triangle.exists_onEdge_mem_segment` |
| A segment with both ends outside a counterclockwise triangle that avoids two of its edges misses the triangle | `Triangle.disjoint_toSet_of_avoid` |
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
| Off the boundary the winding number is locally constant, so continuous | `RawPolygon.windingNumber_eventually_eq`, `RawPolygon.continuousAt_windingNumber` |
| It is constant on preconnected sets avoiding the boundary | `RawPolygon.windingNumber_eq_of_isPreconnected` |
| The boundary and the closed region are closed; the open region is open | `RawPolygon.isClosed_onBoundary`, `RawPolygon.isClosed_region`, `RawPolygon.isOpen_openRegion`, `SimplePolygon.isOpen_toOpenRegion` |
| Near a point on one edge only, the winding number is a constant plus that edge's contribution, so it goes up by one from right to left across the edge | `RawPolygon.windingNumber_eventually_eq_add_edge`, `RawPolygon.IsSimple.exists_sides` |

An edge's contribution is not locally constant by itself: where the ray from
`p` runs through a vertex, moving `p` up or down hands the count from one edge
at that vertex to the other. Near a point `p` off the edge from `a` to `b`,
the contribution at `q` is `(atOrBelow q a - atOrBelow q b) * crossRight p a b`
(`edgeContribution_eventually_eq`), where `crossRight p a b` depends on `p`
only. Summed around the ring and regrouped by vertices, each vertex off the
ray's height stays on the same side of `q` as of `p`, and each vertex at the
ray's height drops out, because both edges at it cross to the right exactly
when it lies to the right of `p`.

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
and `toOpenRegion` the interior of `toRegion` is the topological half of the
Jordan curve theorem for polygons, not proved here. Its winding-number half
is (next section).

### Winding numbers of simple polygons

| Result | Assumptions | Theorem |
| --- | --- | --- |
| The winding number integrated over a square containing the ring is half the shoelace sum | none | `RawPolygon.signedArea2_eq_integral` |
| If it is nonnegative off the boundary, so is the shoelace sum | none | `RawPolygon.signedArea2_nonneg_of_windingNumber_nonneg` |
| The vertices are not all on one line; some edge is not horizontal; some edge's line misses any given point off the boundary | simple | `IsSimple.not_forall_orient_eq_zero`, `IsSimple.exists_edge_y_ne`, `IsSimple.exists_orient_ne_zero` |
| The reverse of a simple polygon is simple | simple | `IsSimple.reverse` |
| Off the boundary the winding number is `0` or `1` everywhere, or `0` or `-1` everywhere; so at most `1` in absolute value | simple | `IsSimple.windingNumber_cases`, `IsSimple.abs_windingNumber_le_one` |
| A counterclockwise simple polygon winds `0` or `1` times | simple, `IsCCW` | `IsSimple.windsZeroOrOne_of_isCCW`, `SimplePolygon.windsZeroOrOne_of_isCCW` |
| A clockwise simple polygon winds `0` or `-1` times | simple, `IsCW` | `IsSimple.windingNumber_eq_zero_or_neg_one_of_isCW` |

This is the winding-number half of the Jordan curve theorem for polygons, and
the proof is about segments only, not general curves. Beside every edge, on
its left, a thin open triangle (`thinLeft`), and around every vertex, on the
left of its two edges, a small sector (`leftSector`), avoid the boundary when
small, so the winding number is constant on each. A thin triangle reaches
into the sectors at both ends of its edge and consecutive edges share a
sector, so the winding number takes one value `L` on the left of every edge
(`IsSimple.exists_left_value`), and, applied to the reversed ring, one value
`R` on the right. A straight path from a point off the boundary, aimed inside
an edge and away from the lines through the vertices, first meets the
boundary inside an edge, from one side, without crossing it
(`IsSimple.exists_approach`), so every point off the boundary winds `L` or
`R` times. Across a non-horizontal edge `L = R + 1`, and far to the right the
winding number is `0`; so `{L, R}` is `{1, 0}` or `{0, -1}`. Which one is
the sign of the shoelace sum, because the winding number integrates to half
of it.

Not proved: that a simple polygon has a nonzero shoelace sum (it would follow
from the integral once the region where it winds `±1` is known to have
positive area), so a simple polygon is not yet known to be counterclockwise or
clockwise; and the converse, that a simple polygon winding `0` or `1` times is
counterclockwise. `WindsZeroOrOne.signedArea2_nonneg` gives the
nonstrict half of it.

### Ears

An ear is given, not found: nothing here says that a polygon has one.

| Result | Assumptions | Theorem |
| --- | --- | --- |
| Every vertex is convex, reflex or locally degenerate; reflex and degenerate vertices are not ears | none | `convex_or_reflex_or_locallyDegenerate`, `not_isEar_of_reflexVertex`, `not_isEar_of_locallyDegenerate` |
| The diagonal of an ear meets the boundary only at its ends | simple, `4 ≤ n` | `IsEar.earDiagonal_relInterior_inter_boundary` |
| ...edge by edge: edges away from the ear miss the ear triangle, and the edges just before and after meet the diagonal only at its ends | simple, `4 ≤ n` | `IsEar.disjoint_edge_earDiagonal`, `IsEar.edge_prev_prev_inter_earDiagonal`, `IsEar.earDiagonal_inter_edge_next` |
| Removing a vertex leaves one vertex fewer | none | `removeEar_n` |
| Edge sums split along the vertex: the smaller ring's, less the diagonal, plus the two removed edges | `2 ≤ n` | `sum_edges_removeEar` |
| The shoelace sum is the smaller ring's plus the ear triangle's | `2 ≤ n` | `signedArea2_removeEar` |
| The winding number at every point is the smaller ring's plus the ear triangle's | `2 ≤ n` | `windingNumber_removeEar` |
| Cutting an ear off a simple polygon leaves a simple polygon | simple, `4 ≤ n` | `IsEar.isSimple_removeEar`, `SimplePolygon.removeEar` |
| The closed region is the smaller ring's together with the ear triangle | convex vertex, and the ear triangle in the region | `region_removeEar`, `SimplePolygon.toRegion_removeEar` |
| The interior of the ear triangle avoids the boundary | simple, `4 ≤ n` | `IsEar.not_onBoundary_of_mem_interior` |
| Next to the ear the winding number goes up by one into the ear triangle | simple | `IsEar.exists_sides` |
| On the interior of the ear triangle the winding number is `1` | simple, `4 ≤ n`, `WindsZeroOrOne` | `IsEar.windingNumber_eq_one` |
| The interior of the ear triangle is in the open region, the closed ear triangle and the diagonal in the closed region | simple, `4 ≤ n`, `WindsZeroOrOne` | `IsEar.interior_earTriangle_subset_openRegion`, `IsEar.earTriangle_subset_region`, `IsEar.earDiagonal_subset_region`, `SimplePolygon.earTriangle_subset_toRegion` |
| The closed region is the smaller polygon's together with the ear triangle | simple, `4 ≤ n`, `WindsZeroOrOne` | `IsEar.region_removeEar`, `SimplePolygon.toRegion_eq_removeEar_union` |
| The smaller polygon's open region misses the interior of the ear triangle | simple, `4 ≤ n`, `WindsZeroOrOne` | `IsEar.disjoint_openRegion_removeEar`, `SimplePolygon.disjoint_toOpenRegion_removeEar` |
| The smaller polygon again winds `0` or `1` times | simple, `4 ≤ n`, `WindsZeroOrOne` | `IsEar.windsZeroOrOne_removeEar`, `SimplePolygon.windsZeroOrOne_removeEar` |
| All of the above for a counterclockwise polygon, with `IsCCW` in place of `WindsZeroOrOne` | simple, `4 ≤ n`, `IsCCW` | `IsEar.earTriangle_subset_region_of_isCCW`, `IsEar.interior_earTriangle_subset_openRegion_of_isCCW`, `IsEar.region_removeEar_of_isCCW`, `IsEar.disjoint_openRegion_removeEar_of_isCCW`, `IsEar.windsZeroOrOne_removeEar_of_isCCW`, `SimplePolygon.toRegion_eq_removeEar_union_of_isCCW`, `SimplePolygon.disjoint_toOpenRegion_removeEar_of_isCCW` |

The ear test excludes other vertices from the closed ear triangle, not only
from its interior. With only the interior excluded, a vertex could sit on the
diagonal, and cutting the ear would leave a ring that touches itself: in the
L-shaped hexagon the corner at the origin is convex, but the inner corner lies
on its diagonal (`Examples.ell_not_isEar_zero`).

`removeEar` relabels the ring so that the ear comes last, a `Relabel` that
changes nothing geometric (simplicity, edge sums, boundary and region are all
kept), and drops the last vertex. The kept edges are the old edges other than
the ear's two, and the last edge is the diagonal (`dropLast_edge_of_ne_last`,
`dropLast_edge_last`). Simplicity then splits into old edges against old
edges, which the polygon's simplicity covers, and the diagonal against old
edges, which the diagonal theorem covers.

The edge sums split because only three edges change: `prev → i` and
`i → next` go, `prev → next` comes, and the ear triangle's edges are exactly
the two that go and the diagonal reversed. The region identity follows from
the winding identity: off the ear triangle its winding number is `0`, and the
boundaries differ only by the ear triangle's edges.

Whether the ear triangle lies inside the polygon is settled by the winding
number on its interior, which is constant there: the interior is convex and
avoids the boundary. Just across one of the ear's own edges, from outside the
triangle to inside, the winding number goes up by one. That leaves `1`
(inside) or `0` (outside), and nothing local decides between them. Traversed
clockwise, the L-shaped hexagon is simple and its inner corner passes the ear
test, but that ear triangle is the notch, outside the polygon
(`Examples.ellCW_isEar_two`, `Examples.ellCW_earTriangle_not_subset_region`).
So some global fact is needed, and the one used is `WindsZeroOrOne`: off its
boundary the polygon winds `0` or `1` times. The low-level theorems take it as
a hypothesis; every counterclockwise simple polygon satisfies it
(`IsSimple.windsZeroOrOne_of_isCCW`, previous section), and the `_of_isCCW`
versions take `IsCCW` instead. The clockwise L fails it
(`Examples.ellCW_not_windsZeroOrOne`). `IsEar` is a local test whose meaning
depends on the direction of traversal; only for counterclockwise polygons does
it mean what its name says. Given `WindsZeroOrOne`, the value is `1`, so

```
IsEar P i  (P simple, n ≥ 4, IsCCW P, or WindsZeroOrOne P)
  → P.removeEar i simple, with n - 1 vertices
  → P.region = (P.removeEar i).region ∪ (P.earTriangle i).toSet
  → (P.removeEar i).openRegion misses interior (P.earTriangle i).toSet
  → WindsZeroOrOne (P.removeEar i)
```

are all proved, the last because the smaller polygon winds `1 - 1 = 0` times
there.

### Examples

`LeanComputationalGeometry/Examples/Basic.lean` runs concrete coordinates
through the segment and triangle theorems: crossing diagonals, a corner where
two edges only touch, overlapping collinear segments, disjoint parallel
segments, a point in and a point out of a triangle, and the unit square's
shoelace sum. `LeanComputationalGeometry/Examples/Polygons.lean` checks a
point inside, outside and on the boundary of a triangle, the unit square and
a concave L-shaped hexagon (including a point in the notch, with winding
number `0`), and shows the reversed square winding `-1` around its centre
with the same region. `LeanComputationalGeometry/Examples/Ears.lean` proves
the square and the L simple, finds two ears of the square and one of the L,
shows a reflex corner and a convex corner with a vertex on its diagonal not to
be ears, and cuts ears off: the results are simple, with signed double areas
`1` and `4`, and the winding numbers change by the ear's.
`LeanComputationalGeometry/Examples/EarRegion.lean` proves that the square and
the L wind `0` or `1` times, both by direct computation and from their signed
areas through the general theorem, applies the region theorems to their ears
from simplicity and orientation alone, and gives the clockwise L as a simple
polygon with an ear outside it, winding `0` or `-1` times.

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

| Step | Status |
| --- | --- |
| orientation | done |
| segment intersection | done, every case |
| triangle predicates | done: closed, strict interior, boundary |
| signed area | done: translation, rotation, reversal |
| winding / region semantics | done: winding numbers, boundary, closed and open regions, the triangle case end to end |
| ear predicate | done |
| ear removal | done |
| winding topology | done: local constancy off the boundary, constancy on preconnected sets, open and closed regions, the step across an edge |
| polygonal Jordan / winding orientation | done: `WindsZeroOrOne` proved for every simple counterclockwise polygon, `0` or `-1` for clockwise ones |
| ear local correctness | complete for simple counterclockwise polygons: simplicity, signed area, winding number, region identity, disjoint interiors |
| Two Ears Theorem | next |
| ear existence | next |
| well-founded ear clipping | later |
| `n - 2` triangles | later |
| triangulation correctness | later |
| a simple polygon has a nonzero shoelace sum, so is counterclockwise or clockwise | open |
| polygons with holes | later |
| clipping | later |
| convex hull | later |

The Jordan curve theorem for general continuous curves is not attempted, nor
the topological half of the polygonal one (two components, the region the
closure of the open region).

One step of ear clipping now has its shape:

```
SimplePolygon P, n ≥ 4
    ↓  choose an ear i (IsEar)
triangle P.earTriangle i  +  smaller SimplePolygon P.removeEar i, n - 1 vertices
```

with the signed area and the winding number of `P` the sums of the two
parts', the region of `P` their union, and the interiors disjoint, for any
simple counterclockwise `P`. Recursing needs an ear to exist
(the Two Ears Theorem), which is the next step; the vertex count falling by
one (`removeEar_n`) is what will make the recursion terminate with `n - 2`
triangles. The smaller polygon again winds `0` or `1` times
(`IsEar.windsZeroOrOne_removeEar`): off the ear triangle its winding numbers
are the polygon's, and on the ear triangle they are `0`. So the property
carries through the recursion, and only the input polygon needs to be
counterclockwise. A clockwise input can be reversed first; a simple polygon
with zero shoelace sum is not yet ruled out.

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
| `LeanComputationalGeometry/TriangleCrossing.lean` | how a segment can meet a triangle |
| `LeanComputationalGeometry/Polygon/Basic.lean` | raw rings, reversal, simple polygons |
| `LeanComputationalGeometry/Polygon/SignedArea.lean` | the shoelace sum, ring orientation and reversal |
| `LeanComputationalGeometry/Polygon/Winding.lean` | edge crossing contributions and winding numbers |
| `LeanComputationalGeometry/Polygon/Region.lean` | boundary, closed and open regions, `SimplePolygon.toRegion` |
| `LeanComputationalGeometry/Polygon/TriangleRegion.lean` | a triangle's winding region is the closed triangle |
| `LeanComputationalGeometry/Polygon/Ear.lean` | ear triangles and diagonals, convex and reflex vertices, `IsEar`, the diagonal of an ear |
| `LeanComputationalGeometry/Polygon/RemoveEar.lean` | relabelling, `removeEar`, the area, winding and region splits, simplicity |
| `LeanComputationalGeometry/Polygon/WindingTopology.lean` | local constancy of the winding number, open and closed regions, the step across an edge |
| `LeanComputationalGeometry/Polygon/EarRegion.lean` | the ear triangle inside the polygon, the region split, disjoint interiors, given `WindsZeroOrOne` |
| `LeanComputationalGeometry/Polygon/WindingArea.lean` | the winding number integrates to half the shoelace sum |
| `LeanComputationalGeometry/Polygon/Jordan.lean` | simple polygons wind `0` or `±1` times; `WindsZeroOrOne` from `IsCCW`; the ear theorems for counterclockwise polygons |
| `LeanComputationalGeometry/Examples/Basic.lean` | worked examples: segments, triangles, signed area |
| `LeanComputationalGeometry/Examples/Polygons.lean` | worked examples: inside, outside and boundary points of three polygons |
| `LeanComputationalGeometry/Examples/Ears.lean` | worked examples: ears of the square and the L, and cutting them off |
| `LeanComputationalGeometry/Examples/EarRegion.lean` | worked examples: the region theorems for the square and the L, and the clockwise L |
| `LeanComputationalGeometry/Axioms.lean` | the axiom audit |
| `scripts/joint_check.sh` | the joint check with the sibling libraries |
