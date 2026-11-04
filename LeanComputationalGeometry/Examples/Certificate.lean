import LeanComputationalGeometry.Polygon.Certificate
import LeanComputationalGeometry.Examples.EarClip

/-!
# Checking triangulations

Triangulations handed in as vertex index triples, the form an external
triangulator such as Earcut returns, checked with `IsTriangulation`: the side
condition by `decide`, the orientations by `norm_num`. The general theorems
then give that the triangles cover the polygon's region without overlapping.

- the unit square, cut along either diagonal; two wrong lists are rejected
  by the side condition alone: one with a triangle reaching outside the
  square, one repeating a triangle;
- the comb, cut into its four tooth tips and a fan of three triangles from
  the corner at the origin, a triangulation that ear clipping need not
  produce, through three collinear vertices;
- the L, which has a list that passes by completeness, and the clockwise L,
  which has none.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D RawPolygon

noncomputable section

/-! ## The unit square -/

theorem square_isTriangulation : square.IsTriangulation [(0, 1, 2), (0, 2, 3)] where
  isCCW t ht := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      norm_num [Triangle.IsCCW, Triangle.signedArea2, idxTriangle, orient_def]
  sides := by decide

theorem square_isTriangulation' : square.IsTriangulation [(0, 1, 3), (1, 2, 3)] where
  isCCW t ht := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;>
      norm_num [Triangle.IsCCW, Triangle.signedArea2, idxTriangle, orient_def]
  sides := by decide

/-! ## Combinatorial consequences of the side check -/

example : square.sideCount [(0, 1, 2), (0, 2, 3)] 0 2 =
    square.sideCount [(0, 1, 2), (0, 2, 3)] 2 0 := by decide

example : square.sideCount [(0, 1, 2), (0, 2, 3)] 0 2 =
    square.sideCount [(0, 1, 2), (0, 2, 3)] 2 0 :=
  square_isTriangulation.sideCount_eq_of_no_edge 0 2 (by decide) (by decide)

example : square.sideCount [(0, 1, 2), (0, 2, 3)] 0 1 =
    square.sideCount [(0, 1, 2), (0, 2, 3)] 1 0 + 1 := by decide

example : square.sideCount [(0, 1, 2), (0, 2, 3)] 0 1 =
    square.sideCount [(0, 1, 2), (0, 2, 3)] 1 0 + 1 := by
  apply square_isTriangulation.sideCount_eq_reverse_add_one (by decide) 0
  decide

example : ∃ t : Fin 4 × Fin 4 × Fin 4, t ∈ [(0, 1, 2), (0, 2, 3)] ∧
    ((t.1, t.2.1) = (0, 1) ∨ (t.2.1, t.2.2) = (0, 1) ∨ (t.2.2, t.1) = (0, 1)) := by decide

example : ∃ t : Fin 4 × Fin 4 × Fin 4, t ∈ [(0, 1, 2), (0, 2, 3)] ∧
    ((t.1, t.2.1) = (0, 1) ∨ (t.2.1, t.2.2) = (0, 1) ∨ (t.2.2, t.1) = (0, 1)) := by
  exact square_isTriangulation.exists_triangle_side_of_edge (by decide) 0 1 (by decide)

example (t : Fin 4 × Fin 4 × Fin 4) (ht : t ∈ [(0, 1, 2), (0, 2, 3)]) :
    (square.idxTriangle t).a ≠ (square.idxTriangle t).b ∧
      (square.idxTriangle t).b ≠ (square.idxTriangle t).c ∧
      (square.idxTriangle t).c ≠ (square.idxTriangle t).a := by
  exact square_isTriangulation.idxTriangle_vertices_ne t ht

example : [(0, 1, 2), (0, 2, 3)] ≠ ([] : List (Fin 4 × Fin 4 × Fin 4)) := by
  exact square_isTriangulation.nonempty (by decide : 3 ≤ square.n)

example (p : Point2D) : p ∈ square.region ↔
    ∃ t ∈ [((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), (0, 2, 3)], p ∈ (square.idxTriangle t).toSet :=
  square_isTriangulation.mem_region_iff square_isSimple

example : [((0 : Fin 4), (1 : Fin 4), (2 : Fin 4)), (0, 2, 3)].Pairwise fun t t' =>
    Disjoint (interior (square.idxTriangle t).toSet) (interior (square.idxTriangle t').toSet) :=
  square_isTriangulation.pairwise_disjoint square_isSimple

/-- Two triangles over the same corner overlap, and the side from `0` to `2`
is not matched: rejected. -/
example : ¬ ∀ u v, square.sideCount [(0, 1, 2), (1, 2, 3)] u v + square.edgeCount v u =
    square.sideCount [(0, 1, 2), (1, 2, 3)] v u + square.edgeCount u v := by decide

/-- A repeated triangle covers its part twice: rejected. -/
example : ¬ ∀ u v, square.sideCount [(0, 1, 2), (0, 1, 2), (0, 2, 3)] u v + square.edgeCount v u =
    square.sideCount [(0, 1, 2), (0, 1, 2), (0, 2, 3)] v u + square.edgeCount u v := by decide

/-! ## The comb -/

/-- The four tooth tips, then a fan from the origin. -/
abbrev combTriangles : List (Fin 9 × Fin 9 × Fin 9) :=
  [(1, 2, 3), (3, 4, 5), (5, 6, 7), (7, 8, 0), (0, 1, 3), (0, 3, 5), (0, 5, 7)]

theorem comb_isTriangulation : comb.IsTriangulation combTriangles where
  isCCW t ht := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Triangle.IsCCW, Triangle.signedArea2, idxTriangle, orient_def]
  sides := by decide

example (p : Point2D) : p ∈ comb.region ↔ ∃ t ∈ combTriangles, p ∈ (comb.idxTriangle t).toSet :=
  comb_isTriangulation.mem_region_iff comb_isSimple

example : combTriangles.Pairwise fun t t' =>
    Disjoint (interior (comb.idxTriangle t).toSet) (interior (comb.idxTriangle t').toSet) :=
  comb_isTriangulation.pairwise_disjoint comb_isSimple

/-- The areas add up: the comb's signed double area is the sum of the seven. -/
example : comb.signedArea2 = (combTriangles.map fun t => (comb.idxTriangle t).signedArea2).sum :=
  comb_isTriangulation.signedArea2_eq_sum

/-! ## Completeness -/

/-- The L has a list of four index triangles that passes, by completeness. -/
example : ∃ ts, ell.IsTriangulation ts ∧ ts.length = 4 :=
  ell_isSimple.exists_isTriangulation (ell_isSimple.windsZeroOrOne_of_isCCW ell_isCCW)

/-- The clockwise L has none: a list that passes makes the polygon
counterclockwise. -/
example : ¬ ∃ ts, ellCW.IsTriangulation ts := fun h =>
  absurd ((ellCW_isSimple.exists_isTriangulation_iff).mp h) (not_lt.mpr ellCW_isCW.le)

end

end ComputationalGeometry.Examples
