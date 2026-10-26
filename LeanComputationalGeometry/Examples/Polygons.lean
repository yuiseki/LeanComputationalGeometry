import LeanComputationalGeometry.Polygon.TriangleRegion
import LeanComputationalGeometry.Examples.Basic

/-!
# Polygons and their regions

Concrete polygons with a point inside, a point outside and a point on the
boundary: a triangle, the unit square, and a concave L-shaped hexagon. The
reversed square shows the winding number change sign while the region stays
the same.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D

noncomputable section

/-! ## A triangle -/

/-- The right triangle, as a simple polygon. -/
def triPoly : SimplePolygon := tri.toSimplePolygon tri_isCCW.nondegenerate

example : mk (1 / 4) (1 / 4) ∈ triPoly.toRegion :=
  (Triangle.mem_toRegion_iff _).mpr quarter_mem

example : mk 1 1 ∉ triPoly.toRegion := fun h =>
  far_not_mem ((Triangle.mem_toRegion_iff _).mp h)

/-- The midpoint of the bottom edge is on the boundary. -/
example : mk (1 / 2) 0 ∈ triPoly.boundary := by
  refine ⟨(0 : Fin 3), ?_⟩
  show mk (1 / 2) 0 ∈ segment ℝ (mk 0 0) (mk 1 0)
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  apply Point2D.ext <;> norm_num

/-! ## The unit square -/

theorem square_windingNumber_inside : square.windingNumber (mk (1 / 2) (1 / 2)) = 1 := by
  show ∑ i : Fin 4, edgeContribution (mk (1 / 2) (1 / 2)) (![mk 0 0, mk 1 0, mk 1 1, mk 0 1] i)
    (![mk 0 0, mk 1 0, mk 1 1, mk 0 1] (finRotate 4 i)) = 1
  rw [Fin.sum_univ_four]
  rw [show finRotate 4 0 = 1 by decide, show finRotate 4 1 = 2 by decide,
    show finRotate 4 2 = 3 by decide, show finRotate 4 3 = 0 by decide]
  norm_num [edgeContribution, orient_def]

example : mk (1 / 2) (1 / 2) ∈ square.region := Or.inr (by rw [square_windingNumber_inside]; norm_num)

/-- A point to the right of the square is outside. -/
example : mk 2 (1 / 2) ∉ square.region := by
  apply RawPolygon.not_mem_region_of_right
  intro i
  change Fin 4 at i
  fin_cases i <;> simp

/-- The midpoint of the bottom edge is on the boundary. -/
example : square.OnBoundary (mk (1 / 2) 0) := by
  refine ⟨(0 : Fin 4), ?_⟩
  show mk (1 / 2) 0 ∈ segment ℝ (mk 0 0) (mk 1 0)
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  apply Point2D.ext <;> norm_num

/-! ## Reversing the square -/

/-- Traversed clockwise, the square winds `-1` around its centre... -/
example : square.reverse.windingNumber (mk (1 / 2) (1 / 2)) = -1 := by
  rw [RawPolygon.windingNumber_reverse, square_windingNumber_inside]

/-- ...but its region is the same. -/
example : square.reverse.region = square.region := square.region_reverse

theorem square_signedArea2_reverse : square.reverse.signedArea2 = -2 := by
  rw [RawPolygon.signedArea2_reverse, square_signedArea2]

example : square.reverse.IsCW := by
  rw [RawPolygon.IsCW, square_signedArea2_reverse]
  norm_num

/-! ## A concave hexagon -/

/-- An L shape, counterclockwise: the unit squares `[0,2] × [0,1]` and
`[0,1] × [1,2]`, with the notch `[1,2] × [1,2]` cut out. -/
abbrev ell : RawPolygon :=
  ⟨6, ![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2]⟩

@[simp] theorem finRotate_six_zero : finRotate 6 0 = 1 := by decide
@[simp] theorem finRotate_six_one : finRotate 6 1 = 2 := by decide
@[simp] theorem finRotate_six_two : finRotate 6 2 = 3 := by decide
@[simp] theorem finRotate_six_three : finRotate 6 3 = 4 := by decide
@[simp] theorem finRotate_six_four : finRotate 6 4 = 5 := by decide
@[simp] theorem finRotate_six_five : finRotate 6 5 = 0 := by decide

theorem ell_windingNumber (p : Point2D) :
    ell.windingNumber p = edgeContribution p (mk 0 0) (mk 2 0) +
      edgeContribution p (mk 2 0) (mk 2 1) + edgeContribution p (mk 2 1) (mk 1 1) +
      edgeContribution p (mk 1 1) (mk 1 2) + edgeContribution p (mk 1 2) (mk 0 2) +
      edgeContribution p (mk 0 2) (mk 0 0) := by
  show ∑ i : Fin 6, edgeContribution p (![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2] i)
    (![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2] (finRotate 6 i)) = _
  rw [Fin.sum_univ_six]
  simp

/-- A point in the lower arm is inside. -/
example : ell.windingNumber (mk (1 / 2) (1 / 2)) = 1 := by
  rw [ell_windingNumber]
  norm_num [edgeContribution, orient_def]

/-- A point in the upper arm is inside: the ray crosses the inner edge. -/
example : ell.windingNumber (mk (1 / 2) (3 / 2)) = 1 := by
  rw [ell_windingNumber]
  norm_num [edgeContribution, orient_def]

/-- A point in the notch has winding number `0`... -/
theorem ell_windingNumber_notch : ell.windingNumber (mk (3 / 2) (3 / 2)) = 0 := by
  rw [ell_windingNumber]
  norm_num [edgeContribution, orient_def]

/-- ...and is on no edge, so it is outside. -/
example : mk (3 / 2) (3 / 2) ∉ ell.region := by
  rintro (⟨i, hi⟩ | hw)
  · have key : ∀ j : Fin 6, mk (3 / 2) (3 / 2) ∉ (⟨![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2] j,
        ![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2] (finRotate 6 j)⟩ : Segment).toSet := by
      intro j
      rw [mem_toSet_iff]
      fin_cases j <;> norm_num [orient_def, Set.mem_uIcc]
    exact key i hi
  · exact hw ell_windingNumber_notch

/-- The inner corner's edge is boundary. -/
example : ell.OnBoundary (mk 1 (3 / 2)) := by
  refine ⟨(3 : Fin 6), ?_⟩
  show mk 1 (3 / 2) ∈ segment ℝ (mk 1 1) (mk 1 2)
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  apply Point2D.ext <;> norm_num

end

end ComputationalGeometry.Examples
