import LeanComputationalGeometry.Polygon.RemoveEar
import LeanComputationalGeometry.Examples.Polygons

/-!
# Ears

The unit square, a convex quadrilateral: a corner is an ear, and cutting it
off leaves a simple triangle whose signed area and winding numbers are the
square's less the ear's. The concave L-shaped hexagon: a convex corner whose
ear triangle holds another vertex is not an ear, a reflex corner is not an
ear, and a convex corner with an empty ear triangle is.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D

noncomputable section

/-- Two segments miss each other if no point is on both lines. -/
theorem disjoint_segment_of_orient {a b c d : Point2D}
    (h : ∀ x, orient a b x = 0 → orient c d x = 0 → False) :
    Disjoint (segment ℝ a b) (segment ℝ c d) :=
  Set.disjoint_left.mpr fun x h₁ h₂ =>
    h x (Segment.orient_eq_zero_of_mem ⟨a, b⟩ h₁)
      (Segment.orient_eq_zero_of_mem ⟨c, d⟩ h₂)

/-! ## The unit square -/

@[simp] theorem finRotate_four_zero : finRotate 4 0 = 1 := by decide
@[simp] theorem finRotate_four_one : finRotate 4 1 = 2 := by decide
@[simp] theorem finRotate_four_two : finRotate 4 2 = 3 := by decide
@[simp] theorem finRotate_four_three : finRotate 4 3 = 0 := by decide

theorem square_prev_zero : square.prev 0 = 3 := by
  show (finRotate 4).symm 0 = 3
  rw [Equiv.symm_apply_eq]
  decide

theorem square_next_zero : square.next 0 = 1 := finRotate_four_zero

/-- The unit square is a simple polygon. -/
theorem square_isSimple : square.IsSimple := by
  refine ⟨by show 3 ≤ 4; norm_num, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · change Fin 4 at i
    fin_cases i <;>
      simp [RawPolygon.edge, RawPolygon.next, Segment.Nondegenerate, square, ext_iff']
  · change Fin 4 at i
    fin_cases i <;> simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, square] <;> simp <;>
      exact Triangle.segment_inter_segment_eq (by norm_num [orient_def])
  · change Fin 4 at i j
    change finRotate 4 i ≠ j at h₁
    change finRotate 4 j ≠ i at h₂
    fin_cases i <;> fin_cases j <;> simp at hij h₁ h₂ <;>
      simp only [RawPolygon.edge, RawPolygon.next, Segment.toSet, square] <;> simp <;>
      exact disjoint_segment_of_orient fun x e₁ e₂ => by
        simp [orient_def] at e₁ e₂; linarith

theorem square_earTriangle_zero : square.earTriangle 0 = ⟨mk 0 1, mk 0 0, mk 1 0⟩ := by
  simp [RawPolygon.earTriangle, RawPolygon.prevVertex, RawPolygon.nextVertex, square_prev_zero,
    square_next_zero, square]

/-- Corner `0` of the square is an ear: it is convex, and the far corner
`(1, 1)` is outside its ear triangle. -/
theorem square_isEar_zero : square.IsEar 0 := by
  have hT : (square.earTriangle 0).IsCCW := by
    rw [square_earTriangle_zero]
    norm_num [Triangle.IsCCW, Triangle.signedArea2, orient_def]
  refine ⟨hT, fun j h₁ h₂ h₃ => ?_⟩
  rw [square_prev_zero] at h₁
  rw [square_next_zero] at h₃
  rw [Triangle.mem_toSet_iff_containsTest hT, square_earTriangle_zero]
  change Fin 4 at j
  fin_cases j
  · exact absurd rfl h₂
  · exact absurd rfl h₃
  · rintro ⟨-, -, h⟩
    norm_num [square, orient_def] at h
  · exact absurd rfl h₁

/-- Cutting it off leaves three vertices... -/
example : (square.removeEar 0).n = 3 := square.removeEar_n 0

/-- ...forming a simple polygon. -/
theorem square_removeEar_isSimple : (square.removeEar 0).IsSimple :=
  square_isEar_zero.isSimple_removeEar square_isSimple le_rfl

/-- As a `SimplePolygon`. -/
def squareCut : SimplePolygon :=
  SimplePolygon.removeEar ⟨square, square_isSimple⟩ le_rfl 0 square_isEar_zero

/-- The square's signed double area `2` is the triangle's `1` plus the ear's
`1`. -/
example : (square.removeEar 0).signedArea2 = 1 := by
  have := RawPolygon.signedArea2_removeEar square (by show 2 ≤ 4; norm_num) 0
  rw [square_signedArea2, square_earTriangle_zero] at this
  norm_num [Triangle.signedArea2, orient_def] at this
  linarith

theorem square_windingNumber (p : Point2D) :
    square.windingNumber p = edgeContribution p (mk 0 0) (mk 1 0) +
      edgeContribution p (mk 1 0) (mk 1 1) + edgeContribution p (mk 1 1) (mk 0 1) +
      edgeContribution p (mk 0 1) (mk 0 0) := by
  show ∑ i : Fin 4, edgeContribution p (![mk 0 0, mk 1 0, mk 1 1, mk 0 1] i)
    (![mk 0 0, mk 1 0, mk 1 1, mk 0 1] (finRotate 4 i)) = _
  rw [Fin.sum_univ_four]
  simp

/-- A point of the ear is no longer inside once the ear is cut off... -/
example : (square.removeEar 0).windingNumber (mk (1 / 4) (1 / 4)) = 0 := by
  have := RawPolygon.windingNumber_removeEar square (by show 2 ≤ 4; norm_num) 0
    (mk (1 / 4) (1 / 4))
  rw [square_windingNumber, square_earTriangle_zero] at this
  norm_num [Triangle.winding3, edgeContribution, orient_def] at this
  linarith

/-- ...while a point away from the ear still is. -/
example : (square.removeEar 0).windingNumber (mk (3 / 4) (3 / 4)) = 1 := by
  have := RawPolygon.windingNumber_removeEar square (by show 2 ≤ 4; norm_num) 0
    (mk (3 / 4) (3 / 4))
  rw [square_windingNumber, square_earTriangle_zero] at this
  norm_num [Triangle.winding3, edgeContribution, orient_def] at this
  linarith

/-! ## The L-shaped hexagon -/

theorem ell_prev_zero : ell.prev 0 = 5 := by
  show (finRotate 6).symm 0 = 5
  rw [Equiv.symm_apply_eq]
  decide

theorem ell_prev_one : ell.prev 1 = 0 := by
  show (finRotate 6).symm 1 = 0
  rw [Equiv.symm_apply_eq]
  decide

theorem ell_prev_three : ell.prev 3 = 2 := by
  show (finRotate 6).symm 3 = 2
  rw [Equiv.symm_apply_eq]
  decide

theorem ell_earTriangle_zero : ell.earTriangle 0 = ⟨mk 0 2, mk 0 0, mk 2 0⟩ := by
  simp [RawPolygon.earTriangle, RawPolygon.prevVertex, RawPolygon.nextVertex, ell_prev_zero,
    RawPolygon.next, ell]

theorem ell_earTriangle_one : ell.earTriangle 1 = ⟨mk 0 0, mk 2 0, mk 2 1⟩ := by
  simp [RawPolygon.earTriangle, RawPolygon.prevVertex, RawPolygon.nextVertex, ell_prev_one,
    RawPolygon.next, ell]

/-- The corner at the origin turns left... -/
theorem ell_convexVertex_zero : ell.ConvexVertex 0 := by
  show 0 < (ell.earTriangle 0).signedArea2
  rw [ell_earTriangle_zero]
  norm_num [Triangle.signedArea2, orient_def]

/-- ...but is not an ear: the inner corner `(1, 1)` lies on its diagonal, so
cutting it off would leave a ring that touches itself. -/
theorem ell_not_isEar_zero : ¬ ell.IsEar 0 := by
  intro h
  refine h.empty 3 (by rw [ell_prev_zero]; decide) (by decide)
    (by show (3 : Fin 6) ≠ finRotate 6 0; simp) ?_
  rw [Triangle.mem_toSet_iff_containsTest h.isCCW, ell_earTriangle_zero]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ell, orient_def]

/-- The inner corner turns right, so it is not an ear. -/
theorem ell_reflexVertex_three : ell.ReflexVertex 3 := by
  show orient (ell.vertex (ell.prev 3)) (ell.vertex 3) (ell.vertex (ell.next 3)) < 0
  rw [ell_prev_three]
  norm_num [RawPolygon.next, ell, orient_def]

example : ¬ ell.IsEar 3 := RawPolygon.not_isEar_of_reflexVertex ell_reflexVertex_three

/-- The corner `(2, 0)` is an ear: the other vertices are all outside its ear
triangle, beyond the diagonal from `(2, 1)` back to the origin. -/
theorem ell_isEar_one : ell.IsEar 1 := by
  have hT : (ell.earTriangle 1).IsCCW := by
    rw [ell_earTriangle_one]
    norm_num [Triangle.IsCCW, Triangle.signedArea2, orient_def]
  refine ⟨hT, fun j h₁ h₂ h₃ => ?_⟩
  rw [ell_prev_one] at h₁
  change j ≠ finRotate 6 1 at h₃
  rw [finRotate_six_one] at h₃
  rw [Triangle.mem_toSet_iff_containsTest hT, ell_earTriangle_one]
  change Fin 6 at j
  fin_cases j
  · exact absurd rfl h₁
  · exact absurd rfl h₂
  · exact absurd rfl h₃
  all_goals rintro ⟨-, -, h⟩; norm_num [ell, orient_def] at h

theorem ell_signedArea2 : ell.signedArea2 = 6 := by
  show ∑ i : Fin 6, cross (![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2] i)
    (![mk 0 0, mk 2 0, mk 2 1, mk 1 1, mk 1 2, mk 0 2] (finRotate 6 i)) = 6
  rw [Fin.sum_univ_six]
  simp [cross]
  norm_num

/-- Cutting the ear off the L leaves a pentagon of signed double area `4`:
the L's `6` less the ear's `2`. -/
example : (ell.removeEar 1).signedArea2 = 4 := by
  have := RawPolygon.signedArea2_removeEar ell (by show 2 ≤ 6; norm_num) 1
  rw [ell_signedArea2, ell_earTriangle_one] at this
  norm_num [Triangle.signedArea2, orient_def] at this
  linarith

example : (ell.removeEar 1).n = 5 := ell.removeEar_n 1

end

end ComputationalGeometry.Examples
