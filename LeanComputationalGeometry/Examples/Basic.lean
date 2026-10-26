import LeanComputationalGeometry.Polygon.SignedArea

/-!
# Worked examples

Concrete coordinates run through the general theorems, one case of each kind:
a counterclockwise turn, crossing diagonals, segments touching at an
endpoint, overlapping collinear segments, disjoint parallel segments, a point
in and a point out of a triangle, and the signed area of the unit square.
-/

namespace ComputationalGeometry.Examples

open ComputationalGeometry Point2D

noncomputable section

/-- `(0,0) → (1,0) → (0,1)` turns counterclockwise. -/
example : orient (mk 0 0) (mk 1 0) (mk 0 1) = 1 := by
  simp [orient_def]

/-- The diagonals of the unit square. -/
def diag₁ : Segment := ⟨mk 0 0, mk 1 1⟩
def diag₂ : Segment := ⟨mk 1 0, mk 0 1⟩

theorem diagonals_crossTest : CrossTest diag₁ diag₂ := by
  refine ⟨?_, ?_⟩ <;> simp [Straddles, diag₁, diag₂, orient_def]

/-- They cross properly. -/
theorem diagonals_properlyIntersect : ProperlyIntersect diag₁ diag₂ :=
  (properlyIntersect_iff_crossTest _ _).mpr diagonals_crossTest

/-- Two edges of the square meeting at a corner. -/
def bottom : Segment := ⟨mk 0 0, mk 1 0⟩
def right : Segment := ⟨mk 1 0, mk 1 1⟩

/-- They intersect, at the shared endpoint... -/
theorem corner_intersects : Intersects bottom right :=
  (intersects_iff_intersectTest _ _).mpr (Or.inr (Or.inl (by simpa [bottom, right] using
    bottom.q_mem_toSet)))

/-- ...but not properly: the strict test fails, since the corner is on both
lines. -/
theorem corner_not_properlyIntersect : ¬ ProperlyIntersect bottom right := by
  rw [properlyIntersect_iff_crossTest]
  rintro ⟨h, -⟩
  simp [Straddles, bottom, right, orient_def] at h

/-- Overlapping collinear segments on the x-axis. -/
def left₂ : Segment := ⟨mk 0 0, mk 2 0⟩
def right₂ : Segment := ⟨mk 1 0, mk 3 0⟩

theorem overlap_intersects : Intersects left₂ right₂ := by
  rw [intersects_iff_intersectTest]
  right; left
  rw [mem_toSet_iff]
  refine ⟨by simp [left₂, right₂, orient_def], ?_, ?_⟩ <;> simp [left₂, right₂]

/-- Disjoint parallel segments. -/
def lower : Segment := ⟨mk 0 0, mk 1 0⟩
def upper : Segment := ⟨mk 0 1, mk 1 1⟩

theorem parallel_not_intersects : ¬ Intersects lower upper := by
  rw [intersects_iff_intersectTest]
  have off : ∀ {s : Segment} {x : Point2D}, orient s.p s.q x ≠ 0 → x ∉ s.toSet :=
    fun {s _} h hx => h (Segment.orient_eq_zero_of_mem s hx)
  rintro (⟨h, -⟩ | h | h | h | h)
  · norm_num [Straddles, lower, upper, orient_def] at h
  · exact off (by simp [lower, upper, orient_def]) h
  · exact off (by simp [lower, upper, orient_def]) h
  · exact off (by simp [lower, upper, orient_def]) h
  · exact off (by simp [lower, upper, orient_def]) h

/-- The right triangle `(0,0), (1,0), (0,1)`, counterclockwise. -/
def tri : Triangle := ⟨mk 0 0, mk 1 0, mk 0 1⟩

theorem tri_isCCW : tri.IsCCW := by
  simp [Triangle.IsCCW, Triangle.signedArea2, tri, orient_def]

theorem quarter_mem : mk (1 / 4) (1 / 4) ∈ tri.toSet := by
  rw [Triangle.mem_toSet_iff_containsTest tri_isCCW]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tri, orient_def]

theorem far_not_mem : mk 1 1 ∉ tri.toSet := by
  rw [Triangle.mem_toSet_iff_containsTest tri_isCCW]
  rintro ⟨-, h, -⟩
  simp [tri, orient_def] at h
  norm_num at h

/-- The triangle is a simple polygon, and its shoelace sum is its signed
double area, `1`. -/
example : tri.toPolygon.IsSimple := Triangle.isSimple_toPolygon tri_isCCW.nondegenerate

example : tri.toPolygon.signedArea2 = 1 := by
  rw [Triangle.signedArea2_toPolygon]
  simp [Triangle.signedArea2, tri, orient_def]

/-- The unit square, counterclockwise from the origin. -/
def square : RawPolygon := ⟨4, ![mk 0 0, mk 1 0, mk 1 1, mk 0 1]⟩

theorem square_signedArea2 : square.signedArea2 = 2 := by
  show ∑ i : Fin 4, cross (![mk 0 0, mk 1 0, mk 1 1, mk 0 1] i)
    (![mk 0 0, mk 1 0, mk 1 1, mk 0 1] (finRotate 4 i)) = 2
  rw [Fin.sum_univ_four]
  rw [show finRotate 4 0 = 1 by decide, show finRotate 4 1 = 2 by decide,
    show finRotate 4 2 = 3 by decide, show finRotate 4 3 = 0 by decide]
  simp [cross]
  norm_num

/-- Moving it does not change its area. -/
example : (square.translate (mk 5 7)).signedArea2 = 2 := by
  rw [RawPolygon.signedArea2_translate, square_signedArea2]

end

end ComputationalGeometry.Examples
