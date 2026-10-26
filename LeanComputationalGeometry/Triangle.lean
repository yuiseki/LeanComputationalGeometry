import LeanComputationalGeometry.Segment
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination

/-!
# Triangles

A `Triangle` is three vertices, in order. Its signed double area is the
orientation of the vertices (`signedArea2`), positive for a counterclockwise
triangle; the signed area is half of it, and both are the shoelace sums of
the three vertices (`signedArea2_eq_cross_sum`). A triangle is nondegenerate
when the signed area is nonzero, which is Mathlib's affine independence of
the vertices (`nondegenerate_iff_affineIndependent`).

The closed triangle is Mathlib's convex hull of the vertices (`toSet`). For a
counterclockwise triangle, a point is in it exactly when it lies on the left
of, or on, each of the three edges, read as orientations
(`mem_toSet_iff_containsTest`). The proof goes through barycentric
coordinates: the orientations against the three edges sum to the triangle's
(`orient_sum`) and weight the vertices to give the point (`orient_smul_sum`).
-/

namespace ComputationalGeometry

open Set Point2D

/-- Three vertices, in order. -/
structure Triangle where
  a : Point2D
  b : Point2D
  c : Point2D

namespace Triangle

variable (T : Triangle)

/-- Twice the signed area: the orientation of the vertices. -/
def signedArea2 : ℝ := orient T.a T.b T.c

/-- The signed area. -/
noncomputable def signedArea : ℝ := T.signedArea2 / 2

/-- The vertices are not collinear. -/
def Nondegenerate : Prop := T.signedArea2 ≠ 0

/-- The vertices turn counterclockwise. -/
def IsCCW : Prop := 0 < T.signedArea2

/-- The closed triangle: the convex hull of the vertices. -/
def toSet : Set Point2D := convexHull ℝ {T.a, T.b, T.c}

/-- `p` is on the left of, or on, each edge. For a counterclockwise triangle
this is membership (`mem_toSet_iff_containsTest`). -/
def ContainsTest (p : Point2D) : Prop :=
  0 ≤ orient T.a T.b p ∧ 0 ≤ orient T.b T.c p ∧ 0 ≤ orient T.c T.a p

/-- `p` is strictly on the left of each edge. -/
def StrictContainsTest (p : Point2D) : Prop :=
  0 < orient T.a T.b p ∧ 0 < orient T.b T.c p ∧ 0 < orient T.c T.a p

/-- The same triangle, traversed the other way. -/
def reverse : Triangle := ⟨T.a, T.c, T.b⟩

theorem signedArea2_eq_cross_sum : T.signedArea2 = cross T.a T.b + cross T.b T.c + cross T.c T.a :=
  orient_eq_cross_sum _ _ _

theorem signedArea2_reverse : T.reverse.signedArea2 = -T.signedArea2 := orient_swap₂₃ _ _ _

theorem nondegenerate_iff_not_collinear : T.Nondegenerate ↔ ¬ Collinear ℝ {T.a, T.b, T.c} := by
  rw [Nondegenerate, signedArea2, ne_eq, orient_eq_zero_iff_collinear]

theorem nondegenerate_iff_affineIndependent :
    T.Nondegenerate ↔ AffineIndependent ℝ ![T.a, T.b, T.c] :=
  orient_ne_zero_iff_affineIndependent _ _ _

theorem IsCCW.nondegenerate {T : Triangle} (h : T.IsCCW) : T.Nondegenerate := h.ne'

/-- The orientations against the three edges sum to the triangle's. -/
theorem orient_sum (p : Point2D) :
    orient T.b T.c p + orient T.c T.a p + orient T.a T.b p = T.signedArea2 := by
  simp only [signedArea2, orient_def]
  ring

/-- Barycentric coordinates: the orientations against the edges weight the
vertices to give the point. -/
theorem orient_smul_sum (p : Point2D) :
    orient T.b T.c p • T.a + orient T.c T.a p • T.b + orient T.a T.b p • T.c =
      T.signedArea2 • p := by
  apply Point2D.ext <;>
  · simp only [signedArea2, orient_def, x_add, y_add, x_smul, y_smul]
    ring

theorem a_mem_toSet : T.a ∈ T.toSet := subset_convexHull ℝ _ (by simp)
theorem b_mem_toSet : T.b ∈ T.toSet := subset_convexHull ℝ _ (by simp)
theorem c_mem_toSet : T.c ∈ T.toSet := subset_convexHull ℝ _ (by simp)

end Triangle

/-- The closed left half-plane of the line through `a` and `b` is convex. -/
theorem convex_left (a b : Point2D) : Convex ℝ {p | 0 ≤ orient a b p} := by
  intro x hx y hy α β hα hβ hαβ
  obtain rfl : α = 1 - β := by linarith
  simp only [mem_ofPred_eq, orient_lineMap] at hx hy ⊢
  nlinarith [mul_nonneg hα hx, mul_nonneg hβ hy]

namespace Triangle

variable {T : Triangle}

/-- For a counterclockwise triangle, a point is in it exactly when it is on
the left of, or on, each edge. -/
theorem mem_toSet_iff_containsTest (h : T.IsCCW) (p : Point2D) :
    p ∈ T.toSet ↔ T.ContainsTest p := by
  have hA : 0 < orient T.a T.b T.c := h
  constructor
  · intro hp
    have sub : ∀ {u v w : Point2D}, 0 < orient u v w → {u, v, w} ⊆ {x | 0 ≤ orient u v x} := by
      intro u v w huvw
      simp only [insert_subset_iff, singleton_subset_iff, mem_ofPred_eq, orient_self₁₃,
        orient_self₂₃, le_refl, true_and]
      exact huvw.le
    refine ⟨convexHull_min (sub hA) (convex_left _ _) hp, ?_, ?_⟩
    · have hs : ({T.b, T.c, T.a} : Set Point2D) = {T.a, T.b, T.c} := by
        ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto
      have hp' : p ∈ convexHull ℝ {T.b, T.c, T.a} := by rw [hs]; exact hp
      exact convexHull_min (sub (by rw [orient_rotate]; exact hA)) (convex_left _ _) hp'
    · have hs : ({T.c, T.a, T.b} : Set Point2D) = {T.a, T.b, T.c} := by
        ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto
      have hp' : p ∈ convexHull ℝ {T.c, T.a, T.b} := by rw [hs]; exact hp
      exact convexHull_min (sub (by rw [← orient_rotate]; exact hA)) (convex_left _ _) hp'
  · rintro ⟨h₁, h₂, h₃⟩
    set A := T.signedArea2
    have hA' : A ≠ 0 := hA.ne'
    have hp : p = (orient T.b T.c p / A) • T.a + (orient T.c T.a p / A) • T.b +
        (orient T.a T.b p / A) • T.c := by
      have key := T.orient_smul_sum p
      apply smul_right_injective _ hA'
      simp only [smul_add, smul_smul, mul_div_cancel₀ _ hA']
      exact key.symm
    rw [hp]
    have hsum := T.orient_sum p
    have := (convex_convexHull ℝ ({T.a, T.b, T.c} : Set Point2D)).sum_mem
      (t := Finset.univ) (w := ![orient T.b T.c p / A, orient T.c T.a p / A, orient T.a T.b p / A])
      (z := ![T.a, T.b, T.c]) ?_ ?_ ?_
    · simpa [Fin.sum_univ_three, add_assoc, toSet] using this
    · intro i _
      fin_cases i <;> simp <;> positivity
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      field_simp
      linarith
    · intro i _
      fin_cases i <;> simp [subset_convexHull ℝ _ (by simp : T.a ∈ ({T.a, T.b, T.c} : Set Point2D)),
        subset_convexHull ℝ _ (by simp : T.b ∈ ({T.a, T.b, T.c} : Set Point2D)),
        subset_convexHull ℝ _ (by simp : T.c ∈ ({T.a, T.b, T.c} : Set Point2D))]

/-- A point strictly inside each edge's left side is in the closed triangle. -/
theorem mem_toSet_of_strictContainsTest (h : T.IsCCW) {p : Point2D}
    (hp : T.StrictContainsTest p) : p ∈ T.toSet :=
  (mem_toSet_iff_containsTest h p).mpr ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩

/-- Two edges of a nondegenerate triangle meet only at their shared vertex. -/
theorem segment_inter_segment_eq {a b c : Point2D} (h : orient a b c ≠ 0) :
    segment ℝ a b ∩ segment ℝ b c = {b} := by
  apply Subset.antisymm
  · rintro x ⟨hab, hbc⟩
    have hx := Segment.orient_eq_zero_of_mem ⟨a, b⟩ hab
    obtain ⟨s, -, rfl⟩ := Segment.mem_toSet_iff_exists ⟨b, c⟩ |>.mp hbc
    simp only [orient_lineMap, orient_self₂₃, mul_zero, zero_add] at hx
    have hs : s = 0 := (mul_eq_zero.mp hx).resolve_right h
    simp [hs]
  · rintro x rfl
    exact ⟨right_mem_segment ℝ a x, left_mem_segment ℝ x c⟩

end Triangle

end ComputationalGeometry
