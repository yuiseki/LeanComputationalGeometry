import LeanComputationalGeometry.Segment
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.Algebra.Order.Field

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
(`mem_toSet_iff_containsTest`). Its topological interior and frontier, in
Mathlib's sense, are read the same way:

- strictly inside: `p ∈ interior T.toSet` exactly when every edge has
  `orient > 0` (`mem_interior_toSet_iff`);
- on the boundary: `p ∈ frontier T.toSet` exactly when `p` is in the triangle
  and some edge has `orient = 0` (`mem_frontier_toSet_iff`), which is being on
  one of the three edge segments (`mem_frontier_toSet_iff_edges`). The proof goes through barycentric
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

/-! ## Edges, interior and frontier -/

/-- The same triangle, starting from the second vertex. -/
def rotate (T : Triangle) : Triangle := ⟨T.b, T.c, T.a⟩

@[simp] theorem rotate_a (T : Triangle) : T.rotate.a = T.b := rfl
@[simp] theorem rotate_b (T : Triangle) : T.rotate.b = T.c := rfl
@[simp] theorem rotate_c (T : Triangle) : T.rotate.c = T.a := rfl

theorem toSet_rotate (T : Triangle) : T.rotate.toSet = T.toSet := by
  unfold toSet
  congr 1
  ext; simp only [rotate_a, rotate_b, rotate_c, mem_insert_iff, mem_singleton_iff]; tauto

theorem signedArea2_rotate (T : Triangle) : T.rotate.signedArea2 = T.signedArea2 :=
  orient_rotate _ _ _

theorem isCCW_rotate {T : Triangle} : T.rotate.IsCCW ↔ T.IsCCW := by
  rw [IsCCW, IsCCW, signedArea2_rotate]

theorem containsTest_rotate {T : Triangle} {p : Point2D} :
    T.rotate.ContainsTest p ↔ T.ContainsTest p := by
  simp only [ContainsTest, rotate_a, rotate_b, rotate_c]; tauto

theorem strictContainsTest_rotate {T : Triangle} {p : Point2D} :
    T.rotate.StrictContainsTest p ↔ T.StrictContainsTest p := by
  simp only [StrictContainsTest, rotate_a, rotate_b, rotate_c]; tauto

/-- For a counterclockwise triangle, a point is on the edge from `a` to `b`
exactly when it is on that edge's line and on the inner side of the other
two. -/
theorem mem_segment_iff_of_isCCW (h : T.IsCCW) (p : Point2D) :
    p ∈ segment ℝ T.a T.b ↔ orient T.a T.b p = 0 ∧ 0 ≤ orient T.b T.c p ∧ 0 ≤ orient T.c T.a p := by
  have hA : 0 < orient T.a T.b T.c := h
  constructor
  · intro hp
    obtain ⟨t, ht, rfl⟩ := Segment.mem_toSet_iff_exists ⟨T.a, T.b⟩ |>.mp hp
    refine ⟨Segment.orient_eq_zero_of_mem ⟨T.a, T.b⟩ hp, ?_, ?_⟩
    · dsimp only
      rw [orient_lineMap, orient_self₁₃, orient_rotate]
      nlinarith [ht.2]
    · dsimp only
      rw [orient_lineMap, orient_self₂₃]
      have : orient T.c T.a T.b = orient T.a T.b T.c := by rw [orient_rotate, orient_rotate]
      rw [this]
      nlinarith [ht.1]
  · rintro ⟨h₀, h₁, h₂⟩
    have hA' : T.signedArea2 ≠ 0 := hA.ne'
    have key := T.orient_smul_sum p
    have hsum := T.orient_sum p
    rw [h₀, zero_smul, add_zero] at key
    rw [h₀, add_zero] at hsum
    refine ⟨orient T.b T.c p / T.signedArea2, orient T.c T.a p / T.signedArea2,
      div_nonneg h₁ hA.le, div_nonneg h₂ hA.le, ?_, ?_⟩
    · rw [← add_div, hsum, div_self hA']
    · apply smul_right_injective _ hA'
      simp only [smul_add, smul_smul]
      rw [mul_div_cancel₀ _ hA', mul_div_cancel₀ _ hA']
      exact key

/-- The closed triangle is the set its test describes. -/
theorem toSet_eq_containsTest (h : T.IsCCW) : T.toSet = {p | T.ContainsTest p} :=
  Set.ext fun p => mem_toSet_iff_containsTest h p

theorem isClosed_toSet (h : T.IsCCW) : IsClosed T.toSet := by
  rw [toSet_eq_containsTest h]
  exact ((isClosed_le continuous_const (continuous_orient _ _)).inter
    ((isClosed_le continuous_const (continuous_orient _ _)).inter
      (isClosed_le continuous_const (continuous_orient _ _))))

/-- A point in the interior of a set lying on the left of a line, or on it, is
strictly on the left. -/
theorem pos_of_mem_interior {a b p : Point2D} (hab : a ≠ b) {S : Set Point2D}
    (hS : S ⊆ {q | 0 ≤ orient a b q}) (hp : p ∈ interior S) : 0 < orient a b p := by
  have h0 : 0 ≤ orient a b p := hS (interior_subset hp)
  rcases h0.lt_or_eq with hpos | hzero
  · exact hpos
  exfalso
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  set u := b - a
  set w : Point2D := Point2D.mk (-u.y) u.x
  have hu : u ≠ 0 := sub_ne_zero.mpr hab.symm
  have hcw : 0 < cross u w := by
    have : u.x ≠ 0 ∨ u.y ≠ 0 := by
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hu (Point2D.ext (by simp [hc.1]) (by simp [hc.2]))
    simp only [cross, w, x_mk, y_mk]
    rcases this with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u.y]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u.x]
  set t := ε / (2 * (‖w‖ + 1))
  have ht : 0 < t := by positivity
  have hq : p + (-t) • w ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_neg,
      Real.norm_of_nonneg ht.le]
    have : t * ‖w‖ < ε := by
      have h1 : t * ‖w‖ ≤ t * (‖w‖ + 1) := by nlinarith [norm_nonneg w]
      have h2 : t * (‖w‖ + 1) = ε / 2 := by
        simp only [t]; field_simp
      linarith
    exact this
  have := hS (hball hq)
  simp only [mem_ofPred_eq, orient_add, ← hzero, cross_smul_right] at this
  nlinarith

/-- For a counterclockwise triangle, a point is in its topological interior
exactly when it is strictly on the left of every edge. -/
theorem mem_interior_toSet_iff (h : T.IsCCW) (p : Point2D) :
    p ∈ interior T.toSet ↔ T.StrictContainsTest p := by
  have hA : 0 < orient T.a T.b T.c := h
  have hne : ∀ {u v w : Point2D}, 0 < orient u v w → u ≠ v := by
    rintro u v w huvw rfl; simp at huvw
  have sub : T.toSet ⊆ {q | T.ContainsTest q} := (toSet_eq_containsTest h).le
  constructor
  · intro hp
    refine ⟨pos_of_mem_interior (hne hA) (fun q hq => (sub hq).1) hp,
      pos_of_mem_interior (hne (show 0 < orient T.b T.c T.a by rwa [orient_rotate]))
        (fun q hq => (sub hq).2.1) hp,
      pos_of_mem_interior (hne (show 0 < orient T.c T.a T.b by rwa [orient_rotate, orient_rotate]))
        (fun q hq => (sub hq).2.2) hp⟩
  · intro hp
    have hmem : p ∈ {q | 0 < orient T.a T.b q} ∩
        ({q | 0 < orient T.b T.c q} ∩ {q | 0 < orient T.c T.a q}) := ⟨hp.1, hp.2.1, hp.2.2⟩
    refine interior_maximal ?_ ?_ hmem
    · intro q hq
      exact (mem_toSet_iff_containsTest h q).mpr ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩
    · exact (isOpen_lt continuous_const (continuous_orient _ _)).inter
        ((isOpen_lt continuous_const (continuous_orient _ _)).inter
          (isOpen_lt continuous_const (continuous_orient _ _)))

/-- For a counterclockwise triangle, a point is on its frontier exactly when
it is in the triangle and on the line of some edge. -/
theorem mem_frontier_toSet_iff (h : T.IsCCW) (p : Point2D) :
    p ∈ frontier T.toSet ↔
      T.ContainsTest p ∧ (orient T.a T.b p = 0 ∨ orient T.b T.c p = 0 ∨ orient T.c T.a p = 0) := by
  rw [frontier, (isClosed_toSet h).closure_eq, mem_sdiff, mem_interior_toSet_iff h,
    mem_toSet_iff_containsTest h]
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    by_contra hz
    simp only [not_or] at hz
    exact hs ⟨lt_of_le_of_ne hc.1 (Ne.symm hz.1), lt_of_le_of_ne hc.2.1 (Ne.symm hz.2.1),
      lt_of_le_of_ne hc.2.2 (Ne.symm hz.2.2)⟩
  · rintro ⟨hc, hz⟩
    refine ⟨hc, fun hs => ?_⟩
    rcases hz with hz | hz | hz
    · exact hs.1.ne' hz
    · exact hs.2.1.ne' hz
    · exact hs.2.2.ne' hz

/-- For a counterclockwise triangle, the frontier is the three edges. -/
theorem mem_frontier_toSet_iff_edges (h : T.IsCCW) (p : Point2D) :
    p ∈ frontier T.toSet ↔
      p ∈ segment ℝ T.a T.b ∨ p ∈ segment ℝ T.b T.c ∨ p ∈ segment ℝ T.c T.a := by
  have h' : T.rotate.IsCCW := isCCW_rotate.mpr h
  have h'' : T.rotate.rotate.IsCCW := isCCW_rotate.mpr h'
  rw [mem_frontier_toSet_iff h, mem_segment_iff_of_isCCW h,
    show segment ℝ T.b T.c = segment ℝ T.rotate.a T.rotate.b from rfl,
    mem_segment_iff_of_isCCW h',
    show segment ℝ T.c T.a = segment ℝ T.rotate.rotate.a T.rotate.rotate.b from rfl,
    mem_segment_iff_of_isCCW h'']
  simp only [rotate_a, rotate_b, rotate_c, ContainsTest]
  constructor
  · rintro ⟨⟨h₁, h₂, h₃⟩, hz | hz | hz⟩
    · exact Or.inl ⟨hz, h₂, h₃⟩
    · exact Or.inr (Or.inl ⟨hz, h₃, h₁⟩)
    · exact Or.inr (Or.inr ⟨hz, h₁, h₂⟩)
  · rintro (⟨hz, h₂, h₃⟩ | ⟨hz, h₃, h₁⟩ | ⟨hz, h₁, h₂⟩)
    · exact ⟨⟨hz.ge, h₂, h₃⟩, Or.inl hz⟩
    · exact ⟨⟨h₁, hz.ge, h₃⟩, Or.inr (Or.inl hz)⟩
    · exact ⟨⟨h₁, h₂, hz.ge⟩, Or.inr (Or.inr hz)⟩

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
