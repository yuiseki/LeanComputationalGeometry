import LeanComputationalGeometry.Triangle
import Mathlib.Topology.Order.IntermediateValue

/-!
# Segments meeting a triangle

Three facts about how a segment can meet a counterclockwise triangle
`T = ⟨a, b, c⟩`, used to cut ears off polygons.

- `exists_onEdge_mem_segment`: going from a point of the triangle to a point
  outside it, a segment reaches the triangle's boundary. The minimum of the
  three edge orientations changes sign along the way, and the intermediate
  value theorem finds where it vanishes.
- `disjoint_toSet_of_avoid`: a segment whose endpoints lie outside the
  triangle and which avoids the edges `a b` and `b c` does not meet the
  triangle at all. It would have to enter and leave through the third edge
  `c a`; it cannot run along that edge's line without touching `a` or `c`,
  and if it crosses the line, just past the crossing it is inside the
  triangle, from where it cannot leave.
- `segment_inter_segment_eq_of_not_mem`: two segments from a common endpoint
  meet only there, unless one contains the other's far endpoint.
-/

namespace ComputationalGeometry

open Set Point2D

namespace Triangle

variable {T : Triangle}

/-- Going from a point of a counterclockwise triangle to a point outside, a
segment reaches the boundary. -/
theorem exists_onEdge_mem_segment (h : T.IsCCW) {x w : Point2D} (hx : x ∈ T.toSet)
    (hw : w ∉ T.toSet) :
    ∃ q ∈ segment ℝ x w, T.ContainsTest q ∧
      (orient T.a T.b q = 0 ∨ orient T.b T.c q = 0 ∨ orient T.c T.a q = 0) := by
  rw [mem_toSet_iff_containsTest h] at hx hw
  set z : ℝ → Point2D := fun t => (1 - t) • x + t • w with hz
  set φ : ℝ → ℝ := fun t =>
    min (orient T.a T.b (z t)) (min (orient T.b T.c (z t)) (orient T.c T.a (z t))) with hφ
  have hcont : Continuous φ := by
    have hl : ∀ u v : Point2D, Continuous fun t => orient u v (z t) := by
      intro u v
      simp only [z, orient_lineMap]
      fun_prop
    exact (hl _ _).min ((hl _ _).min (hl _ _))
  have h0 : 0 ≤ φ 0 := by
    simp only [φ, z, sub_zero, one_smul, zero_smul, add_zero]
    exact le_min hx.1 (le_min hx.2.1 hx.2.2)
  have h1 : φ 1 < 0 := by
    simp only [φ, z, sub_self, zero_smul, one_smul, zero_add]
    by_contra hc
    rw [not_lt] at hc
    exact hw ⟨(le_min_iff.mp hc).1, (le_min_iff.mp (le_min_iff.mp hc).2).1,
      (le_min_iff.mp (le_min_iff.mp hc).2).2⟩
  obtain ⟨t, ht, hφt⟩ :=
    intermediate_value_Icc' zero_le_one hcont.continuousOn ⟨h1.le, h0⟩
  refine ⟨z t, ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩, ?_, ?_⟩
  · have := hφt.ge
    simp only [φ, le_min_iff] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  · have hge : 0 ≤ φ t := hφt.ge
    simp only [φ, le_min_iff] at hge
    have heq : min (orient T.a T.b (z t)) (min (orient T.b T.c (z t)) (orient T.c T.a (z t))) = 0 :=
      hφt
    rcases min_choice (orient T.a T.b (z t)) (min (orient T.b T.c (z t)) (orient T.c T.a (z t)))
      with e | e
    · exact Or.inl (e ▸ heq)
    · rw [e] at heq
      rcases min_choice (orient T.b T.c (z t)) (orient T.c T.a (z t)) with e' | e'
      · exact Or.inr (Or.inl (e' ▸ heq))
      · exact Or.inr (Or.inr (e' ▸ heq))

/-- A point of the boundary of a counterclockwise triangle is on one of its
edges. -/
theorem mem_edges_of_onEdge (h : T.IsCCW) {q : Point2D} (hq : T.ContainsTest q)
    (hz : orient T.a T.b q = 0 ∨ orient T.b T.c q = 0 ∨ orient T.c T.a q = 0) :
    q ∈ segment ℝ T.a T.b ∨ q ∈ segment ℝ T.b T.c ∨ q ∈ segment ℝ T.c T.a :=
  (mem_frontier_toSet_iff_edges h q).mp ((mem_frontier_toSet_iff h q).mpr ⟨hq, hz⟩)

theorem segment_subset_toSet {u v : Point2D} (hu : u ∈ ({T.a, T.b, T.c} : Set Point2D))
    (hv : v ∈ ({T.a, T.b, T.c} : Set Point2D)) : segment ℝ u v ⊆ T.toSet :=
  segment_subset_convexHull hu hv

/-- A segment with both ends outside a counterclockwise triangle that avoids
the edges `a b` and `b c` misses the triangle. -/
theorem disjoint_toSet_of_avoid (h : T.IsCCW) {u w : Point2D} (hu : u ∉ T.toSet)
    (hw : w ∉ T.toSet) (hab : Disjoint (segment ℝ u w) (segment ℝ T.a T.b))
    (hbc : Disjoint (segment ℝ u w) (segment ℝ T.b T.c)) :
    Disjoint (segment ℝ u w) T.toSet := by
  have hA : 0 < orient T.a T.b T.c := h
  rw [Set.disjoint_iff]
  rintro x ⟨hxe, hxT⟩
  have he : Convex ℝ (segment ℝ u w) := convex_segment u w
  have hca : segment ℝ T.c T.a ⊆ T.toSet := segment_subset_toSet (by simp) (by simp)
  have hA_ab : T.a ∈ segment ℝ T.a T.b := left_mem_segment ℝ _ _
  have hC_bc : T.c ∈ segment ℝ T.b T.c := right_mem_segment ℝ _ _
  -- A point of the segment on the triangle's boundary is on the edge `c a`.
  have on_ca : ∀ {q : Point2D}, q ∈ segment ℝ u w → T.ContainsTest q →
      (orient T.a T.b q = 0 ∨ orient T.b T.c q = 0 ∨ orient T.c T.a q = 0) →
      q ∈ segment ℝ T.c T.a := by
    intro q hq hc hz
    rcases mem_edges_of_onEdge h hc hz with h' | h' | h'
    · exact absurd h' (Set.disjoint_left.mp hab hq)
    · exact absurd h' (Set.disjoint_left.mp hbc hq)
    · exact h'
  -- Leaving towards `u`, the segment reaches the edge `c a`.
  obtain ⟨q, hq, hqc, hqz⟩ := exists_onEdge_mem_segment h hxT hu
  have hqe : q ∈ segment ℝ u w := he.segment_subset hxe (left_mem_segment ℝ u w) hq
  have hqca := on_ca hqe hqc hqz
  by_cases hcol : orient T.c T.a u = 0 ∧ orient T.c T.a w = 0
  · -- Along the line of `c a`: then `a` or `c` is on the segment.
    have hint : Intersects ⟨u, w⟩ ⟨T.c, T.a⟩ := ⟨q, hqe, hqca⟩
    rcases (intersects_iff_intersectTest _ _).mp hint with hx | hx | hx | hx | hx
    · have := hx.2
      simp only [Straddles, hcol.1, hcol.2, mul_zero, lt_self_iff_false] at this
    · exact absurd hC_bc (Set.disjoint_left.mp hbc hx)
    · exact absurd hA_ab (Set.disjoint_left.mp hab hx)
    · exact hu (hca hx)
    · exact hw (hca hx)
  · -- Across the line of `c a`: the endpoints straddle it.
    have hqu : q ≠ u := fun e => hu (e ▸ hca hqca)
    have hqw : q ≠ w := fun e => hw (e ▸ hca hqca)
    have hqC : q ≠ T.c := fun e => (Set.disjoint_iff.mp hbc) ⟨hqe, e ▸ hC_bc⟩
    have hqA : q ≠ T.a := fun e => (Set.disjoint_iff.mp hab) ⟨hqe, e ▸ hA_ab⟩
    have hpar : cross (Segment.direction ⟨u, w⟩) (Segment.direction ⟨T.c, T.a⟩) ≠ 0 := by
      intro hc0
      apply hcol
      obtain ⟨t, -, rfl⟩ := (Segment.mem_toSet_iff_exists ⟨u, w⟩).mp hqe
      have hq0 := Segment.orient_eq_zero_of_mem ⟨T.c, T.a⟩ hqca
      simp only [Segment.direction] at hc0 hq0
      simp only [orient_def, cross, x_add, y_add, x_smul, y_smul, x_sub, y_sub] at hc0 hq0 ⊢
      constructor
      · linear_combination hq0 + t * hc0
      · linear_combination hq0 - (1 - t) * hc0
    have hprop : ProperlyIntersect ⟨u, w⟩ ⟨T.c, T.a⟩ :=
      ⟨hpar, q, mem_openSegment_of_ne_left_right hqu.symm hqw.symm hqe,
        mem_openSegment_of_ne_left_right hqC.symm hqA.symm hqca⟩
    have hstr := ((properlyIntersect_iff_crossTest _ _).mp hprop).2
    simp only [Straddles] at hstr
    -- `q` is strictly inside the edge `c a`, so strictly on the inner side of the
    -- other two edges.
    obtain ⟨s, hs, hsq⟩ := (Segment.mem_relInterior_iff_exists ⟨T.c, T.a⟩).mp
      (mem_openSegment_of_ne_left_right hqC.symm hqA.symm hqca)
    have hα : 0 < orient T.b T.c q := by
      rw [← hsq]; simp only [orient_lineMap, orient_self₂₃, mul_zero, zero_add]
      rw [orient_rotate]; exact mul_pos hs.1 hA
    have hγ : 0 < orient T.a T.b q := by
      rw [← hsq]; simp only [orient_lineMap, orient_self₁₃, mul_zero, add_zero]
      exact mul_pos (by linarith [hs.2]) hA
    have hβq : orient T.c T.a q = 0 := Segment.orient_eq_zero_of_mem ⟨T.c, T.a⟩ hqca
    -- The endpoint on the inner side of `c a`.
    obtain ⟨w', hw'e, hw'T, hβw'⟩ : ∃ w' ∈ segment ℝ u w, w' ∉ T.toSet ∧ 0 < orient T.c T.a w' := by
      rcases lt_or_gt_of_ne (show orient T.c T.a u ≠ 0 by rintro e; simp [e] at hstr) with hu' | hu'
      · refine ⟨w, right_mem_segment ℝ u w, hw, ?_⟩
        nlinarith
      · exact ⟨u, left_mem_segment ℝ u w, hu, hu'⟩
    -- Just past `q` towards `w'` the segment is strictly inside the triangle.
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0),
        0 < ε ∧ ε < 1 ∧ 0 < (1 - ε) * orient T.a T.b q + ε * orient T.a T.b w' ∧
          0 < (1 - ε) * orient T.b T.c q + ε * orient T.b T.c w' := by
      have c1 : ∀ k₁ k₂ : ℝ, 0 < k₁ → ∀ᶠ ε in nhds (0 : ℝ), 0 < (1 - ε) * k₁ + ε * k₂ := by
        intro k₁ k₂ hk
        have : Continuous fun ε : ℝ => (1 - ε) * k₁ + ε * k₂ := by fun_prop
        exact this.continuousAt.eventually (lt_mem_nhds (by simpa using hk))
      refine (eventually_mem_nhdsWithin.mono fun ε (hε : ε ∈ Ioi 0) => hε).and
        (((gt_mem_nhds zero_lt_one).and ((c1 _ _ hγ).and (c1 _ _ hα))).filter_mono
          nhdsWithin_le_nhds)
    obtain ⟨ε, hε0, hε1, hγε, hαε⟩ := hev.exists
    set y : Point2D := (1 - ε) • q + ε • w'
    have hye : y ∈ segment ℝ u w :=
      he.segment_subset hqe hw'e ⟨1 - ε, ε, by linarith, hε0.le, by ring, rfl⟩
    have hβy : 0 < orient T.c T.a y := by
      simp only [y, orient_lineMap, hβq, mul_zero, zero_add]
      exact mul_pos hε0 hβw'
    have hyT : y ∈ T.toSet := by
      rw [mem_toSet_iff_containsTest h]
      refine ⟨?_, ?_, hβy.le⟩
      · simp only [y, orient_lineMap]; exact hγε.le
      · simp only [y, orient_lineMap]; exact hαε.le
    -- From there towards `w'` the segment must reach the edge `c a`, where the
    -- orientation against `c a` is `0`; but it stays positive.
    obtain ⟨q', hq', hq'c, hq'z⟩ := exists_onEdge_mem_segment h hyT hw'T
    have hq'e : q' ∈ segment ℝ u w := he.segment_subset hye hw'e hq'
    have hq'ca := on_ca hq'e hq'c hq'z
    have hβq' := Segment.orient_eq_zero_of_mem ⟨T.c, T.a⟩ hq'ca
    obtain ⟨r, hr, rfl⟩ := (Segment.mem_toSet_iff_exists ⟨y, w'⟩).mp hq'
    simp only [orient_lineMap] at hβq'
    rcases hr.1.eq_or_lt with hr0 | hr0
    · subst hr0; simp at hβq'; linarith
    · nlinarith [mul_pos hr0 hβw', mul_nonneg (sub_nonneg.2 hr.2) hβy.le]

/-- Two segments from a common endpoint `a` meet only at `a`, unless one
contains the other's far endpoint. -/
theorem segment_inter_segment_eq_of_not_mem {p a c : Point2D} (hp : p ∉ segment ℝ a c)
    (hc : c ∉ segment ℝ p a) : segment ℝ p a ∩ segment ℝ a c = {a} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨s, hs, rfl⟩ := (Segment.mem_toSet_iff_exists ⟨p, a⟩).mp hx₁
    obtain ⟨t, ht, ht'⟩ := (Segment.mem_toSet_iff_exists ⟨a, c⟩).mp hx₂
    simp only at ht'
    by_contra hne
    rw [mem_singleton_iff] at hne
    have hs1 : s ≠ 1 := by rintro rfl; simp at hne
    have hs1' : 0 < 1 - s := by rcases hs with ⟨-, h⟩; exact lt_of_le_of_ne (by linarith) (by
      intro e; exact hs1 (by linarith))
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht'; exact hne ht'.symm
    have ht0' : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hx := congrArg Point2D.x ht'
    have hy := congrArg Point2D.y ht'
    simp only [x_add, x_smul, y_add, y_smul] at hx hy
    set lam := t / (1 - s)
    have hlam : 0 < lam := div_pos ht0' hs1'
    rcases le_or_gt lam 1 with hl | hl
    · apply hp
      refine ⟨1 - lam, lam, by linarith, hlam.le, by ring, ?_⟩
      apply Point2D.ext
      · simp only [x_add, x_smul, lam]; field_simp; linarith
      · simp only [y_add, y_smul, lam]; field_simp; linarith
    · apply hc
      refine ⟨1 / lam, 1 - 1 / lam, by positivity, ?_, by ring, ?_⟩
      · have : 1 / lam < 1 := by rw [div_lt_one hlam]; exact hl
        linarith
      · apply Point2D.ext
        · simp only [x_add, x_smul, lam]; field_simp; linarith
        · simp only [y_add, y_smul, lam]; field_simp; linarith
  · rintro x rfl
    exact ⟨right_mem_segment ℝ p x, left_mem_segment ℝ x c⟩

end Triangle

end ComputationalGeometry
