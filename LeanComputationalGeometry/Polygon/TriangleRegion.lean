import LeanComputationalGeometry.Polygon.Region

/-!
# A triangle's winding region is the triangle

For a nondegenerate triangle seen as a simple polygon, the region the
winding semantics gives it is the closed triangle, Mathlib's convex hull of
its vertices, and the open region is that triangle's topological interior:

```
Triangle.mem_toRegion_iff     : p ∈ (T.toSimplePolygon h).toRegion ↔ p ∈ T.toSet
Triangle.mem_toOpenRegion_iff : p ∈ (T.toSimplePolygon h).toOpenRegion ↔ p ∈ interior T.toSet
```

This is the first end-to-end check of the region semantics: ray crossings on
one side, convex hulls on the other.

The proof, for a counterclockwise triangle:

- The boundary is the three edges, which is where the point is in the
  triangle and on some edge's line (`onBoundary_toPolygon_iff_onEdge`).
- Off the boundary, the winding number is nonzero exactly at the points
  strictly inside (`winding3_ne_zero_iff`). Whether each vertex lies at or
  below the ray's height decides which edges can count. If all three or none
  do, no edge counts and the point is not inside. Otherwise, after rotating
  the triangle, one vertex `a` is alone on its side, and the two edges at `a`
  are the only ones that can count (`winding3_ne_zero_iff_of_up`,
  `winding3_ne_zero_iff_of_down`). The rest is the identity
  `o_bc (a.y - p.y) + o_ca (b.y - p.y) + o_ab (c.y - p.y) = 0`, the
  y-coordinate of the barycentric formula (`orient_y_identity`).

A clockwise triangle reversed is counterclockwise, with the same convex hull,
the same boundary and the opposite winding number.
-/

namespace ComputationalGeometry

open Set Point2D

namespace Triangle

variable (T : Triangle) (p : Point2D)

/-- The triangle's winding number at `p`, edge by edge. -/
noncomputable def winding3 : ℤ :=
  edgeContribution p T.a T.b + edgeContribution p T.b T.c + edgeContribution p T.c T.a

/-- `p` is in the triangle and on the line of an edge: the frontier. -/
def OnEdge : Prop :=
  T.ContainsTest p ∧ (orient T.a T.b p = 0 ∨ orient T.b T.c p = 0 ∨ orient T.c T.a p = 0)

theorem windingNumber_toPolygon : T.toPolygon.windingNumber p = T.winding3 p := by
  show ∑ i : Fin 3, edgeContribution p (![T.a, T.b, T.c] i) (![T.a, T.b, T.c] (finRotate 3 i)) = _
  rw [Fin.sum_univ_three]
  simp [winding3]

theorem onBoundary_toPolygon_iff :
    T.toPolygon.OnBoundary p ↔
      p ∈ segment ℝ T.a T.b ∨ p ∈ segment ℝ T.b T.c ∨ p ∈ segment ℝ T.c T.a := by
  constructor
  · rintro ⟨i, hi⟩
    change Fin 3 at i
    fin_cases i <;> simp [RawPolygon.edge, RawPolygon.next, Segment.toSet, toPolygon] at hi <;> tauto
  · rintro (h | h | h)
    · exact ⟨(0 : Fin 3), by simpa [RawPolygon.edge, RawPolygon.next, Segment.toSet, toPolygon]⟩
    · exact ⟨(1 : Fin 3), by simpa [RawPolygon.edge, RawPolygon.next, Segment.toSet, toPolygon]⟩
    · exact ⟨(2 : Fin 3), by simpa [RawPolygon.edge, RawPolygon.next, Segment.toSet, toPolygon]⟩

theorem winding3_rotate : T.rotate.winding3 p = T.winding3 p := by
  simp only [winding3, rotate_a, rotate_b, rotate_c]
  ring

theorem onEdge_rotate : T.rotate.OnEdge p ↔ T.OnEdge p := by
  simp only [OnEdge, containsTest_rotate, rotate_a, rotate_b, rotate_c]
  tauto

/-- The y-coordinate of the barycentric formula, relative to `p`. -/
theorem orient_y_identity :
    orient T.b T.c p * (T.a.y - p.y) + orient T.c T.a p * (T.b.y - p.y) +
      orient T.a T.b p * (T.c.y - p.y) = 0 := by
  simp only [orient_def]
  ring

variable {T p}

/-- One vertex at or below the ray's height, two above. -/
theorem winding3_ne_zero_iff_of_up (h : T.IsCCW) (hnb : ¬ T.OnEdge p) (ha : T.a.y ≤ p.y)
    (hb : p.y < T.b.y) (hc : p.y < T.c.y) : T.winding3 p ≠ 0 ↔ T.StrictContainsTest p := by
  have hA : 0 < orient T.a T.b T.c := h
  have hid := T.orient_y_identity p
  have hsum := T.orient_sum p
  have hsum' : orient T.b T.c p + orient T.c T.a p + orient T.a T.b p = orient T.a T.b T.c := hsum
  unfold winding3
  rw [edgeContribution_of_up ha hb, edgeContribution_of_above hb hc, edgeContribution_of_down hc ha]
  constructor
  · intro hw
    by_cases h₁ : 0 < orient T.a T.b p <;> by_cases h₃ : orient T.c T.a p < 0
    · simp [h₁, h₃] at hw
    · have h₃' : 0 ≤ orient T.c T.a p := not_lt.mp h₃
      have h₂ : 0 < orient T.b T.c p := by
        by_contra h₂
        have h₂' : orient T.b T.c p ≤ 0 := not_lt.mp h₂
        nlinarith [mul_nonneg_of_nonpos_of_nonpos h₂' (sub_nonpos.mpr ha),
          mul_nonneg h₃' (sub_pos.mpr hb).le, mul_pos h₁ (sub_pos.mpr hc)]
      refine ⟨h₁, h₂, lt_of_le_of_ne h₃' fun h₃'' => hnb ⟨⟨h₁.le, h₂.le, h₃'⟩, ?_⟩⟩
      exact Or.inr (Or.inr h₃''.symm)
    · exfalso
      have h₁' : orient T.a T.b p ≤ 0 := not_lt.mp h₁
      have h₂ : orient T.b T.c p < 0 := by
        by_contra h₂
        have h₂' : 0 ≤ orient T.b T.c p := not_lt.mp h₂
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h₂' (sub_nonpos.mpr ha),
          mul_neg_of_neg_of_pos h₃ (sub_pos.mpr hb), mul_nonpos_of_nonpos_of_nonneg h₁' (sub_pos.mpr hc).le]
      linarith
    · simp [h₁, h₃] at hw
  · intro hs
    simp [hs.1, not_lt.mpr hs.2.2.le]

/-- One vertex above the ray's height, two at or below. -/
theorem winding3_ne_zero_iff_of_down (h : T.IsCCW) (hnb : ¬ T.OnEdge p) (ha : p.y < T.a.y)
    (hb : T.b.y ≤ p.y) (hc : T.c.y ≤ p.y) : T.winding3 p ≠ 0 ↔ T.StrictContainsTest p := by
  have hA : 0 < orient T.a T.b T.c := h
  have hid := T.orient_y_identity p
  have hsum' : orient T.b T.c p + orient T.c T.a p + orient T.a T.b p = orient T.a T.b T.c :=
    T.orient_sum p
  unfold winding3
  rw [edgeContribution_of_down ha hb, edgeContribution_of_below hb hc, edgeContribution_of_up hc ha]
  constructor
  · intro hw
    by_cases h₁ : orient T.a T.b p < 0 <;> by_cases h₃ : 0 < orient T.c T.a p
    · simp [h₁, h₃] at hw
    · exfalso
      have h₃' : orient T.c T.a p ≤ 0 := not_lt.mp h₃
      have h₂ : orient T.b T.c p ≤ 0 := by
        by_contra h₂
        have h₂' : 0 < orient T.b T.c p := not_le.mp h₂
        nlinarith [mul_pos h₂' (sub_pos.mpr ha), mul_nonneg_of_nonpos_of_nonpos h₃' (sub_nonpos.mpr hb),
          mul_nonneg_of_nonpos_of_nonpos h₁.le (sub_nonpos.mpr hc)]
      linarith
    · have h₁' : 0 ≤ orient T.a T.b p := not_lt.mp h₁
      have h₂ : 0 ≤ orient T.b T.c p := by
        by_contra h₂
        have h₂' : orient T.b T.c p < 0 := not_le.mp h₂
        nlinarith [mul_neg_of_neg_of_pos h₂' (sub_pos.mpr ha),
          mul_nonpos_of_nonneg_of_nonpos h₃.le (sub_nonpos.mpr hb),
          mul_nonpos_of_nonneg_of_nonpos h₁' (sub_nonpos.mpr hc)]
      have hc' : T.ContainsTest p := ⟨h₁', h₂, h₃.le⟩
      refine ⟨lt_of_le_of_ne h₁' fun e => hnb ⟨hc', Or.inl e.symm⟩,
        lt_of_le_of_ne h₂ fun e => hnb ⟨hc', Or.inr (Or.inl e.symm)⟩, h₃⟩
    · simp [h₁, h₃] at hw
  · intro hs
    simp [hs.2.2, not_lt.mpr hs.1.le]

/-- No vertex above the ray's height: nothing counts, and `p` is not inside. -/
theorem winding3_ne_zero_iff_of_below (h : T.IsCCW) (ha : T.a.y ≤ p.y) (hb : T.b.y ≤ p.y)
    (hc : T.c.y ≤ p.y) : T.winding3 p ≠ 0 ↔ T.StrictContainsTest p := by
  have hA : 0 < orient T.a T.b T.c := h
  have hid := T.orient_y_identity p
  unfold winding3
  rw [edgeContribution_of_below ha hb, edgeContribution_of_below hb hc,
    edgeContribution_of_below hc ha]
  simp only [add_zero, ne_eq, not_true_eq_false, false_iff]
  rintro ⟨h₁, h₂, h₃⟩
  have t₁ := mul_nonpos_of_nonneg_of_nonpos h₂.le (sub_nonpos.mpr ha)
  have t₂ := mul_nonpos_of_nonneg_of_nonpos h₃.le (sub_nonpos.mpr hb)
  have t₃ := mul_nonpos_of_nonneg_of_nonpos h₁.le (sub_nonpos.mpr hc)
  have ea : T.a.y = p.y := by
    have : orient T.b T.c p * (T.a.y - p.y) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left h₂.ne'
    linarith
  have eb : T.b.y = p.y := by
    have : orient T.c T.a p * (T.b.y - p.y) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left h₃.ne'
    linarith
  have ec : T.c.y = p.y := by
    have : orient T.a T.b p * (T.c.y - p.y) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left h₁.ne'
    linarith
  rw [orient_def, ea, eb, ec] at hA
  simp at hA

/-- Every vertex above the ray's height: nothing counts, and `p` is not
inside. -/
theorem winding3_ne_zero_iff_of_above (ha : p.y < T.a.y) (hb : p.y < T.b.y) (hc : p.y < T.c.y) :
    T.winding3 p ≠ 0 ↔ T.StrictContainsTest p := by
  have hid := T.orient_y_identity p
  unfold winding3
  rw [edgeContribution_of_above ha hb, edgeContribution_of_above hb hc,
    edgeContribution_of_above hc ha]
  simp only [add_zero, ne_eq, not_true_eq_false, false_iff]
  rintro ⟨h₁, h₂, h₃⟩
  nlinarith [mul_pos h₂ (sub_pos.mpr ha), mul_pos h₃ (sub_pos.mpr hb), mul_pos h₁ (sub_pos.mpr hc)]

/-- Off the boundary of a counterclockwise triangle, the winding number is
nonzero exactly at the points strictly inside. -/
theorem winding3_ne_zero_iff (h : T.IsCCW) (hnb : ¬ T.OnEdge p) :
    T.winding3 p ≠ 0 ↔ T.StrictContainsTest p := by
  have h₁ : T.rotate.IsCCW := isCCW_rotate.mpr h
  have h₂ : T.rotate.rotate.IsCCW := isCCW_rotate.mpr h₁
  have n₁ : ¬ T.rotate.OnEdge p := by rwa [onEdge_rotate]
  have n₂ : ¬ T.rotate.rotate.OnEdge p := by rwa [onEdge_rotate, onEdge_rotate]
  have r₁ : (T.rotate.winding3 p ≠ 0 ↔ T.rotate.StrictContainsTest p) ↔
      (T.winding3 p ≠ 0 ↔ T.StrictContainsTest p) := by
    rw [winding3_rotate, strictContainsTest_rotate]
  have r₂ : (T.rotate.rotate.winding3 p ≠ 0 ↔ T.rotate.rotate.StrictContainsTest p) ↔
      (T.winding3 p ≠ 0 ↔ T.StrictContainsTest p) := by
    rw [winding3_rotate, winding3_rotate, strictContainsTest_rotate, strictContainsTest_rotate]
  rcases le_or_gt T.a.y p.y with ha | ha <;> rcases le_or_gt T.b.y p.y with hb | hb <;>
    rcases le_or_gt T.c.y p.y with hc | hc
  · exact winding3_ne_zero_iff_of_below h ha hb hc
  · exact r₂.mp (winding3_ne_zero_iff_of_down h₂ n₂ hc ha hb)
  · exact r₁.mp (winding3_ne_zero_iff_of_down h₁ n₁ hb hc ha)
  · exact winding3_ne_zero_iff_of_up h hnb ha hb hc
  · exact winding3_ne_zero_iff_of_down h hnb ha hb hc
  · exact r₁.mp (winding3_ne_zero_iff_of_up h₁ n₁ hb hc ha)
  · exact r₂.mp (winding3_ne_zero_iff_of_up h₂ n₂ hc ha hb)
  · exact winding3_ne_zero_iff_of_above ha hb hc

/-- Strictly inside a counterclockwise triangle the winding number is `1`. -/
theorem winding3_eq_one (h : T.IsCCW) (hs : T.StrictContainsTest p) : T.winding3 p = 1 := by
  have up : ∀ {T : Triangle}, T.StrictContainsTest p → T.a.y ≤ p.y → p.y < T.b.y →
      p.y < T.c.y → T.winding3 p = 1 := by
    intro T hs ha hb hc
    unfold winding3
    rw [edgeContribution_of_up ha hb, edgeContribution_of_above hb hc,
      edgeContribution_of_down hc ha]
    simp [hs.1, not_lt.mpr hs.2.2.le]
  have down : ∀ {T : Triangle}, T.StrictContainsTest p → p.y < T.a.y → T.b.y ≤ p.y →
      T.c.y ≤ p.y → T.winding3 p = 1 := by
    intro T hs ha hb hc
    unfold winding3
    rw [edgeContribution_of_down ha hb, edgeContribution_of_below hb hc,
      edgeContribution_of_up hc ha]
    simp [hs.2.2, not_lt.mpr hs.1.le]
  have s₁ : T.rotate.StrictContainsTest p := strictContainsTest_rotate.mpr hs
  have s₂ : T.rotate.rotate.StrictContainsTest p := strictContainsTest_rotate.mpr s₁
  have r₁ : T.rotate.winding3 p = T.winding3 p := winding3_rotate T p
  have r₂ : T.rotate.rotate.winding3 p = T.winding3 p := by rw [winding3_rotate, winding3_rotate]
  rcases le_or_gt T.a.y p.y with ha | ha <;> rcases le_or_gt T.b.y p.y with hb | hb <;>
    rcases le_or_gt T.c.y p.y with hc | hc
  · have := (winding3_ne_zero_iff_of_below h ha hb hc).mpr hs
    unfold winding3 at this
    rw [edgeContribution_of_below ha hb, edgeContribution_of_below hb hc,
      edgeContribution_of_below hc ha] at this
    simp at this
  · rw [← r₂]; exact down s₂ hc ha hb
  · rw [← r₁]; exact down s₁ hb hc ha
  · exact up hs ha hb hc
  · exact down hs ha hb hc
  · rw [← r₁]; exact up s₁ hb hc ha
  · rw [← r₂]; exact up s₂ hc ha hb
  · have := (winding3_ne_zero_iff_of_above ha hb hc).mpr hs
    unfold winding3 at this
    rw [edgeContribution_of_above ha hb, edgeContribution_of_above hb hc,
      edgeContribution_of_above hc ha] at this
    simp at this

/-! ## The regions of a counterclockwise triangle -/

theorem onBoundary_toPolygon_iff_onEdge (h : T.IsCCW) : T.toPolygon.OnBoundary p ↔ T.OnEdge p := by
  rw [onBoundary_toPolygon_iff, ← mem_frontier_toSet_iff_edges h, mem_frontier_toSet_iff h]
  rfl

theorem mem_region_toPolygon_iff_of_isCCW (h : T.IsCCW) : p ∈ T.toPolygon.region ↔ p ∈ T.toSet := by
  rw [mem_toSet_iff_containsTest h]
  show T.toPolygon.OnBoundary p ∨ T.toPolygon.windingNumber p ≠ 0 ↔ _
  rw [onBoundary_toPolygon_iff_onEdge h, windingNumber_toPolygon]
  constructor
  · rintro (hb | hw)
    · exact hb.1
    · by_cases hb : T.OnEdge p
      · exact hb.1
      · obtain ⟨h₁, h₂, h₃⟩ := (winding3_ne_zero_iff h hb).mp hw
        exact ⟨h₁.le, h₂.le, h₃.le⟩
  · intro hc
    by_cases hb : T.OnEdge p
    · exact Or.inl hb
    · right
      refine (winding3_ne_zero_iff h hb).mpr ⟨?_, ?_, ?_⟩
      · exact lt_of_le_of_ne hc.1 fun e => hb ⟨hc, Or.inl e.symm⟩
      · exact lt_of_le_of_ne hc.2.1 fun e => hb ⟨hc, Or.inr (Or.inl e.symm)⟩
      · exact lt_of_le_of_ne hc.2.2 fun e => hb ⟨hc, Or.inr (Or.inr e.symm)⟩

theorem mem_openRegion_toPolygon_iff_of_isCCW (h : T.IsCCW) :
    p ∈ T.toPolygon.openRegion ↔ p ∈ interior T.toSet := by
  rw [mem_interior_toSet_iff h]
  show ¬ T.toPolygon.OnBoundary p ∧ T.toPolygon.windingNumber p ≠ 0 ↔ _
  rw [onBoundary_toPolygon_iff_onEdge h, windingNumber_toPolygon]
  constructor
  · rintro ⟨hb, hw⟩
    exact (winding3_ne_zero_iff h hb).mp hw
  · intro hs
    have hb : ¬ T.OnEdge p := by
      rintro ⟨-, e | e | e⟩
      · exact hs.1.ne' e
      · exact hs.2.1.ne' e
      · exact hs.2.2.ne' e
    exact ⟨hb, (winding3_ne_zero_iff h hb).mpr hs⟩

/-! ## Clockwise triangles -/

theorem toSet_reverse (T : Triangle) : T.reverse.toSet = T.toSet := by
  unfold toSet
  congr 1
  ext; simp only [reverse, mem_insert_iff, mem_singleton_iff]; tauto

theorem winding3_reverse (T : Triangle) (p : Point2D) : T.reverse.winding3 p = -T.winding3 p := by
  simp only [winding3, reverse, edgeContribution_swap p T.a T.c, edgeContribution_swap p T.c T.b,
    edgeContribution_swap p T.b T.a]
  ring

theorem onBoundary_toPolygon_reverse (T : Triangle) (p : Point2D) :
    T.reverse.toPolygon.OnBoundary p ↔ T.toPolygon.OnBoundary p := by
  rw [onBoundary_toPolygon_iff, onBoundary_toPolygon_iff]
  simp only [reverse]
  rw [segment_symm ℝ T.a T.c, segment_symm ℝ T.c T.b, segment_symm ℝ T.b T.a]
  tauto

theorem region_toPolygon_reverse (T : Triangle) : T.reverse.toPolygon.region = T.toPolygon.region := by
  ext p
  show T.reverse.toPolygon.OnBoundary p ∨ T.reverse.toPolygon.windingNumber p ≠ 0 ↔
    T.toPolygon.OnBoundary p ∨ T.toPolygon.windingNumber p ≠ 0
  rw [onBoundary_toPolygon_reverse, windingNumber_toPolygon, windingNumber_toPolygon,
    winding3_reverse, ne_eq, neg_eq_zero]

theorem openRegion_toPolygon_reverse (T : Triangle) :
    T.reverse.toPolygon.openRegion = T.toPolygon.openRegion := by
  ext p
  show ¬ T.reverse.toPolygon.OnBoundary p ∧ T.reverse.toPolygon.windingNumber p ≠ 0 ↔
    ¬ T.toPolygon.OnBoundary p ∧ T.toPolygon.windingNumber p ≠ 0
  rw [onBoundary_toPolygon_reverse, windingNumber_toPolygon, windingNumber_toPolygon,
    winding3_reverse, ne_eq, neg_eq_zero]

theorem isCCW_reverse_of_signedArea2_neg {T : Triangle} (h : T.signedArea2 < 0) : T.reverse.IsCCW := by
  rw [IsCCW, signedArea2_reverse]
  linarith

/-! ## Every nondegenerate triangle -/

theorem mem_region_toPolygon_iff (h : T.Nondegenerate) : p ∈ T.toPolygon.region ↔ p ∈ T.toSet := by
  rcases lt_or_gt_of_ne h with hn | hp
  · rw [← region_toPolygon_reverse, ← toSet_reverse]
    exact mem_region_toPolygon_iff_of_isCCW (isCCW_reverse_of_signedArea2_neg hn)
  · exact mem_region_toPolygon_iff_of_isCCW hp

theorem mem_openRegion_toPolygon_iff (h : T.Nondegenerate) :
    p ∈ T.toPolygon.openRegion ↔ p ∈ interior T.toSet := by
  rcases lt_or_gt_of_ne h with hn | hp
  · rw [← openRegion_toPolygon_reverse, ← toSet_reverse]
    exact mem_openRegion_toPolygon_iff_of_isCCW (isCCW_reverse_of_signedArea2_neg hn)
  · exact mem_openRegion_toPolygon_iff_of_isCCW hp

/-- A nondegenerate triangle as a simple polygon. -/
noncomputable def toSimplePolygon (T : Triangle) (h : T.Nondegenerate) : SimplePolygon :=
  ⟨T.toPolygon, isSimple_toPolygon h⟩

/-- The winding region of a nondegenerate triangle is the closed triangle. -/
theorem mem_toRegion_iff (h : T.Nondegenerate) :
    p ∈ (T.toSimplePolygon h).toRegion ↔ p ∈ T.toSet :=
  mem_region_toPolygon_iff h

/-- Its open winding region is the triangle's topological interior. -/
theorem mem_toOpenRegion_iff (h : T.Nondegenerate) :
    p ∈ (T.toSimplePolygon h).toOpenRegion ↔ p ∈ interior T.toSet :=
  mem_openRegion_toPolygon_iff h

theorem toRegion_eq (T : Triangle) (h : T.Nondegenerate) : (T.toSimplePolygon h).toRegion = T.toSet :=
  Set.ext fun _ => mem_toRegion_iff h

theorem toOpenRegion_eq (T : Triangle) (h : T.Nondegenerate) :
    (T.toSimplePolygon h).toOpenRegion = interior T.toSet :=
  Set.ext fun _ => mem_toOpenRegion_iff h

end Triangle

end ComputationalGeometry
