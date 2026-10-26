import LeanComputationalGeometry.Polygon.Region

/-!
# The winding number off the boundary is locally constant

An edge's contribution to the winding number is not locally constant on its
own: where the ray from `p` runs through a vertex, moving `p` up or down hands
the count from one edge at that vertex to the other. The sum is, and the
proof makes the hand-over explicit.

Fix `p` off the edge from `a` to `b`. Near `p`, the contribution at `q` is
`(atOrBelow q a - atOrBelow q b) * crossRight p a b`
(`edgeContribution_eventually_eq`): the edge counts when its ends lie on
either side of the ray's height, with a sign telling which way it goes, and
`crossRight p a b`, which depends on `p` only, says whether it crosses to the
right of `p`. Summed around the ring and regrouped by vertices, the winding
number near `p` is `∑ atOrBelow q (vertex i) * (crossRight of edge i - crossRight
of edge (prev i))`. A vertex off the ray's height is on the same side of `q`
as of `p` for `q` near `p`; for a vertex at the ray's height, both edges at it
cross to the right exactly when it is to the right of `p`, so its term
vanishes. Hence the winding number does not change near `p`
(`windingNumber_eventually_eq`).

Consequences: it is continuous off the boundary, it is constant on preconnected
sets avoiding the boundary (`windingNumber_eq_of_isPreconnected`), the
boundary and the closed region are closed, and the open region is open.

The same regrouping, with one edge set aside, shows that the winding number
goes up by one across an edge from right to left (`windingNumber_jump`).
-/

namespace ComputationalGeometry

open Set Point2D Filter Topology

/-- `1` if `v` is at or below the height of `q`, else `0`. -/
noncomputable def atOrBelow (q v : Point2D) : ℤ := by
  classical exact if v.y ≤ q.y then 1 else 0

open Classical in
/-- Whether the edge from `a` to `b` crosses the height of `p` to the right of
`p`: `1` or `0`. An end at the height of `p` crosses there. -/
noncomputable def crossRight (p a b : Point2D) : ℤ :=
  if a.y = p.y then (if p.x < a.x then 1 else 0)
  else if b.y = p.y then (if p.x < b.x then 1 else 0)
  else if a.y < b.y then (if 0 < orient a b p then 1 else 0)
  else (if orient a b p < 0 then 1 else 0)

theorem atOrBelow_of_le {q v : Point2D} (h : v.y ≤ q.y) : atOrBelow q v = 1 := by
  simp [atOrBelow, h]

theorem atOrBelow_of_lt {q v : Point2D} (h : q.y < v.y) : atOrBelow q v = 0 := by
  simp [atOrBelow, not_le.mpr h]

/-- A point on the line of a non-horizontal segment, at a height between its
ends, is on it. -/
theorem mem_segment_of_orient_eq_zero {a b p : Point2D} (h : orient a b p = 0) (hab : a.y ≠ b.y)
    (hy : p.y ∈ uIcc a.y b.y) : p ∈ segment ℝ a b := by
  have hd : b.y - a.y ≠ 0 := sub_ne_zero.mpr hab.symm
  set t := (p.y - a.y) / (b.y - a.y) with ht
  have ht01 : 0 ≤ t ∧ t ≤ 1 := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · rw [uIcc_of_le hlt.le] at hy
      have hpos : 0 < b.y - a.y := by linarith
      exact ⟨div_nonneg (by linarith [hy.1]) hpos.le,
        (div_le_one hpos).mpr (by linarith [hy.2])⟩
    · rw [uIcc_of_ge hgt.le] at hy
      have hneg : b.y - a.y < 0 := by linarith
      exact ⟨div_nonneg_of_nonpos (by linarith [hy.2]) hneg.le,
        (div_le_one_of_neg hneg).mpr (by linarith [hy.1])⟩
  refine ⟨1 - t, t, by linarith, ht01.1, by ring, ?_⟩
  have hty : t * (b.y - a.y) = p.y - a.y := by rw [ht]; field_simp
  rw [orient_def] at h
  apply Point2D.ext
  · simp only [x_add, x_smul]
    have : t * (b.y - a.y) * (b.x - a.x) = (b.y - a.y) * (p.x - a.x) := by
      rw [hty]; linarith
    have hx : t * (b.x - a.x) = p.x - a.x := by
      apply mul_left_cancel₀ hd; linarith
    linarith
  · simp only [y_add, y_smul]
    linarith

/-- On the height of `p`, a horizontal segment avoiding `p` lies on one side
of it. -/
theorem lt_x_iff_of_horizontal {a b p : Point2D} (ha : a.y = p.y) (hb : b.y = p.y)
    (h : p ∉ segment ℝ a b) : p.x < a.x ↔ p.x < b.x := by
  have key : ∀ {u w : Point2D}, u.y = p.y → w.y = p.y → p ∉ segment ℝ u w → p.x < u.x →
      p.x < w.x := by
    intro u w hu hw hn hpu
    by_contra hpw
    apply hn
    show p ∈ Segment.toSet ⟨u, w⟩
    rw [mem_toSet_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp only [orient_def, hu, hw]; ring
    · exact ⟨min_le_of_right_le (not_lt.mp hpw), le_max_of_le_left hpu.le⟩
    · simp [hu, hw]
  refine ⟨key ha hb h, key hb ha (by rwa [segment_symm])⟩

theorem ne_of_not_mem_segment_left {a b p : Point2D} (h : p ∉ segment ℝ a b) : p ≠ a :=
  fun e => h (e ▸ left_mem_segment ℝ a b)

theorem ne_of_not_mem_segment_right {a b p : Point2D} (h : p ∉ segment ℝ a b) : p ≠ b :=
  fun e => h (e ▸ right_mem_segment ℝ a b)

/-- A point at the height of `a` other than `a` differs from it in `x`. -/
theorem x_ne_of_y_eq {a p : Point2D} (hy : a.y = p.y) (hne : p ≠ a) : p.x ≠ a.x :=
  fun hx => hne (Point2D.ext hx hy.symm)

section Eventually

variable {p : Point2D}

theorem eventually_y_gt {v : Point2D} (h : v.y < p.y) : ∀ᶠ q in 𝓝 p, v.y < q.y :=
  continuous_y.continuousAt.eventually (lt_mem_nhds h)

theorem eventually_y_lt {v : Point2D} (h : p.y < v.y) : ∀ᶠ q in 𝓝 p, q.y < v.y :=
  continuous_y.continuousAt.eventually (gt_mem_nhds h)

theorem eventually_orient_pos {a b : Point2D} (h : 0 < orient a b p) :
    ∀ᶠ q in 𝓝 p, 0 < orient a b q :=
  (continuous_orient a b).continuousAt.eventually (lt_mem_nhds h)

theorem eventually_orient_neg {a b : Point2D} (h : orient a b p < 0) :
    ∀ᶠ q in 𝓝 p, orient a b q < 0 :=
  (continuous_orient a b).continuousAt.eventually (gt_mem_nhds h)

end Eventually

/-! ## One edge near a point off it -/

/-- Near a point `p` off the edge from `a` to `b`, the edge's contribution at
`q` is `atOrBelow q a - atOrBelow q b` times `crossRight p a b`. -/
theorem edgeContribution_eventually_eq {p a b : Point2D} (h : p ∉ segment ℝ a b) :
    ∀ᶠ q in 𝓝 p, edgeContribution q a b = (atOrBelow q a - atOrBelow q b) * crossRight p a b := by
  have hpa := ne_of_not_mem_segment_left h
  have hpb := ne_of_not_mem_segment_right h
  rcases lt_trichotomy a.y p.y with ha | ha | ha <;>
    rcases lt_trichotomy b.y p.y with hb | hb | hb
  · -- both ends below
    filter_upwards [eventually_y_gt ha, eventually_y_gt hb] with q h₁ h₂
    rw [edgeContribution_of_below h₁.le h₂.le, atOrBelow_of_le h₁.le, atOrBelow_of_le h₂.le]
    ring
  · -- `a` below, `b` at the height of `p`
    have hcr : crossRight p a b = if p.x < b.x then 1 else 0 := by
      simp [crossRight, ha.ne, hb]
    have ho : orient a b p = (b.y - a.y) * (b.x - p.x) := by rw [orient_def, ← hb]; ring
    rcases lt_or_gt_of_ne (x_ne_of_y_eq hb hpb) with hx | hx
    · have ho' : 0 < orient a b p := by rw [ho]; exact mul_pos (by linarith) (by linarith)
      filter_upwards [eventually_y_gt ha, eventually_orient_pos ho'] with q h₁ h₂
      by_cases hq : b.y ≤ q.y
      · rw [edgeContribution_of_below h₁.le hq, atOrBelow_of_le h₁.le, atOrBelow_of_le hq]; ring
      · rw [not_le] at hq
        rw [edgeContribution_of_up h₁.le hq, atOrBelow_of_le h₁.le, atOrBelow_of_lt hq, hcr]
        simp [hx, h₂]
    · have ho' : orient a b p < 0 := by
        rw [ho]; exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
      filter_upwards [eventually_y_gt ha, eventually_orient_neg ho'] with q h₁ h₂
      by_cases hq : b.y ≤ q.y
      · rw [edgeContribution_of_below h₁.le hq, atOrBelow_of_le h₁.le, atOrBelow_of_le hq]; ring
      · rw [not_le] at hq
        rw [edgeContribution_of_up h₁.le hq, atOrBelow_of_le h₁.le, atOrBelow_of_lt hq, hcr]
        simp [not_lt.mpr hx.le, not_lt.mpr h₂.le]
  · -- upward across the height of `p`
    have hcr : crossRight p a b = if 0 < orient a b p then 1 else 0 := by
      simp [crossRight, ha.ne, hb.ne', ha.trans hb]
    have ho : orient a b p ≠ 0 := fun h0 =>
      h (mem_segment_of_orient_eq_zero h0 (ha.trans hb).ne (Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩)))
    rcases lt_or_gt_of_ne ho with ho' | ho'
    · filter_upwards [eventually_y_gt ha, eventually_y_lt hb, eventually_orient_neg ho'] with q h₁ h₂ h₃
      rw [edgeContribution_of_up h₁.le h₂, atOrBelow_of_le h₁.le, atOrBelow_of_lt h₂, hcr]
      simp [not_lt.mpr ho'.le, not_lt.mpr h₃.le]
    · filter_upwards [eventually_y_gt ha, eventually_y_lt hb, eventually_orient_pos ho'] with q h₁ h₂ h₃
      rw [edgeContribution_of_up h₁.le h₂, atOrBelow_of_le h₁.le, atOrBelow_of_lt h₂, hcr]
      simp [ho', h₃]
  · -- `a` at the height of `p`, `b` below
    have hcr : crossRight p a b = if p.x < a.x then 1 else 0 := by simp [crossRight, ha]
    have ho : orient a b p = (a.y - b.y) * (p.x - a.x) := by rw [orient_def, ← ha]; ring
    rcases lt_or_gt_of_ne (x_ne_of_y_eq ha hpa) with hx | hx
    · have ho' : orient a b p < 0 := by
        rw [ho]; exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
      filter_upwards [eventually_y_gt hb, eventually_orient_neg ho'] with q h₁ h₂
      by_cases hq : a.y ≤ q.y
      · rw [edgeContribution_of_below hq h₁.le, atOrBelow_of_le hq, atOrBelow_of_le h₁.le]; ring
      · rw [not_le] at hq
        rw [edgeContribution_of_down hq h₁.le, atOrBelow_of_lt hq, atOrBelow_of_le h₁.le, hcr]
        simp [hx, h₂]
    · have ho' : 0 < orient a b p := by rw [ho]; exact mul_pos (by linarith) (by linarith)
      filter_upwards [eventually_y_gt hb, eventually_orient_pos ho'] with q h₁ h₂
      by_cases hq : a.y ≤ q.y
      · rw [edgeContribution_of_below hq h₁.le, atOrBelow_of_le hq, atOrBelow_of_le h₁.le]; ring
      · rw [not_le] at hq
        rw [edgeContribution_of_down hq h₁.le, atOrBelow_of_lt hq, atOrBelow_of_le h₁.le, hcr]
        simp [not_lt.mpr hx.le, not_lt.mpr h₂.le]
  · -- horizontal, at the height of `p`
    refine Eventually.of_forall fun q => ?_
    have e : atOrBelow q a = atOrBelow q b := by simp [atOrBelow, ha, hb]
    rw [edgeContribution_of_horizontal (ha.trans hb.symm), e]
    ring
  · -- `a` at the height of `p`, `b` above
    have hcr : crossRight p a b = if p.x < a.x then 1 else 0 := by simp [crossRight, ha]
    have ho : orient a b p = (b.y - a.y) * (a.x - p.x) := by rw [orient_def, ← ha]; ring
    rcases lt_or_gt_of_ne (x_ne_of_y_eq ha hpa) with hx | hx
    · have ho' : 0 < orient a b p := by rw [ho]; exact mul_pos (by linarith) (by linarith)
      filter_upwards [eventually_y_lt hb, eventually_orient_pos ho'] with q h₁ h₂
      by_cases hq : a.y ≤ q.y
      · rw [edgeContribution_of_up hq h₁, atOrBelow_of_le hq, atOrBelow_of_lt h₁, hcr]
        simp [hx, h₂]
      · rw [not_le] at hq
        rw [edgeContribution_of_above hq h₁, atOrBelow_of_lt hq, atOrBelow_of_lt h₁]; ring
    · have ho' : orient a b p < 0 := by
        rw [ho]; exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
      filter_upwards [eventually_y_lt hb, eventually_orient_neg ho'] with q h₁ h₂
      by_cases hq : a.y ≤ q.y
      · rw [edgeContribution_of_up hq h₁, atOrBelow_of_le hq, atOrBelow_of_lt h₁, hcr]
        simp [not_lt.mpr hx.le, not_lt.mpr h₂.le]
      · rw [not_le] at hq
        rw [edgeContribution_of_above hq h₁, atOrBelow_of_lt hq, atOrBelow_of_lt h₁]; ring
  · -- downward across the height of `p`
    have hcr : crossRight p a b = if orient a b p < 0 then 1 else 0 := by
      simp [crossRight, ha.ne', hb.ne, not_lt.mpr (hb.trans ha).le]
    have ho : orient a b p ≠ 0 := fun h0 =>
      h (mem_segment_of_orient_eq_zero h0 (hb.trans ha).ne' (Set.mem_uIcc.mpr (Or.inr ⟨hb.le, ha.le⟩)))
    rcases lt_or_gt_of_ne ho with ho' | ho'
    · filter_upwards [eventually_y_lt ha, eventually_y_gt hb, eventually_orient_neg ho'] with q h₁ h₂ h₃
      rw [edgeContribution_of_down h₁ h₂.le, atOrBelow_of_lt h₁, atOrBelow_of_le h₂.le, hcr]
      simp [ho', h₃]
    · filter_upwards [eventually_y_lt ha, eventually_y_gt hb, eventually_orient_pos ho'] with q h₁ h₂ h₃
      rw [edgeContribution_of_down h₁ h₂.le, atOrBelow_of_lt h₁, atOrBelow_of_le h₂.le, hcr]
      simp [not_lt.mpr ho'.le, not_lt.mpr h₃.le]
  · -- `a` above, `b` at the height of `p`
    have hcr : crossRight p a b = if p.x < b.x then 1 else 0 := by
      simp [crossRight, ha.ne', hb]
    have ho : orient a b p = (b.y - a.y) * (b.x - p.x) := by rw [orient_def, ← hb]; ring
    rcases lt_or_gt_of_ne (x_ne_of_y_eq hb hpb) with hx | hx
    · have ho' : orient a b p < 0 := by
        rw [ho]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
      filter_upwards [eventually_y_lt ha, eventually_orient_neg ho'] with q h₁ h₂
      by_cases hq : b.y ≤ q.y
      · rw [edgeContribution_of_down h₁ hq, atOrBelow_of_lt h₁, atOrBelow_of_le hq, hcr]
        simp [hx, h₂]
      · rw [not_le] at hq
        rw [edgeContribution_of_above h₁ hq, atOrBelow_of_lt h₁, atOrBelow_of_lt hq]; ring
    · have ho' : 0 < orient a b p := by
        rw [ho]; exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      filter_upwards [eventually_y_lt ha, eventually_orient_pos ho'] with q h₁ h₂
      by_cases hq : b.y ≤ q.y
      · rw [edgeContribution_of_down h₁ hq, atOrBelow_of_lt h₁, atOrBelow_of_le hq, hcr]
        simp [not_lt.mpr hx.le, not_lt.mpr h₂.le]
      · rw [not_le] at hq
        rw [edgeContribution_of_above h₁ hq, atOrBelow_of_lt h₁, atOrBelow_of_lt hq]; ring
  · -- both ends above
    filter_upwards [eventually_y_lt ha, eventually_y_lt hb] with q h₁ h₂
    rw [edgeContribution_of_above h₁ h₂, atOrBelow_of_lt h₁, atOrBelow_of_lt h₂]
    ring

theorem crossRight_of_left_level {p a b : Point2D} (ha : a.y = p.y) :
    crossRight p a b = if p.x < a.x then 1 else 0 := by
  simp [crossRight, ha]

/-- An edge ending at the height of `p` crosses there. -/
theorem crossRight_of_right_level {p a b : Point2D} (hb : b.y = p.y) (h : p ∉ segment ℝ a b) :
    crossRight p a b = if p.x < b.x then 1 else 0 := by
  by_cases ha : a.y = p.y
  · rw [crossRight_of_left_level ha]
    simp only [lt_x_iff_of_horizontal ha hb h]
  · simp [crossRight, ha, hb]

theorem isClosed_segment (a b : Point2D) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact (isCompact_Icc.image
    (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Point2D).continuous_of_finiteDimensional).isClosed

/-! ## The ring near a point off its boundary -/

namespace RawPolygon

variable (P : RawPolygon)

/-- Summation by parts around the ring. -/
theorem sum_sub_next_mul (B X : Fin P.n → ℤ) :
    ∑ i, (B i - B (P.next i)) * X i = ∑ i, B i * (X i - X (P.prev i)) := by
  have hshift : ∑ i, B (P.next i) * X i = ∑ i, B i * X (P.prev i) := by
    have : ∑ i, B (P.next i) * X i = ∑ i, B (P.next i) * X (P.prev (P.next i)) := by
      simp only [prev_next]
    rw [this]
    exact Equiv.sum_comp (finRotate P.n) (fun j => B j * X (P.prev j))
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, hshift]

theorem not_mem_edge_of_not_onBoundary {p : Point2D} (hp : ¬ P.OnBoundary p) (i : Fin P.n) :
    p ∉ segment ℝ (P.vertex i) (P.vertex (P.next i)) :=
  fun h => hp ⟨i, h⟩

/-- Near a point, an edge sum regrouped by vertices does not change, provided
the two edges at each vertex at the point's height agree on `crossRight`. -/
theorem eventually_sum_atOrBelow_eq {p : Point2D} (X : Fin P.n → ℤ)
    (hX : ∀ i, (P.vertex i).y = p.y → X i = X (P.prev i)) :
    ∀ᶠ q in 𝓝 p, ∑ i, atOrBelow q (P.vertex i) * (X i - X (P.prev i)) =
      ∑ i, atOrBelow p (P.vertex i) * (X i - X (P.prev i)) := by
  have hterm : ∀ᶠ q in 𝓝 p, ∀ i, atOrBelow q (P.vertex i) * (X i - X (P.prev i)) =
      atOrBelow p (P.vertex i) * (X i - X (P.prev i)) := by
    refine eventually_all.mpr fun i => ?_
    rcases lt_trichotomy (P.vertex i).y p.y with h | h | h
    · filter_upwards [eventually_y_gt h] with q hq
      rw [atOrBelow_of_le hq.le, atOrBelow_of_le h.le]
    · exact Eventually.of_forall fun q => by rw [hX i h, sub_self, mul_zero, mul_zero]
    · filter_upwards [eventually_y_lt h] with q hq
      rw [atOrBelow_of_lt hq, atOrBelow_of_lt h]
  filter_upwards [hterm] with q hq
  exact Finset.sum_congr rfl fun i _ => hq i

/-- Off the boundary, the winding number does not change nearby. -/
theorem windingNumber_eventually_eq {p : Point2D} (hp : ¬ P.OnBoundary p) :
    ∀ᶠ q in 𝓝 p, P.windingNumber q = P.windingNumber p := by
  set X : Fin P.n → ℤ := fun i => crossRight p (P.vertex i) (P.vertex (P.next i)) with hXdef
  have hc : ∀ᶠ q in 𝓝 p, ∀ i, edgeContribution q (P.vertex i) (P.vertex (P.next i)) =
      (atOrBelow q (P.vertex i) - atOrBelow q (P.vertex (P.next i))) * X i :=
    eventually_all.mpr fun i => edgeContribution_eventually_eq (P.not_mem_edge_of_not_onBoundary hp i)
  have hX : ∀ i, (P.vertex i).y = p.y → X i = X (P.prev i) := by
    intro i hi
    have h' := P.not_mem_edge_of_not_onBoundary hp (P.prev i)
    rw [next_prev] at h'
    simp only [hXdef, next_prev]
    rw [crossRight_of_left_level hi, crossRight_of_right_level hi h']
  have hw : ∀ q, (∀ i, edgeContribution q (P.vertex i) (P.vertex (P.next i)) =
      (atOrBelow q (P.vertex i) - atOrBelow q (P.vertex (P.next i))) * X i) →
      P.windingNumber q = ∑ i, atOrBelow q (P.vertex i) * (X i - X (P.prev i)) := by
    intro q hq
    rw [windingNumber, Finset.sum_congr rfl fun i _ => hq i]
    exact P.sum_sub_next_mul (fun i => atOrBelow q (P.vertex i)) X
  filter_upwards [hc, P.eventually_sum_atOrBelow_eq X hX] with q hq hsum
  rw [hw q hq, hsum, hw p hc.self_of_nhds]

theorem continuousAt_windingNumber {p : Point2D} (hp : ¬ P.OnBoundary p) :
    ContinuousAt P.windingNumber p :=
  Filter.EventuallyEq.continuousAt (P.windingNumber_eventually_eq hp)

/-- On a preconnected set avoiding the boundary the winding number is
constant. -/
theorem windingNumber_eq_of_isPreconnected {C : Set Point2D} (hC : IsPreconnected C)
    (havoid : ∀ p ∈ C, ¬ P.OnBoundary p) {p q : Point2D} (hp : p ∈ C) (hq : q ∈ C) :
    P.windingNumber p = P.windingNumber q :=
  hC.constant (fun x hx => (P.continuousAt_windingNumber (havoid x hx)).continuousWithinAt) hp hq

/-! ## Open and closed regions -/

theorem isClosed_onBoundary : IsClosed {p | P.OnBoundary p} := by
  have : {p | P.OnBoundary p} = ⋃ i, segment ℝ (P.vertex i) (P.vertex (P.next i)) := by
    ext p
    simp [OnBoundary, edge, Segment.toSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_segment _ _

theorem eventually_not_onBoundary {p : Point2D} (hp : ¬ P.OnBoundary p) :
    ∀ᶠ q in 𝓝 p, ¬ P.OnBoundary q :=
  P.isClosed_onBoundary.isOpen_compl.mem_nhds hp

/-- The open region is open. -/
theorem isOpen_openRegion : IsOpen P.openRegion := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hb, hw⟩
  filter_upwards [P.eventually_not_onBoundary hb, P.windingNumber_eventually_eq hb] with q hq hwq
  exact ⟨hq, by rw [hwq]; exact hw⟩

/-- The closed region is closed. -/
theorem isClosed_region : IsClosed P.region := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  have hp' : ¬ P.OnBoundary p ∧ P.windingNumber p = 0 := by
    simpa [region, not_or] using hp
  filter_upwards [P.eventually_not_onBoundary hp'.1, P.windingNumber_eventually_eq hp'.1]
    with q hq hwq
  simp only [region, mem_compl_iff, mem_ofPred_eq, not_or, not_not]
  exact ⟨hq, by rw [hwq]; exact hp'.2⟩

/-! ## Across an edge -/

/-- Near a point on no edge but `j`, at a height different from both ends of
edge `j`, the winding number is a constant plus the contribution of edge
`j`. -/
theorem windingNumber_eventually_eq_add_edge {p : Point2D} (j : Fin P.n)
    (hoff : ∀ k, k ≠ j → p ∉ segment ℝ (P.vertex k) (P.vertex (P.next k)))
    (ha : (P.vertex j).y ≠ p.y) (hb : (P.vertex (P.next j)).y ≠ p.y) :
    ∃ K : ℤ, ∀ᶠ q in 𝓝 p,
      P.windingNumber q = K + edgeContribution q (P.vertex j) (P.vertex (P.next j)) := by
  classical
  set X : Fin P.n → ℤ := fun i => crossRight p (P.vertex i) (P.vertex (P.next i)) with hXdef
  set T : Point2D → Fin P.n → ℤ := fun q i =>
    (atOrBelow q (P.vertex i) - atOrBelow q (P.vertex (P.next i))) * X i with hTdef
  have hc : ∀ᶠ q in 𝓝 p, ∀ k, k ≠ j →
      edgeContribution q (P.vertex k) (P.vertex (P.next k)) = T q k := by
    refine eventually_all.mpr fun k => ?_
    by_cases hk : k = j
    · exact Eventually.of_forall fun q h => absurd hk h
    · filter_upwards [edgeContribution_eventually_eq (hoff k hk)] with q hq _
      exact hq
  -- The two edges at a vertex at the height of `p` are not edge `j`.
  have hX : ∀ i, (P.vertex i).y = p.y → X i = X (P.prev i) := by
    intro i hi
    have hij : i ≠ j := fun e => ha (e ▸ hi)
    have hpj : P.prev i ≠ j := fun e => hb (by rw [← e, next_prev]; exact hi)
    have h' := hoff (P.prev i) hpj
    rw [next_prev] at h'
    simp only [hXdef, next_prev]
    rw [crossRight_of_left_level hi, crossRight_of_right_level hi h']
  -- The term of edge `j` in the regrouped sum does not change either.
  have hTj : ∀ᶠ q in 𝓝 p, T q j = T p j := by
    have e : ∀ {v : Point2D}, v.y ≠ p.y → ∀ᶠ q in 𝓝 p, atOrBelow q v = atOrBelow p v := by
      intro v hv
      rcases lt_or_gt_of_ne hv with h | h
      · filter_upwards [eventually_y_gt h] with q hq
        rw [atOrBelow_of_le hq.le, atOrBelow_of_le h.le]
      · filter_upwards [eventually_y_lt h] with q hq
        rw [atOrBelow_of_lt hq, atOrBelow_of_lt h]
    filter_upwards [e ha, e hb] with q h₁ h₂
    simp only [hTdef, h₁, h₂]
  refine ⟨∑ i, atOrBelow p (P.vertex i) * (X i - X (P.prev i)) - T p j, ?_⟩
  filter_upwards [hc, hTj, P.eventually_sum_atOrBelow_eq X hX] with q hq hqj hsum
  have hsplit : P.windingNumber q = ∑ i, T q i +
      (edgeContribution q (P.vertex j) (P.vertex (P.next j)) - T q j) := by
    rw [windingNumber]
    have : ∀ i, edgeContribution q (P.vertex i) (P.vertex (P.next i)) =
        T q i + if i = j then edgeContribution q (P.vertex j) (P.vertex (P.next j)) - T q j
          else 0 := by
      intro i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi, hq i hi]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hT : ∑ i, T q i = ∑ i, atOrBelow q (P.vertex i) * (X i - X (P.prev i)) :=
    P.sum_sub_next_mul (fun i => atOrBelow q (P.vertex i)) X
  rw [hsplit, hT, hsum, hqj]
  ring

end RawPolygon

namespace SimplePolygon

theorem isOpen_toOpenRegion (P : SimplePolygon) : IsOpen P.toOpenRegion := P.1.isOpen_openRegion

theorem isClosed_toRegion (P : SimplePolygon) : IsClosed P.toRegion := P.1.isClosed_region

theorem isClosed_boundary (P : SimplePolygon) : IsClosed P.boundary := P.1.isClosed_onBoundary

end SimplePolygon

end ComputationalGeometry
