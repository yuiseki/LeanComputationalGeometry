import LeanComputationalGeometry.Polygon.EarRegion

/-!
# Winding numbers of simple polygons

A simple polygon winds `0` or `1` times around every point off its boundary
when it is counterclockwise, and `0` or `-1` times when it is clockwise. This
is the winding-number half of the Jordan curve theorem for polygons; the
proof here uses only the polygon's finitely many segments.
-/

namespace ComputationalGeometry

open Set Point2D Filter Topology

namespace RawPolygon

variable {P : RawPolygon}

/-! ## The reversed ring -/

theorem reverse_vertex (i : Fin P.reverse.n) : P.reverse.vertex i = P.vertex (Fin.rev i) := rfl

/-- The reverse of a simple polygon is simple. -/
theorem IsSimple.reverse (hP : P.IsSimple) : P.reverse.IsSimple := by
  have hnext : ∀ i : Fin P.reverse.n, Fin.rev (P.reverse.next i) = P.prev (Fin.rev i) :=
    P.rev_next_reverse
  refine ⟨hP.three_le, fun i => ?_, fun i => ?_, fun i j hij h₁ h₂ => ?_⟩
  · rw [show P.reverse.edge i = (P.edge (P.prev (Fin.rev i))).swap from P.reverse_edge i]
    exact fun h => hP.edge_nondegenerate _ h.symm
  · have key : (P.edge (P.prev (P.prev (Fin.rev i)))).toSet ∩ (P.edge (P.prev (Fin.rev i))).toSet =
        {P.vertex (P.prev (Fin.rev i))} := by
      have h := hP.adjacent_inter (P.prev (P.prev (Fin.rev i)))
      rwa [next_prev] at h
    have e₁ : P.reverse.edge i = (P.edge (P.prev (Fin.rev i))).swap := P.reverse_edge i
    have e₂ : P.reverse.edge (P.reverse.next i) =
        (P.edge (P.prev (P.prev (Fin.rev i)))).swap :=
      (P.reverse_edge _).trans (congrArg (fun k : Fin P.n => (P.edge (P.prev k)).swap) (hnext i))
    have e₃ : P.reverse.vertex (P.reverse.next i) = P.vertex (P.prev (Fin.rev i)) :=
      congrArg P.vertex (hnext i)
    rw [e₁, e₂, e₃, Segment.toSet_swap, Segment.toSet_swap, inter_comm]
    exact key
  · rw [show P.reverse.edge i = (P.edge (P.prev (Fin.rev i))).swap from P.reverse_edge i,
      show P.reverse.edge j = (P.edge (P.prev (Fin.rev j))).swap from P.reverse_edge j,
      Segment.toSet_swap, Segment.toSet_swap]
    have hrev : Function.Injective (fun k : Fin P.n => P.prev (Fin.rev k)) :=
      fun a b h => Fin.rev_injective ((finRotate P.n).symm.injective h)
    refine hP.nonadjacent_disjoint _ _ (hrev.ne hij) ?_ ?_
    · rw [next_prev, ← hnext]
      exact fun h => h₂ (Fin.rev_injective h).symm
    · rw [next_prev, ← hnext]
      exact fun h => h₁ (Fin.rev_injective h).symm

/-! ## A simple polygon is not flat -/

theorem iterate_next_zero (h : 0 < P.n) (j : Fin P.n) : P.next^[j.val] ⟨0, h⟩ = j := by
  ext
  rw [val_iterate_next]
  simp [Nat.mod_eq_of_lt j.isLt]

/-- A point of a line between two others on it is on the segment joining them. -/
theorem add_smul_mem_segment {c e : Point2D} {α β τ : ℝ} (hα : α ≤ τ) (hβ : τ ≤ β) :
    c + τ • e ∈ segment ℝ (c + α • e) (c + β • e) := by
  rcases eq_or_lt_of_le (hα.trans hβ) with hab | hab
  · have : τ = α := le_antisymm (hab ▸ hβ) hα
    subst this
    exact left_mem_segment ℝ _ _
  refine ⟨(β - τ) / (β - α), (τ - α) / (β - α), div_nonneg (by linarith) (by linarith),
    div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
  have hd : β - α ≠ 0 := by linarith
  apply Point2D.ext <;> simp only [x_add, x_smul, y_add, y_smul] <;> field_simp <;> ring

/-- The vertices of a simple polygon are not all on one line. -/
theorem IsSimple.not_forall_orient_eq_zero (hP : P.IsSimple) {c d : Point2D} (hcd : c ≠ d) :
    ¬ ∀ i, orient c d (P.vertex i) = 0 := by
  intro h
  have hu : d - c ≠ 0 := sub_ne_zero.mpr hcd.symm
  have hμ : ∀ i, ∃ μ : ℝ, P.vertex i = c + μ • (d - c) := by
    intro i
    obtain ⟨μ, hμ⟩ := exists_smul_of_cross_eq_zero hu (w := P.vertex i - c) (by
      have := h i
      simp only [orient_def] at this
      simp only [cross, x_sub, y_sub]
      linarith)
    exact ⟨μ, by rw [← hμ, add_sub_cancel]⟩
  choose μ hμ using hμ
  have hne : (Finset.univ : Finset (Fin P.n)).Nonempty := ⟨⟨0, by have := hP.three_le; omega⟩,
    Finset.mem_univ _⟩
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ μ hne
  have hinj : ∀ i j, μ i = μ j → P.vertex i = P.vertex j := by
    intro i j e; rw [hμ i, hμ j, e]
  set u := P.prev i₀
  set b := P.next i₀
  have hu₀ : μ u < μ i₀ := lt_of_le_of_ne (hmax u (Finset.mem_univ _)) fun e => by
    have := hP.edge_nondegenerate u
    exact this (by simp only [edge, u, next_prev]; exact hinj _ _ e)
  have hb₀ : μ b < μ i₀ := lt_of_le_of_ne (hmax b (Finset.mem_univ _)) fun e =>
    hP.edge_nondegenerate i₀ (hinj _ _ e).symm
  set τ := (max (μ u) (μ b) + μ i₀) / 2
  have hτ : max (μ u) (μ b) < τ ∧ τ < μ i₀ := by
    constructor <;> simp only [τ] <;> linarith [max_lt hu₀ hb₀]
  have h₁ : c + τ • (d - c) ∈ (P.edge u).toSet := by
    simp only [edge_toSet, u, next_prev, hμ]
    exact add_smul_mem_segment (le_trans (le_max_left _ _) hτ.1.le) hτ.2.le
  have h₂ : c + τ • (d - c) ∈ (P.edge i₀).toSet := by
    simp only [edge_toSet, hμ]
    rw [segment_symm]
    exact add_smul_mem_segment (le_trans (le_max_right _ _) hτ.1.le) hτ.2.le
  have hadj := hP.adjacent_inter u
  simp only [u, next_prev] at hadj
  have := hadj.subset ⟨h₁, h₂⟩
  rw [mem_singleton_iff, hμ i₀] at this
  have hτeq : τ = μ i₀ := by
    have e := congrArg (fun q => q - c) this
    simp only [add_sub_cancel_left] at e
    exact smul_left_injective ℝ hu e
  linarith [hτ.2]

/-- A simple polygon has an edge that is not horizontal. -/
theorem IsSimple.exists_edge_y_ne (hP : P.IsSimple) : ∃ e, (P.vertex e).y ≠ (P.vertex (P.next e)).y := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have h0 : 0 < P.n := by have := hP.three_le; omega
  set c := P.vertex ⟨0, h0⟩
  have hy : ∀ j, (P.vertex j).y = c.y := by
    intro j
    rw [← iterate_next_zero h0 j]
    induction j.val with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ← hall, ih]
  apply hP.not_forall_orient_eq_zero (c := c) (d := c + Point2D.mk 1 0) (by
    intro e
    have := congrArg Point2D.x e
    simp at this)
  intro i
  simp only [orient_def, x_add, y_add, Point2D.x_mk, Point2D.y_mk, hy]
  ring

/-- For a point off the boundary, some edge's line misses it. -/
theorem IsSimple.exists_orient_ne_zero (hP : P.IsSimple) {p : Point2D} (hp : ¬ P.OnBoundary p) :
    ∃ e, orient (P.vertex e) (P.vertex (P.next e)) p ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have h0 : 0 < P.n := by have := hP.three_le; omega
  set c := P.vertex ⟨0, h0⟩
  have hpv : ∀ j, P.vertex j ≠ p := fun j e => hp (e ▸ P.onBoundary_vertex j)
  have hcp : p ≠ c := (hpv _).symm
  have hu : c - p ≠ 0 := sub_ne_zero.mpr hcp.symm
  -- Every vertex is on the line through `p` and the first vertex.
  have hline : ∀ j, ∃ s : ℝ, P.vertex j - p = s • (c - p) := by
    intro j
    rw [← iterate_next_zero h0 j]
    induction j.val with
    | zero => exact ⟨1, by simp [c]⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      set w := P.next^[k] ⟨0, h0⟩
      have hw : P.vertex w - p ≠ 0 := sub_ne_zero.mpr (hpv w)
      obtain ⟨t, ht⟩ := exists_smul_of_cross_eq_zero hw (u := P.vertex w - p)
        (w := P.vertex (P.next w) - p) (by
          have := hall w
          simp only [orient_def] at this
          simp only [cross, x_sub, y_sub]
          linarith)
      refine ⟨t * s, ?_⟩
      rw [Function.iterate_succ_apply', ht, hs, smul_smul]
  apply hP.not_forall_orient_eq_zero hcp
  intro j
  obtain ⟨s, hs⟩ := hline j
  have hj : P.vertex j = p + s • (c - p) := by rw [← hs]; abel
  rw [hj]
  simp only [orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]
  ring

/-- At a straight vertex of a simple polygon the ring goes on, not back. -/
theorem IsSimple.dot_pos_of_locallyDegenerate (hP : P.IsSimple) {i : Fin P.n}
    (h : P.LocallyDegenerate i) :
    0 < (P.vertex i - P.prevVertex i).x * (P.nextVertex i - P.vertex i).x +
      (P.vertex i - P.prevVertex i).y * (P.nextVertex i - P.vertex i).y := by
  have hd₁ : P.vertex i - P.prevVertex i ≠ 0 := by
    have := hP.edge_nondegenerate (P.prev i)
    simp only [edge, Segment.Nondegenerate, next_prev] at this
    exact sub_ne_zero.mpr (Ne.symm this)
  obtain ⟨l, hl⟩ := exists_smul_of_cross_eq_zero hd₁ (w := P.nextVertex i - P.vertex i) (by
    have := h
    simp only [LocallyDegenerate, orient_def] at this
    simp only [cross, x_sub, y_sub]
    linarith)
  have hb : P.nextVertex i ≠ P.vertex i := Ne.symm (hP.edge_nondegenerate i)
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp only [zero_smul, sub_eq_zero] at hl
    exact hb hl
  rcases lt_or_gt_of_ne hl0 with hneg | hpos
  · -- Going back along the incoming edge: the two edges overlap near the vertex.
    exfalso
    set s := min 1 (-l) / 2
    have hm : 0 < min 1 (-l) := lt_min one_pos (neg_pos.mpr hneg)
    have hs : 0 < s := by simp only [s]; linarith
    have hs1 : s < 1 := by simp only [s]; linarith [min_le_left 1 (-l)]
    have hsl : s < -l := by simp only [s]; linarith [min_le_right 1 (-l), lt_min one_pos (neg_pos.mpr hneg)]
    set q := P.vertex i + s • (P.prevVertex i - P.vertex i)
    have hq₁ : q ∈ (P.edge (P.prev i)).toSet := by
      simp only [edge_toSet, next_prev]
      refine ⟨s, 1 - s, hs.le, by linarith, by ring, ?_⟩
      simp only [q, prevVertex]
      apply Point2D.ext <;> simp only [x_add, x_smul, y_add, y_smul, x_sub, y_sub] <;> ring
    have hq₂ : q ∈ (P.edge i).toSet := by
      simp only [edge_toSet]
      have hnb : P.vertex (P.next i) = P.vertex i + (-l) • (P.prevVertex i - P.vertex i) := by
        have : P.nextVertex i = P.vertex i + l • (P.vertex i - P.prevVertex i) := by
          rw [← hl]; abel
        rw [show P.vertex (P.next i) = P.nextVertex i from rfl, this]
        module
      rw [hnb]
      refine ⟨1 - s / (-l), s / (-l), by rw [sub_nonneg, div_le_one (by linarith)]; linarith,
        div_nonneg hs.le (by linarith), by ring, ?_⟩
      have hl' : -l ≠ 0 := by linarith
      simp only [q]
      apply Point2D.ext <;> simp only [x_add, x_smul, y_add, y_smul, x_sub, y_sub] <;>
        field_simp <;> ring
    have hadj := hP.adjacent_inter (P.prev i)
    simp only [next_prev] at hadj
    have := hadj.subset ⟨hq₁, hq₂⟩
    rw [mem_singleton_iff] at this
    have e := congrArg (fun z => z - P.vertex i) this
    simp only [q, add_sub_cancel_left, sub_self] at e
    rcases smul_eq_zero.mp e with e | e
    · linarith
    · exact hd₁ (by rw [← neg_sub, e, neg_zero])
  · have hsq : 0 < (P.vertex i - P.prevVertex i).x ^ 2 + (P.vertex i - P.prevVertex i).y ^ 2 := by
      by_contra hle
      apply hd₁
      apply Point2D.ext
      · simp only [x_zero]; nlinarith [sq_nonneg (P.vertex i - P.prevVertex i).x,
          sq_nonneg (P.vertex i - P.prevVertex i).y]
      · simp only [y_zero]; nlinarith [sq_nonneg (P.vertex i - P.prevVertex i).x,
          sq_nonneg (P.vertex i - P.prevVertex i).y]
    rw [hl]
    simp only [x_smul, y_smul]
    nlinarith

/-! ## Small regions beside the boundary

Beside each edge, on its left, a thin open triangle with the edge as its base
(`thinLeft`); around each vertex, on the left of the two edges there, a small
sector (`leftSector`). Both avoid the boundary when small enough, both are
preconnected, and each thin triangle meets the sectors at both its ends. -/

/-- The dot product of two vectors of the plane. -/
def dot (u w : Point2D) : ℝ := u.x * w.x + u.y * w.y

theorem dist_le_abs_add_abs (q z : Point2D) : dist q z ≤ |q.x - z.x| + |q.y - z.y| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq]
  rw [Real.sqrt_le_left]
  · show (|q.x - z.x|) ^ 2 + (|q.y - z.y|) ^ 2 ≤ (|q.x - z.x| + |q.y - z.y|) ^ 2
    nlinarith [abs_nonneg (q.x - z.x), abs_nonneg (q.y - z.y)]
  · positivity

theorem convex_orient_pos (a b : Point2D) : Convex ℝ {q | 0 < orient a b q} := by
  intro x hx y hy α β hα hβ hαβ
  obtain rfl : α = 1 - β := by linarith
  simp only [mem_ofPred_eq, orient_lineMap] at hx hy ⊢
  rcases eq_or_lt_of_le hβ with h | h
  · subst h; simpa using hx
  · nlinarith [mul_nonneg hα hx.le]

open Classical in
/-- The points near vertex `i` on the left of the boundary there: within `r`
of the vertex, and on the left of both edges at a convex or straight vertex,
of either at a reflex one. -/
noncomputable def leftSector (P : RawPolygon) (i : Fin P.n) (r : ℝ) : Set Point2D :=
  {q | dist q (P.vertex i) < r ∧
    if 0 ≤ orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) then
      0 < orient (P.prevVertex i) (P.vertex i) q ∧ 0 < orient (P.vertex i) (P.nextVertex i) q
    else 0 < orient (P.prevVertex i) (P.vertex i) q ∨ 0 < orient (P.vertex i) (P.nextVertex i) q}

/-- The thin open triangle on the left of edge `e`, of height `h` over the
middle of the edge. -/
def thinLeft (P : RawPolygon) (e : Fin P.n) (h : ℝ) : Set Point2D :=
  {q | 0 < orient (P.vertex e) (P.vertex (P.next e)) q ∧
    orient (P.vertex e) (P.vertex (P.next e)) q <
      2 * h * dot (q - P.vertex e) (P.vertex (P.next e) - P.vertex e) ∧
    orient (P.vertex e) (P.vertex (P.next e)) q <
      2 * h * (dot (P.vertex (P.next e) - P.vertex e) (P.vertex (P.next e) - P.vertex e) -
        dot (q - P.vertex e) (P.vertex (P.next e) - P.vertex e))}

theorem convex_thinLeft (e : Fin P.n) (h : ℝ) : Convex ℝ (P.thinLeft e h) := by
  intro x hx y hy α β hα hβ hαβ
  obtain rfl : α = 1 - β := by linarith
  simp only [thinLeft, mem_ofPred_eq, orient_lineMap, dot, x_sub, y_sub, x_add, y_add,
    x_smul, y_smul] at hx hy ⊢
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  obtain ⟨hy₁, hy₂, hy₃⟩ := hy
  rcases eq_or_lt_of_le hβ with hb | hb
  · subst hb
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact ⟨hx₁, by nlinarith, by nlinarith⟩
  refine ⟨by nlinarith [mul_nonneg hα hx₁.le],
    by nlinarith [mul_nonneg hα (sub_nonneg.mpr hx₂.le)],
    by nlinarith [mul_nonneg hα (sub_nonneg.mpr hx₃.le)]⟩

theorem isPreconnected_thinLeft (e : Fin P.n) (h : ℝ) : IsPreconnected (P.thinLeft e h) :=
  (convex_thinLeft e h).isPreconnected

/-- Small sectors at a vertex of a simple polygon avoid the boundary. -/
theorem IsSimple.eventually_leftSector_not_onBoundary (hP : P.IsSimple) (i : Fin P.n) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ q ∈ P.leftSector i r, ¬ P.OnBoundary q := by
  classical
  have hfar : ∀ᶠ q in 𝓝 (P.vertex i), ∀ j, j ≠ i → j ≠ P.prev i →
      q ∉ segment ℝ (P.vertex j) (P.vertex (P.next j)) := by
    refine eventually_all.mpr fun j => ?_
    by_cases hj : j ≠ i ∧ j ≠ P.prev i
    · have hv : P.vertex i ∉ segment ℝ (P.vertex j) (P.vertex (P.next j)) := by
        intro hm
        rcases hP.vertex_mem_edge (j := j) (k := i) hm with e | e
        · exact hj.1 e
        · exact hj.2 (by rw [← e, prev_next])
      exact Filter.mem_of_superset ((isClosed_segment _ _).isOpen_compl.mem_nhds hv)
        fun q hq _ _ => hq
    · exact Eventually.of_forall fun q h₁ h₂ => absurd ⟨h₁, h₂⟩ hj
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hfar
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr q hq ⟨j, hj⟩
  rw [edge_toSet] at hj
  obtain ⟨hqd, hqs⟩ := hq
  by_cases e₁ : j = i
  · -- On the outgoing edge: on its line, and on the inner side of the incoming one only at
    -- a convex vertex.
    subst e₁
    obtain ⟨t, ht, hqt⟩ := (Segment.mem_toSet_iff_exists ⟨_, _⟩).mp hj
    have hq' : q = (1 - t) • P.vertex j + t • P.nextVertex j := hqt.symm
    have hu : orient (P.prevVertex j) (P.vertex j) q =
        t * orient (P.prevVertex j) (P.vertex j) (P.nextVertex j) := by
      rw [hq', orient_lineMap, orient_self₂₃]; ring
    have hb : orient (P.vertex j) (P.nextVertex j) q = 0 := by
      rw [hq', orient_lineMap, orient_self₁₃, orient_self₂₃]; ring
    split_ifs at hqs with hc
    · exact lt_irrefl 0 (hb ▸ hqs.2)
    · rcases hqs with h | h
      · rw [hu] at h
        nlinarith [ht.1]
      · exact lt_irrefl 0 (hb ▸ h)
  by_cases e₂ : j = P.prev i
  · -- On the incoming edge, symmetrically.
    subst e₂
    rw [next_prev] at hj
    obtain ⟨t, ht, hqt⟩ := (Segment.mem_toSet_iff_exists ⟨_, _⟩).mp hj
    have hq' : q = (1 - t) • P.prevVertex i + t • P.vertex i := hqt.symm
    have hu : orient (P.prevVertex i) (P.vertex i) q = 0 := by
      rw [hq', orient_lineMap, orient_self₁₃, orient_self₂₃]; ring
    have hb : orient (P.vertex i) (P.nextVertex i) q =
        (1 - t) * orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) := by
      rw [hq', orient_lineMap, orient_self₁₃, orient_rotate]; ring
    split_ifs at hqs with hc
    · exact lt_irrefl 0 (hu ▸ hqs.1)
    · rcases hqs with h | h
      · exact lt_irrefl 0 (hu ▸ h)
      · rw [hb] at h
        nlinarith [ht.2]
  exact hball (hqd.trans hr.2) j e₁ e₂ hj

theorem isPreconnected_leftSector (i : Fin P.n) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (P.leftSector i r) := by
  classical
  by_cases hc : 0 ≤ orient (P.prevVertex i) (P.vertex i) (P.nextVertex i)
  · have : P.leftSector i r = Metric.ball (P.vertex i) r ∩
        {q | 0 < orient (P.prevVertex i) (P.vertex i) q} ∩
        {q | 0 < orient (P.vertex i) (P.nextVertex i) q} := by
      ext q; simp [leftSector, hc, Metric.mem_ball, and_assoc]
    rw [this]
    exact (((convex_ball _ _).inter (convex_orient_pos _ _)).inter
      (convex_orient_pos _ _)).isPreconnected
  · have : P.leftSector i r = (Metric.ball (P.vertex i) r ∩
        {q | 0 < orient (P.prevVertex i) (P.vertex i) q}) ∪ (Metric.ball (P.vertex i) r ∩
        {q | 0 < orient (P.vertex i) (P.nextVertex i) q}) := by
      ext q; simp [leftSector, hc, Metric.mem_ball, and_or_left]
    rw [this]
    -- A common point: off the vertex towards both inner sides.
    set w := (P.vertex i - P.prevVertex i) - (P.nextVertex i - P.vertex i)
    set ε := r / (|w.x| + |w.y| + 1)
    have hε : 0 < ε := div_pos hr (by positivity)
    set z := P.vertex i + ε • w
    have hzd : dist z (P.vertex i) < r := by
      calc dist z (P.vertex i) ≤ |z.x - (P.vertex i).x| + |z.y - (P.vertex i).y| :=
            dist_le_abs_add_abs _ _
        _ = ε * (|w.x| + |w.y|) := by
            simp only [z, x_add, y_add, x_smul, y_smul, add_sub_cancel_left, abs_mul,
              abs_of_pos hε]; ring
        _ < r := by
            rw [show r = ε * (|w.x| + |w.y| + 1) by simp only [ε]; field_simp]
            nlinarith
    have hO : orient (P.prevVertex i) (P.vertex i) (P.nextVertex i) < 0 := not_le.mp hc
    have h₁ : orient (P.prevVertex i) (P.vertex i) z =
        -(ε * orient (P.prevVertex i) (P.vertex i) (P.nextVertex i)) := by
      simp only [z, w, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have h₂ : orient (P.vertex i) (P.nextVertex i) z =
        -(ε * orient (P.prevVertex i) (P.vertex i) (P.nextVertex i)) := by
      simp only [z, w, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have hpos : 0 < -(ε * orient (P.prevVertex i) (P.vertex i) (P.nextVertex i)) := by
      nlinarith
    refine IsPreconnected.union z ⟨Metric.mem_ball.mpr hzd, ?_⟩ ⟨Metric.mem_ball.mpr hzd, ?_⟩
      ((convex_ball _ _).inter (convex_orient_pos _ _)).isPreconnected
      ((convex_ball _ _).inter (convex_orient_pos _ _)).isPreconnected
    · show 0 < orient _ _ z; rw [h₁]; exact hpos
    · show 0 < orient _ _ z; rw [h₂]; exact hpos

theorem isCompact_segment (a b : Point2D) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image (AffineMap.lineMap a b : ℝ →ᵃ[ℝ] Point2D).continuous_of_finiteDimensional

/-- Thin triangles beside an edge of a simple polygon avoid the boundary. -/
theorem IsSimple.eventually_thinLeft_not_onBoundary (hP : P.IsSimple) (e : Fin P.n) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ q ∈ P.thinLeft e h, ¬ P.OnBoundary q := by
  set v := P.vertex e
  set v' := P.vertex (P.next e)
  set d := v' - v
  set D := dot d d
  have hvv : v ≠ v' := hP.edge_nondegenerate e
  have hD : 0 < D := by
    have hd : d ≠ 0 := sub_ne_zero.mpr hvv.symm
    by_contra hle
    apply hd
    simp only [D, dot] at hle
    apply Point2D.ext
    · simp only [x_zero]; nlinarith [sq_nonneg d.x, sq_nonneg d.y]
    · simp only [y_zero]; nlinarith [sq_nonneg d.x, sq_nonneg d.y]
  have key : ∀ j, ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ q ∈ P.thinLeft e h,
      q ∉ segment ℝ (P.vertex j) (P.vertex (P.next j)) := by
    intro j
    by_cases e₁ : j = e
    · subst e₁
      exact Eventually.of_forall fun h q hq hj =>
        lt_irrefl 0 (Segment.orient_eq_zero_of_mem ⟨_, _⟩ hj ▸ hq.1)
    by_cases e₂ : j = P.prev e
    · subst e₂
      set u := P.vertex (P.prev e)
      set O := orient v v' u
      set K := dot (u - v) d
      have hE : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < O → 2 * h * K < O := by
        by_cases hO : 0 < O
        · have : ∀ᶠ h in 𝓝 (0 : ℝ), 2 * h * K < O := by
            have hc : Continuous fun h : ℝ => 2 * h * K := by fun_prop
            exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hO))
          exact (this.filter_mono nhdsWithin_le_nhds).mono fun h hh _ => hh
        · exact Eventually.of_forall fun h h' => absurd h' hO
      filter_upwards [hE, self_mem_nhdsWithin] with h hh hpos q hq hj
      rw [next_prev] at hj
      obtain ⟨t, ht, hqt⟩ := (Segment.mem_toSet_iff_exists ⟨_, _⟩).mp hj
      have hq' : q = (1 - t) • u + t • v := hqt.symm
      obtain ⟨h₁, h₂, -⟩ := hq
      have e₁ : orient v v' q = (1 - t) * O := by
        rw [hq', orient_lineMap, orient_self₁₃]; ring
      have e₂ : dot (q - v) d = (1 - t) * K := by
        simp only [hq', K, dot, x_sub, y_sub, x_add, y_add, x_smul, y_smul]; ring
      rw [e₁] at h₁ h₂
      rw [e₂] at h₂
      have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
      by_cases hO : 0 < O
      · nlinarith [hh hO, mul_le_mul_of_nonneg_left (hh hO).le ht1]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht1 (not_lt.mp hO)]
    by_cases e₃ : j = P.next e
    · subst e₃
      set w := P.vertex (P.next (P.next e))
      set O := orient v v' w
      set K := dot (w - v') d
      have hE : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < O → -(2 * h * K) < O := by
        by_cases hO : 0 < O
        · have : ∀ᶠ h in 𝓝 (0 : ℝ), -(2 * h * K) < O := by
            have hc : Continuous fun h : ℝ => -(2 * h * K) := by fun_prop
            exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hO))
          exact (this.filter_mono nhdsWithin_le_nhds).mono fun h hh _ => hh
        · exact Eventually.of_forall fun h h' => absurd h' hO
      filter_upwards [hE, self_mem_nhdsWithin] with h hh hpos q hq hj
      obtain ⟨t, ht, hqt⟩ := (Segment.mem_toSet_iff_exists ⟨_, _⟩).mp hj
      have hq' : q = (1 - t) • v' + t • w := hqt.symm
      obtain ⟨h₁, -, h₃⟩ := hq
      have e₁ : orient v v' q = t * O := by
        rw [hq', orient_lineMap, orient_self₂₃]; ring
      have e₂ : dot (q - v) d = D + t * K := by
        simp only [hq', K, D, d, dot, x_sub, y_sub, x_add, y_add, x_smul, y_smul]; ring
      rw [e₁] at h₁ h₃
      rw [e₂] at h₃
      have ht0 : 0 ≤ t := ht.1
      by_cases hO : 0 < O
      · nlinarith [hh hO, mul_le_mul_of_nonneg_left (hh hO).le ht0]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht0 (not_lt.mp hO)]
    -- An edge away from `e`: at a positive distance, which the thin triangles do not reach.
    have hdis : Disjoint (segment ℝ v v') (segment ℝ (P.vertex j) (P.vertex (P.next j))) :=
      hP.nonadjacent_disjoint e j (Ne.symm e₁) (Ne.symm e₃) (fun h => e₂ (by rw [← h, prev_next]))
    obtain ⟨δ, hδ, hthick⟩ := hdis.exists_thickenings (isCompact_segment _ _) (isClosed_segment _ _)
    set C := |d.x| + |d.y|
    have hE : ∀ᶠ h in 𝓝[>] (0 : ℝ), h * (C + 1) < δ := by
      have hc : Continuous fun h : ℝ => h * (C + 1) := by fun_prop
      exact (hc.continuousAt.eventually (gt_mem_nhds (by simpa using hδ))).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hE, self_mem_nhdsWithin] with h hh hpos q hq hj
    obtain ⟨h₁, h₂, h₃⟩ := hq
    set o := orient v v' q
    set τ := dot (q - v) d
    have h₃' : o < 2 * h * (D - τ) := h₃
    have h2 : (0 : ℝ) ≤ 2 * h := by linarith [show (0:ℝ) < h from hpos]
    have hτ : 0 < τ := by
      by_contra hτ
      have := mul_nonpos_of_nonneg_of_nonpos h2 (not_lt.mp hτ)
      linarith
    have hτD : τ < D := by
      by_contra hτ
      have := mul_nonpos_of_nonneg_of_nonpos h2 (by linarith [not_lt.mp hτ] : D - τ ≤ 0)
      linarith
    have hoD : o < h * D := by linarith
    set z := v + (τ / D) • d
    have hz : z ∈ segment ℝ v v' := by
      refine ⟨1 - τ / D, τ / D, by rw [sub_nonneg, div_le_one hD]; exact hτD.le,
        div_nonneg hτ.le hD.le, by ring, ?_⟩
      simp only [z, d]
      apply Point2D.ext <;> simp only [x_add, x_smul, y_add, y_smul, x_sub, y_sub] <;> ring
    have hD0 : D ≠ 0 := hD.ne'
    have hzx : q.x - z.x = -(o / D) * d.y := by
      have : z.x = v.x + τ / D * d.x := by simp [z]
      rw [this]
      field_simp
      simp only [o, τ, D, d, dot, orient_def, x_sub, y_sub]
      ring
    have hzy : q.y - z.y = (o / D) * d.x := by
      have : z.y = v.y + τ / D * d.y := by simp [z]
      rw [this]
      field_simp
      simp only [o, τ, D, d, dot, orient_def, x_sub, y_sub]
      ring
    have hoD' : 0 < o / D := div_pos h₁ hD
    have hdist : dist q z < δ := by
      calc dist q z ≤ |q.x - z.x| + |q.y - z.y| := dist_le_abs_add_abs _ _
        _ = o / D * C := by
            rw [hzx, hzy, abs_mul, abs_mul, abs_neg, abs_of_pos hoD']; simp only [C]; ring
        _ ≤ h * (C + 1) := by
            have : o / D < h := by rw [div_lt_iff₀ hD]; linarith
            nlinarith [abs_nonneg d.x, abs_nonneg d.y]
        _ < δ := hh
    exact Set.disjoint_left.mp hthick (Metric.mem_thickening_iff.mpr ⟨z, hz, hdist⟩)
      (Metric.self_subset_thickening hδ _ hj)
  filter_upwards [eventually_all.mpr key] with h hh q hq ⟨j, hj⟩
  exact hh j q hq hj

/-- Near a point inside an edge, the points on its left are in each thin
triangle beside it. -/
theorem eventually_mem_thinLeft (e : Fin P.n) {h : ℝ} (hh : 0 < h)
    (hvv : P.vertex e ≠ P.vertex (P.next e)) {q₀ : Point2D}
    (hq₀ : q₀ ∈ openSegment ℝ (P.vertex e) (P.vertex (P.next e))) :
    ∀ᶠ q in 𝓝 q₀, 0 < orient (P.vertex e) (P.vertex (P.next e)) q → q ∈ P.thinLeft e h := by
  set v := P.vertex e
  set v' := P.vertex (P.next e)
  set D := dot (v' - v) (v' - v)
  have hD : 0 < D := by
    have hd : v' - v ≠ 0 := sub_ne_zero.mpr hvv.symm
    by_contra hle
    apply hd
    simp only [D, dot] at hle
    apply Point2D.ext
    · simp only [x_zero]; nlinarith [sq_nonneg (v' - v).x, sq_nonneg (v' - v).y]
    · simp only [y_zero]; nlinarith [sq_nonneg (v' - v).x, sq_nonneg (v' - v).y]
  obtain ⟨a, τ, ha, hτ, hsum, rfl⟩ := hq₀
  obtain rfl : a = 1 - τ := by linarith
  have e₁ : orient v v' ((1 - τ) • v + τ • v') = 0 := by
    rw [orient_lineMap, orient_self₁₃, orient_self₂₃]; ring
  have e₂ : dot ((1 - τ) • v + τ • v' - v) (v' - v) = τ * D := by
    simp only [D, dot, x_sub, y_sub, x_add, y_add, x_smul, y_smul]; ring
  have hc₂ : Continuous fun q => 2 * h * dot (q - v) (v' - v) - orient v v' q := by
    unfold dot; fun_prop
  have hc₃ : Continuous fun q => 2 * h * (D - dot (q - v) (v' - v)) - orient v v' q := by
    unfold dot; fun_prop
  have p₂ : 0 < 2 * h * dot ((1 - τ) • v + τ • v' - v) (v' - v) -
      orient v v' ((1 - τ) • v + τ • v') := by
    rw [e₁, e₂]; nlinarith [mul_pos (mul_pos hh hτ) hD]
  have p₃ : 0 < 2 * h * (D - dot ((1 - τ) • v + τ • v' - v) (v' - v)) -
      orient v v' ((1 - τ) • v + τ • v') := by
    rw [e₁, e₂]; nlinarith [mul_pos (mul_pos hh ha) hD]
  filter_upwards [hc₂.continuousAt.eventually (lt_mem_nhds p₂),
    hc₃.continuousAt.eventually (lt_mem_nhds p₃)] with q h₂ h₃ h₁
  exact ⟨h₁, by linarith, by linarith⟩

theorem dot_self_pos {d : Point2D} (hd : d ≠ 0) : 0 < dot d d := by
  by_contra hle
  apply hd
  simp only [dot] at hle
  apply Point2D.ext
  · simp only [x_zero]; nlinarith [sq_nonneg d.x, sq_nonneg d.y]
  · simp only [y_zero]; nlinarith [sq_nonneg d.x, sq_nonneg d.y]

/-- A thin triangle beside an edge reaches into every sector at the edge's
start. -/
theorem IsSimple.eventually_thinLeft_meets_leftSector (hP : P.IsSimple) (e : Fin P.n) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ r, 0 < r → (P.thinLeft e h ∩ P.leftSector e r).Nonempty := by
  classical
  set u := P.prevVertex e
  set v := P.vertex e
  set v' := P.vertex (P.next e)
  set d := v' - v
  set D := dot d d
  have hD : 0 < D := dot_self_pos (sub_ne_zero.mpr (hP.edge_nondegenerate e).symm)
  set O := orient u v v'
  set K := dot (v - u) d
  have hE : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ O → 0 < O + h * K := by
    rcases lt_trichotomy O 0 with hO | hO | hO
    · exact Eventually.of_forall fun h h' => absurd h' (not_le.mpr hO)
    · have hK : 0 < K := hP.dot_pos_of_locallyDegenerate hO
      filter_upwards [self_mem_nhdsWithin] with h hh _
      rw [hO, zero_add]; exact mul_pos hh hK
    · have hc : Continuous fun h : ℝ => O + h * K := by fun_prop
      exact ((hc.continuousAt.eventually (lt_mem_nhds (by simpa using hO))).filter_mono
        nhdsWithin_le_nhds).mono fun h hh _ => hh
  filter_upwards [hE, self_mem_nhdsWithin] with h hE (hpos : 0 < h) r hr
  set w : Point2D := d + h • Point2D.mk (-d.y) d.x
  set C := |w.x| + |w.y|
  set s := (1 / 4 : ℝ) * min 1 (r / (C + 1))
  have hC : 0 ≤ C := by positivity
  have hm : 0 < min 1 (r / (C + 1)) := lt_min one_pos (div_pos hr (by linarith))
  have hs : 0 < s := by simp only [s]; positivity
  have hs4 : s ≤ 1 / 4 := by simp only [s]; linarith [min_le_left 1 (r / (C + 1))]
  have hsC : s * C < r := by
    have h1 : min 1 (r / (C + 1)) * (C + 1) ≤ r := by
      calc min 1 (r / (C + 1)) * (C + 1) ≤ r / (C + 1) * (C + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ = r := by field_simp
    simp only [s]; nlinarith
  set q := v + s • w
  have o₁ : orient v v' q = s * h * D := by
    simp only [q, w, d, D, dot, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub,
      Point2D.x_mk, Point2D.y_mk]; ring
  have o₂ : dot (q - v) d = s * D := by
    simp only [q, w, d, D, dot, x_add, y_add, x_smul, y_smul, x_sub, y_sub,
      Point2D.x_mk, Point2D.y_mk]; ring
  have o₃ : orient u v q = s * (O + h * K) := by
    simp only [q, w, d, O, K, dot, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub,
      Point2D.x_mk, Point2D.y_mk]; ring
  have hqd : dist q v < r := by
    calc dist q v ≤ |q.x - v.x| + |q.y - v.y| := dist_le_abs_add_abs _ _
      _ = s * C := by
          simp only [q, x_add, y_add, x_smul, y_smul, add_sub_cancel_left, abs_mul, abs_of_pos hs, C]
          ring
      _ < r := hsC
  have hshD : 0 < s * h * D := by positivity
  refine ⟨q, ⟨?_, ?_, ?_⟩, hqd, ?_⟩
  · show 0 < orient v v' q; rw [o₁]; exact hshD
  · show orient v v' q < 2 * h * dot (q - v) d; rw [o₁, o₂]; nlinarith
  · show orient v v' q < 2 * h * (D - dot (q - v) d); rw [o₁, o₂]; nlinarith
  · show if 0 ≤ O then 0 < orient u v q ∧ 0 < orient v v' q else 0 < orient u v q ∨ 0 < orient v v' q
    split_ifs with hc
    · exact ⟨by rw [o₃]; exact mul_pos hs (hE hc), by rw [o₁]; exact hshD⟩
    · exact Or.inr (by rw [o₁]; exact hshD)

/-- A thin triangle beside an edge reaches into every sector at the edge's
end. -/
theorem IsSimple.eventually_thinLeft_meets_leftSector_next (hP : P.IsSimple) (e : Fin P.n) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ r, 0 < r →
      (P.thinLeft e h ∩ P.leftSector (P.next e) r).Nonempty := by
  classical
  set v := P.vertex e
  set v' := P.vertex (P.next e)
  set w₀ := P.nextVertex (P.next e)
  have hpv : P.prevVertex (P.next e) = v := by simp [prevVertex, v]
  set d := v' - v
  set D := dot d d
  have hD : 0 < D := dot_self_pos (sub_ne_zero.mpr (hP.edge_nondegenerate e).symm)
  set O := orient v v' w₀
  set K := dot d (w₀ - v')
  have hE : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ O → 0 < O + h * K := by
    rcases lt_trichotomy O 0 with hO | hO | hO
    · exact Eventually.of_forall fun h h' => absurd h' (not_le.mpr hO)
    · have hdeg : P.LocallyDegenerate (P.next e) := by
        show orient (P.prevVertex (P.next e)) _ _ = 0
        rw [hpv]; exact hO
      have hK : 0 < K := by
        have := hP.dot_pos_of_locallyDegenerate hdeg
        rw [hpv] at this
        exact this
      filter_upwards [self_mem_nhdsWithin] with h hh _
      rw [hO, zero_add]; exact mul_pos hh hK
    · have hc : Continuous fun h : ℝ => O + h * K := by fun_prop
      exact ((hc.continuousAt.eventually (lt_mem_nhds (by simpa using hO))).filter_mono
        nhdsWithin_le_nhds).mono fun h hh _ => hh
  filter_upwards [hE, self_mem_nhdsWithin] with h hE (hpos : 0 < h) r hr
  set w : Point2D := -d + h • Point2D.mk (-d.y) d.x
  set C := |w.x| + |w.y|
  set s := (1 / 4 : ℝ) * min 1 (r / (C + 1))
  have hC : 0 ≤ C := by positivity
  have hm : 0 < min 1 (r / (C + 1)) := lt_min one_pos (div_pos hr (by linarith))
  have hs : 0 < s := by simp only [s]; positivity
  have hs4 : s ≤ 1 / 4 := by simp only [s]; linarith [min_le_left 1 (r / (C + 1))]
  have hsC : s * C < r := by
    have h1 : min 1 (r / (C + 1)) * (C + 1) ≤ r := by
      calc min 1 (r / (C + 1)) * (C + 1) ≤ r / (C + 1) * (C + 1) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ = r := by field_simp
    simp only [s]; nlinarith
  set q := v' + s • w
  have o₁ : orient v v' q = s * h * D := by
    simp only [q, w, d, D, dot, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub, x_neg,
      y_neg, Point2D.x_mk, Point2D.y_mk]; ring
  have o₂ : dot (q - v) d = D - s * D := by
    simp only [q, w, d, D, dot, x_add, y_add, x_smul, y_smul, x_sub, y_sub, x_neg, y_neg,
      Point2D.x_mk, Point2D.y_mk]; ring
  have o₃ : orient v' w₀ q = s * (O + h * K) := by
    simp only [q, w, d, O, K, dot, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub, x_neg,
      y_neg, Point2D.x_mk, Point2D.y_mk]; ring
  have hqd : dist q v' < r := by
    calc dist q v' ≤ |q.x - v'.x| + |q.y - v'.y| := dist_le_abs_add_abs _ _
      _ = s * C := by
          simp only [q, x_add, y_add, x_smul, y_smul, add_sub_cancel_left, abs_mul, abs_of_pos hs, C]
          ring
      _ < r := hsC
  have hshD : 0 < s * h * D := by positivity
  refine ⟨q, ⟨?_, ?_, ?_⟩, hqd, ?_⟩
  · show 0 < orient v v' q; rw [o₁]; exact hshD
  · show orient v v' q < 2 * h * dot (q - v) d; rw [o₁, o₂]; nlinarith
  · show orient v v' q < 2 * h * (D - dot (q - v) d); rw [o₁, o₂]; nlinarith
  · show if 0 ≤ orient (P.prevVertex (P.next e)) v' w₀ then
        0 < orient (P.prevVertex (P.next e)) v' q ∧ 0 < orient v' w₀ q
      else 0 < orient (P.prevVertex (P.next e)) v' q ∨ 0 < orient v' w₀ q
    rw [hpv]
    split_ifs with hc
    · exact ⟨by rw [o₁]; exact hshD, by rw [o₃]; exact mul_pos hs (hE hc)⟩
    · exact Or.inl (by rw [o₁]; exact hshD)

end RawPolygon

end ComputationalGeometry
