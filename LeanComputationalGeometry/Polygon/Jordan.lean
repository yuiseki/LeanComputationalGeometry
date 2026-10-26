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

end RawPolygon

end ComputationalGeometry
