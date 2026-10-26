import LeanComputationalGeometry.Polygon.Diagonal

/-!
# Two ears

Every simple polygon with at least four vertices that winds `0` or `1` times
has an ear (`IsSimple.exists_ear`), and indeed two ears whose triangles do not
overlap (`IsSimple.exists_two_nonoverlapping_ears`). This is Meisters' Two
Ears Theorem, for the ear test `IsEar` of this library: a convex vertex with
no other vertex in the closed ear triangle. Collinear vertices are allowed
throughout; no general position is assumed.

1. A convex vertex: the vertex with the largest `x`, and among those the
   largest `y`, turns left (`IsSimple.exists_convexVertex`). It cannot go
   straight on, since both neighbours lie on the same side of it, and it
   cannot turn right, since the sector on the left of the boundary there
   would reach to the right of every vertex, where the winding number is `0`.
2. A diagonal (`IsSimple.exists_diagonal`). If the convex vertex `v` is an ear,
   the segment joining its neighbours is one (`IsEar.isDiagonal`). If not,
   some other vertex lies in its closed ear triangle `u v w`; of those, the
   one farthest from the line `u w` gives a diagonal from `v`
   (`ConvexVertex.exists_isDiagonal`). The triangle cut off at `v` by the
   parallel to `u w` just below a point of that segment holds no other vertex,
   so an edge crossing the segment would have to enter and leave it through
   its side on the parallel, which a segment cannot do.
3. A diagonal cuts off a chain with fewer vertices (`Polygon/Diagonal.lean`),
   simple and winding `0` or `1` times, whose open region lies in that of the
   polygon. A diagonal of the chain gives, on its side away from the closing
   segment, a diagonal of the polygon cutting off fewer steps. So by strong
   induction a chain of two steps is reached, and its middle vertex is an ear
   (`IsDiagonal.exists_ear`). Both sides of one diagonal give an ear each,
   and the ear triangles lie in the disjoint open regions of the two sides.
-/

namespace ComputationalGeometry

open Set Point2D Filter Topology

namespace RawPolygon

variable {P : RawPolygon}

/-! ## A convex vertex -/

/-- A vertex with the largest `x`, and among those the largest `y`. -/
theorem exists_lex_max (h : 0 < P.n) : ∃ v, ∀ j, (P.vertex j).x ≤ (P.vertex v).x ∧
    ((P.vertex j).x = (P.vertex v).x → (P.vertex j).y ≤ (P.vertex v).y) := by
  have : Nonempty (Fin P.n) := ⟨⟨0, h⟩⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => (P.vertex j).x)
    Finset.univ_nonempty
  obtain ⟨v, hv, hvmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun j => (P.vertex j).x = (P.vertex i₀).x) (fun j => (P.vertex j).y)
    ⟨i₀, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hvmax
  exact ⟨v, fun j => ⟨by rw [hv]; exact hi₀ j (Finset.mem_univ _),
    fun hj => hvmax j (hj.trans hv)⟩⟩

theorem prev_ne_self (h3 : 3 ≤ P.n) (v : Fin P.n) : P.prev v ≠ v := by
  intro e
  apply P.iterate_next_ne v (k := 1) one_pos (by omega)
  calc P.next v = P.next (P.prev v) := by rw [e]
    _ = v := P.next_prev v

theorem next_ne_self (h3 : 3 ≤ P.n) (v : Fin P.n) : P.next v ≠ v :=
  P.iterate_next_ne v (k := 1) one_pos (by omega)

/-- A simple polygon that winds `0` or `1` times turns left at some vertex:
at the vertex with the largest `x`, and among those the largest `y`. -/
theorem IsSimple.exists_convexVertex (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    ∃ i, P.ConvexVertex i := by
  have h3 := hP.three_le
  obtain ⟨v, hv⟩ := exists_lex_max (P := P) (by omega)
  refine ⟨v, ?_⟩
  have hu : P.prevVertex v ≠ P.vertex v := fun e => prev_ne_self h3 v (hP.vertex_injective e)
  have hw : P.nextVertex v ≠ P.vertex v := fun e => next_ne_self h3 v (hP.vertex_injective e)
  -- Coordinates relative to `v`.
  set ax := (P.prevVertex v).x - (P.vertex v).x
  set ay := (P.prevVertex v).y - (P.vertex v).y
  set bx := (P.nextVertex v).x - (P.vertex v).x
  set by' := (P.nextVertex v).y - (P.vertex v).y
  have hax : ax ≤ 0 := by have := (hv (P.prev v)).1; simp only [ax, prevVertex]; linarith
  have hbx : bx ≤ 0 := by have := (hv (P.next v)).1; simp only [bx, nextVertex]; linarith
  have hay : ax = 0 → ay < 0 := by
    intro h0
    have h1 := (hv (P.prev v)).2 (by simp only [ax, prevVertex] at h0 ⊢; linarith)
    rcases (show ay ≤ 0 by simp only [ay, prevVertex]; linarith).lt_or_eq with h | h
    · exact h
    · exact absurd (Point2D.ext_iff'.mpr ⟨by linarith, by linarith⟩) hu
  have hby : bx = 0 → by' < 0 := by
    intro h0
    have h1 := (hv (P.next v)).2 (by simp only [bx, nextVertex] at h0 ⊢; linarith)
    rcases (show by' ≤ 0 by simp only [by', nextVertex]; linarith).lt_or_eq with h | h
    · exact h
    · exact absurd (Point2D.ext_iff'.mpr ⟨by linarith, by linarith⟩) hw
  have ho : orient (P.prevVertex v) (P.vertex v) (P.nextVertex v) = ay * bx - ax * by' := by
    simp only [ax, ay, bx, by', orient_def]; ring
  rcases lt_trichotomy 0 (orient (P.prevVertex v) (P.vertex v) (P.nextVertex v)) with h | h | h
  · exact h
  · -- Going straight on, one neighbour would be on the other side.
    exfalso
    have hd := hP.dot_pos_of_locallyDegenerate (i := v) h.symm
    have hd' : ax * bx + ay * by' < 0 := by
      simp only [ax, ay, bx, by', x_sub, y_sub] at hd ⊢; linarith
    rw [ho] at h
    rcases lt_trichotomy ay 0 with h₁ | h₁ | h₁
    · have hb : 0 < by' := by nlinarith [mul_nonneg_of_nonpos_of_nonpos hax hbx]
      have hb' : bx < 0 := lt_of_le_of_ne hbx (fun e => absurd (hby e) (not_lt.mpr hb.le))
      nlinarith [mul_pos_of_neg_of_neg h₁ hb']
    · rw [h₁, zero_mul, add_zero] at hd'; linarith [mul_nonneg_of_nonpos_of_nonpos hax hbx]
    · have ha' : ax < 0 := lt_of_le_of_ne hax (fun e => absurd (hay e) (not_lt.mpr h₁.le))
      have hb : by' < 0 := by nlinarith [mul_nonneg_of_nonpos_of_nonpos hax hbx]
      nlinarith [mul_pos_of_neg_of_neg ha' hb]
  · -- Turning right, the sector on the left reaches past every vertex.
    exfalso
    obtain ⟨L, -, hiff, -, hsec, -⟩ := hP.exists_side_values
    have hL := hiff.mp hJ
    obtain ⟨r, hr, hr0⟩ := ((hsec v).and self_mem_nhdsWithin).exists
    have hr0 : (0 : ℝ) < r := hr0
    set q := Point2D.mk ((P.vertex v).x + r / 2) (P.vertex v).y
    have hq : q ∈ P.leftSector v r := by
      simp only [leftSector, mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · refine lt_of_le_of_lt (dist_le_abs_add_abs q (P.vertex v)) ?_
        simp only [q, Point2D.x_mk, Point2D.y_mk, add_sub_cancel_left, sub_self, abs_zero,
          add_zero, abs_of_pos (half_pos hr0)]
        linarith
      · split_ifs with hc
        · exact absurd hc (not_le.mpr h)
        have h₁ : orient (P.prevVertex v) (P.vertex v) q = ay * (r / 2) := by
          simp only [q, ay, orient_def, Point2D.x_mk, Point2D.y_mk]; ring
        have h₂ : orient (P.vertex v) (P.nextVertex v) q = -(by' * (r / 2)) := by
          simp only [q, by', orient_def, Point2D.x_mk, Point2D.y_mk]; ring
        rw [h₁, h₂, ho] at *
        by_contra hc
        simp only [not_or, not_lt] at hc
        have hay' : ay ≤ 0 := by nlinarith [hc.1]
        have hby' : 0 ≤ by' := by nlinarith [hc.2]
        nlinarith [mul_nonneg_of_nonpos_of_nonpos hay' hbx, mul_nonpos_of_nonpos_of_nonneg hax hby']
    have h0 := P.windingNumber_eq_zero_of_right (p := q) fun j => by
      simp only [q, Point2D.x_mk]; linarith [(hv j).1]
    rw [hr q hq] at h0
    omega

/-! ## Diagonals at a convex vertex -/

/-- Two different edges of a simple polygon meet only at a vertex they share. -/
theorem IsSimple.eq_of_mem_edge_inter (hP : P.IsSimple) {j l : Fin P.n} (hjl : j ≠ l)
    {y : Point2D} (hj : y ∈ (P.edge j).toSet) (hl : y ∈ (P.edge l).toSet) :
    (P.next j = l ∧ y = P.vertex l) ∨ (P.next l = j ∧ y = P.vertex j) := by
  by_cases h₁ : P.next j = l
  · subst h₁
    have := (hP.adjacent_inter j).subset ⟨hj, hl⟩
    exact Or.inl ⟨rfl, this⟩
  by_cases h₂ : P.next l = j
  · subst h₂
    have := (hP.adjacent_inter l).subset ⟨hl, hj⟩
    exact Or.inr ⟨rfl, this⟩
  exact absurd (hP.nonadjacent_disjoint j l hjl h₁ h₂) (Set.not_disjoint_iff.mpr ⟨y, hj, hl⟩)

/-- The diagonal of an ear runs in the open region of a simple polygon that
winds `0` or `1` times. -/
theorem IsEar.openSegment_subset_openRegion (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n}
    (h : P.IsEar i) (hJ : P.WindsZeroOrOne) :
    openSegment ℝ (P.prevVertex i) (P.nextVertex i) ⊆ P.openRegion := by
  intro x hx
  have hb : ¬ P.OnBoundary x := fun hb =>
    Set.eq_empty_iff_forall_notMem.mp (h.earDiagonal_relInterior_inter_boundary hP h4) x ⟨hx, hb⟩
  refine ⟨hb, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hx
  obtain rfl : α = 1 - β := by linarith
  set A := P.prevVertex i
  set B := P.vertex i
  set C := P.nextVertex i
  have hD : 0 < orient A B C := h.convex
  set x := (1 - β) • A + β • C
  have hγ : Tendsto (fun ε : ℝ => x + ε • (B - x)) (𝓝[>] 0) (𝓝 x) := by
    have : Continuous fun ε : ℝ => x + ε • (B - x) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Moving from the diagonal towards the vertex enters the ear triangle.
  have hin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), x + ε • (B - x) ∈ interior (P.earTriangle i).toSet := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    rw [Triangle.mem_interior_toSet_iff h.isCCW]
    have e₁ : orient A B (x + ε • (B - x)) = (1 - ε) * β * orient A B C := by
      simp only [x, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have e₂ : orient B C (x + ε • (B - x)) = (1 - ε) * (1 - β) * orient A B C := by
      simp only [x, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have e₃ : orient C A (x + ε • (B - x)) = ε * orient A B C := by
      simp only [x, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have h1ε : 0 < 1 - ε := by linarith [hε.2]
    have h1β : 0 < 1 - β := by linarith
    refine ⟨?_, ?_, ?_⟩
    · show 0 < orient A B _; rw [e₁]; positivity
    · show 0 < orient B C _; rw [e₂]; positivity
    · show 0 < orient C A _; rw [e₃]; exact mul_pos hε.1 hD
  obtain ⟨ε, h₁, h₂⟩ := ((hγ.eventually (P.windingNumber_eventually_eq hb)).and hin).exists
  rw [← h₁, h.windingNumber_eq_one hP h4 hJ h₂]
  exact one_ne_zero

/-- The diagonal of an ear is a diagonal. -/
theorem IsEar.isDiagonal (hP : P.IsSimple) (h4 : 4 ≤ P.n) {i : Fin P.n} (h : P.IsEar i)
    (hJ : P.WindsZeroOrOne) : P.IsDiagonal (P.prev i) 2 where
  two_le := le_rfl
  add_two_le := h4
  openSegment_subset := by
    show openSegment ℝ (P.vertex (P.prev i)) (P.vertex (P.next (P.next (P.prev i)))) ⊆ _
    rw [next_prev]
    exact h.openSegment_subset_openRegion hP h4 hJ

/-- `n - 1` steps on is the previous vertex. -/
theorem iterate_next_pred (h : 0 < P.n) (v : Fin P.n) : P.next^[P.n - 1] v = P.prev v := by
  apply P.next_injective
  rw [next_prev, ← Function.iterate_succ_apply' P.next, Nat.succ_eq_add_one,
    Nat.sub_add_cancel h, iterate_next_n]

/-- At a convex vertex that is not an ear, a diagonal starts: to the vertex in
the closed ear triangle farthest from the line through the two neighbours. -/
theorem ConvexVertex.exists_isDiagonal (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) (h4 : 4 ≤ P.n)
    {v : Fin P.n} (hv : P.ConvexVertex v) (hne : ¬ P.IsEar v) : ∃ k, P.IsDiagonal v k := by
  classical
  set u := P.prevVertex v with hu
  set B := P.vertex v with hB
  set w := P.nextVertex v with hw
  set D := orient u B w
  have hD : 0 < D := hv
  set T := P.earTriangle v
  have hT : T.IsCCW := hv
  -- The vertices other than `v` and its neighbours in the closed ear triangle.
  set C := Finset.univ.filter fun j =>
    j ≠ P.prev v ∧ j ≠ v ∧ j ≠ P.next v ∧ P.vertex j ∈ T.toSet
  have hC : C.Nonempty := by
    by_contra hC
    apply hne
    refine ⟨hv, fun j h₁ h₂ h₃ hj => hC ⟨j, ?_⟩⟩
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h₁, h₂, h₃, hj⟩
  obtain ⟨z, hzC, hzmax⟩ := Finset.exists_max_image C (fun j => orient w u (P.vertex j)) hC
  simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hzC hzmax
  obtain ⟨hz₁, hz₂, hz₃, hzT⟩ := hzC
  set Z := P.vertex z
  have hzT' := (Triangle.mem_toSet_iff_containsTest hT Z).mp hzT
  obtain ⟨hzα, hzβ, hzg⟩ := hzT'
  change 0 ≤ orient u B Z at hzα
  change 0 ≤ orient B w Z at hzβ
  change 0 ≤ orient w u Z at hzg
  -- `z` is off the two edges at `v`.
  have hα : 0 < orient u B Z := by
    refine lt_of_le_of_ne hzα fun e => ?_
    have hs : Z ∈ segment ℝ u B :=
      (Triangle.mem_segment_iff_of_isCCW hT Z).mpr ⟨e.symm, hzβ, hzg⟩
    have hs' : Z ∈ (P.edge (P.prev v)).toSet := by
      rw [edge_toSet, next_prev]; exact hs
    rcases hP.vertex_mem_edge hs' with e' | e'
    · exact hz₁ e'.symm
    · rw [next_prev] at e'; exact hz₂ e'.symm
  have hβ : 0 < orient B w Z := by
    refine lt_of_le_of_ne hzβ fun e => ?_
    have hs : Z ∈ segment ℝ B w :=
      (Triangle.mem_segment_iff_of_isCCW (T := T.rotate) (Triangle.isCCW_rotate.mpr hT) Z).mpr
        ⟨e.symm, hzg, hzα⟩
    have hs' : Z ∈ (P.edge v).toSet := by rw [edge_toSet]; exact hs
    rcases hP.vertex_mem_edge hs' with e' | e'
    · exact hz₂ e'.symm
    · exact hz₃ e'.symm
  have hsum := T.orient_sum Z
  change orient B w Z + orient w u Z + orient u B Z = D at hsum
  have hgD : orient w u Z < D := by linarith
  -- The index of `z`.
  obtain ⟨k, hk, hkz⟩ := exists_iterate_next_eq v z
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · exact absurd hkz.symm hz₂
      · exact absurd hkz.symm hz₃
    · exact h
  have hkn : k + 2 ≤ P.n := by
    by_contra h
    have : k = P.n - 1 := by omega
    rw [this, iterate_next_pred (by omega)] at hkz
    exact hz₁ hkz.symm
  refine ⟨k, hk2, hkn, ?_⟩
  rw [hkz]
  change openSegment ℝ B Z ⊆ P.openRegion
  -- Along the segment from `v` to `z`.
  have hpt : ∀ s : ℝ, orient u B ((1 - s) • B + s • Z) = s * orient u B Z ∧
      orient B w ((1 - s) • B + s • Z) = s * orient B w Z ∧
      orient w u ((1 - s) • B + s • Z) = (1 - s) * D + s * orient w u Z := by
    intro s
    refine ⟨?_, ?_, ?_⟩ <;> simp only [D, orient_def, x_add, y_add, x_smul, y_smul] <;> ring
  -- The open segment avoids the boundary.
  have hoff : ∀ x ∈ openSegment ℝ B Z, ¬ P.OnBoundary x := by
    rintro x ⟨a', s, ha', hs, has, rfl⟩ ⟨j, hj⟩
    obtain rfl : a' = 1 - s := by linarith
    obtain ⟨hxα, hxβ, hxg⟩ := hpt s
    have hs1 : s < 1 := by linarith
    by_cases hj₁ : j = P.prev v
    · rw [hj₁] at hj
      have := Segment.orient_eq_zero_of_mem _ hj
      simp only [edge, next_prev] at this
      change orient u B _ = 0 at this
      rw [hxα] at this
      exact (mul_pos hs hα).ne' this
    by_cases hj₂ : j = v
    · rw [hj₂] at hj
      have := Segment.orient_eq_zero_of_mem _ hj
      simp only [edge] at this
      change orient B w _ = 0 at this
      rw [hxβ] at this
      exact (mul_pos hs hβ).ne' this
    -- The small triangle cut off at `v` by a parallel to `u w`.
    set x := (1 - s) • B + s • Z
    set c := (orient w u Z + orient w u x) / 2
    have hgx : orient w u Z < orient w u x := by rw [hxg]; nlinarith
    have hc0 : 0 < c := by simp only [c]; linarith
    have hcx : c < orient w u x := by simp only [c]; linarith
    have hcZ : orient w u Z < c := by simp only [c]; linarith
    have hxD : orient w u x < D := by rw [hxg]; nlinarith
    set l := 1 - c / D
    have hcD : (1 - l) * D = c := by simp only [l]; field_simp; ring
    have hl0 : 0 < l := by
      simp only [l]; rw [sub_pos, div_lt_one hD]; linarith
    have hl1 : l < 1 := by simp only [l]; have := div_pos hc0 hD; linarith
    set uc := B + l • (u - B)
    set wc := B + l • (w - B)
    set T' : Triangle := ⟨uc, B, wc⟩
    have i₁ : ∀ p, orient uc B p = l * orient u B p := fun p => by
      simp only [uc, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have i₂ : ∀ p, orient B wc p = l * orient B w p := fun p => by
      simp only [wc, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have i₃ : ∀ p, orient wc uc p = l * (orient w u p - (1 - l) * D) := fun p => by
      simp only [uc, wc, D, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
    have hT' : T'.IsCCW := by
      show 0 < orient uc B wc
      rw [i₁]
      have : orient u B wc = l * D := by
        simp only [wc, D, orient_def, x_add, y_add, x_smul, y_smul, x_sub, y_sub]; ring
      rw [this]; positivity
    have memT' : ∀ p, p ∈ T'.toSet ↔
        0 ≤ orient u B p ∧ 0 ≤ orient B w p ∧ c ≤ orient w u p := by
      intro p
      rw [Triangle.mem_toSet_iff_containsTest hT']
      show 0 ≤ orient uc B p ∧ 0 ≤ orient B wc p ∧ 0 ≤ orient wc uc p ↔ _
      rw [i₁, i₂, i₃, hcD, mul_nonneg_iff_of_pos_left hl0, mul_nonneg_iff_of_pos_left hl0,
        mul_nonneg_iff_of_pos_left hl0, sub_nonneg]
    have hxT' : x ∈ T'.toSet := (memT' x).mpr ⟨by rw [hxα]; positivity,
      by rw [hxβ]; positivity, hcx.le⟩
    -- No vertex but `v` is in the small triangle.
    have hgu : orient w u u = 0 := by simp
    have hgw : orient w u w = 0 := by simp
    have hnot : ∀ m, m ≠ v → P.vertex m ∉ T'.toSet := by
      intro m hm hmT
      obtain ⟨h₁, h₂, h₃⟩ := (memT' _).mp hmT
      by_cases hm₁ : m = P.prev v
      · subst hm₁; change c ≤ orient w u u at h₃; rw [hgu] at h₃; linarith
      by_cases hm₃ : m = P.next v
      · subst hm₃; change c ≤ orient w u w at h₃; rw [hgw] at h₃; linarith
      have hmT : P.vertex m ∈ T.toSet :=
        (Triangle.mem_toSet_iff_containsTest hT _).mpr ⟨h₁, h₂, by
          show 0 ≤ orient w u _; linarith⟩
      have := hzmax m ⟨hm₁, hm, hm₃, hmT⟩
      linarith
    have hnext : P.next j ≠ v := fun e => hj₁ (by rw [← e, prev_next])
    have hsub₁ : segment ℝ uc B ⊆ segment ℝ u B := by
      refine (convex_segment u B).segment_subset ?_ (right_mem_segment ℝ u B)
      refine ⟨l, 1 - l, hl0.le, by linarith, by ring, ?_⟩
      simp only [uc]; apply Point2D.ext <;> simp only [x_add, y_add, x_smul, y_smul, x_sub, y_sub] <;>
        ring
    have hsub₂ : segment ℝ B wc ⊆ segment ℝ B w := by
      refine (convex_segment B w).segment_subset (left_mem_segment ℝ B w) ?_
      refine ⟨1 - l, l, by linarith, hl0.le, by ring, ?_⟩
      simp only [wc]; apply Point2D.ext <;> simp only [x_add, y_add, x_smul, y_smul, x_sub, y_sub] <;>
        ring
    have hdisj := Triangle.disjoint_toSet_of_avoid hT' (u := P.vertex j) (w := P.vertex (P.next j))
      (hnot j hj₂) (hnot _ hnext)
      (by
        rw [Set.disjoint_left]
        intro y hy₁ hy₂
        have hyT : y ∈ T'.toSet := Triangle.segment_subset_toSet (by simp [T']) (by simp [T']) hy₂
        have hy₂' : y ∈ (P.edge (P.prev v)).toSet := by
          rw [edge_toSet, next_prev]; exact hsub₁ hy₂
        rcases hP.eq_of_mem_edge_inter hj₁ hy₁ hy₂' with ⟨-, rfl⟩ | ⟨e, -⟩
        · have := ((memT' _).mp hyT).2.2
          change c ≤ orient w u u at this
          rw [hgu] at this
          linarith
        · rw [next_prev] at e; exact hj₂ e.symm)
      (by
        rw [Set.disjoint_left]
        intro y hy₁ hy₂
        have hyT : y ∈ T'.toSet := Triangle.segment_subset_toSet (by simp [T']) (by simp [T']) hy₂
        have hy₂' : y ∈ (P.edge v).toSet := by rw [edge_toSet]; exact hsub₂ hy₂
        rcases hP.eq_of_mem_edge_inter hj₂ hy₁ hy₂' with ⟨e, -⟩ | ⟨e, rfl⟩
        · exact hj₁ (by rw [← e, prev_next])
        · have := ((memT' _).mp hyT).2.2
          rw [← e] at this
          change c ≤ orient w u w at this
          rw [hgw] at this
          linarith)
    exact Set.disjoint_left.mp hdisj hj hxT'
  -- Near `v` the segment is in the sector on the left, where the winding number is `1`.
  obtain ⟨L, -, hiff, -, hsec, -⟩ := hP.exists_side_values
  have hL := hiff.mp hJ
  obtain ⟨r, hr, hr0⟩ := ((hsec v).and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hr0
  have hγ : Tendsto (fun t : ℝ => (1 - t) • B + t • Z) (𝓝[>] 0) (𝓝 B) := by
    have : Continuous fun t : ℝ => (1 - t) • B + t • Z := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht₁, ht₃⟩ := ((hγ.eventually (Metric.ball_mem_nhds B hr0)).and
    ((Ioo_mem_nhdsGT one_pos))).exists
  have hq : (1 - t) • B + t • Z ∈ P.leftSector v r := by
    simp only [leftSector, mem_ofPred_eq]
    refine ⟨Metric.mem_ball.mp ht₁, ?_⟩
    split_ifs with hc
    swap; · exact absurd hD.le hc
    obtain ⟨e₁, e₂, -⟩ := hpt t
    exact ⟨by rw [e₁]; exact mul_pos ht₃.1 hα, by rw [e₂]; exact mul_pos ht₃.1 hβ⟩
  have hqseg : (1 - t) • B + t • Z ∈ openSegment ℝ B Z :=
    ⟨1 - t, t, by linarith [ht₃.2], ht₃.1, by ring, rfl⟩
  intro x hx
  refine ⟨hoff x hx, ?_⟩
  rw [P.windingNumber_eq_of_isPreconnected (convex_openSegment B Z).isPreconnected hoff hx hqseg,
    hr _ hq, hL]
  exact one_ne_zero

/-- A simple polygon with at least four vertices that winds `0` or `1` times
has a diagonal. -/
theorem IsSimple.exists_diagonal (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) (h4 : 4 ≤ P.n) :
    ∃ i k, P.IsDiagonal i k := by
  obtain ⟨v, hv⟩ := hP.exists_convexVertex hJ
  by_cases he : P.IsEar v
  · exact ⟨_, _, he.isDiagonal hP h4 hJ⟩
  · obtain ⟨k, hk⟩ := hv.exists_isDiagonal hP hJ h4 he
    exact ⟨v, k, hk⟩

/-! ## Ears inside a chain -/

/-- A chain of two steps is the ear triangle of its middle vertex. -/
theorem chain_two_eq (i : Fin P.n) : P.chain i 2 = (P.earTriangle (P.next i)).toPolygon := by
  unfold chain Triangle.toPolygon
  congr 1
  funext m
  fin_cases m <;> simp [earTriangle, prevVertex, nextVertex]

/-- The middle vertex of a chain of two steps cut off by a diagonal is an ear. -/
theorem IsDiagonal.isEar_two (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) {i : Fin P.n}
    (hD : P.IsDiagonal i 2) : P.IsEar (P.next i) := by
  set T := P.earTriangle (P.next i)
  have hQ := hD.isSimple_chain hP
  have hQJ := hD.windsZeroOrOne_chain hP hJ
  rw [chain_two_eq] at hQ hQJ
  have hTa : T.a = P.vertex i := by simp [T, earTriangle, prevVertex]
  -- The triangle is not flat, the chain being simple.
  have hnd : T.signedArea2 ≠ 0 := by
    have hab : T.a ≠ T.b := by
      rw [hTa]; exact fun e => next_ne_self hP.three_le i (hP.vertex_injective e).symm
    obtain ⟨m, hm⟩ := not_forall.mp (hQ.not_forall_orient_eq_zero hab)
    fin_cases m
    · exact (hm (by show orient T.a T.b T.a = 0; simp)).elim
    · exact (hm (by show orient T.a T.b T.b = 0; simp)).elim
    · exact hm
  have hpos : 0 ≤ T.signedArea2 := by
    have := hQJ.signedArea2_nonneg
    rwa [Triangle.signedArea2_toPolygon] at this
  have hT : T.IsCCW := lt_of_le_of_ne hpos (Ne.symm hnd)
  refine ⟨hT, fun j h₁ h₂ h₃ hj => ?_⟩
  rw [prev_next] at h₁
  by_cases hint : P.vertex j ∈ interior T.toSet
  · have h₀ := (Triangle.mem_openRegion_toPolygon_iff_of_isCCW hT).mpr hint
    rw [← chain_two_eq] at h₀
    exact (hD.openRegion_chain_subset hP hJ h₀).1 (P.onBoundary_vertex j)
  have hfr : P.vertex j ∈ frontier T.toSet := ⟨subset_closure hj, hint⟩
  rcases (Triangle.mem_frontier_toSet_iff_edges hT _).mp hfr with h | h | h
  · have h' : P.vertex j ∈ (P.edge i).toSet := by
      rw [edge_toSet]; simpa [T, earTriangle, prevVertex, nextVertex] using h
    rcases hP.vertex_mem_edge h' with e | e
    · exact h₁ e.symm
    · exact h₂ e.symm
  · have h' : P.vertex j ∈ (P.edge (P.next i)).toSet := by
      rw [edge_toSet]; simpa [T, earTriangle, prevVertex, nextVertex] using h
    rcases hP.vertex_mem_edge h' with e | e
    · exact h₂ e.symm
    · exact h₃ e.symm
  · have h' : P.vertex j ∈ segment ℝ (P.vertex i) (P.vertex (P.next^[2] i)) := by
      rw [segment_symm]; simpa [T, earTriangle, prevVertex, nextVertex] using h
    rcases hD.eq_or_eq_of_onBoundary h' (P.onBoundary_vertex j) with e | e
    · exact h₁ (hP.vertex_injective e)
    · exact h₃ (hP.vertex_injective e)

/-- Inside the chain cut off by a diagonal there is an ear: strictly between
the ends of the diagonal. -/
theorem IsDiagonal.exists_ear (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) :
    ∀ {k : ℕ} {i : Fin P.n}, P.IsDiagonal i k → ∃ m, 0 < m ∧ m < k ∧ P.IsEar (P.next^[m] i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i hD
  rcases hD.two_le.eq_or_lt with h2 | h2
  · subst h2
    exact ⟨1, one_pos, by omega, hD.isEar_two hP hJ⟩
  -- A diagonal of the chain, on the side away from the closing segment.
  set Q := P.chain i k
  have hQ := hD.isSimple_chain hP
  have hQJ := hD.windsZeroOrOne_chain hP hJ
  obtain ⟨a, l, hDQ⟩ := hQ.exists_diagonal hQJ (by simp only [chain_n]; omega)
  obtain ⟨a', l', hDQ', hfit⟩ : ∃ a' l', Q.IsDiagonal a' l' ∧ a'.val + l' ≤ k := by
    by_cases hfit : a.val + l ≤ k
    · exact ⟨a, l, hDQ, hfit⟩
    · refine ⟨_, _, hDQ.symm, ?_⟩
      have ha := a.isLt
      have hl := hDQ.add_two_le
      have hv := val_iterate_next (P.chain i k) a l
      simp only [Q, chain_n] at ha hl hv ⊢
      rw [hv, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  have hl' := hDQ'.add_two_le
  simp only [Q, chain_n] at hl'
  -- It is a diagonal of the polygon, cutting off fewer steps.
  have hPD : P.IsDiagonal (P.next^[a'.val] i) l' := by
    refine ⟨hDQ'.two_le, by have := hD.add_two_le; omega, ?_⟩
    have e₂ : Q.vertex (Q.next^[l'] a') = P.vertex (P.next^[l'] (P.next^[a'.val] i)) := by
      have hv := val_iterate_next Q a' l'
      change _ = (a'.val + l') % (k + 1) at hv
      rw [chain_vertex, hv, Nat.mod_eq_of_lt (by omega), ← iterate_next_add, Nat.add_comm]
    rw [show P.vertex (P.next^[a'.val] i) = Q.vertex a' from rfl, ← e₂]
    exact hDQ'.openSegment_subset.trans (hD.openRegion_chain_subset hP hJ)
  obtain ⟨m', hm'0, hm'l, hear⟩ := ih l' (by omega) hPD
  refine ⟨m' + a'.val, by omega, by omega, ?_⟩
  rwa [iterate_next_add]

/-! ## Ears of the polygon as ears of a chain -/

section ChainEar

variable {i : Fin P.n} {k m : ℕ}

theorem chain_val_next_of_lt (x : Fin (P.chain i k).n) (hx : x.val < k) :
    ((P.chain i k).next x).val = x.val + 1 := by
  rw [chain_val_next]; exact Nat.mod_eq_of_lt (by omega)

theorem chain_val_prev_of_pos (x : Fin (P.chain i k).n) (hx0 : 0 < x.val) :
    ((P.chain i k).prev x).val = x.val - 1 := by
  have hx := x.isLt
  simp only [chain_n] at hx
  have : (P.chain i k).next ⟨x.val - 1, by simp only [chain_n]; omega⟩ = x :=
    Fin.ext (by rw [chain_val_next_of_lt _ (by show x.val - 1 < k; omega)]; show x.val - 1 + 1 = _; omega)
  calc ((P.chain i k).prev x).val
      = ((P.chain i k).prev ((P.chain i k).next ⟨x.val - 1, by simp only [chain_n]; omega⟩)).val := by
        rw [this]
    _ = x.val - 1 := by rw [prev_next]

theorem iterate_next_pred_of_pos (hm0 : 0 < m) : P.prev (P.next^[m] i) = P.next^[m - 1] i := by
  rw [← Nat.sub_add_cancel hm0, Function.iterate_succ_apply', prev_next, Nat.add_sub_cancel]

/-- At an inner vertex, the ear triangle of a chain is that of the polygon. -/
theorem chain_earTriangle (hm0 : 0 < m) (hm : m < k) :
    (P.chain i k).earTriangle ⟨m, by simp only [chain_n]; omega⟩ =
      P.earTriangle (P.next^[m] i) := by
  simp only [earTriangle, prevVertex, nextVertex, chain_vertex]
  rw [chain_val_prev_of_pos _ hm0, chain_val_next_of_lt _ hm, iterate_next_pred_of_pos hm0,
    Function.iterate_succ_apply']

/-- An ear of the polygon at an inner vertex of a chain, with fewer than `n`
steps, is an ear of the chain. -/
theorem isEar_chain (hkn : k < P.n) (hm0 : 0 < m) (hm : m < k)
    (h : P.IsEar (P.next^[m] i)) :
    (P.chain i k).IsEar ⟨m, by simp only [chain_n]; omega⟩ := by
  refine ⟨?_, fun j h₁ h₂ h₃ hj => ?_⟩
  · show (P.chain i k).earTriangle _ |>.IsCCW
    rw [chain_earTriangle hm0 hm]; exact h.convex
  rw [chain_earTriangle hm0 hm, chain_vertex] at hj
  have hjk := j.isLt
  simp only [chain_n] at hjk
  refine h.empty _ (fun e => h₁ ?_) (fun e => h₂ ?_) (fun e => h₃ ?_) hj
  · rw [iterate_next_pred_of_pos hm0] at e
    have := iterate_next_inj i (by omega) (by omega) e
    ext; rw [chain_val_prev_of_pos _ hm0]; exact this
  · have := iterate_next_inj i (by omega) (by omega) e
    ext; exact this
  · rw [← Function.iterate_succ_apply' P.next] at e
    have := iterate_next_inj i (by omega) (by omega) e
    ext; rw [chain_val_next_of_lt _ hm]; exact this

/-- The ear triangle of an ear inside the chain cut off by a diagonal lies, but
for its boundary, in the open region of the chain. -/
theorem IsDiagonal.interior_earTriangle_subset (hP : P.IsSimple) (hJ : P.WindsZeroOrOne)
    (hD : P.IsDiagonal i k) (hm0 : 0 < m) (hm : m < k) (h : P.IsEar (P.next^[m] i)) :
    interior (P.earTriangle (P.next^[m] i)).toSet ⊆ (P.chain i k).openRegion := by
  rcases hD.two_le.eq_or_lt with h2 | h2
  · subst h2
    obtain rfl : m = 1 := by omega
    intro x hx
    rw [chain_two_eq]
    exact (Triangle.mem_openRegion_toPolygon_iff_of_isCCW h.isCCW).mpr hx
  · have := (isEar_chain (by have := hD.add_two_le; omega) hm0 hm h).interior_earTriangle_subset_openRegion
      (hD.isSimple_chain hP) (by simp only [chain_n]; omega) (hD.windsZeroOrOne_chain hP hJ)
    rwa [chain_earTriangle hm0 hm] at this

end ChainEar

/-! ## Two ears -/

/-- A simple polygon with at least four vertices that winds `0` or `1` times
has an ear. -/
theorem IsSimple.exists_ear (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) (h4 : 4 ≤ P.n) :
    ∃ i, P.IsEar i := by
  obtain ⟨i, k, hD⟩ := hP.exists_diagonal hJ h4
  obtain ⟨m, -, -, h⟩ := hD.exists_ear hP hJ
  exact ⟨_, h⟩

/-- Meisters' Two Ears Theorem: a simple polygon with at least four vertices
that winds `0` or `1` times has two ears whose triangles do not overlap. -/
theorem IsSimple.exists_two_nonoverlapping_ears (hP : P.IsSimple) (hJ : P.WindsZeroOrOne)
    (h4 : 4 ≤ P.n) :
    ∃ i j : Fin P.n, i ≠ j ∧ P.IsEar i ∧ P.IsEar j ∧
      Disjoint (interior (P.earTriangle i).toSet) (interior (P.earTriangle j).toSet) := by
  obtain ⟨i, k, hD⟩ := hP.exists_diagonal hJ h4
  have hn := hD.add_two_le
  obtain ⟨m₁, h₁0, h₁k, h₁⟩ := hD.exists_ear hP hJ
  obtain ⟨m₂, h₂0, h₂k, h₂⟩ := hD.symm.exists_ear hP hJ
  refine ⟨_, _, fun e => ?_, h₁, h₂, ?_⟩
  · rw [← iterate_next_add] at e
    have := iterate_next_inj i (by omega) (by omega) e
    omega
  · exact (hD.disjoint_openRegion_chain hP hJ).mono
      (hD.interior_earTriangle_subset hP hJ h₁0 h₁k h₁)
      (hD.symm.interior_earTriangle_subset hP hJ h₂0 h₂k h₂)

/-- Two different ears. -/
theorem IsSimple.exists_two_ears (hP : P.IsSimple) (hJ : P.WindsZeroOrOne) (h4 : 4 ≤ P.n) :
    ∃ i j : Fin P.n, i ≠ j ∧ P.IsEar i ∧ P.IsEar j := by
  obtain ⟨i, j, hij, hi, hj, -⟩ := hP.exists_two_nonoverlapping_ears hJ h4
  exact ⟨i, j, hij, hi, hj⟩

theorem IsSimple.exists_ear_of_isCCW (hP : P.IsSimple) (hccw : P.IsCCW) (h4 : 4 ≤ P.n) :
    ∃ i, P.IsEar i :=
  hP.exists_ear (hP.windsZeroOrOne_of_isCCW hccw) h4

theorem IsSimple.exists_two_nonoverlapping_ears_of_isCCW (hP : P.IsSimple) (hccw : P.IsCCW)
    (h4 : 4 ≤ P.n) :
    ∃ i j : Fin P.n, i ≠ j ∧ P.IsEar i ∧ P.IsEar j ∧
      Disjoint (interior (P.earTriangle i).toSet) (interior (P.earTriangle j).toSet) :=
  hP.exists_two_nonoverlapping_ears (hP.windsZeroOrOne_of_isCCW hccw) h4

end RawPolygon

namespace SimplePolygon

theorem exists_ear (P : SimplePolygon) (hJ : P.1.WindsZeroOrOne) (h4 : 4 ≤ P.1.n) :
    ∃ i, P.1.IsEar i :=
  P.2.exists_ear hJ h4

/-- Some ear, chosen without a policy, to be cut by `SimplePolygon.removeEar`. -/
noncomputable def someEar (P : SimplePolygon) (hJ : P.1.WindsZeroOrOne) (h4 : 4 ≤ P.1.n) :
    Fin P.1.n :=
  Classical.choose (P.exists_ear hJ h4)

theorem isEar_someEar (P : SimplePolygon) (hJ : P.1.WindsZeroOrOne) (h4 : 4 ≤ P.1.n) :
    P.1.IsEar (P.someEar hJ h4) :=
  Classical.choose_spec (P.exists_ear hJ h4)

theorem exists_ear_of_isCCW (P : SimplePolygon) (hccw : P.1.IsCCW) (h4 : 4 ≤ P.1.n) :
    ∃ i, P.1.IsEar i :=
  P.2.exists_ear_of_isCCW hccw h4

theorem exists_two_nonoverlapping_ears (P : SimplePolygon) (hJ : P.1.WindsZeroOrOne)
    (h4 : 4 ≤ P.1.n) :
    ∃ i j : Fin P.1.n, i ≠ j ∧ P.1.IsEar i ∧ P.1.IsEar j ∧
      Disjoint (interior (P.1.earTriangle i).toSet) (interior (P.1.earTriangle j).toSet) :=
  P.2.exists_two_nonoverlapping_ears hJ h4

theorem exists_two_nonoverlapping_ears_of_isCCW (P : SimplePolygon) (hccw : P.1.IsCCW)
    (h4 : 4 ≤ P.1.n) :
    ∃ i j : Fin P.1.n, i ≠ j ∧ P.1.IsEar i ∧ P.1.IsEar j ∧
      Disjoint (interior (P.1.earTriangle i).toSet) (interior (P.1.earTriangle j).toSet) :=
  P.2.exists_two_nonoverlapping_ears_of_isCCW hccw h4

end SimplePolygon

end ComputationalGeometry
